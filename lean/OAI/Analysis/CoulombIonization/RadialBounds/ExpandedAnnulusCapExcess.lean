import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.ExpandedAnnulusCapNumerics
import OAI.Analysis.CoulombIonization.FieldAnalysis.ExpandedAnnulusSmallEventIntegral

namespace OAI

open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

 theorem actual_expandedAnnulus_cap_excess_eventually {ι : Type*} {l : Filter ι}
    {r₀ s Z lam : ι → ℝ} {y : ι → Space} {N K : ι → ℕ}
    {F : ∀ i, fermionGraph (N i)} {j : ∀ i, Fin (K i+1)} {B c₁ δ : ℝ} (hB : 1 ≤ B)
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0))
    (hband : ∀ᶠ i in l, 0 < r₀ i ∧ (2:ℝ)^(j i).val*r₀ i ≤ s i ∧
      ((2:ℝ)^(j i).val*r₀ i)/2 ≤ ‖y i‖ ∧ ‖y i‖ ≤ B*((2:ℝ)^(j i).val*r₀ i))
    (hstate : ∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
      OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
        (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) :
    ∀ᶠ i in l,
      (∫ z, max ((localCellRadius (y i))^4*
        originalQueryField (F i) (Z i) (lam i) (r₀ i) (j i) c₁ (r₀ i) (s i) z (y i)-
        (tfPatchCapConstant+2)) 0 ∂physicalObservationLaw (graphRawLaw (F i)) (K i)) ≤
      (tfPatchCapConstant+2)*((2:ℝ)^(j i).val*r₀ i)^60 := by
  let u := fun i => (2:ℝ)^(j i).val*r₀ i
  have hb : ∀ᶠ i in l, 0 < r₀ i ∧ r₀ i ≤ u i ∧ u i ≤ s i ∧
      u i/2 ≤ ‖y i‖ ∧ ‖y i‖ ≤ B*u i := by
    filter_upwards [hband] with i hi
    refine ⟨hi.1,?_,hi.2⟩
    dsimp only [u]
    exact le_mul_of_one_le_left hi.1.le (one_le_pow₀ (by norm_num))
  have hnum := cap_expandedAnnulus_numerics_eventually hB hc hcL hδ hs0 hb
  have hw := own_probability_expandedAnnulus_cap_uniform_eventually hB hc hδ hs0 (hb.mono fun _ hi => hi.1)
  filter_upwards [hb,hnum,hw,hstate,hs0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))]
    with i hbi hni hwi hFi hsi
  have hui : 0 < u i := hbi.1.trans_le hbi.2.1
  have hsy : 0 < s i := hui.trans_le hbi.2.2.1
  have hy : y i ≠ 0 := norm_pos_iff.mp (by linarith [hbi.2.2.2.1])
  have ha := localCellRadius_pos hy
  have hu1 := hbi.2.2.1.trans hsi.le
  let A : Set (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)) := {z | (tfPatchCapConstant+2)/(localCellRadius (y i))^4 <
    originalQueryField (F i) (Z i) (lam i) (r₀ i) (j i) c₁ (r₀ i) (s i) z (y i)}
  have hA : MeasurableSet[observationInformation
      (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) (j i)] A :=
    measurableSet_lt measurable_const
      (originalQueryField_info_measurable (F i) (Z i) (lam i) (r₀ i) (j i) hc hbi.1 hsy (y i))
  have hp := hFi.2.2.rare_cap_event_of_cell hFi.1 hFi.2.1 hbi.1 hc hcL hbi.1 hsy hsi.le
    (j i) hy hu1 hni.1 hni.2
  have hsml := hFi.2.2.expandedAnnulus_small_event_integral hFi.1 hFi.2.1 hbi.1 hc hcL hbi.1 hsy hsi.le
    (j i) hbi.2.2.2.1 hu1 hni.1
    (fun p hpp hpu => hwi (u i) (y i) p hbi.2.1 hbi.2.2.1 hbi.2.2.2.1 hbi.2.2.2.2 hpp hpu)
    A hA hp.le
  have hC : 0 ≤ tfPatchCapConstant+2 := by linarith [tfPatchCapConstant_pos]
  have hh := integral_positive_excess_le (physicalObservationLaw (graphRawLaw (F i)) (K i))
    (originalQueryField_integrable (F i) (Z i) (lam i) (r₀ i) (j i) hc hbi.1 hsy (y i))
    hC (pow_pos ha 4)
    ((observationInformation_le (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) (j i)) A hA)
  exact hh.trans hsml

theorem actual_expandedAnnulus_cap_excess_uniform_eventually {ι : Type*} {l : Filter ι}
    {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ}
    {F : ∀ i, fermionGraph (N i)} {B c₁ δ : ℝ} (hB : 1 ≤ B)
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0)) (hr₀ : ∀ᶠ i in l, 0 < r₀ i)
    (hstate : ∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
      OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
        (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) :
    ∀ᶠ i in l, ∀ (j : Fin (K i+1)) (y : Space),
      (2:ℝ)^j.val*r₀ i ≤ s i →
      ((2:ℝ)^j.val*r₀ i)/2 ≤ ‖y‖ → ‖y‖ ≤ B*((2:ℝ)^j.val*r₀ i) →
      (∫ z, max ((localCellRadius y)^4*
        originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) z y-
        (tfPatchCapConstant+2)) 0 ∂physicalObservationLaw (graphRawLaw (F i)) (K i)) ≤
      (tfPatchCapConstant+2)*((2:ℝ)^j.val*r₀ i)^60 := by
  let A : ι → Type := fun i => {p : Fin (K i+1) × Space //
    (2:ℝ)^p.1.val*r₀ i ≤ s i ∧
    ((2:ℝ)^p.1.val*r₀ i)/2 ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ B*((2:ℝ)^p.1.val*r₀ i)}
  let π : (Σ i, A i) → ι := Sigma.fst
  let L : Filter (Σ i, A i) := Filter.comap π l
  have ht : Tendsto π L l := tendsto_comap
  have hb : ∀ᶠ q in L, 0 < r₀ (π q) ∧
      (2:ℝ)^q.2.1.1.val*r₀ (π q) ≤ s (π q) ∧
      ((2:ℝ)^q.2.1.1.val*r₀ (π q))/2 ≤ ‖q.2.1.2‖ ∧
      ‖q.2.1.2‖ ≤ B*((2:ℝ)^q.2.1.1.val*r₀ (π q)) := by
    filter_upwards [ht.eventually hr₀] with q hq
    exact ⟨hq,q.2.2⟩
  have hh := actual_expandedAnnulus_cap_excess_eventually
    (F := fun q : Σ i, A i => F (π q)) (j := fun q => q.2.1.1)
    hB hc hcL hδ (hs0.comp ht) hb (ht.eventually hstate)
  have he := Filter.eventually_comap.mp hh
  filter_upwards [he] with i hi
  intro j y hjs hyl hyu
  exact hi ⟨i,⟨(j,y),hjs,hyl,hyu⟩⟩ rfl

end CoulombAtom

end

end OAI
