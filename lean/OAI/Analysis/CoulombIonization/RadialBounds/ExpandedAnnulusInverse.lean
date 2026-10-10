import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.ActualBandInverseBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.ExpandedAnnulusGeometry
import OAI.Analysis.CoulombIonization.RadialBounds.PointInverseEventsCell

namespace OAI

noncomputable section

namespace CoulombAtom

section
open MeasureTheory Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior

 theorem actual_expandedAnnulus_inverse_eventually {ι : Type*} {l : Filter ι}
    {r₀ s Z lam : ι → ℝ} {y : ι → Space} {N K : ι → ℕ}
    {F : ∀ i, fermionGraph (N i)} {j : ∀ i, Fin (K i)} {B c₁ h xi δ : ℝ}
    (hB : 1 ≤ B) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hxi : 0 < xi) (hxih : xi < 2*h) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0))
    (hband : ∀ᶠ i in l, 0 < r₀ i ∧ (2:ℝ)^(j i).val*r₀ i ≤ s i ∧
      ((2:ℝ)^(j i).val*r₀ i)/2 ≤ ‖y i‖ ∧ ‖y i‖ ≤ B*((2:ℝ)^(j i).val*r₀ i))
    (hstate : ∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
      TailTiltState (Z i) (lam i) (r₀ i) (K i) (tailPolynomialThreshold (r₀ i)) δ (F i)) :
    ∀ᶠ i in l,
    (physicalObservationLaw (graphRawLaw (F i)) (K i)).real
      {z | (h+xi)/(localCellRadius (y i))^4 ≤ originalQueryField (F i) (Z i) (lam i) (r₀ i) (j i) c₁ (r₀ i) (s i) z (y i) ∧
        originalQueryDensity (F i) (r₀ i) (j i) c₁ (r₀ i) (s i) z (y i) ≤ localTFResponse h/(localCellRadius (y i))^6} <
        2*((2:ℝ)^(j i).val*r₀ i)^40 ∧
    (physicalObservationLaw (graphRawLaw (F i)) (K i)).real
      {z | originalQueryField (F i) (Z i) (lam i) (r₀ i) (j i) c₁ (r₀ i) (s i) z (y i) ≤ (h-xi)/(localCellRadius (y i))^4 ∧
        localTFResponse h/(localCellRadius (y i))^6 ≤ originalQueryDensity (F i) (r₀ i) (j i) c₁ (r₀ i) (s i) z (y i)} <
        2*((2:ℝ)^(j i).val*r₀ i)^40 := by
  let u := fun i => (2:ℝ)^(j i).val*r₀ i
  have hb : ∀ᶠ i in l, 0 < r₀ i ∧ r₀ i ≤ u i ∧ u i ≤ s i ∧
      u i/2 ≤ ‖y i‖ ∧ ‖y i‖ ≤ B*u i := by
    filter_upwards [hband] with i hi
    refine ⟨hi.1,?_,hi.2⟩
    dsimp only [u]
    exact le_mul_of_one_le_left hi.1.le (one_le_pow₀ (by norm_num))
  have hn := expandedAnnulus_inverse_numerics_eventually hB hc hcL hxi hxih hδ hs0 hb
  have hs1 := hs0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [hb,hn,hs1,hstate] with i hi hni hsi hFi
  have hui : 0 < u i := hi.1.trans_le hi.2.1
  have hsy : 0 < s i := hui.trans_le hi.2.2.1
  have hy : y i ≠ 0 := norm_pos_iff.mp (by linarith [hi.2.2.2.1])
  have hpow : tailPolynomialThreshold (r₀ i) (j i).castSucc = (u i)^40 := by
    unfold tailPolynomialThreshold
    exact min_eq_right (pow_le_one₀ hui.le (hi.2.2.1.trans hsi.le))
  have hell : dyadicObservationWidth (r₀ i) (j i) = (u i)^(101/100:ℝ) := by
    unfold dyadicObservationWidth u
    norm_num
  have hh := hFi.2.2.point_inverse_events_of_cell hFi.1 hFi.2.1 hi.1
    (tailPolynomialThreshold_pos hi.1) hc hcL hi.1 hsy hsi.le hxi hxih
    (j i).castSucc (j i) (by rfl) hy
    (by simpa only [hell] using hni.1)
    (by simpa only [Fin.val_castSucc,hpow,hell] using hni.2.1)
    (by simpa only [Fin.val_castSucc,hpow,hell] using hni.2.2.1)
    (by simpa only [Fin.val_castSucc,hpow] using hni.2.2.2)
  simpa only [Fin.val_castSucc,hpow] using hh

end
open MeasureTheory Filter Set
open scoped Topology BigOperators
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior

theorem actual_expandedAnnulus_inverse_uniform_eventually {ι : Type*} {l : Filter ι}
    {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ}
    {F : ∀ i, fermionGraph (N i)} {B c₁ h xi δ : ℝ}
    (hB : 1 ≤ B) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hxi : 0 < xi) (hxih : xi < 2*h) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0)) (hr₀ : ∀ᶠ i in l, 0 < r₀ i)
    (hstate : ∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
      TailTiltState (Z i) (lam i) (r₀ i) (K i) (tailPolynomialThreshold (r₀ i)) δ (F i)) :
    ∀ᶠ i in l, ∀ (j : Fin (K i)) (y : Space),
      (2:ℝ)^j.val*r₀ i ≤ s i →
      ((2:ℝ)^j.val*r₀ i)/2 ≤ ‖y‖ → ‖y‖ ≤ B*((2:ℝ)^j.val*r₀ i) →
      OriginalPointInverseBounds (F i) (Z i) (lam i) (r₀ i) (s i) c₁ h xi j y := by
  let A : ι → Type := fun i => {p : Fin (K i) × Space //
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
  have hh := actual_expandedAnnulus_inverse_eventually
    (F := fun q : Σ i, A i => F (π q)) (j := fun q => q.2.1.1)
    hB hc hcL hxi hxih hδ (hs0.comp ht) hb (ht.eventually hstate)
  have he := Filter.eventually_comap.mp hh
  filter_upwards [he] with i hi
  intro j y hjs hyl hyu
  exact hi ⟨i,⟨(j,y),hjs,hyl,hyu⟩⟩ rfl

theorem actual_expandedAnnulus_inverse_net_uniform_eventually {ι : Type*} {l : Filter ι}
    {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ}
    {F : ∀ i, fermionGraph (N i)} {B c₁ h xi δ : ℝ}
    (hB : 1 ≤ B) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hxi : 0 < xi) (hxih : xi < 2*h) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0)) (hr₀ : ∀ᶠ i in l, 0 < r₀ i)
    (hstate : ∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
      TailTiltState (Z i) (lam i) (r₀ i) (K i) (tailPolynomialThreshold (r₀ i)) δ (F i)) :
    ∀ᶠ i in l, ∀ (j : Fin (K i)),
      (2:ℝ)^j.val*r₀ i ≤ s i → ∀ Q : Finset Space,
      (∀ y ∈ Q, ((2:ℝ)^j.val*r₀ i)/2 ≤ ‖y‖ ∧ ‖y‖ ≤ B*((2:ℝ)^j.val*r₀ i)) →
      ∀ A : ℝ, 0 ≤ A → (Q.card:ℝ) ≤ A/((2:ℝ)^j.val*r₀ i)^3 →
      (physicalObservationLaw (graphRawLaw (F i)) (K i)).real
        (⋃ y ∈ Q, originalLowFailure (F i) (Z i) (lam i) (r₀ i) (s i) c₁ h xi j y ∪
          originalHighFailure (F i) (Z i) (lam i) (r₀ i) (s i) c₁ h xi j y) ≤
        4*A*((2:ℝ)^j.val*r₀ i)^37 := by
  filter_upwards [hr₀,actual_expandedAnnulus_inverse_uniform_eventually hB hc hcL hxi hxih hδ hs0 hr₀ hstate]
    with i hri hi
  intro j hjs Q hQ A hA hcard
  apply (original_inverse_net_union_bound Q (fun y hy => hi j y hjs (hQ y hy).1 (hQ y hy).2)).trans
  have hu : 0 < (2:ℝ)^j.val*r₀ i := mul_pos (pow_pos (by norm_num) _) hri
  calc
    _ ≤ 4*(A/((2:ℝ)^j.val*r₀ i)^3)*((2:ℝ)^j.val*r₀ i)^40 := by gcongr
    _ = _ := by field_simp

end CoulombAtom

end

end OAI
