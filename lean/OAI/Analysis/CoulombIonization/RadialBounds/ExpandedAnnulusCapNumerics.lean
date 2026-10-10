import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.ExpandedAnnulusGeometry

namespace OAI

open Filter Set
open scoped Topology
noncomputable section
namespace CoulombAtom
open CoulombAnalysis CoulombBarrier

lemma cap_expandedAnnulus_numerics_eventually {ι : Type*} {l : Filter ι}
    {r₀ u s : ι → ℝ} {y : ι → Space} {B c₁ δ : ℝ} (hB : 1 ≤ B)
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0))
    (hband : ∀ᶠ i in l, 0 < r₀ i ∧ r₀ i ≤ u i ∧ u i ≤ s i ∧
      u i/2 ≤ ‖y i‖ ∧ ‖y i‖ ≤ B*u i) :
    ∀ᶠ i in l,
      InverseFiniteGeometry c₁ (r₀ i) (s i) ((u i)^(101/100:ℝ)) (y i) ∧
      originalFieldCapBudget (u i) ((u i)^80) δ c₁ (r₀ i) (s i) (y i)
        ((localCellRadius (y i))^(6/5:ℝ))
        (localCellRadius (y i)*(localCellRadius (y i))^masterExponent) <
          (tfPatchCapConstant+2)/(localCellRadius (y i))^4 := by
  have hr := hband.mono fun _ hi => hi.1
  have hu := hband.mono fun _ hi => hi.1.trans_le hi.2.1
  have hs := hband.mono fun _ hi => (hi.1.trans_le hi.2.1).trans_le hi.2.2.1
  have hus := hband.mono fun _ hi => hi.2.2.1
  have hyu := hband.mono fun _ hi => hi.2.2.2.2
  have hry : ∀ᶠ i in l, r₀ i ≤ 2*‖y i‖ := hband.mono fun _ hi => by
    linarith [hi.2.1,hi.2.2.2.1]
  have hu0 : Tendsto u l (𝓝 0) := squeeze_zero' (hu.mono fun _ hi => hi.le) hus hs0
  have hy : ∀ᶠ i in l, y i ≠ 0 := by
    filter_upwards [hband] with i hi
    exact norm_pos_iff.mp (by linarith [hi.1,hi.2.1,hi.2.2.2.1])
  have ha0 := fullAnnulus_local_radius_tendsto (by linarith : 0 ≤ B) hs0 hu hus hyu
  have hD := fullAnnulus_event_excess_tendsto 80 (δ := δ) (by linarith : 0 ≤ B) hu hu0 hyu
    (by norm_num [masterExponent] : masterExponent < 1/10) hδ
  have hwidth := masterWidth_relative_tendsto_half hc hr hs hs0 hry
  have ht : ∀ᶠ i in l, 0 ≤ masterWidth c₁ (r₀ i) (s i) (y i) := by
    filter_upwards [hr,hs] with i hri hsi
    exact (masterWidth_pos hc hri hsi _).le
  have hlim := physical_field_cap_tendsto hy ha0 hD ht hwidth
  have hbound := hlim.eventually (gt_mem_nhds (by linarith :
    tfPatchCapConstant < tfPatchCapConstant+2))
  have hgeom := expandedAnnulus_inverse_numerics_eventually (h := 1) (xi := 1) (δ := 0) hB hc hcL
    (by norm_num) (by norm_num) (by norm_num) hs0 hband
  filter_upwards [hy,hbound,hgeom] with i hyi hi hgi
  refine ⟨hgi.1,?_⟩
  apply (lt_div_iff₀ (pow_pos (localCellRadius_pos hyi) 4)).mpr
  change _*physicalFieldCapBudget _ _ _ _ _ < _ at hi
  simpa only [originalFieldCapBudget,physicalFieldCapBudget,mul_comm] using hi

theorem own_probability_expandedAnnulus_cap_uniform_eventually {ι : Type*} {l : Filter ι}
    {r₀ s : ι → ℝ} {B c₁ δ : ℝ} (hB : 1 ≤ B)
    (hc : 0 < c₁) (hδ : 0 ≤ δ) (hs0 : Tendsto s l (𝓝 0))
    (hr₀ : ∀ᶠ i in l, 0 < r₀ i) :
    ∀ᶠ i in l, ∀ (u : ℝ) (y : Space) (p : ℝ),
      r₀ i ≤ u → u ≤ s i → u/2 ≤ ‖y‖ → ‖y‖ ≤ B*u → 0 < p → p ≤ u^80 →
      (localCellRadius y)^4*(p*originalFieldCapBudget u p δ c₁ (r₀ i) (s i) y
        ((localCellRadius y)^(6/5:ℝ)) (localCellRadius y*(localCellRadius y)^masterExponent)) ≤
      p^(3/4:ℝ)*(tfPatchCapConstant+1) := by
  let A : ι → Type := fun i => {q : ℝ × Space × ℝ //
    r₀ i ≤ q.1 ∧ q.1 ≤ s i ∧ q.1/2 ≤ ‖q.2.1‖ ∧ ‖q.2.1‖ ≤ B*q.1 ∧
      0 < q.2.2 ∧ q.2.2 ≤ q.1^80}
  let π : (Σ i, A i) → ι := Sigma.fst
  let L : Filter (Σ i, A i) := Filter.comap π l
  have hπ : Tendsto π L l := tendsto_comap
  have hb : ∀ᶠ q in L, 0 < r₀ (π q) ∧ r₀ (π q) ≤ q.2.1.1 ∧
      q.2.1.1 ≤ s (π q) ∧ q.2.1.1/2 ≤ ‖q.2.1.2.1‖ ∧ ‖q.2.1.2.1‖ ≤ B*q.2.1.1 := by
    filter_upwards [hπ.eventually hr₀] with q hq
    exact ⟨hq,q.2.2.1,q.2.2.2.1,q.2.2.2.2.1,q.2.2.2.2.2.1⟩
  have hu0 : Tendsto (fun q : Σ i, A i => q.2.1.1) L (𝓝 0) :=
    squeeze_zero' (hb.mono fun _ h => (h.1.trans_le h.2.1).le)
      (hb.mono fun _ h => h.2.2.1) (hs0.comp hπ)
  have hp : ∀ᶠ q : Σ i, A i in L, 0 < q.2.1.2.2 :=
    Eventually.of_forall fun q => q.2.2.2.2.2.2.1
  have hp0 : Tendsto (fun q : Σ i, A i => q.2.1.2.2) L (𝓝 0) := by
    apply squeeze_zero' (hp.mono fun _ h => h.le)
      (Eventually.of_forall fun q => q.2.2.2.2.2.2.2)
    simpa using hu0.pow 80
  have hh := own_probability_expandedAnnulus_weighted_cap_eventually (by linarith : 0 ≤ B) hc hδ (hs0.comp hπ) hp hp0 hb
  have he := Filter.eventually_comap.mp hh
  filter_upwards [he] with i hi
  intro u y p hru hus hyl hyu hpv hpu
  exact hi ⟨i,⟨(u,y,p),hru,hus,hyl,hyu,hpv,hpu⟩⟩ rfl

end CoulombAtom

end

end OAI
