import Mathlib
import OAI.Probability.Ballisticity.Crossings.CoordinateHitExact

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma single_step_dirac_le_hitKernel {d : ℕ} (ω : Environment d) (x : Lattice d)
    (e : Direction d) {S T : Set (Lattice d)} (hST : Disjoint S T)
    (hx : x ∈ S) (he : x+step e ∈ T) :
    ((ω x).1 e : ℝ≥0∞) • Measure.dirac (x+step e) ≤ hitKernel S T (ω,x) := by
  intro U
  have hU := (Set.to_countable U).measurableSet
  rw [Measure.smul_apply, smul_eq_mul]
  by_cases hu : x+step e ∈ U
  · rw [Measure.dirac_apply_of_mem hu, mul_one,hitKernel_apply_eq_hit hST]
    have hsub : wordCylinder x [e] ⊆ Hit S (T ∩ U) := by
      intro X hX
      apply Set.mem_iUnion.mpr
      refine ⟨1,?_,?_⟩
      · have h1 := hX 1 (by simp)
        simp only [wordPath] at h1
        simpa only [h1] using (show x+step e ∈ T ∩ U from ⟨he,hu⟩)
      · intro j hj
        have hj0 : j=0 := by omega
        subst j
        have h0 := hX 0 (by simp)
        simpa only [wordPath_zero] using h0 ▸ hx
    have hm := measure_mono (μ := quenchedKernel (ω,x)) hsub
    simpa only [quenched_wordCylinder,wordWeight,mul_one,ENNReal.ofReal_coe_nnreal] using hm
  · rw [Measure.dirac_apply' _ hU,Set.indicator_of_notMem hu,mul_zero]
    exact bot_le

lemma elliptic_single_step_le_hitKernel {d : ℕ} (ω : Environment d) (x : Lattice d)
    (e : Direction d) {κ : ℝ≥0} (hκ : κ ≤ (ω x).1 e)
    {S T : Set (Lattice d)} (hST : Disjoint S T)
    (hx : x ∈ S) (he : x+step e ∈ T) :
    (κ : ℝ≥0∞) • Measure.dirac (x+step e) ≤ hitKernel S T (ω,x) := by
  intro U
  exact (mul_le_mul_left (ENNReal.coe_le_coe.mpr hκ) ((Measure.dirac (x+step e)) U)).trans
    ((single_step_dirac_le_hitKernel ω x e hST hx he) U)

lemma hitKernel_direct_step_retention {d : ℕ} (ω : Environment d) (x : Lattice d)
    (e : Direction d) {κ : ℝ≥0} (hκ : ∀ y, κ ≤ (ω y).1 e)
    {S₁ T₁ S₂ T₂ S : Set (Lattice d)}
    (hST₁ : Disjoint S₁ T₁) (hST₂ : Disjoint S₂ T₂) (hST : Disjoint S T₂)
    (h₁ : S₁ ⊆ S) (h₂ : S₂ ⊆ S)
    (hy : ∀ᵐ y ∂hitKernel S₁ T₁ (ω,x), y ∈ S₂ ∧ y+step e ∈ T₂) :
    (κ : ℝ≥0∞) • (hitKernel S₁ T₁ (ω,x)).map (fun y => y+step e) ≤
      hitKernel S T₂ (ω,x) := by
  intro U
  have hU := (Set.to_countable U).measurableSet
  have hm : Measurable (fun y : Lattice d => y+step e) := measurable_of_countable _
  rw [Measure.smul_apply,smul_eq_mul,Measure.map_apply hm hU]
  have heq : (κ : ℝ≥0∞)*hitKernel S₁ T₁ (ω,x) ((fun y => y+step e) ⁻¹' U) =
      ∫⁻ y, ((κ : ℝ≥0∞) • Measure.dirac (y+step e)) U ∂hitKernel S₁ T₁ (ω,x) := by
    simp only [Measure.smul_apply,smul_eq_mul,Measure.dirac_apply' _ hU]
    rw [lintegral_const_mul _ (measurable_of_countable _)]
    congr 1
    rw [← lintegral_indicator_one (hm hU)]
    apply lintegral_congr
    intro y
    by_cases hy : y+step e ∈ U <;> simp [hy]
  rw [heq]
  apply le_trans _ (hitKernel_comp_le ω x hST₁ hST₂ hST h₁ h₂ U)
  apply lintegral_mono_ae
  filter_upwards [hy] with y hy
  exact (elliptic_single_step_le_hitKernel ω y e (hκ y) hST₂ hy.1 hy.2) U

lemma coordinate_hitKernel_supported {d : ℕ} (e : Direction d) (x : Lattice d)
    (H : ℕ) (ω : Environment d) :
    ∀ᵐ y ∂hitKernel (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) (ω,x),
      signedHeight e y = signedHeight e x+H := by
  rw [ae_iff,hitKernel_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro n
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
  intro hbad
  have hh : X ∈ HitAt (Strip (realPosition (step e)) x H)
      (Upper (realPosition (step e)) x H) n := ⟨hbad.1.1,hbad.2⟩
  exact hbad.1.2 (coordinate_hitAt_exact e x X h0 hnn H n hh)

lemma coordinate_hitKernel_upward_retention {d : ℕ} (e : Direction d) (x : Lattice d)
    (H : ℕ) (ω : Environment d) {κ : ℝ≥0} (hκ : ∀ y, κ ≤ (ω y).1 e) :
    (κ : ℝ≥0∞) • (hitKernel (Strip (realPosition (step e)) x H)
        (Upper (realPosition (step e)) x H) (ω,x)).map (fun y => y+step e) ≤
      hitKernel (Strip (realPosition (step e)) x (H+1))
        (Upper (realPosition (step e)) x (H+1)) (ω,x) := by
  apply hitKernel_direct_step_retention ω x e hκ (disjoint_strip_upper _ _ _)
    (disjoint_strip_upper _ _ _) (disjoint_strip_upper _ _ _) ?_ (fun _ h => h) ?_
  · intro y hy
    exact ⟨hy.1,by have := hy.2; dsimp [Strip] at *; linarith⟩
  · filter_upwards [coordinate_hitKernel_supported e x H ω] with y hy
    have hh : dot (realPosition y) (realPosition (step e)) =
        dot (realPosition x) (realPosition (step e))+(H:ℝ) := by
      simp only [signedHeight_projection]
      exact_mod_cast hy
    constructor
    · constructor
      · rw [hh]
        exact le_add_of_nonneg_right (Nat.cast_nonneg H)
      · rw [hh]
        linarith
    · change _ ≤ dot (realPosition (y+step e)) (realPosition (step e))
      rw [dot_realPosition_add,signed_direction_unit,hh]
      linarith
end DirectionalTransience

end

end

end OAI
