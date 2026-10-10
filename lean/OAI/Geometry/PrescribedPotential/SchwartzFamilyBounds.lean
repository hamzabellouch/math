import Mathlib
import OAI.Geometry.PrescribedPotential.LocalRegularity

namespace OAI

/-! Schwartz Family Bounds. -/

section

noncomputable section
open Set Filter Topology MeasureTheory TemperedDistribution
open scoped SchwartzMap ContDiff
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def schwartzCoordCLM (s : ℝ) : 𝓢(E,ℂ) →L[ℂ] L2 E :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 volume) ∘L
    SchwartzMap.fourierMultiplierCLM ℂ (fun x : E => (((1+‖x‖^2)^(s/2) : ℝ) : ℂ))

lemma schwartzCoordCLM_apply (s : ℝ) (f : 𝓢(E,ℂ)) :
    schwartzCoordCLM s f = schwartzCoord s f := by
  apply l2_injective
  change ((SchwartzMap.fourierMultiplierCLM ℂ (fun x : E => (((1+‖x‖^2)^(s/2) : ℝ) : ℂ)) f).toLp 2 : 𝓢'(E,ℂ)) = _
  rw [Lp.toTemperedDistribution_toLp_eq,Lp.toTemperedDistributionCLM_apply,← bessel_realize s,realize_schwartzCoord]
  exact (fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop) f).symm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma schwartz_family_bounded {I : Type*} (f : I → 𝓢(E,ℂ)) {K : Set E}
    (hK : IsCompact K) (hsupp : ∀ i, tsupport (f i : E → ℂ) ⊆ K)
    (hjet : ∀ m : ℕ, ∃ C : ℝ, ∀ i x, x ∈ K → ‖iteratedFDeriv ℝ m (f i) x‖ ≤ C) :
    Bornology.IsVonNBounded ℂ (Set.range f) := by
  apply (schwartz_withSeminorms ℂ E ℂ).isVonNBounded_iff_seminorm_bounded.mpr
  rintro ⟨a,m⟩
  obtain ⟨R,hR,hRK⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨C,hC⟩ := hjet m
  let B := R^a * max 0 C
  have hB : 0 ≤ B := mul_nonneg (pow_nonneg hR.le a) (le_max_left _ _)
  refine ⟨B+1,by linarith,?_⟩
  rintro _ ⟨i,rfl⟩
  apply lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℂ a m (f i) hB ?_) (by linarith)
  intro x
  by_cases hx : x ∈ K
  · exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) (hRK x hx) a)
      ((hC i x hx).trans (le_max_right _ _)) (norm_nonneg _) (pow_nonneg hR.le a)
  · have hz : iteratedFDeriv ℝ m (f i) x = 0 := Function.notMem_support.mp
      (fun ha => hx (hsupp i (support_iteratedFDeriv_subset m ha)))
    simpa [hz] using hB

lemma schwartzCoord_family_bound {I : Type*} (f : I → 𝓢(E,ℂ)) {K : Set E}
    (hK : IsCompact K) (hsupp : ∀ i, tsupport (f i : E → ℂ) ⊆ K)
    (hjet : ∀ m : ℕ, ∃ C : ℝ, ∀ i x, x ∈ K → ‖iteratedFDeriv ℝ m (f i) x‖ ≤ C)
    (s : ℝ) : ∃ C : ℝ, ∀ i, ‖schwartzCoord s (f i)‖ ≤ C := by
  have hb := (schwartz_family_bounded f hK hsupp hjet).image (schwartzCoordCLM s)
  obtain ⟨C,hC⟩ := (NormedSpace.isVonNBounded_iff' ℂ).mp hb
  exact ⟨C,fun i => by simpa only [schwartzCoordCLM_apply] using hC _ ⟨f i,⟨i,rfl⟩,rfl⟩⟩
end SobolevChart

end
end

end OAI
