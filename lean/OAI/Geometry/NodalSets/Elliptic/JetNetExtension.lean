import OAI.Geometry.NodalSets.Elliptic.NormalizedJetBounds
import OAI.Geometry.NodalSets.Waves.NetProbability

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set MeasureTheory
open scoped ContDiff ENNReal
noncomputable section

lemma normalizedRealJet_contDiff (f S : Coord → ℝ) (hf : ContDiff ℝ ∞ f)
    (hS : ContDiff ℝ ∞ S) (N : ℝ) :
    ContDiff ℝ ∞ (fun x ↦ normalizedRealJet f N (S x) x) := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 5 ↦ ℝ)).symm.toContinuousLinearMap
  have hq : ContDiff ℝ ∞ (fun x ↦ (Fin.cons (Real.exp (-N*S x)*f x)
      (fun i : Fin 4 ↦ Real.exp (-N*S x)*N⁻¹*fderiv ℝ f x (Pi.single i 1)) : Fin 5 → ℝ)) := by
    apply contDiff_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact ((contDiff_const.mul hS).exp).mul hf
    · exact (((contDiff_const.mul hS).exp).mul contDiff_const).mul (real_partial_contDiff f hf j)
  exact L.contDiff.comp hq

lemma jet_mesh_arithmetic {N : ℝ} (hN : 1 ≤ N) :
    (4*N^69)⁻¹ ≤ (N^2)⁻¹ ∧ N^13*(4*N^69)⁻¹ ≤ (N^56)⁻¹ := by
  have hp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hpow : N^2 ≤ N^69 := pow_le_pow_right₀ hN (by omega)
  constructor
  · apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    nlinarith [pow_pos hp 69]
  · have he : N^13*(4*N^69)⁻¹ = (4*N^56)⁻¹ := by field_simp
    rw [he]
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    nlinarith [pow_pos hp 56]

lemma net_failure_le_union {Ω X F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup F] (μ : Measure Ω) (t : Finset X) (E : Set X)
    (Z : Ω → X → F) (good : Set Ω) (r : ℝ)
    (happrox : ∀ a ∈ good, ∀ x ∈ E, ∃ y ∈ t, ‖Z a y-Z a x‖ ≤ r) :
    μ {a | ∃ x ∈ E, ‖Z a x‖ < r} ≤
      μ goodᶜ+μ {a | ∃ y ∈ t, ‖Z a y‖ ≤ 2*r} := by
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro a ha
  by_cases hg : a ∈ good
  · obtain ⟨x,hx,hr⟩ := ha
    obtain ⟨y,hy,hd⟩ := happrox a hg x hx
    right
    refine ⟨y,hy,?_⟩
    have h := norm_le_norm_sub_add (Z a y) (Z a x)
    linarith
  · exact Or.inl hg

end
end Yau.Geometry

end OAI
