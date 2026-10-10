import Mathlib
import OAI.Geometry.PrescribedRicci.LocalDeterminantEquation
import OAI.Geometry.PrescribedRicci.UniformDeterminantRemainder
import OAI.Geometry.PrescribedRicci.UniformL2

namespace OAI

/-! Local Determinant Bound. -/

section

 

noncomputable section
open Set Filter Topology Matrix _root_.MeasureTheory _root_.OAI.MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap Classical Matrix.Norms.Elementwise BoundedContinuousFunction ENNReal
namespace TameInterpolation
open SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ} [Nonempty (Fin n)] {Z : Type*}
omit [Fintype ι] [Nonempty ι] in
lemma detJetRemainder_memLp (e : ι → E) (F : Fin n → Fin n → 𝓢(E,ℂ))
    (hc : ∀ i j, HasCompactSupport (F i j : E → ℂ)) (ws : List ι) :
    MemLp (detJetRemainder e (fun x i j => F i j x) ws) 2 volume := by
  have hs (σ : Equiv.Perm (Fin n)) : ∀ L : List (Fin n → List ι),
      MemLp (fun x => (L.map (fun s => monoEval e (fun i x => F (σ i) i x) s x)).sum) 2 volume := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih =>
      exact ((monoEval_smooth e _ (fun i => (F (σ i) i).smooth') a).continuous.memLp_of_hasCompactSupport
        (monoEval_compact e _ (fun i => hc (σ i) i) a)).add ih
  have hh := memLp_finsetSum Finset.univ (fun σ _ => (hs σ (monoRemainder ws)).const_mul (Equiv.Perm.sign σ : ℂ))
  convert! hh using 1

lemma detJetRemainder_uniformL2 (e : ι → E) (F : Z → Fin n → Fin n → 𝓢(E,ℂ))
    (hc : ∀ z i j, HasCompactSupport (F z i j : E → ℂ)) (ws : List ι)
    (h0 : ∀ σ : Equiv.Perm (Fin n), ∃ A : ℝ, 0 ≤ A ∧ ∀ z,
      familyJetNorm e (realComponents (initialJet e (fun i x => F z (σ i) i x))) 0 ∞ ≤ A)
    (hS : ∀ i j, UniformSobolev ((ws.length:ℝ)-1) (fun z => F z i j)) :
    UniformL2 (fun z => detJetRemainder e (fun x i j => F z i j x) ws) :=
  ⟨fun z => detJetRemainder_memLp e (F z) (hc z) ws,detJetRemainder_uniform_bound e F hc ws h0 hS⟩
end TameInterpolation

namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart FrozenPoisson MetricLocalization TameInterpolation
variable {d : ℕ} {Z : Type*}
lemma norm_trace_mul_le_sum (M N : Matrix (Fin d) (Fin d) ℂ) {B : ℝ}
    (hB : ∀ i j, ‖M i j‖ ≤ B) :
    ‖(M*N).trace‖ ≤ B*∑ i, ∑ j, ‖N j i‖ := by
  change ‖∑ i, ∑ j, M i j*N j i‖ ≤ _
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB i j) (norm_nonneg _)))

lemma determinant_word_cutoff_bound
    {ι : Type*} (e : ι → EC d) (ws : List ι) (hw : ws ≠ [])
    (κ f : 𝓢(EC d,ℂ)) (G H : Fin d → Fin d → 𝓢(EC d,ℂ))
    (ρ : 𝓢(EC d,ℂ)) (y : EC d)
    (he : ∀ i j, (H i j : EC d → ℂ) =ᶠ[𝓝 y]
      (fun x => G i j x+hessianEntrySchwartz i j f x))
    (hρ : (fun x => (show Matrix (Fin d) (Fin d) ℂ from fun i j => H i j x).det) =ᶠ[𝓝 y] ρ)
    (hinv : IsUnit (show Matrix (Fin d) (Fin d) ℂ from fun i j => H i j y).det)
    {B J K : ℝ} (hB : 0 ≤ B) (hJ : 0 ≤ J)
    (hb : ∀ i j, ‖(show Matrix (Fin d) (Fin d) ℂ from fun i j => H i j y)⁻¹ i j‖ ≤ B)
    (hj : ‖(show Matrix (Fin d) (Fin d) ℂ from fun i j => H i j y).det⁻¹‖ ≤ J)
    (hk : ‖κ y‖ ≤ K) :
    ‖(((show Matrix (Fin d) (Fin d) ℂ from fun i j => H i j y)⁻¹) *
      (show Matrix (Fin d) (Fin d) ℂ from fun i j => hessianEntrySchwartz i j
        (SchwartzMap.smulLeftCLM ℂ κ (schwartzWord (ws.map e) f)) y)).trace‖ ≤
      K*J*(‖schwartzWord (ws.map e) ρ y‖+‖detJetRemainder e (fun x i j => H i j x) ws y‖)+
      B*∑ i, ∑ j, (‖wordHessianError κ (ws.map e) j i f y‖+K*‖schwartzWord (ws.map e) (G j i) y‖) := by
  rw [determinant_word_cutoff_trace e ws hw κ f G H ρ y he hρ hinv]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [norm_mul,norm_mul]
    exact mul_le_mul (mul_le_mul hk hj (norm_nonneg _) (le_trans (norm_nonneg _) hk))
      (norm_sub_le _ _) (norm_nonneg _) (mul_nonneg (le_trans (norm_nonneg _) hk) hJ)
  · apply (norm_trace_mul_le_sum _ _ hb).trans
    apply mul_le_mul_of_nonneg_left _ hB
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    change ‖wordHessianError κ (ws.map e) j i f y-κ y*schwartzWord (ws.map e) (G j i) y‖ ≤ _
    apply (norm_sub_le _ _).trans
    apply add_le_add_right
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hk (norm_nonneg _)
end GlobalElliptic

end
end

end OAI
