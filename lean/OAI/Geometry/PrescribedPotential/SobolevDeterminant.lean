import Mathlib
import OAI.Geometry.PrescribedPotential.CompletedProduct
import OAI.Geometry.PrescribedPotential.GlobalOperator
import OAI.Geometry.PrescribedPotential.PatchCutoffs

namespace OAI

/-! Sobolev Determinant. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff Classical BoundedContinuousFunction
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

def finiteProduct (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) :
    ∀ n : ℕ, (Fin n → D.localizers.Sobolev (k : ℝ)) → D.localizers.Sobolev (k : ℝ)
  | 0, _ => D.localizers.embed (k : ℝ) (Smooth.const 1)
  | n+1, f => D.product k hk (f 0) (finiteProduct k hk n (fun i => f i.succ))

lemma finiteProduct_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (n : ℕ)
    (f : Fin n → E → D.localizers.Sobolev (k : ℝ)) (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    ContDiff ℝ ∞ (fun u => D.finiteProduct k hk n (fun i => f i u)) := by
  induction n with
  | zero => exact contDiff_const
  | succ n ih =>
    exact ((D.product k hk).contDiff.comp (hf 0)).clm_apply (ih _ (fun i => hf i.succ))

lemma finiteProduct_strong (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (n : ℕ)
    (f : Fin n → D.localizers.Sobolev (k : ℝ)) (x : X) :
    D.localizers.strong (k : ℝ) (D.finiteProduct k hk n f) x =
      ∏ i, D.localizers.strong (k : ℝ) (f i) x := by
  have hs : (Module.finrank ℝ (EC d) : ℝ) < 2*(k : ℝ) := by
    have hh : (Module.finrank ℝ (EC d) : ℝ) < (k : ℝ) := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α := ℝ) k]
  induction n with
  | zero =>
    rw [finiteProduct, D.localizers.strong_embed _ hs]
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    rfl
  | succ n ih =>
    rw [finiteProduct, D.product_strong, BoundedContinuousFunction.mul_apply,
      ih, Fin.prod_univ_succ]

def determinant (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (n : ℕ)
    (M : Matrix (Fin n) (Fin n) (D.localizers.Sobolev (k : ℝ))) :
    D.localizers.Sobolev (k : ℝ) :=
  ∑ σ : Equiv.Perm (Fin n), ((↑(Equiv.Perm.sign σ) : ℤ) : ℝ) •
    D.finiteProduct k hk n (fun i => M (σ i) i)

lemma determinant_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (n : ℕ)
    (M : Fin n → Fin n → E → D.localizers.Sobolev (k : ℝ))
    (hM : ∀ i j, ContDiff ℝ ∞ (M i j)) :
    ContDiff ℝ ∞ (fun u => D.determinant k hk n (fun i j => M i j u)) := by
  apply ContDiff.sum
  intro σ _
  exact (D.finiteProduct_contDiff k hk n _ (fun i => hM (σ i) i)).const_smul _

lemma determinant_strong (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (n : ℕ)
    (M : Matrix (Fin n) (Fin n) (D.localizers.Sobolev (k : ℝ))) (x : X) :
    D.localizers.strong (k : ℝ) (D.determinant k hk n M) x =
      Matrix.det (fun i j => D.localizers.strong (k : ℝ) (M i j) x) := by
  change (Fin n → Fin n → D.localizers.Sobolev (k : ℝ)) at M
  simp only [determinant, map_sum, map_smul, BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.smul_apply]
  erw [Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  rw [D.finiteProduct_strong]
  simp only [Complex.real_smul, Complex.ofReal_intCast]

end GluingData
end GlobalElliptic

end
end

end OAI
