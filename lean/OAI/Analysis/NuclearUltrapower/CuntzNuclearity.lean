import OAI.Analysis.NuclearUltrapower.CuntzIntertwining
import OAI.Analysis.NuclearUltrapower.TensorNorms

namespace OAI

section

noncomputable section
open Filter
open scoped Topology TensorProduct
namespace NuclearUltrapower.CuntzAveraging
open CuntzUniversal
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H))

local instance : IsBoundedSMul ℂ (CuntzModel.Space ⊗[ℂ] H) := NormedSpace.toIsBoundedSMul
local instance : NormedSpace ℂ (Target H) := inferInstance

/-- The finite-level intertwining estimate extends to every star polynomial,
with no continuity assumption on a presentation of that polynomial. -/
theorem defect_polynomial_tendsto (p : CuntzPolynomial.Poly) :
    Tendsto (fun n => defect R n (inclusion p)) atTop (𝓝 0) := by
  have hl (a : CuntzPolynomial.Letter) :
      Tendsto (fun n => defect R n (inclusion (MonoidAlgebra.of ℂ CuntzPolynomial.Word
        (FreeMonoid.of a)))) atTop (𝓝 0) := by
    rcases a with ⟨i,b⟩
    cases b
    · exact defect_generator_tendsto R i
    · have hg : (MonoidAlgebra.of ℂ CuntzPolynomial.Word (FreeMonoid.of (i,true)) : CuntzPolynomial.Poly) =
          star (CuntzPolynomial.generator i) := by
        rw [CuntzPolynomial.generator,CuntzPolynomial.star_single,CuntzPolynomial.star_word_of,star_one]
        rfl
      rw [hg,map_star]
      exact defect_adjoint_tendsto R i
  have hw (w : CuntzPolynomial.Word) :
      Tendsto (fun n => defect R n (inclusion (MonoidAlgebra.of ℂ CuntzPolynomial.Word w)))
        atTop (𝓝 0) := by
    induction w using FreeMonoid.recOn with
    | one => simpa only [map_one,defect_one] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : H →L[ℂ] Target H)) atTop (𝓝 0))
    | of_mul a w ih =>
      simp only [map_mul]
      exact intertwiningDefect_tendsto_mul R amplified.toNonUnitalStarAlgHom (averaged R) (hl a) ih
  induction p using MonoidAlgebra.induction_on with
  | of w => exact hw w
  | add p q hp hq => simpa only [map_add,add_zero] using hp.add hq
  | smul c p hp => simpa only [map_smul,smul_zero] using hp.const_smul c

/-- Uniform contractivity of the averages extends polynomial intertwining to
the norm completion, rather than just its algebraic dense subalgebra. -/
theorem defect_tendsto (a : Algebra) :
    Tendsto (fun n => defect R n a) atTop (𝓝 0) := by
  apply dense_bounded_tendsto_zero (defect R) 2 (by norm_num) _ inclusion
    UniformSpace.Completion.denseRange_coe (defect_polynomial_tendsto R) a
  intro n b
  exact intertwiningDefect_bound R amplified.toNonUnitalStarAlgHom (averaged R n)
    (averaged_norm_le R n) b

end NuclearUltrapower.CuntzAveraging
end
end

section

noncomputable section
open Filter
open scoped TensorProduct Topology
namespace NuclearUltrapower
namespace CuntzAveraging
open CuntzUniversal CuntzModel

variable {C : Type} [NonUnitalCStarAlgebra C] (H : ComplexHilbert.{0})
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (S : C →⋆ₙₐ[ℂ] (H →L[ℂ] H))

local instance : IsBoundedSMul ℂ (Space ⊗[ℂ] H) := NormedSpace.toIsBoundedSMul
local instance : NormedSpace ℂ (Target H) := inferInstance

/-- The concrete spatial representation on the completed Hilbert tensor product. -/
def completedEval : Algebra ⊗[ℂ] C →ₗ[ℂ] (Target H →L[ℂ] Target H) :=
  commutingEval ⟨Target H⟩
    (tensorLeftRep (H := ⟨Space⟩) (K := H) concrete.toNonUnitalStarAlgHom)
    (tensorRightRep (H := ⟨Space⟩) (K := H) S)

@[simp] theorem completedEval_tmul (a : Algebra) (c : C) :
    completedEval H S (a ⊗ₜ[ℂ] c) = amplified a * right (S c) := rfl

theorem completedEval_norm_le (x : Algebra ⊗[ℂ] C) :
    ‖completedEval H S x‖ ≤ minTensorNorm.{0,0,0} x := by
  change ‖commutingEval ⟨Target H⟩
    (tensorLeftRep (H := ⟨Space⟩) (K := H) concrete.toNonUnitalStarAlgHom)
    (tensorRightRep (H := ⟨Space⟩) (K := H) S) x‖ ≤ _
  calc
    _ = ‖(spatialEval ⟨Space⟩ H concrete.toNonUnitalStarAlgHom S x).completion‖ :=
      congrArg norm (completed_spatial_eq ⟨Space⟩ H concrete.toNonUnitalStarAlgHom S x).symm
    _ = ‖spatialEval ⟨Space⟩ H concrete.toNonUnitalStarAlgHom S x‖ := completed_norm _
    _ ≤ _ := norm_spatialEval_le x ⟨Space⟩ H concrete.toNonUnitalStarAlgHom S

def jointDefect (n : ℕ) (x : Algebra ⊗[ℂ] C) : H →L[ℂ] Target H :=
  (averaged R n).comp (commutingEval H R S x) - (completedEval H S x).comp (averaged R n)

@[simp] theorem jointDefect_zero (n : ℕ) : jointDefect H R S n 0 = 0 := by
  unfold jointDefect
  erw [map_zero (commutingEval H R S),map_zero (completedEval H S)]
  rw [ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp,sub_self]

@[simp] theorem jointDefect_add (n : ℕ) (x y : Algebra ⊗[ℂ] C) :
    jointDefect H R S n (x+y) = jointDefect H R S n x + jointDefect H R S n y := by
  unfold jointDefect
  erw [map_add (commutingEval H R S),map_add (completedEval H S)]
  rw [ContinuousLinearMap.comp_add,ContinuousLinearMap.add_comp]
  abel

theorem jointDefect_tmul (hRS : ∀ a c, Commute (R a) (S c)) (n : ℕ) (a : Algebra) (c : C) :
    jointDefect H R S n (a ⊗ₜ[ℂ] c) = (defect R n a).comp (S c) := by
  ext x
  change averaged R n (R a (S c x)) - amplified a (right (S c) (averaged R n x)) =
    averaged R n (R a (S c x)) - amplified a (averaged R n (S c x))
  have hh := congrArg (fun T : H →L[ℂ] Target H => T x)
    (averaged_commuting R n (S c) (fun a => hRS a c))
  change averaged R n (S c x) = right (S c) (averaged R n x) at hh
  exact congrArg (fun y => averaged R n (R a (S c x)) - amplified a y) hh.symm

/-- Norm convergence of the averaged intertwining errors for every algebraic
tensor; the second algebra is completely arbitrary and may be nonunital. -/
theorem jointDefect_tendsto (hRS : ∀ a c, Commute (R a) (S c)) (x : Algebra ⊗[ℂ] C) :
    Tendsto (fun n => jointDefect H R S n x) atTop (𝓝 0) := by
  induction x using TensorProduct.inductionOn with
  | tmul a c =>
    have hc : Continuous (fun T : H →L[ℂ] Target H => T.comp (S c)) := by fun_prop
    have hh := hc.continuousAt.tendsto.comp (defect_tendsto R a)
    simpa only [Function.comp_def,ContinuousLinearMap.zero_comp,← jointDefect_tmul H R S hRS] using hh
  | add x y hx hy => simpa only [jointDefect_add,add_zero] using hx.add hy

/-- The output of any commuting tensor evaluation lies in the support of R. -/
theorem commutingEval_support (x : Algebra ⊗[ℂ] C) :
    R 1 * commutingEval H R S x = commutingEval H R S x := by
  induction x using TensorProduct.inductionOn with
  | tmul a c =>
    change R 1 * (R a * S c) = R a * S c
    rw [← mul_assoc,← map_mul,one_mul]
  | add x y hx hy =>
    erw [map_add (commutingEval H R S)]
    rw [mul_add,hx,hy]

/-- Averaging proves the nontrivial maximal-to-minimal inequality directly;
no faithfulness, separability or nondegeneracy of the input representations is
assumed. -/
theorem commutingEval_norm_le_min (hRS : ∀ a c, Commute (R a) (S c)) (x : Algebra ⊗[ℂ] C) :
    ‖commutingEval H R S x‖ ≤ minTensorNorm.{0,0,0} x := by
  apply ContinuousLinearMap.opNorm_le_bound _ (minTensorNorm_nonneg x)
  intro v
  have hs : R 1 (commutingEval H R S x v) = commutingEval H R S x v :=
    congrArg (fun T : H →L[ℂ] H => T v) (commutingEval_support H R S x)
  have hb (n : ℕ) : ‖commutingEval H R S x v‖ ≤
      ‖jointDefect H R S n x‖ * ‖v‖ + minTensorNorm.{0,0,0} x * ‖v‖ := by
    calc
      _ = ‖averaged R n (commutingEval H R S x v)‖ := by rw [averaged_norm,hs]
      _ = ‖jointDefect H R S n x v + completedEval H S x (averaged R n v)‖ := by
        rw [jointDefect,sub_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,sub_add_cancel]
      _ ≤ ‖jointDefect H R S n x v‖ + ‖completedEval H S x (averaged R n v)‖ := norm_add_le _ _
      _ ≤ ‖jointDefect H R S n x‖ * ‖v‖ + minTensorNorm.{0,0,0} x * ‖v‖ := by
        apply add_le_add (ContinuousLinearMap.le_opNorm _ _)
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (completedEval_norm_le H S x)
            ((averaged R n).le_of_opNorm_le (averaged_norm_le R n) v |>.trans_eq (one_mul _))
            (norm_nonneg _) (minTensorNorm_nonneg x))
  have ht := ((jointDefect_tendsto H R S hRS x).norm.mul_const ‖v‖).add_const
    (minTensorNorm.{0,0,0} x * ‖v‖)
  simpa only [norm_zero,zero_mul,zero_add] using
    ge_of_tendsto ht (Filter.Eventually.of_forall hb)

end CuntzAveraging

/-- The actually constructed universal Cuntz algebra is nuclear in the full
spatial/commuting tensor-norm sense used in the obstruction theorem. -/
theorem CuntzUniversal.nuclear : IsNuclear.{0,0} CuntzUniversal.Algebra := by
  intro C inst x
  apply le_antisymm (minTensorNorm_le_maxTensorNorm x)
  apply maxTensorNorm_le_of_commuting
  intro H R S hRS
  exact CuntzAveraging.commutingEval_norm_le_min H R S hRS x

end NuclearUltrapower
end
end

end OAI
