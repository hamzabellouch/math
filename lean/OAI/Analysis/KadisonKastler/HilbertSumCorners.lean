import OAI.Analysis.KadisonKastler.IsometricCornerAlgebra
import OAI.Analysis.KadisonKastler.HilbertSumOperators

namespace OAI

/-! # The reducing coordinate corners of a Hilbert sum -/

namespace KadisonKastler

open KadisonSimilarity
open scoped InnerProductSpace

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℂ (E n)] [∀ n, CompleteSpace (E n)]

def hilbertSumInclusion (n : ℕ) : E n →ₗᵢ[ℂ] lp E 2 where
  toLinearMap := (lp.singleContinuousLinearMap ℂ E 2 n).toLinearMap
  norm_map' v := lp.norm_single (by norm_num) n v

omit [∀ n, CompleteSpace (E n)] in
@[simp] theorem hilbertSumInclusion_apply (n : ℕ) (v : E n) :
    hilbertSumInclusion n v = lp.single 2 n v := rfl

theorem hilbertSumInclusion_adjoint_apply (n : ℕ) (f : lp E 2) :
    (hilbertSumInclusion (E := E) n).toContinuousLinearMap.adjoint f = f n := by
  apply ext_inner_left ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact lp.inner_single_left n v f

abbrev hilbertSumProjection (n : ℕ) : lp E 2 →L[ℂ] lp E 2 :=
  isometricExtension (hilbertSumInclusion n) 1

@[simp] theorem hilbertSumProjection_apply (n : ℕ) (f : lp E 2) :
    hilbertSumProjection n f = lp.single 2 n (f n) := by
  change hilbertSumInclusion n ((hilbertSumInclusion n).toContinuousLinearMap.adjoint f) = _
  rw [hilbertSumInclusion_adjoint_apply, hilbertSumInclusion_apply]

theorem hilbertSumInclusion_extension_apply (n : ℕ) (T : E n →L[ℂ] E n) (f : lp E 2) :
    isometricExtension (hilbertSumInclusion n) T f = lp.single 2 n (T (f n)) := by
  change hilbertSumInclusion n (T ((hilbertSumInclusion n).toContinuousLinearMap.adjoint f)) = _
  rw [hilbertSumInclusion_adjoint_apply, hilbertSumInclusion_apply]

def hilbertSumCompression (n : ℕ) (T : lp E 2 →L[ℂ] lp E 2) : E n →L[ℂ] E n :=
  rangeCompression (hilbertSumInclusion n) T

@[simp] theorem hilbertSumCompression_apply (n : ℕ) (T : lp E 2 →L[ℂ] lp E 2) (v : E n) :
    hilbertSumCompression n T v = T (lp.single 2 n v) n :=
  hilbertSumInclusion_adjoint_apply n _

theorem hilbertSumCompression_norm_le (n : ℕ) (T : lp E 2 →L[ℂ] lp E 2) :
    ‖hilbertSumCompression n T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro v
  rw [hilbertSumCompression_apply]
  exact (lp.norm_apply_le_norm (by norm_num) _ n).trans
    ((T.le_opNorm _).trans_eq (by rw [lp.norm_single (by norm_num)]))

theorem hilbertSumCompression_extension (n : ℕ) (T : lp E 2 →L[ℂ] lp E 2) :
    isometricExtension (hilbertSumInclusion n) (hilbertSumCompression n T) =
      hilbertSumProjection n * T * hilbertSumProjection n := by
  ext f
  rfl

theorem hilbertSum_diagonal_of_commutes (T : lp E 2 →L[ℂ] lp E 2)
    (hT : ∀ n, hilbertSumProjection n * T = T * hilbertSumProjection n)
    (f : lp E 2) (n : ℕ) : T f n = hilbertSumCompression n T (f n) := by
  have h := congrArg (fun S : lp E 2 →L[ℂ] lp E 2 => S f n) (hT n)
  simpa only [mul_apply_eq_comp, hilbertSumProjection_apply,
    lp.single_apply_self, hilbertSumCompression_apply] using h

theorem hilbertSumCompression_mem_corner (M : VonNeumannAlgebra (lp E 2)) (n : ℕ)
    (hn : hilbertSumProjection n ∈ M) (T : lp E 2 →L[ℂ] lp E 2) (hT : T ∈ M) :
    hilbertSumCompression n T ∈ isometricCornerAlgebra (hilbertSumInclusion (E := E) n) M hn := by
  rw [mem_isometricCornerAlgebra_iff, hilbertSumCompression_extension]
  exact M.mul_mem (M.mul_mem hn hT) hn

theorem hilbertSum_corner_commutes (M : VonNeumannAlgebra (lp E 2)) (n : ℕ)
    (hn : hilbertSumProjection n ∈ M) (F : E n →L[ℂ] E n)
    (hF : F ∈ isometricCornerAlgebra (hilbertSumInclusion (E := E) n) M hn)
    (S : lp E 2 →L[ℂ] lp E 2) (hS : S ∈ M.commutant) (v : E n) :
    F (hilbertSumCompression n S v) = hilbertSumCompression n S (F v) := by
  have hExt := (mem_isometricCornerAlgebra_iff
    (hilbertSumInclusion (E := E) n) M hn F).mp hF
  have hc := (VonNeumannAlgebra.mem_commutant_iff.mp hS) _ hExt
  have h := congrArg (fun R : lp E 2 →L[ℂ] lp E 2 => R (lp.single 2 n v) n) hc
  simpa only [mul_apply_eq_comp, hilbertSumInclusion_extension_apply,
    lp.single_apply_self, hilbertSumCompression_apply] using h

end

end KadisonKastler

end OAI
