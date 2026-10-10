import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.SquareInterval

namespace OAI

open Matrix

namespace CurrentKS.RationalRoot
open scoped BigOperators

variable {N : ℕ}

def sqSum (v : Fin N → ℚ) : ℚ := ∑ i,(v i)^2

def initialScale (v : Fin N → ℚ) : Fin N → ℚ := fun i => v i/(1+sqSum v)

def normalize (v : Fin N → ℚ) (β : ℚ) : Fin N → ℚ :=
  let u := initialScale v
  fun i => u i/upperSqrt (sqSum u) (β*sqSum u)

noncomputable def realVector (v : Fin N → ℚ) : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 fun i => (v i:ℝ)

lemma sqSum_nonneg (v : Fin N → ℚ) : 0 ≤ sqSum v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma sqSum_pos (v : Fin N → ℚ) (hv : v ≠ 0) : 0 < sqSum v := by
  have he : ∃ i,v i ≠ 0 := by
    by_contra! h
    apply hv
    funext i
    exact h i
  obtain ⟨i,hi⟩ := he
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i,Finset.mem_univ _,sq_pos_of_ne_zero hi⟩

lemma sqSum_initialScale (v : Fin N → ℚ) :
    sqSum (initialScale v)=sqSum v/(1+sqSum v)^2 := by
  simp only [sqSum,initialScale,div_pow,Finset.sum_div]

lemma initialScale_spec (v : Fin N → ℚ) (hv : v ≠ 0) :
    0 < sqSum (initialScale v) ∧ sqSum (initialScale v) ≤ 1 := by
  have h := sqSum_pos v hv
  have hr : (0:ℚ)<1+sqSum v := by linarith
  rw [sqSum_initialScale]
  refine ⟨div_pos h (sq_pos_of_pos hr),?_⟩
  apply (div_le_one (sq_pos_of_pos hr)).mpr
  nlinarith [sq_nonneg (sqSum v)]

lemma norm_realVector (v : Fin N → ℚ) : ‖realVector v‖=Real.sqrt (sqSum v:ℝ) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp only [realVector,WithLp.ofLp_toLp,Real.norm_eq_abs,sq_abs,sqSum,Rat.cast_sum,Rat.cast_pow]

lemma realVector_div (v : Fin N → ℚ) (r : ℚ) :
    realVector (fun i => v i/r) = ((r:ℝ)⁻¹) • realVector v := by
  apply PiLp.ext
  intro i
  simp only [realVector,WithLp.ofLp_toLp,PiLp.smul_apply,smul_eq_mul,Rat.cast_div]
  ring

theorem normalize_spec (v : Fin N → ℚ) (hv : v ≠ 0) (β : ℚ) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    1-(β:ℝ) ≤ ‖realVector (normalize v β)‖ ∧ ‖realVector (normalize v β)‖ ≤ 1 ∧
    ∃ c : ℚ, 0 < c ∧ normalize v β = fun i => c*v i := by
  let u := initialScale v
  let q := sqSum u
  let U := upperSqrt q (β*q)
  have hq := initialScale_spec v hv
  have hqp : (0:ℝ)<q := by exact_mod_cast hq.1
  have hq1 : (q:ℝ)≤1 := by exact_mod_cast hq.2
  have hp : (0:ℝ)<β := by exact_mod_cast hβ
  have hp1 : (β:ℝ)≤1 := by exact_mod_cast hβ1
  have hs := upperSqrt_spec q (β*q) (mul_pos hβ hq.1) hq.1.le hq.2
  have hspos : 0 < Real.sqrt (q:ℝ) := Real.sqrt_pos.mpr hqp
  have hs1 : Real.sqrt (q:ℝ) ≤ 1 := Real.sqrt_le_one.mpr hq1
  have hql : (q:ℝ) ≤ Real.sqrt (q:ℝ) := by
    nlinarith [Real.sq_sqrt hqp.le]
  have hUpos : (0:ℝ)<U := hspos.trans_le hs.1
  have hUposQ : 0 < U := by exact_mod_cast hUpos
  have hUupper : (U:ℝ) ≤ (1+(β:ℝ))*Real.sqrt (q:ℝ) := by
    have he : ((β*q:ℚ):ℝ)=(β:ℝ)*(q:ℝ) := Rat.cast_mul ..
    rw [he] at hs
    nlinarith
  have hn : ‖realVector (normalize v β)‖=Real.sqrt (q:ℝ)/(U:ℝ) := by
    change ‖realVector (fun i => u i/U)‖=_
    rw [realVector_div,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hUpos),norm_realVector]
    ring
  rw [hn]
  refine ⟨?_,(div_le_one hUpos).mpr hs.1,?_⟩
  · apply (le_div_iff₀ hUpos).mpr
    have hu := mul_le_mul_of_nonneg_left hUupper (sub_nonneg.mpr hp1)
    nlinarith [mul_nonneg (sq_nonneg (β:ℝ)) hspos.le]
  · have hr : (0:ℚ)<1+sqSum v := by linarith [sqSum_nonneg v]
    refine ⟨((1+sqSum v)*U)⁻¹,inv_pos.mpr (mul_pos hr hUposQ),?_⟩
    funext i
    change (v i/(1+sqSum v))/U=((1+sqSum v)*U)⁻¹*v i
    simp only [div_eq_mul_inv,_root_.mul_inv_rev]
    ring
end CurrentKS.RationalRoot

end OAI
