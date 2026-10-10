import Mathlib
import OAI.Analysis.MatrixSigning.Realization.FaceQueryRealization

namespace OAI

/-! Rational inverse. -/

section


namespace AlgorithmicThinTrees.RationalInverse
open Matrix Finset
variable {n : ℕ}

lemma posDef_of_cast (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q:ℝ))).PosDef) : A.PosDef := by
  apply PosDef.of_dotProduct_mulVec_pos
  · exact (isHermitian_iff_isSymm.mpr (KS.W07.rational_isSymm_of_cast_posSemidef hA.posSemidef))
  · intro x hx
    have hx' : (fun i => (x i:ℝ)) ≠ 0 := by
      intro he
      apply hx
      funext i
      have hh := congrFun he i
      change (x i:ℝ)=0 at hh
      change x i=0
      exact_mod_cast hh
    have hh := hA.dotProduct_mulVec_pos hx'
    simp only [star_trivial,dotProduct,mulVec,map_apply] at hh ⊢
    exact_mod_cast hh

lemma schur_posDef (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (hA : A.PosDef) : (KS.W17.schurTail A).PosDef := by
  have hs : A.IsSymm := isHermitian_iff_isSymm.mp hA.isHermitian
  apply PosDef.of_dotProduct_mulVec_pos
  · exact isHermitian_iff_isSymm.mpr (KS.W17.schurTail_isSymm A hs)
  · intro x hx
    have hlift : KS.W17.schurWitnessLift A x ≠ 0 := by
      intro h
      apply hx
      funext i
      exact congrFun h i.succ
    simpa only [star_trivial,KS.W07.fin_schurWitnessLift_quadratic A hs hA.diag_pos.ne'] using
      hA.dotProduct_mulVec_pos hlift

def liftSolve (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (B : Matrix (Fin n) (Fin n) ℚ) (b : Fin (n+1) → ℚ) : Fin (n+1) → ℚ :=
  let y := B*ᵥ(fun i => b i.succ-A i.succ 0*(b 0/A 0 0))
  Fin.cons ((b 0-(fun j => A 0 j.succ) ⬝ᵥ y)/A 0 0) y

lemma liftSolve_correct (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (B : Matrix (Fin n) (Fin n) ℚ) (b : Fin (n+1) → ℚ)
    (hp : A 0 0 ≠ 0) (hB : KS.W17.schurTail A*B=1) :
    A*ᵥliftSolve A B b=b := by
  let y := B*ᵥ(fun i => b i.succ-A i.succ 0*(b 0/A 0 0))
  have hy : KS.W17.schurTail A*ᵥy=(fun i => b i.succ-A i.succ 0*(b 0/A 0 0)) := by
    rw [show y=B*ᵥ(fun i => b i.succ-A i.succ 0*(b 0/A 0 0)) from rfl,
      Matrix.mulVec_mulVec,hB,Matrix.one_mulVec]
  ext i
  rw [mulVec,dotProduct,Fin.sum_univ_succ]
  change A i 0*((b 0-(fun j => A 0 j.succ) ⬝ᵥ y)/A 0 0)+
    ∑j, A i j.succ*y j=b i
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [mul_div_cancel₀ _ hp]
    simp only [dotProduct]
    ring
  · have he := congrFun hy i
    change (∑j, (A i.succ j.succ-A i.succ 0*A 0 j.succ/A 0 0)*y j)=
      b i.succ-A i.succ 0*(b 0/A 0 0) at he
    have he' : (∑j, A i.succ j.succ*y j)-
        A i.succ 0*(A 0 0)⁻¹*((fun j => A 0 j.succ) ⬝ᵥ y)=
      b i.succ-A i.succ 0*(b 0/A 0 0) := by
      have hsum : (∑j, (A i.succ j.succ-A i.succ 0*A 0 j.succ/A 0 0)*y j)=
          (∑j, A i.succ j.succ*y j)-
          A i.succ 0*(A 0 0)⁻¹*((fun j => A 0 j.succ) ⬝ᵥ y) := by
        simp only [dotProduct,mul_sum,←sum_sub_distrib]
        apply sum_congr rfl
        intro j hj
        ring
      rwa [hsum] at he
    simp only [div_eq_mul_inv]
    linear_combination he'

def inverse : (n : ℕ) → Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ
  | 0,_ => 1
  | n+1,A =>
    let B := inverse n (KS.W17.schurTail A)
    fun i j => liftSolve A B (Pi.single j 1) i

lemma inverse_mul_correct : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ),
    A.PosDef → A*inverse n A=1 := by
  intro n
  induction n with
  | zero => intro A hA;ext i;exact Fin.elim0 i
  | succ n ih =>
    intro A hA
    have hB := ih (KS.W17.schurTail A) (schur_posDef A hA)
    ext i j
    have hh := congrFun (liftSolve_correct A (inverse n (KS.W17.schurTail A))
      (Pi.single j 1) hA.diag_pos.ne' hB) i
    simpa only [inverse,Matrix.mul_apply,Matrix.mulVec,dotProduct,Pi.single_apply,
      one_apply,eq_comm] using! hh

lemma inverse_eq (A : Matrix (Fin n) (Fin n) ℚ) (hA : A.PosDef) : inverse n A=A⁻¹ := by
  exact (inv_eq_right_inv (inverse_mul_correct n A hA)).symm

lemma inverse_eq_of_cast (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q:ℝ))).PosDef) : inverse n A=A⁻¹ :=
  inverse_eq A (posDef_of_cast A hA)

end AlgorithmicThinTrees.RationalInverse
end

end OAI
