import OAI.Combinatorics.ThinTrees.SpectralSplit

namespace OAI

universe uI uD uE

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree
variable {I : Type uI} {D : Type uD} {E : Type uE} [Fintype I] [Fintype D] [Fintype E]
  [DecidableEq I] [DecidableEq D] [DecidableEq E]

omit [Fintype I] [DecidableEq I] [DecidableEq D] [Fintype E] [DecidableEq E] in
lemma qform_covariance (v : I → D → ℝ) (A : Finset I) (x : D → ℝ) :
    qform (∑i ∈ A, vecMulVec (v i) (v i)) x=∑i ∈ A, (x ⬝ᵥ v i)^2 := by
  simp only [qform,sum_mulVec,dotProduct_sum]
  apply sum_congr rfl
  intro i _
  rw [vecMulVec_mulVec,dotProduct_smul,dotProduct_comm (v i) x]
  simp [pow_two]

omit [Fintype I] [DecidableEq I] [DecidableEq D] [DecidableEq E] in
lemma dotProduct_sum_elim (a x : D → ℝ) (b y : E → ℝ) :
    (Sum.elim a b) ⬝ᵥ (Sum.elim x y)=a ⬝ᵥ x+b ⬝ᵥ y := by
  simp [dotProduct,Fintype.sum_sum_type]

omit [DecidableEq I] in

theorem split_two_systems (a : I → D → ℝ) (z : I → E → ℝ) {ε : ℝ}
    (hε : 0 < ε)
    (ha : ∀x : D → ℝ, (∑i, (x ⬝ᵥ a i)^2) ≤ x ⬝ᵥ x)
    (hz : ∀y : E → ℝ, (∑i, (y ⬝ᵥ z i)^2) = y ⬝ᵥ y)
    (hsize : ∀i, a i ⬝ᵥ a i+z i ⬝ᵥ z i ≤ ε) :
    ∃A : Finset I,
      (∀x : D → ℝ, (∑i ∈ A, (x ⬝ᵥ a i)^2) ≤
        (1/2:ℝ)*(∑i, (x ⬝ᵥ a i)^2)+(2*Real.sqrt ε+ε)*(x ⬝ᵥ x)) ∧
      (∀y : E → ℝ, (1/2-(2*Real.sqrt ε+ε))*(y ⬝ᵥ y) ≤
        ∑i ∈ A, (y ⬝ᵥ z i)^2) := by
  let w : I → D ⊕ E → ℝ := fun i => Sum.elim (a i) (z i)
  let C : Matrix (D ⊕ E) (D ⊕ E) ℝ := ∑i, vecMulVec (w i) (w i)
  have hC : C.PosSemidef := Matrix.posSemidef_sum _ (fun i _ => by
    simpa only [star_trivial] using posSemidef_vecMulVec_self_star (w i))
  have hcov : C ≤ (2:ℝ) • (1 : Matrix (D ⊕ E) (D ⊕ E) ℝ) := by
    apply Matrix.le_iff.mpr
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((Matrix.PosSemidef.one.smul (by norm_num : (0:ℝ) ≤ 2)).isHermitian.sub hC.isHermitian)
    intro v
    have hv : v=Sum.elim (fun i => v (.inl i)) (fun j => v (.inr j)) := by ext i; cases i <;> rfl
    rw [show star v=v by rfl]
    change 0 ≤ qform ((2:ℝ) • (1 : Matrix (D ⊕ E) (D ⊕ E) ℝ)-C) v
    rw [qform_sub,qform_smul]
    have hc : qform C v=∑i, (v ⬝ᵥ w i)^2 := qform_covariance w univ v
    rw [hc]
    have hterm := Finset.sum_le_sum (s:=univ) (fun i (_ : i ∈ (univ : Finset I)) =>
      show (v ⬝ᵥ w i)^2 ≤ 2*((fun j => v (.inl j)) ⬝ᵥ a i)^2+
          2*((fun j => v (.inr j)) ⬝ᵥ z i)^2 by
        rw [hv]
        simp only [w,dotProduct_sum_elim,Sum.elim_inl,Sum.elim_inr]
        nlinarith [sq_nonneg (((fun j => v (.inl j)) ⬝ᵥ a i)-((fun j => v (.inr j)) ⬝ᵥ z i))])
    rw [sum_add_distrib,←mul_sum,←mul_sum,hz] at hterm
    have hh := ha (fun j => v (.inl j))
    have hn : qform (1 : Matrix (D ⊕ E) (D ⊕ E) ℝ) v =
        ((fun j => v (.inl j)) ⬝ᵥ (fun j => v (.inl j)))+
        ((fun j => v (.inr j)) ⬝ᵥ (fun j => v (.inr j))) := by
      rw [qform,one_mulVec,hv,dotProduct_sum_elim]
      rfl
    rw [hn]
    linarith
  have hwsize : ∀i, (vecMulVec (w i) (w i)).trace ≤ ε := by
    intro i
    simpa only [trace_vecMulVec,w,dotProduct_sum_elim] using hsize i
  obtain ⟨A,hlo,hhi⟩ := MSS.two_sided_split w hε hcov hwsize
  have heq (x : D → ℝ) (y : E → ℝ) :
      qform (1 : Matrix (D ⊕ E) (D ⊕ E) ℝ) (Sum.elim x y)=x ⬝ᵥ x+y ⬝ᵥ y := by
    rw [qform,one_mulVec,dotProduct_sum_elim]
  refine ⟨A,?_,?_⟩
  · intro x
    have hh := qform_mono hhi (Sum.elim x (0:E → ℝ))
    simp only [qform_add,qform_smul,qform_covariance,heq,w,dotProduct_sum_elim,zero_dotProduct,add_zero] at hh
    exact hh
  · intro y
    have hh := qform_mono hlo (Sum.elim (0:D → ℝ) y)
    simp only [qform_sub,qform_smul,qform_covariance,heq,w,dotProduct_sum_elim,zero_dotProduct,zero_add,hz] at hh
    nlinarith

end StrongThinTree

end
end

end OAI
