import OAI.Combinatorics.HadwigerCounterexample.SmallCoverBounds

namespace OAI

/-! # Polynomial Rank Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Submodule Function Finset
open scoped BigOperators
variable {A B : Type} [Fintype A] [Fintype B]

def mpMask (P Q : Mat A B) : Mat A B := Matrix.of (fun x y => P x y * Q x y)

theorem rank_mask (P Q : Mat A B) :
    (mpMask P Q).rank ≤ P.rank*Q.rank := by
  classical
  obtain ⟨X,Y,hX,hY,hP⟩ := rank_product P
  obtain ⟨U,V,hU,hV,hQ⟩ := rank_product Q
  let R := Fin P.rank × Fin Q.rank
  let f : Mat A R := Matrix.of (fun x r => X x r.1*U x r.2)
  let g : Mat R B := Matrix.of (fun r y => Y r.1 y * V r.2 y)
  have he : mpMask P Q=f*g := by
    ext i j
    have h (a : Fin P.rank) (b : Fin Q.rank) :
        f i (a,b)*g (a,b) j=(X i a*Y a j)*(U i b*V b j) := by
      unfold f g; simp only [Matrix.of_apply]; ring
    change P i j*Q i j = ∑ x : Fin P.rank × Fin Q.rank, f i x*g x j
    have ht :
        (∑ a,X i a * Y a j)*(∑ b,U i b*V b j)=P i j*Q i j :=
      congrArg₂ (·*·) (congr_fun (congr_fun hP i) j) (congr_fun (congr_fun hQ i) j)
    exact ht.symm.trans (by
      rw [Finset.sum_mul,Fintype.sum_prod_type]
      simp_rw [Finset.mul_sum,h])
  rw [he]
  exact (Matrix.rank_mul_le_left ..).trans (f.rank_le_card_width.trans_eq (by simp [R]))

private theorem choose_draws (w : Wgt A) (T : ℕ) (hw : IsLaw w)
    (i j : Fin T) (h : i≠j) :
    mapW (draws (Fin T) w) (fun x => (x i,x j))=pairW w w := by
  classical
  let g : Bool → Fin T := fun b => if b then i else j
  have hg : Injective g := by intro x y; cases x <;> cases y <;> simp [g,h,h.symm]
  funext x
  let P (b : Bool) := fun y : A => y=onSide x b
  have ht := prodW_pr_inj hg (w:=fun _ => w) (fun _ => hw) P
  have hm (z : Fin T → A) : (z i,z j)=x ↔ ∀ b,P b (z (g b)) := by
    simp [Bool.forall_bool, P, Prod.ext_iff,onSide,g,and_comm]
  unfold mapW
  simp_rw [hm]
  refine ht.trans ?_
  rw [Fintype.prod_bool]; unfold P onSide
  simp only [Bool.false_eq_true,ite_true,ite_false,pr_point']

  rfl

/-- Here T counts k^2+1 draws, union bound uses crude T^2.
Even repeats give the event. -/
theorem simultaneous_czeros (P : Mat A A) (k : ℕ)
    (w : Wgt A) (hw : IsLaw w) (hK : 1+P.rank ≤ k)
    (h : ∀ x,P x x=0) :
    1 ≤ ((k:ℝ)^2+1)^2 * pr (pairW w w) (fun x => P x.1 x.2=0 ∧ P x.2 x.1=0) := by
  classical
  let O : Vec A := fun _ => 1
  let Q := vecMulVec O O+P
  let V := mpMask Q Qᵀ
  have hr : Q.rank≤ k := (mrk_add_le ..).trans
    ((Nat.add_le_add_right (Matrix.rank_vecMulVec_le O O) _).trans hK)
  have he : V.rank ≤ k^2 := (rank_mask Q Qᵀ).trans (by rw [Matrix.rank_transpose]; nlinarith)
  let T := k^2+1
  let p := fun x : A×A => P x.1 x.2=0 ∧ P x.2 x.1=0
  let f := fun i : Fin T × Fin T => fun z : Fin T → A => i.1≠i.2 ∧ p (z i.1,z i.2)
  have hx (z : Fin T→A) : ∃ i,f i z := by
    by_contra! hz
    have heq : V.submatrix z z = 1 := by
      ext i j
      change (1+P (z i) (z j))*(1+P (z j) (z i)) = (1:Mat (Fin T) (Fin T)) i j
      by_cases h' : i=j
      · subst j; rw [Matrix.one_apply_eq,h]; simp
      rw [Matrix.one_apply_ne h']
      rcases bit_cases (P (z i) (z j)) with hP|hP
      · have hv := (bit_cases (P (z j) (z i))).resolve_left
          (fun hc => hz (i,j) ⟨h',hP,hc⟩)
        rw [hv,char_two,mul_zero]
      rw [hP,char_two,zero_mul]
    have hk := (V.rank_submatrix_le z z).trans he
    rw [heq,Matrix.rank_one,Fintype.card_fin] at hk; omega
  let μ := draws (Fin T) w
  have hm : IsLaw μ := draws_law hw
  have hB (i : Fin T×Fin T) :
      pr μ (f i) ≤ pr (pairW w w) p := by
    by_cases he : i.1=i.2
    · simp only [f,he,ne_eq,not_true_eq_false,false_and,pr_false]
      exact pr_nonneg (pairW_law hw hw).nz
    · rw [← choose_draws w T hw _ _ he, mapW_pr]
      simp only [μ,f,he,ne_eq,not_false_eq_true,true_and,le_refl]
  have hh : 1 = pr μ (fun z => ∃ i,f i z) := by
    simp_rw [show ∀ z,(∃ i,f i z)=True from (fun z => eq_true (hx z)),pr_true,hm.total]
  refine hh.trans_le (((pr_exists_le hm.nz f).trans
    (Finset.sum_le_sum fun i _ => hB i)).trans_eq ?_)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_prod,Fintype.card_fin,T]
  push_cast; unfold p; ring
end HadwigerCounterexample

end

end OAI
