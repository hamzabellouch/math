import OAI.Combinatorics.ContingencyTables.Transport.BalancedFamily

namespace OAI

/-!
# Balanced elimination as a finite assignment sum

The recursive integer marginal equals the finite sum over the choices in
all eliminated large-cell pairs. This identifies the signature marginal
with the completion count.
-/

namespace ContingencyTables.BalancedEnumeration

open scoped BigOperators Classical
open BalancedFamily IntegerMarginal BalancedBox

@[reducible] def Assignments : List ℕ → Type
  | [] => PUnit
  | M::Ms => Assignments Ms × Fin (M+1)

@[reducible] instance assignmentsFintype (Ms : List ℕ) : Fintype (Assignments Ms) := by
  induction Ms with
  | nil => exact inferInstanceAs (Fintype PUnit)
  | cons M Ms ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Assignments Ms × Fin (M+1)))

def embedding {I : Type*} : (Ms : List ℕ) → (I → ℕ) → Assignments Ms → Coordinates I Ms → ℕ
  | [],z,_ => z
  | M::Ms,z,a => profile (embedding Ms z a.1) a.2.val (M-a.2.val)

theorem eliminate_eq_sum {I : Type*} (Ms : List ℕ)
    (F : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ) :
    eliminate Ms F z=∑ a : Assignments Ms, F (embedding Ms z a) := by
  induction Ms with
  | nil => simp only [eliminate,Assignments,embedding,Fintype.sum_unique]
  | cons M Ms ih =>
    change eliminate Ms (marginal F M) z=
      ∑ a : Assignments Ms × Fin (M+1), F (profile (embedding Ms z a.1) a.2.val (M-a.2.val))
    rw [ih,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    unfold marginal
    exact (Fin.sum_univ_eq_sum_range (fun j => F (profile (embedding Ms z a) j (M-j))) (M+1)).symm

lemma embedding_inBox {I : Type*} (Ms : List ℕ) (m : I → ℕ) (z : I → ℕ)
    (hz : InBox m z) (a : Assignments Ms) : InBox (bounds m Ms) (embedding Ms z a) := by
  induction Ms with
  | nil => exact hz
  | cons M Ms ih =>
    apply profile_inBox (bounds m Ms) (embedding Ms z a.1) M a.2.val (M-a.2.val)
    · exact ih a.1
    · have ha := a.2.isLt; omega
    · exact Nat.sub_le _ _

lemma embedding_total {I : Type*} [Fintype I] (Ms : List ℕ) (z : I → ℕ)
    (a : Assignments Ms) :
    (∑ i, embedding Ms z a i)=(∑ i, z i)+Ms.sum := by
  induction Ms with
  | nil => simp only [embedding,List.sum_nil,add_zero]
  | cons M Ms ih =>
    change (∑ i, profile (embedding Ms z a.1) a.2.val (M-a.2.val) i)=_
    rw [profile_total,ih]
    have ha := a.2.isLt
    simp only [List.sum_cons]
    omega

end ContingencyTables.BalancedEnumeration

end OAI
