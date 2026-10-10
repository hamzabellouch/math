import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators

namespace OAI

/-! Clipped rectangle contours and physical boundary counts. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
open Matrix
open Filter Topology
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.RectangleContours
open scoped BigOperators
variable {L : ℕ}

def rectangle (lo₁ hi₁ lo₂ hi₂ : ℤ) (n : ℕ) : Finset (Vertex L) := by
  classical
  exact Finset.univ.filter (fun v =>
    lo₁-(n:ℤ)≤(v.1.val:ℤ) ∧ (v.1.val:ℤ)≤hi₁+n ∧
    lo₂-(n:ℤ)≤(v.2.val:ℤ) ∧ (v.2.val:ℤ)≤hi₂+n)

@[simp] lemma mem_rectangle (lo₁ hi₁ lo₂ hi₂ : ℤ) (n : ℕ) (v : Vertex L) :
    v∈rectangle lo₁ hi₁ lo₂ hi₂ n ↔
    lo₁-(n:ℤ)≤(v.1.val:ℤ) ∧ (v.1.val:ℤ)≤hi₁+n ∧
    lo₂-(n:ℤ)≤(v.2.val:ℤ) ∧ (v.2.val:ℤ)≤hi₂+n := by
  classical
  simp [rectangle]

lemma monotone_rectangle (lo₁ hi₁ lo₂ hi₂ : ℤ) :
    Monotone (rectangle (L := L) lo₁ hi₁ lo₂ hi₂) := by
  intro n m hnm v hv
  rw [mem_rectangle] at hv ⊢
  omega

lemma neighbor_in_succ (lo₁ hi₁ lo₂ hi₂ : ℤ) (n : ℕ) (v w : Vertex L)
    (h : ForwardAdjacent v w ∨ ForwardAdjacent w v)
    (hv : v∈rectangle lo₁ hi₁ lo₂ hi₂ n) :
    w∈rectangle lo₁ hi₁ lo₂ hi₂ (n+1) := by
  rw [mem_rectangle] at hv ⊢
  rcases h with (⟨hx,hy⟩|⟨hx,hy⟩)|(⟨hx,hy⟩|⟨hx,hy⟩)
  all_goals
    simp only [Fin.ext_iff] at hx hy
    omega

lemma crossing_enters_next (lo₁ hi₁ lo₂ hi₂ : ℤ) (n : ℕ) (e : Edge L)
    (h : (e.val.1∈rectangle lo₁ hi₁ lo₂ hi₂ n ∧ e.val.2∉rectangle lo₁ hi₁ lo₂ hi₂ n) ∨
      (e.val.1∉rectangle lo₁ hi₁ lo₂ hi₂ n ∧ e.val.2∈rectangle lo₁ hi₁ lo₂ hi₂ n)) :
    e.val.1∈rectangle lo₁ hi₁ lo₂ hi₂ (n+1) ∧
      e.val.2∈rectangle lo₁ hi₁ lo₂ hi₂ (n+1) := by
  rcases h with h|h
  · exact ⟨monotone_rectangle lo₁ hi₁ lo₂ hi₂ (Nat.le_succ n) h.1,
      neighbor_in_succ lo₁ hi₁ lo₂ hi₂ n e.val.1 e.val.2 (Or.inl e.property) h.1⟩
  · exact ⟨neighbor_in_succ lo₁ hi₁ lo₂ hi₂ n e.val.2 e.val.1 (Or.inr e.property) h.2,
      monotone_rectangle lo₁ hi₁ lo₂ hi₂ (Nat.le_succ n) h.2⟩

theorem unique_crossing (lo₁ hi₁ lo₂ hi₂ : ℤ) (e : Edge L) (j k : ℕ)
    (hj : (e.val.1∈rectangle lo₁ hi₁ lo₂ hi₂ j ∧ e.val.2∉rectangle lo₁ hi₁ lo₂ hi₂ j) ∨
      (e.val.1∉rectangle lo₁ hi₁ lo₂ hi₂ j ∧ e.val.2∈rectangle lo₁ hi₁ lo₂ hi₂ j))
    (hk : (e.val.1∈rectangle lo₁ hi₁ lo₂ hi₂ k ∧ e.val.2∉rectangle lo₁ hi₁ lo₂ hi₂ k) ∨
      (e.val.1∉rectangle lo₁ hi₁ lo₂ hi₂ k ∧ e.val.2∈rectangle lo₁ hi₁ lo₂ hi₂ k)) : j=k := by
  wlog hle : j≤k generalizing j k
  · exact (this k j hk hj (by omega)).symm
  by_contra hne
  have hlt : j+1≤k := by omega
  have hboth := crossing_enters_next lo₁ hi₁ lo₂ hi₂ j e hj
  have h₁ := monotone_rectangle lo₁ hi₁ lo₂ hi₂ hlt hboth.1
  have h₂ := monotone_rectangle lo₁ hi₁ lo₂ hi₂ hlt hboth.2
  rcases hk with hk|hk
  · exact hk.2 h₂
  · exact hk.1 h₁

private lemma orthogonal_coordinate_bound (lo₁ hi₁ lo₂ hi₂ : ℤ) (n r : ℕ)
    (h₁ : hi₁-lo₁+1≤r) (h₂ : hi₂-lo₂+1≤r) (e : Edge L)
    (he : (e.val.1∈rectangle lo₁ hi₁ lo₂ hi₂ n ∧ e.val.2∉rectangle lo₁ hi₁ lo₂ hi₂ n) ∨
      (e.val.1∉rectangle lo₁ hi₁ lo₂ hi₂ n ∧ e.val.2∈rectangle lo₁ hi₁ lo₂ hi₂ n)) :
    let z : ℤ := if e.val.1.1.val+1=e.val.2.1.val then
      (e.val.1.2.val:ℤ)-(lo₂-n) else (e.val.1.1.val:ℤ)-(lo₁-n)
    0≤z ∧ z<r+2*n := by
  simp only [mem_rectangle] at he
  rcases e.property with ⟨hx,hy⟩|⟨hx,hy⟩
  · simp only [hx,ite_true]
    simp only [Fin.ext_iff] at hy
    omega
  · simp only [Fin.ext_iff] at hx
    have hx' : ¬e.val.1.1.val+1=e.val.2.1.val := by omega
    simp only [hx',ite_false]
    omega

private def boundaryEncoding (lo₁ hi₁ lo₂ hi₂ : ℤ) (n r : ℕ)
    (h₁ : hi₁-lo₁+1≤r) (h₂ : hi₂-lo₂+1≤r)
    (e : {e : Edge L //
      (e.val.1∈rectangle lo₁ hi₁ lo₂ hi₂ n ∧ e.val.2∉rectangle lo₁ hi₁ lo₂ hi₂ n) ∨
      (e.val.1∉rectangle lo₁ hi₁ lo₂ hi₂ n ∧ e.val.2∈rectangle lo₁ hi₁ lo₂ hi₂ n)}) :
    Bool × Bool × Fin (r+2*n) := by
  classical
  let z : ℤ := if e.val.val.1.1.val+1=e.val.val.2.1.val then
      (e.val.val.1.2.val:ℤ)-(lo₂-n) else (e.val.val.1.1.val:ℤ)-(lo₁-n)
  have hz := orthogonal_coordinate_bound lo₁ hi₁ lo₂ hi₂ n r h₁ h₂ e.val e.property
  refine ⟨decide (e.val.val.1.1.val+1=e.val.val.2.1.val),
    decide (e.val.val.1∈rectangle lo₁ hi₁ lo₂ hi₂ n), z.toNat, ?_⟩
  change 0≤z ∧ z<(r:ℤ)+2*(n:ℤ) at hz
  omega

private lemma boundaryEncoding_injective (lo₁ hi₁ lo₂ hi₂ : ℤ) (n r : ℕ)
    (h₁ : hi₁-lo₁+1≤r) (h₂ : hi₂-lo₂+1≤r) :
    Function.Injective (boundaryEncoding (L:=L) lo₁ hi₁ lo₂ hi₂ n r h₁ h₂) := by
  classical
  intro e f hef
  have he := e.property
  have hf := f.property
  have hae := e.val.property
  have haf := f.val.property
  have hze := orthogonal_coordinate_bound lo₁ hi₁ lo₂ hi₂ n r h₁ h₂ e.val e.property
  have hzf := orthogonal_coordinate_bound lo₁ hi₁ lo₂ hi₂ n r h₁ h₂ f.val f.property
  have ht := congrArg Prod.fst hef
  have hi := congrArg (fun x => x.2.1) hef
  have hz := congrArg (fun x => x.2.2.val) hef
  simp only [boundaryEncoding,decide_eq_decide] at ht hi hz
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Prod.ext <;> apply Fin.ext
  all_goals
    simp only [mem_rectangle] at he hf hi
    simp only [ForwardAdjacent,Fin.ext_iff] at hae haf
    split_ifs at hze hzf hz <;> omega

theorem boundaryCard_le (lo₁ hi₁ lo₂ hi₂ : ℤ) (n r : ℕ)
    (h₁ : hi₁-lo₁+1≤r) (h₂ : hi₂-lo₂+1≤r) :
    boundaryCard (rectangle (L:=L) lo₁ hi₁ lo₂ hi₂ n)≤4*(r+2*n) := by
  have h := Fintype.card_le_of_injective _
    (boundaryEncoding_injective (L:=L) lo₁ hi₁ lo₂ hi₂ n r h₁ h₂)
  simpa only [boundaryCard,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,
    ← mul_assoc,Nat.reduceMul] using h

end PolynomialPEPS.Subvolume.RectangleContours

end

end OAI
