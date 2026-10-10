import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic

namespace OAI

/-! Quantitative popular-parameter selection in the finite incidence
argument. No asymptotic notation or hidden logarithmic losses are used. -/
namespace Falconer

/-- Deleting points below a fixed degree threshold loses at most the
threshold times the size of the whole set. -/
theorem finite_popular_mass {α : Type*} (S : Finset α) (w : α → ℝ)
    {I θ L : ℝ} (hθ : 0 ≤ θ) (htotal : I ≤ ∑ x ∈ S, w x)
    (hsmall : θ*(S.card : ℝ) ≤ I/2) (hupper : ∀ x ∈ S, w x ≤ L) :
    let G := S.filter fun x => θ ≤ w x
    I/2 ≤ ∑ x ∈ G, w x ∧ I/2 ≤ L*(G.card : ℝ) := by
  let G := S.filter fun x => θ ≤ w x
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun x => θ ≤ w x) w
  have hbad : (∑ x ∈ S.filter (fun x => ¬θ ≤ w x), w x) ≤ θ*(S.card : ℝ) := by
    calc
      _ ≤ ∑ _x ∈ S.filter (fun x => ¬θ ≤ w x), θ :=
        Finset.sum_le_sum fun x hx => (lt_of_not_ge (Finset.mem_filter.mp hx).2).le
      _ = θ*((S.filter (fun x => ¬θ ≤ w x)).card : ℝ) := by simp [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_filter_le _ _)) hθ
  have hmass : I/2 ≤ ∑ x ∈ G, w x := by
    dsimp [G]
    linarith
  refine ⟨hmass,hmass.trans ?_⟩
  calc
    _ ≤ ∑ _x ∈ G, L := Finset.sum_le_sum fun x hx => hupper x (Finset.mem_filter.mp hx).1
    _ = _ := by simp [G,mul_comm]

noncomputable def familyDegree {α β : Type*} [DecidableEq β] (J : Finset α) (A : α → Finset β) (x : β) : ℝ :=
  ((J.filter fun j => x ∈ A j).card : ℝ)

theorem familyDegree_sum {α β : Type*} [DecidableEq β]
    (J : Finset α) (A : α → Finset β) :
    (∑ x ∈ J.biUnion A, familyDegree J A x) = ∑ j ∈ J, ((A j).card : ℝ) := by
  have hd := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := J) (t := J.biUnion A) (fun j x => x ∈ A j)
  have hf (j) (hj : j ∈ J) : (J.biUnion A).bipartiteAbove (fun j x => x ∈ A j) j = A j := by
    ext x
    simp only [Finset.mem_bipartiteAbove]
    exact and_iff_right_of_imp (fun hx => Finset.mem_biUnion.mpr ⟨j,hj,hx⟩)
  have hsum : (∑ j ∈ J, ((J.biUnion A).bipartiteAbove (fun j x => x ∈ A j) j).card) =
      ∑ j ∈ J, (A j).card := Finset.sum_congr rfl (fun j hj => by rw [hf j hj])
  rw [hsum] at hd
  unfold familyDegree
  have he : (∑ x ∈ J.biUnion A, (J.filter fun j => x ∈ A j).card) =
      ∑ j ∈ J, (A j).card := hd.symm
  exact_mod_cast he

theorem family_popular_selection {α β : Type*} [DecidableEq β]
    (J : Finset α) (A : α → Finset β) (hJ : J.Nonempty) {m : ℝ} (hm : 0 < m)
    (hsize : ∀ j ∈ J, m ≤ ((A j).card : ℝ)) :
    let U := J.biUnion A
    let θ := m*(J.card : ℝ)/(2*(U.card : ℝ))
    ∃ G ⊆ U, m/2 ≤ (G.card : ℝ) ∧
      m*(J.card : ℝ)/2 ≤ ∑ x ∈ G, familyDegree J A x ∧
      ∀ x ∈ G, θ ≤ familyDegree J A x := by
  let U := J.biUnion A
  have hJpos : 0 < (J.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hJ)
  have hUpos : 0 < (U.card : ℝ) := by
    obtain ⟨j,hj⟩ := hJ
    have hjpos : 0 < (A j).card := by exact_mod_cast hm.trans_le (hsize j hj)
    exact Nat.cast_pos.mpr (lt_of_lt_of_le hjpos (Finset.card_le_card (Finset.subset_biUnion_of_mem A hj)))
  let θ := m*(J.card : ℝ)/(2*(U.card : ℝ))
  have htotal : m*(J.card : ℝ) ≤ ∑ x ∈ U, familyDegree J A x := by
    rw [familyDegree_sum]
    calc
      _ = ∑ _j ∈ J, m := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum hsize
  have hsmall : θ*(U.card : ℝ) ≤ m*(J.card : ℝ)/2 := by
    dsimp [θ]
    have he : m*(J.card : ℝ)/(2*(U.card : ℝ))*(U.card : ℝ) = m*(J.card : ℝ)/2 := by field_simp
    exact he.le
  have hupper (x : β) (_hx : x ∈ U) : familyDegree J A x ≤ (J.card : ℝ) := by
    unfold familyDegree
    exact_mod_cast Finset.card_filter_le J (fun j => x ∈ A j)
  have hb := finite_popular_mass U (familyDegree J A) (by dsimp [θ]; positivity)
    htotal hsmall hupper
  refine ⟨U.filter (fun x => θ ≤ familyDegree J A x),Finset.filter_subset _ _,?_,hb.1,?_⟩
  · nlinarith [hb.2]
  · intro x hx
    exact (Finset.mem_filter.mp hx).2

end Falconer

end OAI
