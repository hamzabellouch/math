import OAI.GroupTheory.PolycyclicRecognition.Algebra.CayleyDirichletEnergy
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset

namespace OAI

/-! # Disjoint word-ball packings and their enlarged covers

These are the finite counting estimates used for the averaging map in
Kleiner's polynomial-growth harmonic-function argument, Section 3.2.
-/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {G : Type*} [Group G] [DecidableEq G]

def translatedWordBall (S : Finset G) (r : ℕ) (x : G) : Finset G :=
  (wordBall S r).image (x * ·)

@[simp] theorem mem_translatedWordBall (S : Finset G) (r : ℕ) (x y : G) :
    y ∈ translatedWordBall S r x ↔ x⁻¹ * y ∈ wordBall S r := by
  simp only [translatedWordBall, mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa using hz
  · intro h
    exact ⟨x⁻¹ * y, h, by simp⟩

@[simp] theorem card_translatedWordBall (S : Finset G) (r : ℕ) (x : G) :
    (translatedWordBall S r x).card = (wordBall S r).card :=
  card_image_of_injective _ (fun _ _ h => mul_left_cancel h)

theorem mem_translatedWordBall_self (S : Finset G) (r : ℕ) (x : G) :
    x ∈ translatedWordBall S r x := by
  simpa using one_mem_wordBall S r

theorem translatedWordBall_symm (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    {r : ℕ} {x y : G} (h : y ∈ translatedWordBall S r x) :
    x ∈ translatedWordBall S r y := by
  rw [mem_translatedWordBall] at h ⊢
  simpa using inv_mem_wordBall hS h

theorem translatedWordBall_triangle (S : Finset G) {r t : ℕ} {x y z : G}
    (hy : y ∈ translatedWordBall S r x) (hz : z ∈ translatedWordBall S t y) :
    z ∈ translatedWordBall S (r + t) x := by
  rw [mem_translatedWordBall] at hy hz ⊢
  simpa [mul_assoc] using mul_mem_wordBall hy hz

theorem mem_doubled_ball_of_not_disjoint (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) {r : ℕ} {x y : G}
    (h : ¬ Disjoint (translatedWordBall S r x) (translatedWordBall S r y)) :
    x ∈ translatedWordBall S (2 * r) y := by
  obtain ⟨z, hx, hy⟩ := not_disjoint_iff.mp h
  simpa only [two_mul] using translatedWordBall_triangle S hy
    (translatedWordBall_symm S hS hx)

theorem exists_disjoint_wordBall_cover (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (F : Finset G) (r : ℕ) :
    ∃ C ⊆ F,
      (C : Set G).Pairwise (fun x y =>
        Disjoint (translatedWordBall S r x) (translatedWordBall S r y)) ∧
      ∀ x ∈ F, ∃ y ∈ C, x ∈ translatedWordBall S (2 * r) y := by
  classical
  let P := F.powerset.filter (fun (C : Finset G) => (C : Set G).Pairwise (fun x y =>
    Disjoint (translatedWordBall S r x) (translatedWordBall S r y)))
  have hP : P.Nonempty := ⟨∅, by simp [P]⟩
  obtain ⟨C, hC, hmax⟩ := exists_max_image P card hP
  have hCF : C ⊆ F := mem_powerset.mp (mem_filter.mp hC).1
  have hdis := (mem_filter.mp hC).2
  refine ⟨C, hCF, hdis, fun x hx => ?_⟩
  by_contra! hcov
  have hxC : x ∉ C := fun h => hcov x h (mem_translatedWordBall_self S (2 * r) x)
  have hxy : ∀ y ∈ C,
      Disjoint (translatedWordBall S r x) (translatedWordBall S r y) := by
    intro y hy
    by_contra hn
    exact hcov y hy (mem_doubled_ball_of_not_disjoint S hS hn)
  have hins : insert x C ∈ P := by
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr (insert_subset hx hCF), ?_⟩
    rw [coe_insert, Set.pairwise_insert_of_notMem (by simpa using hxC)]
    exact ⟨hdis, fun y hy => ⟨hxy y hy, (hxy y hy).symm⟩⟩
  have hc := hmax _ hins
  rw [card_insert_of_notMem hxC] at hc
  omega

theorem disjoint_wordBall_packing_bound (S : Finset G) (C : Finset G) {r : ℕ}
    (hdis : (C : Set G).Pairwise (fun x y =>
      Disjoint (translatedWordBall S r x) (translatedWordBall S r y)))
    (z : G) (R : ℕ) (hC : ∀ x ∈ C, x ∈ translatedWordBall S R z) :
    C.card * (wordBall S r).card ≤ (wordBall S (R + r)).card := by
  have hs : C.biUnion (translatedWordBall S r) ⊆ translatedWordBall S (R + r) z := by
    intro y hy
    obtain ⟨x, hx, hy⟩ := mem_biUnion.mp hy
    exact translatedWordBall_triangle S (hC x hx) hy
  calc
    _ = (C.biUnion (translatedWordBall S r)).card := by
      rw [card_biUnion hdis]
      simp
    _ ≤ (translatedWordBall S (R + r) z).card := card_le_card hs
    _ = _ := card_translatedWordBall _ _ _

theorem disjoint_wordBall_overlap_bound (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (C : Finset G) (r t : ℕ)
    (hdis : (C : Set G).Pairwise (fun x y =>
      Disjoint (translatedWordBall S r x) (translatedWordBall S r y))) (z : G) :
    (C.filter (fun x => z ∈ translatedWordBall S t x)).card * (wordBall S r).card ≤
      (wordBall S (t + r)).card := by
  apply disjoint_wordBall_packing_bound S _
    (hdis.mono (fun _ hx => (mem_filter.mp hx).1)) z t
  intro x hx
  exact translatedWordBall_symm S hS (mem_filter.mp hx).2

theorem sum_translatedWordBall_le_overlap (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (C : Finset G) (r R t : ℕ)
    (hdis : (C : Set G).Pairwise (fun x y =>
      Disjoint (translatedWordBall S r x) (translatedWordBall S r y)))
    (hC : C ⊆ wordBall S R) (w : G → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x ∈ C, ∑ y ∈ translatedWordBall S t x, w y) ≤
      (((wordBall S (t + r)).card : ℝ) / (wordBall S r).card) *
        ∑ y ∈ wordBall S (R + t), w y := by
  classical
  have hcard : (0 : ℝ) < (wordBall S r).card :=
    Nat.cast_pos.mpr (card_pos.mpr ⟨1, one_mem_wordBall S r⟩)
  have hsub (x : G) (hx : x ∈ C) :
      translatedWordBall S t x ⊆ wordBall S (R + t) := by
    intro y hy
    have hm : x ∈ translatedWordBall S R 1 := by simpa using hC hx
    simpa using translatedWordBall_triangle S hm hy
  have hsum (x : G) (hx : x ∈ C) :
      (∑ y ∈ translatedWordBall S t x, w y) =
        ∑ y ∈ wordBall S (R + t), if y ∈ translatedWordBall S t x then w y else 0 := by
    calc
      _ = ∑ y ∈ translatedWordBall S t x,
          if y ∈ translatedWordBall S t x then w y else 0 :=
        sum_congr rfl (fun y hy => by simp [hy])
      _ = _ := sum_subset (hsub x hx) (fun y _ hy => by simp [hy])
  calc
    _ = ∑ x ∈ C, ∑ y ∈ wordBall S (R + t),
        if y ∈ translatedWordBall S t x then w y else 0 := sum_congr rfl hsum
    _ = ∑ y ∈ wordBall S (R + t), ∑ x ∈ C,
        if y ∈ translatedWordBall S t x then w y else 0 := sum_comm
    _ ≤ ∑ y ∈ wordBall S (R + t),
        (((wordBall S (t + r)).card : ℝ) / (wordBall S r).card) * w y := by
      apply sum_le_sum
      intro y _
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (hw y)
      apply (le_div_iff₀ hcard).mpr
      exact_mod_cast disjoint_wordBall_overlap_bound S hS C r t hdis y
    _ = _ := (mul_sum ..).symm

end PolycyclicRecognition

end

end OAI
