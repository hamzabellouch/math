import OAI.MeasureTheory.Falconer.Geometry.DyadicCube
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Data.Finset.Union

namespace OAI

/-!
# Finite dyadic trees in the original ambient dimension

All descendants use half-open carriers. Equal-depth cells are disjoint and
partition the parent, so restriction to them is an exact measure splitting.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

noncomputable def cubePaths (d : ℕ) : ℕ → Finset (List (Fin d → Bool))
  | 0 => {[]}
  | n + 1 => Finset.univ.biUnion fun b => (cubePaths d n).image (List.cons b)

@[simp] theorem mem_cubePaths (d n : ℕ) (p : List (Fin d → Bool)) :
    p ∈ cubePaths d n ↔ p.length = n := by
  induction n generalizing p with
  | zero => simp [cubePaths]
  | succ n ih =>
    cases p with
    | nil => simp [cubePaths]
    | cons b p => simp [cubePaths, ih]

theorem card_cubePaths (d n : ℕ) : (cubePaths d n).card = 2^(d*n) := by
  induction n with
  | zero => simp [cubePaths]
  | succ n ih =>
    rw [cubePaths, Finset.card_biUnion]
    · have hc (b : Fin d → Bool) : Function.Injective (List.cons b) :=
        fun _ _ h => (List.cons.inj h).2
      simp only [Finset.card_image_of_injective _ (hc _), ih,
        Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, smul_eq_mul]
      rw [Nat.mul_succ, pow_add]
      exact Nat.mul_comm _ _
    · intro b _ c _ hbc
      apply Finset.disjoint_left.mpr
      intro p hp hq
      obtain ⟨p', _, hp'⟩ := Finset.mem_image.mp hp
      obtain ⟨q', _, hq'⟩ := Finset.mem_image.mp hq
      exact hbc (List.cons.inj (hp'.trans hq'.symm)).1

noncomputable def DyadicCube.descendant {d : ℕ} (Q : DyadicCube d) :
    List (Fin d → Bool) → DyadicCube d
  | [] => Q
  | b :: p => (Q.child b).descendant p

@[simp] theorem DyadicCube.descendant_nil {d : ℕ} (Q : DyadicCube d) :
    Q.descendant [] = Q := rfl

theorem DyadicCube.descendant_append {d : ℕ} (Q : DyadicCube d)
    (p q : List (Fin d → Bool)) :
    Q.descendant (p ++ q) = (Q.descendant p).descendant q := by
  induction p generalizing Q with
  | nil => rfl
  | cons b p ih => exact ih (Q.child b)

theorem DyadicCube.descendant_side {d : ℕ} (Q : DyadicCube d)
    (p : List (Fin d → Bool)) :
    (Q.descendant p).side = Q.side / (2 : ℝ)^p.length := by
  induction p generalizing Q with
  | nil => simp [descendant]
  | cons b p ih =>
    simp only [descendant, ih, child, List.length_cons, pow_succ]
    ring

theorem DyadicCube.descendant_side_pos {d : ℕ} (Q : DyadicCube d)
    (hQ : 0 < Q.side) (p : List (Fin d → Bool)) :
    0 < (Q.descendant p).side := by
  rw [Q.descendant_side]
  positivity

theorem DyadicCube.descendant_subset {d : ℕ} (Q : DyadicCube d)
    (p : List (Fin d → Bool)) : (Q.descendant p).carrier ⊆ Q.carrier := by
  induction p generalizing Q with
  | nil => exact Subset.rfl
  | cons b p ih => exact (ih (Q.child b)).trans (Q.child_subset b)

theorem DyadicCube.descendants_disjoint {d : ℕ} (Q : DyadicCube d)
    {p q : List (Fin d → Bool)} (hlen : p.length = q.length) (hne : p ≠ q) :
    Disjoint (Q.descendant p).carrier (Q.descendant q).carrier := by
  induction p generalizing Q q with
  | nil =>
    have hq : q = [] := by cases q <;> simp_all
    exact (hne hq.symm).elim
  | cons b p ih =>
    cases q with
    | nil => simp at hlen
    | cons c q =>
      by_cases hbc : b = c
      · subst c
        exact ih (Q.child b) (by simpa using hlen)
          (fun he => hne (he ▸ rfl))
      · exact (Q.children_disjoint hbc).mono
          ((Q.child b).descendant_subset p) ((Q.child c).descendant_subset q)

theorem DyadicCube.mem_descendant_at_depth {d : ℕ} (Q : DyadicCube d) (n : ℕ)
    {x : Space d} (hx : x ∈ Q.carrier) :
    ∃ p ∈ cubePaths d n, x ∈ (Q.descendant p).carrier := by
  induction n generalizing Q with
  | zero => exact ⟨[], by simp, hx⟩
  | succ n ih =>
    rw [Q.cover_children] at hx
    obtain ⟨b, hb⟩ := mem_iUnion.mp hx
    obtain ⟨p, hp, hxp⟩ := ih (Q.child b) hb
    exact ⟨b :: p, by simpa using hp, hxp⟩

theorem DyadicCube.cover_descendants {d : ℕ} (Q : DyadicCube d) (n : ℕ) :
    Q.carrier = ⋃ p ∈ cubePaths d n, (Q.descendant p).carrier := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := Q.mem_descendant_at_depth n hx
    exact mem_iUnion₂.mpr ⟨p, hp, hxp⟩
  · exact iUnion₂_subset fun p _ => Q.descendant_subset p

/-- Exact disjoint measure decomposition; no boundaries or extra spatial
cutoffs are added to the original law. -/
theorem DyadicCube.restrict_descendants {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) (n : ℕ) :
    μ.restrict Q.carrier = ∑ p ∈ cubePaths d n, μ.restrict (Q.descendant p).carrier := by
  rw [Q.cover_descendants n]
  rw [Measure.restrict_biUnion_finset]
  · simp only [Measure.sum_fintype, Finset.univ_eq_attach]
    exact Finset.sum_attach (cubePaths d n) (fun p => μ.restrict (Q.descendant p).carrier)
  · intro p hp q hq hpq
    exact Q.descendants_disjoint ((mem_cubePaths d n p).mp hp |>.trans
      ((mem_cubePaths d n q).mp hq).symm) hpq
  · intro p
    exact (Q.descendant p).measurable

noncomputable def DyadicCube.occupiedPaths {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) (n : ℕ) : Finset (List (Fin d → Bool)) :=
  (cubePaths d n).filter fun p => 0 < μ (Q.descendant p).carrier

theorem DyadicCube.card_occupiedPaths_le {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) (n : ℕ) :
    (Q.occupiedPaths μ n).card ≤ 2^(d*n) := by
  rw [← card_cubePaths]
  exact Finset.card_filter_le _ _

theorem DyadicCube.restrict_occupiedPaths {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) (n : ℕ) :
    μ.restrict Q.carrier =
      ∑ p ∈ Q.occupiedPaths μ n, μ.restrict (Q.descendant p).carrier := by
  rw [Q.restrict_descendants μ n]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hpo
  apply Measure.restrict_eq_zero.mpr
  have hz : ¬ 0 < μ (Q.descendant p).carrier := by
    intro hpos
    exact hpo (Finset.mem_filter.mpr ⟨hp, hpos⟩)
  exact le_antisymm (le_of_not_gt hz) bot_le

end Falconer

end OAI
