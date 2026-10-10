import OAI.NumberTheory.TwoPoint.Walks.HighRankMinor
import OAI.NumberTheory.TwoPoint.Bounds.RandomPrimeRank

namespace OAI

/-! Exact coordinate splitting for the high-rank lit equations. -/

namespace TwoPointCorrelations

open Finset Matrix

variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

noncomputable def outsideCoordinates (control pivot : ρ → α) : Finset α :=
  (controlCoordinates control ∪ controlCoordinates pivot)ᶜ

/-- Replace the two disjoint selected coordinate families, keeping all other
coordinates fixed. -/
noncomputable def splitAssignment (control pivot : ρ → α) (base : α → ℤ)
    (c y : ρ → ℤ) : α → ℤ :=
  Function.extend control c (Function.extend pivot y base)

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma splitAssignment_control (control pivot : ρ → α) (base : α → ℤ)
    (hc : Function.Injective control) (c y : ρ → ℤ) (i : ρ) :
    splitAssignment control pivot base c y (control i) = c i := by
  exact hc.extend_apply _ _ _

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma splitAssignment_pivot (control pivot : ρ → α) (base : α → ℤ)
    (hp : Function.Injective pivot) (hdisjoint : ∀ i j, pivot i ≠ control j)
    (c y : ρ → ℤ) (i : ρ) :
    splitAssignment control pivot base c y (pivot i) = y i := by
  unfold splitAssignment
  rw [Function.extend_apply' _ _ _ (by simpa only [not_exists] using fun j => (hdisjoint i j).symm)]
  exact hp.extend_apply _ _ _

omit [DecidableEq ρ] in
lemma splitAssignment_outside (control pivot : ρ → α) (base : α → ℤ)
    (c y : ρ → ℤ) {z : α} (hz : z ∈ outsideCoordinates control pivot) :
    splitAssignment control pivot base c y z = base z := by
  classical
  have hz' : z ∉ controlCoordinates control ∧ z ∉ controlCoordinates pivot := by
    simpa only [outsideCoordinates, mem_compl, mem_union, not_or] using hz
  have hc : ¬ ∃ i, control i = z := by simpa [controlCoordinates] using hz'.1
  have hp : ¬ ∃ i, pivot i = z := by simpa [controlCoordinates] using hz'.2
  simp only [splitAssignment, Function.extend_apply' _ _ _ hc,
    Function.extend_apply' _ _ _ hp]

omit [DecidableEq ρ] in
lemma sum_disjoint_coordinates (control pivot : ρ → α)
    (hc : Function.Injective control) (hp : Function.Injective pivot)
    (hdisjoint : ∀ i j, pivot i ≠ control j) (f : α → ℤ) :
    (∑ z, f z) = (∑ j, f (pivot j)) + (∑ j, f (control j)) +
      ∑ z ∈ outsideCoordinates control pivot, f z := by
  classical
  have hd : Disjoint (controlCoordinates control) (controlCoordinates pivot) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨i, _, rfl⟩ := mem_image.mp hz
    obtain ⟨j, _, heq⟩ := mem_image.mp hz'
    exact hdisjoint j i heq
  have hs := sum_add_sum_compl (controlCoordinates control ∪ controlCoordinates pivot) f
  rw [sum_union hd] at hs
  have hcontrol : (∑ z ∈ controlCoordinates control, f z) = ∑ j, f (control j) :=
    sum_image (fun _ _ _ _ hij => hc hij)
  have hpivot : (∑ z ∈ controlCoordinates pivot, f z) = ∑ j, f (pivot j) :=
    sum_image (fun _ _ _ _ hij => hp hij)
  rw [hcontrol, hpivot] at hs
  dsimp only [outsideCoordinates]
  linarith only [hs]

omit [DecidableEq ρ] in
/-- The complete integral row is exactly its minor part, its controlling
part, and its fixed outside part. -/
theorem row_splitAssignment (w : ρ → α → ℤ) (control pivot : ρ → α)
    (hc : Function.Injective control) (hp : Function.Injective pivot)
    (hdisjoint : ∀ i j, pivot i ≠ control j) (base : α → ℤ) (c y : ρ → ℤ) (i : ρ) :
    (∑ z, w i z * splitAssignment control pivot base c y z) =
      ((fun i j => w i (pivot j)) *ᵥ y +
        (fun i j => w i (control j)) *ᵥ c +
        (fun i => ∑ z ∈ outsideCoordinates control pivot, w i z * base z)) i := by
  rw [sum_disjoint_coordinates control pivot hc hp hdisjoint]
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct,
    splitAssignment_pivot control pivot base hp hdisjoint,
    splitAssignment_control control pivot base hc]
  congr 1
  apply sum_congr rfl
  intro z hz
  rw [splitAssignment_outside control pivot base c y hz]

/-- After fixing the outside variables, the actual selected rows satisfy
the previously proved random-prime rank bound. -/
theorem split_coordinate_prime_rank_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (μ : FiniteLaw P)
    (w : ρ → α → ℤ) (control pivot : ρ → α)
    (hc : Function.Injective control) (hp : Function.Injective pivot)
    (hdisjoint : ∀ i j, pivot i ≠ control j)
    (hdet : (Matrix.of fun i j => w i (pivot j)).det ≠ 0)
    (base : α → ℤ) (M : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hatom : ∀ p, μ.weight p ≤ a)
    (hsize : ∀ y z : ρ → P, ∀ i,
      (primeDifference P (fun i j => w i (pivot j)) y z i).natAbs ≤ M) :
    let ν := FiniteLaw.independent (fun _ : ρ => μ)
    ν.average (fun c => ν.probability (fun y => ∀ i, ((c i).val : ℤ) ∣
      ∑ z, w i z * splitAssignment control pivot base
        (fun j => ((c j).val : ℤ)) (fun j => ((y j).val : ℤ)) z)) ≤
      Real.sqrt ((a * (1 + (Nat.log 2 M : ℝ))) ^ Fintype.card ρ) := by
  let f (c : ρ → P) : ρ → ℤ :=
    (fun i j => w i (control j)) *ᵥ (fun j => ((c j).val : ℤ)) +
      (fun i => ∑ z ∈ outsideCoordinates control pivot, w i z * base z)
  have h := random_prime_rank_bound P hP μ (fun i j => w i (pivot j)) hdet
    f M a ha hatom hsize
  dsimp only at h ⊢
  convert h using 1
  congr 1
  funext c
  congr 1
  funext y
  apply propext
  simp only [row_splitAssignment w control pivot hc hp hdisjoint, f, Pi.add_apply,
    add_assoc]

end TwoPointCorrelations

end OAI
