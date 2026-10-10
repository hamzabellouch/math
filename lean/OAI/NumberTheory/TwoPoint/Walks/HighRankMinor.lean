import OAI.NumberTheory.TwoPoint.Bounds.RegularQuotient
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Basic.Real.Basic

namespace OAI

/-!
# Independent lit pairs yield a disjoint integral minor

The coordinates of the selected control directions are removed before the
minor is chosen. All selections use the fixed coefficient matrix, and no
statement about invertibility modulo a sampled prime is needed.
-/

namespace TwoPointCorrelations

open Finset Submodule Matrix

variable {K α ρ : Type*} [Field K] [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ]

omit [Fintype ρ] [DecidableEq ρ] in
/-- Convert the pair-family form used by maximal selection to two blocks. -/
lemma pairFamily_sum_independent (w : ρ → α → K) (control : ρ → α)
    (hind : LinearIndependent K (fun z : ρ × Fin 2 =>
      if z.2 = 0 then w z.1 else Pi.basisFun K α (control z.1))) :
    LinearIndependent K (Sum.elim w (fun i => Pi.basisFun K α (control i))) := by
  let f : ρ ⊕ ρ → ρ × Fin 2 := Sum.elim (fun i => (i, 0)) (fun i => (i, 1))
  have hf : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y <;> simp_all [f]
  convert hind.comp f hf using 1
  funext z
  cases z <;> simp [f]

omit [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma independent_control_injective (w : ρ → α → K) (control : ρ → α)
    (hind : LinearIndependent K (Sum.elim w (fun i => Pi.basisFun K α (control i)))) :
    Function.Injective control := by
  have hd := hind.comp Sum.inr Sum.inr_injective
  intro i j hij
  apply hd.injective
  simp only [Function.comp_apply, Sum.elim_inr, hij]

noncomputable def controlCoordinates (control : ρ → α) : Finset α := univ.image control

noncomputable def deleteControlCoordinates (control : ρ → α) :
    (α → K) →ₗ[K] ({j : α // j ∉ controlCoordinates control} → K) :=
  LinearMap.pi (fun i => LinearMap.proj (i : α))

lemma deleteControlCoordinates_ker_le (control : ρ → α) (hcontrol : Function.Injective control) :
    LinearMap.ker (deleteControlCoordinates (K := K) control) ≤
      span K (Set.range (fun i => Pi.basisFun K α (control i))) := by
  classical
  intro x hx
  have hzero : ∀ j ∉ controlCoordinates control, x j = 0 := by
    intro j hj
    change deleteControlCoordinates control x = 0 at hx
    exact congrFun hx ⟨j, hj⟩
  have heq : x = ∑ i, x (control i) • Pi.basisFun K α (control i) := by
    ext j
    by_cases hj : j ∈ controlCoordinates control
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hj
      simp [Pi.basisFun_apply, hcontrol.eq_iff, Pi.single_apply]
    · have hne : ∀ i, control i ≠ j := by
        intro i hij
        exact hj (mem_image.mpr ⟨i, mem_univ _, hij⟩)
      simp [Pi.basisFun_apply, hne, hzero j hj]
  rw [heq]
  exact sum_mem (fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩))

/-- The selected difference rows remain independent after every control
coordinate has been deleted. -/
theorem independent_rows_outside_controls (w : ρ → α → K) (control : ρ → α)
    (hind : LinearIndependent K (Sum.elim w (fun i => Pi.basisFun K α (control i)))) :
    LinearIndependent K (fun i => deleteControlCoordinates control (w i)) := by
  have hsplit := linearIndependent_sum.mp hind
  have hcontrol := independent_control_injective w control hind
  apply hsplit.1.map
  apply hsplit.2.2.mono_right
  exact deleteControlCoordinates_ker_le control hcontrol

omit [DecidableEq α] in
/-- Any independent finite row family has a square nonsingular column minor. -/
theorem independent_rows_minor (w : ρ → α → K) (hind : LinearIndependent K w) :
    ∃ pivot : ρ → α, Function.Injective pivot ∧
      (Matrix.of fun i j => w i (pivot j)).det ≠ 0 := by
  classical
  let M : Matrix ρ α K := w
  have hspan : span K (Set.range M.col) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← M.rank_eq_finrank_span_cols, hind.rank_matrix, Module.finrank_pi]
  obtain ⟨η, a, ha, hspan', hind'⟩ := exists_linearIndependent' K M.col
  let : Finite η := Finite.of_injective a ha
  let : Fintype η := Fintype.ofFinite η
  let b : Module.Basis η K (ρ → K) := Module.Basis.mk hind' (by rw [hspan', hspan])
  have hcard : Fintype.card ρ = Fintype.card η := by
    rw [← Module.finrank_pi (ι := ρ) K]
    exact Module.finrank_eq_card_basis b
  let e : ρ ≃ η := Fintype.equivOfCardEq hcard
  let pivot : ρ → α := a ∘ e
  have hpivot : Function.Injective pivot := ha.comp e.injective
  have hcols : LinearIndependent K (fun j => fun i => w i (pivot j)) := by
    exact hind'.comp e e.injective
  have hunit : IsUnit (Matrix.of fun i j => w i (pivot j)) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hcols
  refine ⟨pivot, hpivot, ?_⟩
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

/-- The minor columns are disjoint from every selected controlling label. -/
theorem independent_pairs_disjoint_minor (w : ρ → α → K) (control : ρ → α)
    (hind : LinearIndependent K (Sum.elim w (fun i => Pi.basisFun K α (control i)))) :
    Function.Injective control ∧ ∃ pivot : ρ → α, Function.Injective pivot ∧
      (∀ i j, pivot i ≠ control j) ∧
      (Matrix.of fun i j => w i (pivot j)).det ≠ 0 := by
  classical
  have hc := independent_control_injective w control hind
  obtain ⟨p, hp, hdet⟩ := independent_rows_minor
    (fun i => deleteControlCoordinates control (w i)) (independent_rows_outside_controls w control hind)
  let pivot : ρ → α := fun i => (p i : α)
  refine ⟨hc, pivot, ?_, ?_, ?_⟩
  · intro i j hij
    exact hp (Subtype.ext hij)
  · intro i j hij
    have hn : (p i : α) ∉ controlCoordinates control := by simpa using (p i).property
    exact hn (mem_image.mpr ⟨j, mem_univ _, hij.symm⟩)
  · exact hdet

omit [Field K] in
/-- Real independence of integral rows produces a nonzero integral
minor; the determinant is transported through the injective integer cast. -/
theorem integral_independent_pairs_disjoint_minor (w : ρ → α → ℤ) (control : ρ → α)
    (hind : LinearIndependent ℝ (Sum.elim (fun i z => (w i z : ℝ))
      (fun i => Pi.basisFun ℝ α (control i)))) :
    Function.Injective control ∧ ∃ pivot : ρ → α, Function.Injective pivot ∧
      (∀ i j, pivot i ≠ control j) ∧ (Matrix.of fun i j => w i (pivot j)).det ≠ 0 := by
  obtain ⟨hc, pivot, hp, hdisjoint, hdet⟩ :=
    independent_pairs_disjoint_minor (fun i z => (w i z : ℝ)) control hind
  refine ⟨hc, pivot, hp, hdisjoint, ?_⟩
  intro hz
  apply hdet
  change ((Int.castRingHom ℝ).mapMatrix (Matrix.of fun i j => w i (pivot j))).det = 0
  rw [← (Int.castRingHom ℝ).map_det, hz, map_zero]

end TwoPointCorrelations

end OAI
