import OAI.Algebra.Finitistic.Bar.TwoSidedWeight
import Mathlib.Algebra.BigOperators.Module

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar.SquareZero
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

def baseProjection : Module.End k (TrivSqZeroExt D X) :=
  (inlAlgHom k D X).toLinearMap.comp (fstHom k D X).toLinearMap

def idealProjection : Module.End k (TrivSqZeroExt D X) :=
  LinearMap.id - baseProjection k D X

@[simp] theorem baseProjection_inl (d : D) :
    baseProjection k D X (inl d) = inl d := rfl
@[simp] theorem baseProjection_inr (x : X) :
    baseProjection k D X (inr x) = 0 := rfl
@[simp] theorem idealProjection_inl (d : D) :
    idealProjection k D X (inl d) = 0 := by simp [idealProjection]
@[simp] theorem idealProjection_inr (x : X) :
    idealProjection k D X (inr x) = inr x := by simp [idealProjection]

/-- The actual linear projection onto words with a prescribed X-count. -/
def projection : (n r : ℕ) → Module.End k (term k (TrivSqZeroExt D X) N n)
  | 0, 0 => LinearMap.id
  | 0, _+1 => 0
  | n+1, 0 => TensorProduct.map (baseProjection k D X) (projection n 0)
  | n+1, r+1 => TensorProduct.map (baseProjection k D X) (projection n (r+1)) +
      TensorProduct.map (idealProjection k D X) (projection n r)

@[simp] theorem projection_base (n r : ℕ) (d : D)
    (v : term k (TrivSqZeroExt D X) N n) :
    projection k D X N (n+1) r ((inl d : TrivSqZeroExt D X) ⊗ₜ[k] v) =
      (inl d : TrivSqZeroExt D X) ⊗ₜ[k] projection k D X N n r v := by
  cases r <;> simp [projection]

@[simp] theorem projection_ideal_zero (n : ℕ) (x : X)
    (v : term k (TrivSqZeroExt D X) N n) :
    projection k D X N (n+1) 0 ((inr x : TrivSqZeroExt D X) ⊗ₜ[k] v) = 0 := by
  simp [projection]

@[simp] theorem projection_ideal_succ (n r : ℕ) (x : X)
    (v : term k (TrivSqZeroExt D X) N n) :
    projection k D X N (n+1) (r+1) ((inr x : TrivSqZeroExt D X) ⊗ₜ[k] v) =
      (inr x : TrivSqZeroExt D X) ⊗ₜ[k] projection k D X N n r v := by
  simp [projection]

variable {k D X N}

/-- The projections separate homogeneous bar words exactly. -/
theorem projection_word {n s : ℕ} {v : term k (TrivSqZeroExt D X) N n}
    (hv : Word k D X N n s v) (r : ℕ) :
    projection k D X N n r v = if r = s then v else 0 := by
  induction hv generalizing r with
  | nil v => cases r <;> simp [projection]
  | @base n s v d h ih =>
    rw [projection_base, ih]
    split <;> simp_all
  | @ideal n s v x h ih =>
    cases r with
    | zero =>
      rw [projection_ideal_zero k D X N n x v]
      simp
    | succ r =>
      rw [projection_ideal_succ, ih]
      by_cases hrs : r = s <;> simp [hrs]

/-- Identity on the whole homogeneous subspace, not merely on individual words. -/
theorem projection_self {n r : ℕ} {v : term k (TrivSqZeroExt D X) N n}
    (hv : v ∈ weight k D X N n r) : projection k D X N n r v = v := by
  have hle : weight k D X N n r ≤
      (projection k D X N n r - LinearMap.id).ker := by
    apply Submodule.span_le.mpr
    intro z hz
    change projection k D X N n r z - z = 0
    rw [projection_word hz r, ite_eq_left rfl, sub_self]
  have h := hle hv
  change projection k D X N n r v - v = 0 at h
  exact sub_eq_zero.mp h

/-- Distinct counts are annihilated by the projection. -/
theorem projection_other {n r s : ℕ} (hrs : r ≠ s)
    {v : term k (TrivSqZeroExt D X) N n} (hv : v ∈ weight k D X N n s) :
    projection k D X N n r v = 0 := by
  have hle : weight k D X N n s ≤ (projection k D X N n r).ker := by
    apply Submodule.span_le.mpr
    intro z hz
    change projection k D X N n r z = 0
    rw [projection_word hz r, ite_eq_right hrs]
  exact hle hv

/-- Homogeneous bar subspaces with distinct counts have zero intersection. -/
theorem weight_disjoint (n : ℕ) {r s : ℕ} (hrs : r ≠ s) :
    Disjoint (weight k D X N n r) (weight k D X N n s) := by
  rw [Submodule.disjoint_def]
  intro v hr hs
  rw [← projection_self hr, projection_other hrs hs]


variable (k D X N)

/-- Expanding each actual algebra entry as D ⊕ X spans every absolute bar term. -/
theorem all_words_span (n : ℕ) :
    Submodule.span k {v : term k (TrivSqZeroExt D X) N n |
      ∃ r, Word k D X N n r v} = ⊤ := by
  induction n with
  | zero =>
    apply top_unique
    intro v _
    exact Submodule.subset_span ⟨0, Word.nil v⟩
  | succ n ih =>
    apply top_unique
    intro v _
    induction v using TensorProduct.inductionOn with
    | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
    | tmul a v =>
      let T := Submodule.span k {w : term k (TrivSqZeroExt D X) N (n+1) |
        ∃ r, Word k D X N (n+1) r w}
      let g := TensorProduct.mk k (TrivSqZeroExt D X) (term k (TrivSqZeroExt D X) N n) a
      have hle : Submodule.span k {w | ∃ r, Word k D X N n r w} ≤ T.comap g := by
        apply Submodule.span_le.mpr
        rintro w ⟨r, hw⟩
        change a ⊗ₜ[k] w ∈ T
        rw [← inl_fst_add_inr_snd_eq a, TensorProduct.add_tmul]
        exact Submodule.add_mem _
          (Submodule.subset_span ⟨r, Word.base a.fst hw⟩)
          (Submodule.subset_span ⟨r+1, Word.ideal a.snd hw⟩)
      apply hle
      rw [ih]
      trivial

/-- Every value of the count projection lies in the corresponding homogeneous subspace. -/
theorem projection_mem (n r : ℕ) (v : term k (TrivSqZeroExt D X) N n) :
    projection k D X N n r v ∈ weight k D X N n r := by
  have hle : Submodule.span k {w | ∃ s, Word k D X N n s w} ≤
      (weight k D X N n r).comap (projection k D X N n r) := by
    apply Submodule.span_le.mpr
    rintro w ⟨s, hw⟩
    change projection k D X N n r w ∈ weight k D X N n r
    rw [projection_word hw r]
    split_ifs with h
    · subst s
      exact Submodule.subset_span hw
    · exact Submodule.zero_mem _
  apply hle
  rw [all_words_span]
  trivial

/-- The count subspaces span the entire bar term. -/
theorem weight_iSup (n : ℕ) : (⨆ r, weight k D X N n r) = ⊤ := by
  apply top_unique
  rw [← all_words_span k D X N n]
  apply Submodule.span_le.mpr
  rintro v ⟨r, hr⟩
  exact (le_iSup (fun r => weight k D X N n r) r) (Submodule.subset_span hr)
end DerivedBar.SquareZero

end

end OAI
