import OAI.Combinatorics.HadwigerCounterexample.FiniteLaws
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

namespace OAI

/-! # Product Laws -/

noncomputable section
open scoped BigOperators
namespace HadwigerCounterexample

theorem ind_all {ι : Type*} [Fintype ι] (p : ι → Prop) :
    ind (∀ i, p i) = ∏ i, ind (p i) := by
  classical
  simp [ind, Fintype.prod_ite_zero]

variable {ι κ α : Type*}
variable {β : ι → Type*}

def prodW [Fintype ι] (w : ∀ i, Wgt (β i)) : Wgt (∀ i, β i) := fun x => ∏ i, w i (x i)

section
variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (β i)]

theorem prodW_tot (w : ∀ i, Wgt (β i)) : tot (prodW w) = ∏ i, tot (w i) :=
  (Fintype.prod_sum w).symm

theorem prodW_avg (w f : ∀ i, Wgt (β i)) :
    avg (prodW w) (prodW f) = ∏ i, avg (w i) (f i) := by
  simp only [avg, prodW]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

theorem prodW_pr (w : ∀ i, Wgt (β i)) (p : ∀ i, β i → Prop) :
    pr (prodW w) (fun x => ∀ i, p i (x i)) = ∏ i, pr (w i) (p i) := by
  simp_rw [pr, ind_all]
  exact prodW_avg w (fun i x => ind (p i x))

omit [DecidableEq ι] [∀ i, Fintype (β i)] in
theorem prodW_nonneg {w : ∀ i, Wgt (β i)} (h : ∀ i x, 0 ≤ w i x) (x) : 0 ≤ prodW w x :=
  Finset.prod_nonneg (fun i _ => h i _)

theorem prodW_law {w : ∀ i, Wgt (β i)} (hw : ∀ i, IsLaw (w i)) : IsLaw (prodW w) := by
  refine ⟨prodW_nonneg (fun i => (hw i).nz), ?_⟩
  rw [prodW_tot]
  simp_rw [(hw _).total]
  simp

end

section
variable [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq κ]
/-- Observe distinct coordinates of a (constant-type) product law. -/
theorem prodW_pr_inj {e : ι → κ} (he : Function.Injective e)
    {w : κ → Wgt α} (hw : ∀ k, IsLaw (w k)) (p : ι → α → Prop) :
    pr (prodW (β:=fun _ => α) w) (fun x => ∀ i, p i (x (e i))) =
      ∏ i, pr (w (e i)) (p i) := by
  classical
  let P (k : κ) (x : α) := ∀ i, e i = k → p i x
  have h (x : κ → α) : (∀ i, p i (x (e i))) ↔ ∀ k, P k (x k) :=
    ⟨fun h k i hi => hi ▸ h i, fun h i => h (e i) i rfl⟩
  simp_rw [h]
  rw [prodW_pr _ P]
  let f (k : κ) (i : ι) := if e i = k then pr (w k) (p i) else 1
  have hf (k : κ) : pr (w k) (P k) = ∏ i, f k i := by
    by_cases hk : ∃ i, e i = k
    · obtain ⟨i, rfl⟩ := hk
      have hP : P (e i) = p i := funext fun x => propext
        ⟨fun h => h i rfl, fun h j hj => (he hj).symm ▸ h⟩
      rw [hP]
      symm
      rw [Finset.prod_eq_single i]
      · simp [f]
      · intro j _ hj
        simp [f, show e j ≠ e i from he.ne hj]
      · simp
    · push Not at hk
      have hP : P k = (fun _ => True) := funext fun _ => propext
        ⟨fun _ => trivial, fun _ j hj => (hk j hj).elim⟩
      simp [hP, (hw k).total, f, hk]
  simp_rw [hf]
  rw [Finset.prod_comm]
  simp [f]

theorem prodW_map_inj {e : ι → κ} (he : Function.Injective e)
    {w : κ → Wgt α} (hw : ∀ k, IsLaw (w k)) :
    mapW (prodW (β := fun _ => α) w) (fun x : κ → α => fun i : ι => x (e i)) =
      prodW (β := fun _ => α) (fun i => w (e i)) := by
  funext x
  unfold mapW
  simp_rw [funext_iff]
  have h := prodW_pr_inj he hw (fun i y => y = x i)
  simp_rw [pr_point'] at h
  exact h

/-- Mapping to ordered pairs along a disjoint family of positions. -/
theorem prodW_map_pairs (e : ι ⊕ ι → κ) (he : Function.Injective e)
    {w : Wgt α} (hw : IsLaw w) :
    mapW (prodW (fun _ : κ => w))
      (fun x i => (x (e (.inl i)), x (e (.inr i)))) =
      prodW (fun _ : ι => pairW w w) := by
  funext y
  let p (j : ι ⊕ ι) (x : α) := j.elim (fun i => x = (y i).1) (fun i => x = (y i).2)
  have heq (x : κ → α) :
      ((fun i => (x (e (.inl i)), x (e (.inr i)))) = y) ↔ ∀ j, p j (x (e j)) := by
    simp [funext_iff, Prod.ext_iff, p, Sum.forall, forall_and]
  unfold mapW
  simp_rw [heq]
  have h := prodW_pr_inj he (w:=fun _ => w) (fun _ => hw) p
  rw [h]
  simp [Fintype.prod_sum_type, p, prodW, pairW, Finset.prod_mul_distrib]

end
end HadwigerCounterexample

end

end OAI
