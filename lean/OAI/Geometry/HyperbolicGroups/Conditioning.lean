import Mathlib
import OAI.Geometry.HyperbolicGroups.Random

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace FiniteLaw
variable {I : Type*} [DecidableEq I]

def joinTables (S : Finset I) (a : S → Bool) (b : {i : I // i ∉ S} → Bool) : I → Bool :=
  (Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => Bool)).symm (a,b)

@[simp] lemma joinTables_in (S : Finset I) (a : S → Bool) (b : {i : I // i ∉ S} → Bool)
    (i : S) : joinTables S a b i.val = a i := by
  simp [joinTables,Equiv.piEquivPiSubtypeProd_symm_apply,i.property]

@[simp] lemma joinTables_out (S : Finset I) (a : S → Bool) (b : {i : I // i ∉ S} → Bool)
    (i : {i : I // i ∉ S}) : joinTables S a b i.val = b i := by
  simp [joinTables,Equiv.piEquivPiSubtypeProd_symm_apply,i.property]

variable [Fintype I]

lemma bernoulliProduct_mass_join (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset I) (a : S → Bool) (b : {i : I // i ∉ S} → Bool) :
    (bernoulliProduct p hp).mass (joinTables S a b) =
      (bernoulliProduct (fun i : S => p i.val) (fun i => hp i.val)).mass a *
      (bernoulliProduct (fun i : {i : I // i ∉ S} => p i.val) (fun i => hp i.val)).mass b := by
  change (∏ i, if joinTables S a b i then p i else 1 - p i) = _
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S)]
  simp only [joinTables_in,joinTables_out,bernoulliProduct]
  congr 1
  apply Finset.prod_congr (by ext; simp)
  intros
  rfl

lemma bernoulliProduct_expect_split (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset I) (f : (I → Bool) → ℝ) :
    (bernoulliProduct p hp).expect f =
      (bernoulliProduct (fun i : S => p i.val) (fun i => hp i.val)).expect (fun a =>
        (bernoulliProduct (fun i : {i : I // i ∉ S} => p i.val) (fun i => hp i.val)).expect
          (fun b => f (joinTables S a b))) := by
  unfold expect
  rw [← (Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => Bool)).symm.sum_comp
    (fun w => (bernoulliProduct p hp).mass w * f w),Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  change (bernoulliProduct p hp).mass (joinTables S a b) * f (joinTables S a b) = _
  rw [bernoulliProduct_mass_join]
  ring

/-- Exact independence of an arbitrary outside-trial statistic from the event
that every trial in S is present. -/
theorem bernoulliProduct_event_mul (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset I) (f : (I → Bool) → ℝ)
    (depends : ∀ w z, (∀ i, i ∉ S → w i = z i) → f w = f z) :
    (bernoulliProduct p hp).expect (fun w => if ∀ i ∈ S, w i = true then f w else 0) =
      (∏ i ∈ S, p i) * (bernoulliProduct p hp).expect f := by
  let μ₁ := bernoulliProduct (fun i : S => p i.val) (fun i => hp i.val)
  let μ₂ := bernoulliProduct (fun i : {i : I // i ∉ S} => p i.val) (fun i => hp i.val)
  let g (b : {i : I // i ∉ S} → Bool) := f (joinTables S (fun _ => true) b)
  have hf (a : S → Bool) (b : {i : I // i ∉ S} → Bool) : f (joinTables S a b) = g b := by
    apply depends
    intro i hi
    exact (joinTables_out S a b ⟨i,hi⟩).trans (joinTables_out S (fun _ => true) b ⟨i,hi⟩).symm
  have he (a : S → Bool) (b : {i : I // i ∉ S} → Bool) :
      (∀ i ∈ S, joinTables S a b i = true) ↔ ∀ i, a i = true := by
    constructor
    · intro h i
      simpa only [joinTables_in] using h i.val i.property
    · intro h i hi
      exact (joinTables_in S a b ⟨i,hi⟩).trans (h ⟨i,hi⟩)
  have hmean : (bernoulliProduct p hp).expect f = μ₂.expect g := by
    rw [bernoulliProduct_expect_split p hp S]
    simp only [hf]
    exact μ₁.expect_const _
  have hprob : μ₁.expect (fun a => if ∀ i, a i = true then (1 : ℝ) else 0) = ∏ i ∈ S, p i := by
    have h := bernoulliProduct_all p hp S
    rw [bernoulliProduct_expect_split p hp S] at h
    simp only [he] at h
    simp only [expect_const] at h
    exact h
  rw [bernoulliProduct_expect_split p hp S,hmean]
  simp only [hf,he]
  have hs : ∀ a : S → Bool,
      μ₂.expect (fun b => if ∀ i, a i = true then g b else 0) =
      (if ∀ i, a i = true then (1 : ℝ) else 0) * μ₂.expect g := by
    intro a
    split_ifs <;> simp [expect_const]
  change μ₁.expect (fun a => μ₂.expect (fun b => if ∀ i, a i = true then g b else 0)) = _
  simp_rw [hs]
  calc
    _ = μ₁.expect (fun a => μ₂.expect g * (if ∀ i, a i = true then (1 : ℝ) else 0)) := by
      congr 1; funext a; ring
    _ = μ₂.expect g * μ₁.expect (fun a => if ∀ i, a i = true then (1 : ℝ) else 0) := μ₁.expect_mul _ _
    _ = _ := by rw [hprob]; ring

end FiniteLaw
end HyperbolicObstruction
end
end

section

end
end

end OAI
