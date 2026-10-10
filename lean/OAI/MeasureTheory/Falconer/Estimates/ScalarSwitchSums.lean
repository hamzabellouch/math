import OAI.MeasureTheory.Falconer.Estimates.ScalarPartialSums
import Mathlib.Algebra.Group.Pointwise.Finset.BigOperators

namespace OAI

/-! Exact finite sum identities for changing selected coordinates. All
 switched sums remain in the same fixed-fold sumset of original points. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

noncomputable def scalarSwitchSum {ι : Type*} (I F : Finset ι) (p q : ι → ℝ) : ℝ :=
  ∑ i ∈ I, if i ∈ F then q i else p i

 theorem scalar_switch_sum_eq {ι : Type*} (I F : Finset ι) (hFI : F ⊆ I) (p q : ι → ℝ) :
    scalarSwitchSum I F p q = (∑ i ∈ I, p i)+(∑ i ∈ F, (q i-p i)) := by
  have hf : I.filter (fun i => i ∈ F) = F := by
    ext i; simp only [Finset.mem_filter]; exact ⟨And.right,fun hi => ⟨hFI hi,hi⟩⟩
  calc
    _ = ∑ i ∈ I, (p i+(if i ∈ F then q i-p i else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hif : i ∈ F <;> simp [hif]
    _ = (∑ i ∈ I, p i)+(∑ i ∈ I, if i ∈ F then q i-p i else 0) := Finset.sum_add_distrib
    _ = _ := by rw [← Finset.sum_filter,hf]

 theorem scalar_sum_mem_nsmul {ι : Type*} (I : Finset ι) (f : ι → ℝ) (A : Finset ℝ)
    (hf : ∀ i ∈ I, f i ∈ A) : (∑ i ∈ I, f i) ∈ I.card • A := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi,Finset.card_insert_of_notMem hi,succ_nsmul,add_comm (f i)]
    exact Finset.add_mem_add (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
      (hf i (Finset.mem_insert_self i I))

 theorem scalar_switch_sum_mem {ι : Type*} (I F : Finset ι) (p q : ι → ℝ) (A : Finset ℝ)
    (hp : ∀ i ∈ I, p i ∈ A) (hq : ∀ i ∈ I, q i ∈ A) : scalarSwitchSum I F p q ∈ I.card • A := by
  apply scalar_sum_mem_nsmul
  intro i hi
  split_ifs
  · exact hq i hi
  · exact hp i hi

 theorem scalar_switch_prefix_eq {ι : Type*} [DecidableEq ι] (I : Finset ι) (p q : ι → ℝ)
    (e : ℕ → ι) (J j : ℕ) (hj : j ≤ J)
    (he : ∀ i < J, e i ∈ I) (hinj : Set.InjOn e (Finset.range J : Set ℕ)) :
    scalarSwitchSum I ((Finset.range j).image e) p q =
      (∑ i ∈ I, p i)+scalarPartialSum (fun i => q (e i)-p (e i)) j := by
  have hs : (Finset.range j).image e ⊆ I := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact he i ((Finset.mem_range.mp hi).trans_le hj)
  rw [scalar_switch_sum_eq I _ hs p q]
  congr 1
  unfold scalarPartialSum
  exact Finset.sum_image (hinj.mono (by
    intro i hi
    exact Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hj)))

end Falconer

end OAI
