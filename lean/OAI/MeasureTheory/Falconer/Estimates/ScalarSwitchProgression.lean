import OAI.MeasureTheory.Falconer.Estimates.ScalarIncrementSelection
import OAI.MeasureTheory.Falconer.Estimates.ScalarSwitchSums

namespace OAI

/-! The nonporous branching step: a fixed number of original summands
 produces an approximate arithmetic progression by switching selected
 coordinates. The coordinate ordering is retained for recursive use. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_increment_ordering {ι : Type*} [DecidableEq ι] {ε R ell : ℝ} (hε : 0 < ε)
    (I : Finset ι) (d : ι → ℝ)
    (hlo : ∀ i ∈ I, ell ≤ |d i|) (hhi : ∀ i ∈ I, |d i| ≤ R)
    (L J : ℕ) (hJ : 0 < J) (hR : R ≤ (L:ℝ)*ε)
    (hsize : (2*L+1)*J ≤ I.card) :
    ∃ e : ℕ → ι, (∀ i < J, e i ∈ I) ∧
      Set.InjOn e (Finset.range J : Set ℕ) ∧
      ∃ a : ℝ, ell ≤ |a| ∧ ∀ i < J, |d (e i)-a| < ε := by
  obtain ⟨F,hFI,hFJ,a,ha,hd⟩ := scalar_increment_selection hε I d hhi L J hJ hR hsize
  let E := (Finset.equivFinOfCardEq hFJ).symm
  let e : ℕ → ι := fun i => if hi : i < J then (E ⟨i,hi⟩).val else a
  have he : ∀ i < J, e i ∈ F := by
    intro i hi
    simpa only [e,dite_eq_left hi] using (E ⟨i,hi⟩).property
  refine ⟨e,fun i hi => hFI (he i hi),?_,d a,hlo a (hFI ha),?_⟩
  · intro i hi j hj heq
    have hiJ := Finset.mem_range.mp hi
    have hjJ := Finset.mem_range.mp hj
    have hE : E ⟨i,hiJ⟩ = E ⟨j,hjJ⟩ := by
      apply Subtype.ext
      simpa only [e,dite_eq_left hiJ,dite_eq_left hjJ] using heq
    exact congrArg Fin.val (E.injective hE)
  · intro i hi
    exact hd (e i) (he i hi)

 theorem scalar_switch_progression_error {ι : Type*} [DecidableEq ι] (I : Finset ι) (p q : ι → ℝ)
    (e : ℕ → ι) {ε a : ℝ} (J : ℕ)
    (he : ∀ i < J, e i ∈ I) (hinj : Set.InjOn e (Finset.range J : Set ℕ))
    (hd : ∀ i < J, |q (e i)-p (e i)-a| ≤ ε) :
    ∀ j ≤ J, |scalarSwitchSum I ((Finset.range j).image e) p q-
      ((∑ i ∈ I, p i)+(j:ℝ)*a)| ≤ (j:ℝ)*ε := by
  intro j hj
  rw [scalar_switch_prefix_eq I p q e J j hj he hinj]
  simpa only [add_sub_add_left_eq_sub] using
    scalar_partial_sum_error (fun i => q (e i)-p (e i)) J j hj hd

 theorem scalar_switch_progression_separated {ι : Type*} [DecidableEq ι] (I : Finset ι) (p q : ι → ℝ)
    (e : ℕ → ι) {ε a ρ : ℝ} (hε : 0 ≤ ε) (J : ℕ)
    (he : ∀ i < J, e i ∈ I) (hinj : Set.InjOn e (Finset.range J : Set ℕ))
    (hd : ∀ i < J, |q (e i)-p (e i)-a| ≤ ε)
    (hmargin : ρ+2*(J:ℝ)*ε ≤ |a|) :
    ∀ i ≤ J, ∀ j ≤ J, i ≠ j →
      ρ ≤ |scalarSwitchSum I ((Finset.range i).image e) p q-
        scalarSwitchSum I ((Finset.range j).image e) p q| := by
  intro i hi j hj hij
  rw [scalar_switch_prefix_eq I p q e J i hi he hinj,
    scalar_switch_prefix_eq I p q e J j hj he hinj,add_sub_add_left_eq_sub]
  exact scalar_partial_sums_separated hε _ J hd hmargin i hi j hj hij

 theorem scalar_switch_prefix_displacement {ι : Type*} [DecidableEq ι] (I : Finset ι) (p q : ι → ℝ)
    (e : ℕ → ι) {R : ℝ} (J j : ℕ) (hj : j ≤ J)
    (he : ∀ i < J, e i ∈ I) (hinj : Set.InjOn e (Finset.range J : Set ℕ))
    (hd : ∀ i ∈ I, |q i-p i| ≤ R) :
    |scalarSwitchSum I ((Finset.range j).image e) p q-(∑ i ∈ I, p i)| ≤ (j:ℝ)*R := by
  rw [scalar_switch_prefix_eq I p q e J j hj he hinj,add_sub_cancel_left]
  unfold scalarPartialSum
  calc
    _ ≤ ∑ i ∈ Finset.range j, |q (e i)-p (e i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range j, R := Finset.sum_le_sum (fun i hi =>
      hd (e i) (he i ((Finset.mem_range.mp hi).trans_le hj)))
    _ = _ := by simp

 theorem scalar_sumset_progression {ι : Type*} [DecidableEq ι] {ε R ell ρ : ℝ}
    (hε : 0 < ε) (I : Finset ι) (p q : ι → ℝ) (A : Finset ℝ)
    (hp : ∀ i ∈ I, p i ∈ A) (hq : ∀ i ∈ I, q i ∈ A)
    (hlo : ∀ i ∈ I, ell ≤ |q i-p i|) (hhi : ∀ i ∈ I, |q i-p i| ≤ R)
    (L J : ℕ) (hJ : 0 < J) (hR : R ≤ (L:ℝ)*ε)
    (hsize : (2*L+1)*J ≤ I.card) (hmargin : ρ+2*(J:ℝ)*ε ≤ ell) :
    ∃ e : ℕ → ι, (∀ i < J, e i ∈ I) ∧
      Set.InjOn e (Finset.range J : Set ℕ) ∧
      ∃ a : ℝ, ell ≤ |a| ∧
        (∀ j ≤ J, scalarSwitchSum I ((Finset.range j).image e) p q ∈ I.card • A) ∧
        (∀ j ≤ J, |scalarSwitchSum I ((Finset.range j).image e) p q-
          ((∑ i ∈ I, p i)+(j:ℝ)*a)| ≤ (j:ℝ)*ε) ∧
        (∀ i ≤ J, ∀ j ≤ J, i ≠ j →
          ρ ≤ |scalarSwitchSum I ((Finset.range i).image e) p q-
            scalarSwitchSum I ((Finset.range j).image e) p q|) := by
  obtain ⟨e,he,hinj,a,ha,hd⟩ := scalar_increment_ordering hε I
    (fun i => q i-p i) hlo hhi L J hJ hR hsize
  have hd' : ∀ i < J, |q (e i)-p (e i)-a| ≤ ε := fun i hi => (hd i hi).le
  exact ⟨e,he,hinj,a,ha,fun _ _ => scalar_switch_sum_mem I _ p q A hp hq,
    scalar_switch_progression_error I p q e J he hinj hd',
    scalar_switch_progression_separated I p q e hε.le J he hinj hd' (hmargin.trans ha)⟩

end Falconer

end OAI
