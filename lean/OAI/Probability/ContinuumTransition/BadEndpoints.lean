import OAI.Probability.ContinuumTransition.FreeGrand

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def badEndpoints {ι : Type} [Fintype ι] (t : ℝ) (x : ι → Space) : Finset ι :=
  Finset.univ.filter (fun i => ∃ j, i ≠ j ∧ ‖x i-x j‖ < 1 ∧
    ¬(Real.exp (-t) ≤ ‖x i-x j‖ ∧ ‖x i-x j‖ ≤ (1+shellDelta)*Real.exp (-t)))

lemma badEndpoints_complement_free {ι : Type} [Fintype ι] [DecidableEq ι] (t : ℝ) (x : ι → Space) :
    FreeConfig t (fun i : {i : ι // i ∉ badEndpoints t x} => x i) := by
  intro i j hij hd
  by_contra hh
  apply i.property
  simp only [badEndpoints, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨j,fun he => hij (Subtype.ext he),hd,hh⟩

lemma badEndpoints_energy {ι : Type} [Fintype ι] (t : ℝ) (x : ι → Space) :
    t^2/2*(badEndpoints t x).card ≤ gibbsEnergy (fun x y => coreProfile t ‖x-y‖) x := by
  have hn (i j : ι) : 0 ≤ if i=j then (0 : ℝ) else coreProfile t ‖x i-x j‖ := by
    split_ifs
    · rfl
    · exact coreProfile_nonneg _ _
  have hr (i : ι) : (if i ∈ badEndpoints t x then t^2 else 0) ≤
      ∑ j, if i=j then (0 : ℝ) else coreProfile t ‖x i-x j‖ := by
    split_ifs with hi
    · obtain ⟨j,hij,hd,hs⟩ := (Finset.mem_filter.mp hi).2
      calc
        _ ≤ coreProfile t ‖x i-x j‖ := coreProfile_ge_of_not_shell t _ hd hs
        _ = (if i=j then (0 : ℝ) else coreProfile t ‖x i-x j‖) := by rw [ite_eq_right hij]
        _ ≤ _ := Finset.single_le_sum (fun j _ => hn i j) (Finset.mem_univ j)
    · exact Finset.sum_nonneg (fun j _ => hn i j)
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hr i)
  have he : (∑ i : ι, if i ∈ badEndpoints t x then t^2 else 0) =
      ((badEndpoints t x).card : ℝ)*t^2 := by
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rw [he] at hh
  unfold gibbsEnergy
  linarith only [hh]

noncomputable def idealFamily (d : ℝ) : ConfigFamily :=
  fun ι _ _ => Real.exp (d*Fintype.card ι)

lemma idealFamily_nonneg (d : ℝ) (ι : Type) [Fintype ι] (x : ι → Space) :
    0 ≤ idealFamily d ι x := (Real.exp_pos _).le

lemma idealFamily_relabel (d : ℝ) : RelabelInvariant (idealFamily d) := by
  intro ι κ _ _ e x
  simp only [idealFamily, Fintype.card_congr e]

theorem core_gibbs_bad_endpoints {ι : Type} [Fintype ι] [DecidableEq ι] (t d : ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (x : ι → Space) :
    gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d ι x ≤
      ∑ s : Finset ι, idealFamily (d-β*t^2/2) {i : ι // i ∈ s} (fun i => x i)*
        freeFamily t d {i : ι // i ∉ s} (fun i => x i) := by
  let s := badEndpoints t x
  have hterm : gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d ι x ≤
      idealFamily (d-β*t^2/2) {i : ι // i ∈ s} (fun i => x i)*
        freeFamily t d {i : ι // i ∉ s} (fun i => x i) := by
    have hsfree : FreeConfig t (fun i : {i : ι // i ∉ s} => x i) := badEndpoints_complement_free t x
    simp only [idealFamily, freeFamily, ite_eq_left hsfree, Fintype.card_coe]
    have he : (Fintype.card ι : ℝ) = (s.card : ℝ)+(Fintype.card {i : ι // i ∉ s} : ℝ) := by
      have hh := Fintype.card_subtype_compl (fun i : ι => i ∈ s)
      rw [Fintype.card_coe] at hh
      have hh' : Fintype.card ι = s.card+Fintype.card {i : ι // i ∉ s} := by
        rw [hh]; exact (Nat.add_sub_of_le (Finset.card_le_univ s)).symm
      exact_mod_cast hh'
    unfold gibbsFamily
    split_ifs with hinj
    · rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left (badEndpoints_energy t x) hβ
      rw [he]
      dsimp only [s] at hh ⊢
      nlinarith only [hh]
    · positivity
  exact hterm.trans (Finset.single_le_sum
    (fun r _ => mul_nonneg
      (idealFamily_nonneg (d-β*t^2/2) {i : ι // i ∈ r} (fun i => x i))
      (freeFamily_nonneg t d {i : ι // i ∉ r} (fun i => x i))) (Finset.mem_univ s))

end ContinuumTemperature
end

end OAI
