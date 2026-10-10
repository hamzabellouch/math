import OAI.Probability.ContinuumTransition.MomentExpectations

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def gibbsEnergy (V : Space → Space → ℝ) {ι : Type} [Fintype ι]
    (x : ι → Space) : ℝ :=
  (∑ i, ∑ j, if i = j then 0 else V (x i) (x j))/2

noncomputable def gibbsFamily (V : Space → Space → ℝ) (β h : ℝ) : ConfigFamily :=
  fun ι _ x => if Function.Injective x then Real.exp (h*Fintype.card ι-β*gibbsEnergy V x) else 0

noncomputable def occupation {ι : Type} [Fintype ι] (C : Set Space) (x : ι → Space) : ℝ :=
  Fintype.card {i : ι // x i ∈ C}

theorem occupation_nonneg {ι : Type} [Fintype ι] (C : Set Space) (x : ι → Space) :
    0 ≤ occupation C x := Nat.cast_nonneg _

theorem occupation_eq_sum {ι : Type} [Fintype ι] (C : Set Space) (x : ι → Space) :
    occupation C x = ∑ i, if x i ∈ C then (1 : ℝ) else 0 := by
  classical
  simp only [occupation, ← Finset.sum_boole, Fintype.card_subtype]

theorem measurable_occupation {ι : Type} [Fintype ι] {C : Set Space} (hC : MeasurableSet C) :
    Measurable (fun x : ι → Space => occupation C x) := by
  classical
  simp_rw [occupation_eq_sum]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite (hC.preimage (measurable_pi_apply i)) measurable_const measurable_const

theorem occupation_relabel {ι κ : Type} [Fintype ι] [Fintype κ]
    (C : Set Space) (e : ι ≃ κ) (x : κ → Space) : occupation C (x ∘ e) = occupation C x := by
  classical
  simp_rw [occupation_eq_sum, Function.comp_apply]
  exact Equiv.sum_comp e (fun i => if x i ∈ C then (1 : ℝ) else 0)

theorem occupation_subtype_compl {ι : Type} [Fintype ι] (C : Set Space)
    (s : Finset ι) (x : ι → Space) (h : ∀ i ∈ s, x i ∉ C) :
    occupation C (fun i : {i // i ∉ s} => x i) = occupation C x := by
  classical
  rw [occupation_eq_sum, occupation_eq_sum]
  have hh := Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ s)
    (fun i => if x i ∈ C then (1 : ℝ) else 0)
  have hz : (∑ i : {i // i ∈ s}, if x i ∈ C then (1 : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (h i i.property)
  have hfi : Subtype.fintype (fun i : ι => i ∈ s) = Finset.Subtype.fintype s :=
    Subsingleton.elim _ _
  rw [hfi] at hh
  simpa only [hz, zero_add] using hh

theorem gibbsEnergy_relabel (V : Space → Space → ℝ) {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x : κ → Space) : gibbsEnergy V (x ∘ e) = gibbsEnergy V x := by
  classical
  unfold gibbsEnergy
  simp only [Function.comp_apply, ← e.injective.eq_iff]
  congr 1
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i _
  exact Equiv.sum_comp e (fun j => if e i = j then 0 else V (x (e i)) (x j))

theorem gibbsFamily_relabel (V : Space → Space → ℝ) (β h : ℝ) :
    RelabelInvariant (gibbsFamily V β h) := by
  intro ι κ _ _ e x
  have hh : Function.Injective (x ∘ e) ↔ Function.Injective x := by
    constructor
    · intro hx i j hij
      obtain ⟨i, rfl⟩ := e.surjective i
      obtain ⟨j, rfl⟩ := e.surjective j
      exact congrArg e (hx hij)
    · exact fun hx => hx.comp e.injective
  simp only [gibbsFamily, hh, gibbsEnergy_relabel, Fintype.card_congr e]

theorem gibbsFamily_nonneg (V : Space → Space → ℝ) (β h : ℝ) (ι : Type) [Fintype ι]
    (x : ι → Space) : 0 ≤ gibbsFamily V β h ι x := by
  unfold gibbsFamily
  split_ifs
  · exact (Real.exp_pos _).le
  · rfl

theorem gibbsEnergy_split (V : Space → Space → ℝ) (hsym : ∀ x y, V x y = V y x)
    {ι : Type} [Fintype ι] (p : ι → Prop) [DecidablePred p] (x : ι → Space) :
    gibbsEnergy V x = gibbsEnergy V (fun i : {i // p i} => x i) +
      gibbsEnergy V (fun i : {i // ¬p i} => x i) +
      ∑ i : {i // p i}, ∑ j : {j // ¬p j}, V (x i) (x j) := by
  classical
  have heq := symmetric_matrix_split p (fun i j => if i = j then 0 else V (x i) (x j))
    (fun i j => by by_cases hh : i = j <;> simp [hh, eq_comm, hsym])
  have hcross (i : {i // p i}) (j : {j // ¬p j}) : (i : ι) ≠ j := by
    intro hh
    exact j.property (hh ▸ i.property)
  have hself (a b : {i // p i}) : ((a : ι) = b) ↔ a = b := Subtype.coe_inj
  have hself' (a b : {i // ¬p i}) : ((a : ι) = b) ↔ a = b := Subtype.coe_inj
  unfold gibbsEnergy
  rw [heq]
  simp only [hself, hself', hcross, ite_false]
  ring

theorem measurable_gibbsEnergy {V : Space → Space → ℝ}
    (hV : Measurable (Function.uncurry V)) {ι : Type} [Fintype ι] :
    Measurable (fun x : ι → Space => gibbsEnergy V x) := by
  unfold gibbsEnergy
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  by_cases hij : i = j
  · simp only [ite_eq_left hij]
    exact measurable_const
  · simp only [ite_eq_right hij]
    have hp : Measurable (fun x : ι → Space => (x i, x j)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    exact hV.comp hp

theorem measurableSet_injective_config (ι : Type) [Fintype ι] :
    MeasurableSet {x : ι → Space | Function.Injective x} := by
  have he : {x : ι → Space | Function.Injective x} =
      ⋂ i : ι, ⋂ j : ι, {x : ι → Space | x i = x j → i = j} := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, Function.Injective]
  rw [he]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases hij : i = j
  · simp only [hij, implies_true, ofPred_true]
    exact MeasurableSet.univ
  · have hm : MeasurableSet {x : ι → Space | x i = x j} :=
      measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)
    convert hm.compl using 1
    ext x
    simp [hij]

theorem measurable_gibbsFamily {V : Space → Space → ℝ}
    (hV : Measurable (Function.uncurry V)) (β h : ℝ) (ι : Type) [Fintype ι] :
    Measurable (gibbsFamily V β h ι) := by
  apply Measurable.ite (measurableSet_injective_config ι) _ measurable_const
  exact (measurable_const.sub (measurable_const.mul (measurable_gibbsEnergy hV))).exp

noncomputable def momentFamily (F : ConfigFamily) (C : Set Space) (c : ℝ) : ConfigFamily :=
  fun ι _ x => F ι x * Real.exp (c*(occupation C x)^2)

theorem momentFamily_relabel (F : ConfigFamily) (hF : RelabelInvariant F)
    (C : Set Space) (c : ℝ) : RelabelInvariant (momentFamily F C c) := by
  intro ι κ _ _ e x
  simp only [momentFamily, occupation_relabel, hF ι κ e x]

theorem momentFamily_nonneg (F : ConfigFamily)
    (hF : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (C : Set Space) (c : ℝ) (ι : Type) [Fintype ι] (x : ι → Space) :
    0 ≤ momentFamily F C c ι x := mul_nonneg (hF ι x) (Real.exp_pos _).le

theorem measurable_momentFamily (F : ConfigFamily) {C : Set Space} (hC : MeasurableSet C)
    (c : ℝ) {ι : Type} [Fintype ι] (hF : Measurable (F ι)) :
    Measurable (momentFamily F C c ι) :=
  hF.mul ((measurable_occupation hC).pow_const 2 |>.const_mul c |>.exp)

theorem gibbs_moment_stable_bound (V : Space → Space → ℝ) (β h B c : ℝ)
    (C : Set Space) {ι : Type} [Fintype ι] (x : ι → Space)
    (hbound : c*(occupation C x)^2 ≤ β*gibbsEnergy V x+β*B*Fintype.card ι) :
    momentFamily (gibbsFamily V β h) C c ι x ≤
      Real.exp ((h+β*B)*Fintype.card ι) := by
  by_cases hx : Function.Injective x
  · simp only [momentFamily, gibbsFamily, ite_eq_left hx, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hbound]
  · simp only [momentFamily, gibbsFamily, ite_eq_right hx, zero_mul]
    exact (Real.exp_pos _).le

theorem gibbs_moment_insertion (V : Space → Space → ℝ)
    {A M J β B h : ℝ} (hA : 0 < A) (hM : M ≤ A/8) (hJ : J ≤ M) (hβ : 0 ≤ β)
    (C : Set Space) {ι : Type} [Fintype ι] (s : Finset ι) (x : ι → Space) (X : ℝ)
    (hn : occupation C x = s.card)
    (hE : (A-J/2)*(s.card : ℝ)^2-B*s.card-s.card*X ≤
      gibbsEnergy V x-gibbsEnergy V (fun i : {i // i ∉ s} => x i)) :
    momentFamily (gibbsFamily V β h) C (β*A/4) ι x ≤
      Real.exp ((h+β*B)*s.card) *
        (gibbsFamily V β h {i : ι // i ∉ s} (fun i => x i)*Real.exp (β*X^2/A)) := by
  by_cases hx : Function.Injective x
  swap
  · simp only [momentFamily, gibbsFamily, ite_eq_right hx, zero_mul]
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (gibbsFamily_nonneg V β h _ _) (Real.exp_pos _).le)
  have hout : Function.Injective (fun i : {i : ι // i ∉ s} => x i) :=
    hx.comp Subtype.val_injective
  have hcard : (Fintype.card ι : ℝ) = s.card+Fintype.card {i : ι // i ∉ s} := by
    have hc : Fintype.card {i : ι // i ∉ s} = Fintype.card ι-s.card := by
      rw [Fintype.card_subtype_compl (fun i : ι => i ∈ s), Fintype.card_coe]
    rw [hc]
    rw [Nat.cast_sub (Finset.card_le_univ s)]
    ring
  have he := mul_le_mul_of_nonneg_left hE hβ
  have hex := cell_insertion_exponent (B := B) (h := h) (n := (s.card : ℝ))
    (X := X) hA hM hJ hβ rfl
  simp only [momentFamily, gibbsFamily, ite_eq_left hx, ite_eq_left hout, hn, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [hcard]
  nlinarith only [he, hex]

end ContinuumTemperature
end

end OAI
