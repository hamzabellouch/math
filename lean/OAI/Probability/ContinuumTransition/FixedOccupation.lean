import OAI.Probability.ContinuumTransition.GrandBlocks

namespace OAI

universe u_1

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def countFamily (F : ConfigFamily) (n : ℕ) : ConfigFamily :=
  fun ι _ x => if Fintype.card ι = n then F ι x else 0

noncomputable def fixedOccupationFamily {κ : Type u_1} (A : κ → Set Space) (s : Finset κ)
    (n : κ → ℕ) (F : ConfigFamily) : ConfigFamily :=
  fun ι _ x => if ∀ k ∈ s, occupation (A k) x = (n k : ℝ) then F ι x else 0

theorem countFamily_relabel (F : ConfigFamily) (hF : RelabelInvariant F) (n : ℕ) :
    RelabelInvariant (countFamily F n) := by
  intro ι κ _ _ e x
  simp only [countFamily, Fintype.card_congr e, hF ι κ e x]

theorem fixedOccupationFamily_relabel {κ : Type u_1} (A : κ → Set Space) (s : Finset κ)
    (n : κ → ℕ) (F : ConfigFamily) (hF : RelabelInvariant F) :
    RelabelInvariant (fixedOccupationFamily A s n F) := by
  intro ι τ _ _ e x
  simp only [fixedOccupationFamily, occupation_relabel, hF ι τ e x]

theorem GrandFinite.count {F : ConfigFamily} {D : Set Space} (hF : GrandFinite F D) (n : ℕ) :
    GrandFinite (countFamily F n) D := by
  refine ⟨fun ι _ => ?_, ?_⟩
  · change IntegrableOn (fun x : ι → Space => if Fintype.card ι = n then F ι x else 0) _
    split_ifs
    · exact hF.integrable ι
    · exact integrableOn_zero
  · have he (j : ℕ) : familyTerm (countFamily F n) D j = if j = n then familyTerm F D j else 0 := by
      unfold familyTerm familyIntegral countFamily
      simp only [Fintype.card_fin]
      split_ifs <;> simp
    change Summable (fun j => familyTerm (countFamily F n) D j)
    simp_rw [he]
    exact summable_of_ne_finset_zero (s := {n}) (fun j hj => ite_eq_right (by simpa only [Finset.mem_singleton] using hj))

theorem grandIntegral_countFamily (F : ConfigFamily) (D : Set Space) (n : ℕ) :
    grandIntegral (countFamily F n) D = familyTerm F D n := by
  have he (j : ℕ) : familyTerm (countFamily F n) D j = if j = n then familyTerm F D j else 0 := by
    unfold familyTerm familyIntegral countFamily
    simp only [Fintype.card_fin]
    split_ifs <;> simp
  simp only [grandIntegral, he, tsum_ite_eq]

theorem fixedOccupationFamily_nonneg {κ : Type u_1} (A : κ → Set Space) (s : Finset κ)
    (n : κ → ℕ) (F : ConfigFamily)
    (hF : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (ι : Type) [Fintype ι] (x : ι → Space) : 0 ≤ fixedOccupationFamily A s n F ι x := by
  unfold fixedOccupationFamily
  split_ifs
  · exact hF ι x
  · rfl

theorem GrandFinite.fixedOccupation {κ : Type u_1} {A : κ → Set Space} {s : Finset κ}
    (n : κ → ℕ) (hA : ∀ k ∈ s, MeasurableSet (A k)) {F : ConfigFamily} {D : Set Space}
    (hF : GrandFinite F D) (hm : ∀ (ι : Type) [Fintype ι], Measurable (F ι))
    (h0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x) :
    GrandFinite (fixedOccupationFamily A s n F) D := by
  refine hF.of_le (fun ι _ => ?_) (fixedOccupationFamily_nonneg A s n F h0) ?_
  · apply Measurable.ite ?_ (hm ι) measurable_const
    have hh := MeasurableSet.biInter s.finite_toSet.countable (fun k hk =>
      measurableSet_eq_fun (measurable_occupation (ι := ι) (hA k hk))
        (show Measurable (fun _ : ι → Space => (n k : ℝ)) from measurable_const))
    convert hh using 1
    ext x
    simp only [mem_ofPred_eq, mem_iInter, Finset.mem_coe]
  · intro ι _ x
    unfold fixedOccupationFamily
    split_ifs
    · rfl
    · exact h0 ι x

theorem occupation_binary_left {ι : Type} [Fintype ι] [DecidableEq ι] {A B : Set Space}
    (hd : Disjoint A B) (s : Finset ι) {x : ι → Space} (hx : x ∈ binaryRegion A B s) :
    occupation A x = (Fintype.card {i : ι // i ∈ s} : ℝ) := by
  rw [occupation_eq_sum]
  have he (i : ι) : x i ∈ A ↔ i ∈ s := by
    constructor
    · intro hi
      by_contra his
      exact Set.disjoint_left.mp hd hi (by simpa only [ite_eq_right his] using hx i)
    · intro hi
      simpa only [ite_eq_left hi] using hx i
  simp only [he]
  simp only [Fintype.card_subtype, ← Finset.sum_boole]

theorem occupation_binary_right {ι : Type} [Fintype ι] [DecidableEq ι] {A B C : Set Space}
    (hd : Disjoint A C) (s : Finset ι) {x : ι → Space} (hx : x ∈ binaryRegion A B s) :
    occupation C x = occupation C (fun i : {i : ι // i ∉ s} => x i) := by
  have hh := (occupation_subtype_compl C s x (fun i hi hc =>
    Set.disjoint_left.mp hd (by simpa only [ite_eq_left hi] using hx i) hc)).symm
  convert hh using 1
  congr! 3

theorem injective_binary_iff {ι : Type} [Fintype ι] [DecidableEq ι] {A B : Set Space}
    (hd : Disjoint A B) (s : Finset ι) {x : ι → Space} (hx : x ∈ binaryRegion A B s) :
    Function.Injective x ↔ Function.Injective (fun i : {i : ι // i ∈ s} => x i) ∧
      Function.Injective (fun i : {i : ι // i ∉ s} => x i) := by
  constructor
  · intro hh
    exact ⟨hh.comp Subtype.val_injective, hh.comp Subtype.val_injective⟩
  · rintro ⟨h₁,h₂⟩ i j hij
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ s
    · exact congrArg Subtype.val (h₁ (a₁ := ⟨i,hi⟩) (a₂ := ⟨j,hj⟩) hij)
    · have hia : x i ∈ A := by simpa only [ite_eq_left hi] using hx i
      have hjb : x j ∈ B := by simpa only [ite_eq_right hj] using hx j
      exact False.elim (Set.disjoint_left.mp hd hia (hij.symm ▸ hjb))
    · have hja : x j ∈ A := by simpa only [ite_eq_left hj] using hx j
      have hib : x i ∈ B := by simpa only [ite_eq_right hi] using hx i
      exact False.elim (Set.disjoint_left.mp hd hja (hij ▸ hib))
    · exact congrArg Subtype.val (h₂ (a₁ := ⟨i,hi⟩) (a₂ := ⟨j,hj⟩) hij)

theorem gibbsFamily_binary_eq {U : Space → Space → ℝ} (hU : ∀ x y, U x y = U y x)
    (β h : ℝ) {A B : Set Space} (hd : Disjoint A B)
    (hcross : ∀ x ∈ A, ∀ y ∈ B, U x y = 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : Finset ι) {x : ι → Space} (hx : x ∈ binaryRegion A B s) :
    gibbsFamily U β h ι x = gibbsFamily U β h {i : ι // i ∈ s} (fun i => x i)*
      gibbsFamily U β h {i : ι // i ∉ s} (fun i => x i) := by
  have he : gibbsEnergy U x = gibbsEnergy U (fun i : {i : ι // i ∈ s} => x i)+
      gibbsEnergy U (fun i : {i : ι // i ∉ s} => x i) := by
    have hh := gibbsEnergy_split U hU (fun i => i ∈ s) x
    have hz : (∑ i : {i : ι // i ∈ s}, ∑ j : {j : ι // j ∉ s}, U (x i) (x j)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      exact hcross (x i) (by simpa only [ite_eq_left i.property] using hx i)
        (x j) (by simpa only [ite_eq_right j.property] using hx j)
    have he' : gibbsEnergy U x = gibbsEnergy U (fun i : {i : ι // i ∈ s} => x i)+
        gibbsEnergy U (fun i : {i : ι // i ∉ s} => x i)+
        ∑ i : {i : ι // i ∈ s}, ∑ j : {j : ι // j ∉ s}, U (x i) (x j) := by
      convert hh using 1
      congr! 5
    simpa only [hz, add_zero] using he'
  have hc : (Fintype.card {i : ι // i ∈ s} : ℝ)+Fintype.card {i : ι // i ∉ s} = Fintype.card ι := by
    have hh := Fintype.card_subtype_compl (fun i : ι => i ∈ s)
    have hl := Fintype.card_subtype_le (fun i : ι => i ∈ s)
    have hh' : Fintype.card {i : ι // i ∈ s}+Fintype.card {i : ι // i ∉ s} = Fintype.card ι := by omega
    exact_mod_cast hh'
  simp only [gibbsFamily, injective_binary_iff hd s hx]
  split_ifs <;> try simp_all only [zero_mul, mul_zero, and_false, false_and, not_false_eq_true, and_self, not_true_eq_false]
  rw [← Real.exp_add, ← hc]
  congr 1
  ring

end ContinuumTemperature
end

end OAI
