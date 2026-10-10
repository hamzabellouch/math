import OAI.Geometry.TranslativeCovering.MatchingAlgebra

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2 u_3 u_4

namespace CellCounts

variable {I : Type u_1} {C : Type u_2} [Fintype I] [Fintype C]

noncomputable def assignmentWeight (w : I → C → ℝ) (f : I → C) : ℝ :=
  ∏ i, w i (f i)

noncomputable def injectiveSum (w : I → C → ℝ) : ℝ :=
  ∑ f : I → C, if Function.Injective f then assignmentWeight w f else 0

theorem sum_assignmentWeight (w : I → C → ℝ) :
    ∑ f, assignmentWeight w f = ∏ i, ∑ c, w i c := by
  exact (Fintype.prod_sum w).symm

omit [Fintype C] in
theorem assignmentWeight_nonneg {w : I → C → ℝ}
    (hw : ∀ i c, 0 ≤ w i c) (f : I → C) : 0 ≤ assignmentWeight w f :=
  Finset.prod_nonneg (fun i _ => hw i (f i))

theorem injectiveSum_nonneg {w : I → C → ℝ} (hw : ∀ i c, 0 ≤ w i c) :
    0 ≤ injectiveSum w := by
  apply Finset.sum_nonneg
  intro f _
  split_ifs
  · exact assignmentWeight_nonneg hw f
  · rfl

theorem injectiveSum_le {w : I → C → ℝ} (hw : ∀ i c, 0 ≤ w i c) :
    injectiveSum w ≤ ∏ i, ∑ c, w i c := by
  rw [← sum_assignmentWeight]
  apply Finset.sum_le_sum
  intro f _
  split_ifs
  · rfl
  · exact assignmentWeight_nonneg hw f

noncomputable def collisionSum (w : I → C → ℝ) (i j : I) : ℝ :=
  ∑ f : I → C, if f i = f j then assignmentWeight w f else 0

noncomputable def force (w : I → C → ℝ) (i j : I) (c : C) (v : I) (d : C) : ℝ :=
  if v = i ∨ v = j then if d = c then w v d else 0 else w v d

omit [Fintype C] in
theorem force_weight (w : I → C → ℝ) (i j : I) (c : C) (f : I → C) :
    assignmentWeight (force w i j c) f =
      if f i = c ∧ f j = c then assignmentWeight w f else 0 := by
  classical
  by_cases h : f i = c ∧ f j = c
  · rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro v _
    by_cases hv : v = i ∨ v = j
    · rcases hv with rfl | rfl <;> simp [force, h.1, h.2]
    · simp [force, hv]
  · rw [ite_eq_right h]
    simp only [not_and_or] at h
    rcases h with hi | hj
    · apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [force, hi]
    · apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [force, hj]

theorem collision_decompose (w : I → C → ℝ) (i j : I) :
    collisionSum w i j = ∑ c, ∏ v, ∑ d, force w i j c v d := by
  classical
  simp_rw [← sum_assignmentWeight, force_weight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  by_cases h : f i = f j
  · simp [h]
  · simp [ite_and, h, Ne.symm h]

omit [Fintype I] in
theorem sum_force (w : I → C → ℝ) (i j : I) (c : C) (v : I) :
    ∑ d, force w i j c v d = if v = i ∨ v = j then w v c else ∑ d, w v d := by
  classical
  by_cases hv : v = i ∨ v = j <;> simp [force, hv]

theorem prod_erase_two [DecidableEq I] (b : I → ℝ) {i j : I} (hij : i ≠ j) :
    ∏ v, b v = b i * b j * ∏ v ∈ (Finset.univ.erase i).erase j, b v := by
  rw [← Finset.mul_prod_erase _ b (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase _ b (by simp [Ne.symm hij] : j ∈ Finset.univ.erase i)]
  ring

theorem collision_formula [DecidableEq I] (w : I → C → ℝ) {i j : I} (hij : i ≠ j) :
    collisionSum w i j = (∑ c, w i c * w j c) *
      ∏ v ∈ (Finset.univ.erase i).erase j, ∑ d, w v d := by
  rw [collision_decompose, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  rw [prod_erase_two (fun v => ∑ d, force w i j c v d) hij]
  simp only [sum_force, true_or, ↓reduceIte, or_true]
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  have hi : v ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).1
  have hj : v ≠ j := (Finset.mem_erase.mp hv).1
  simp [hi, hj]

noncomputable def pairs (I : Type u_3) [Fintype I] [LinearOrder I] : Finset (I × I) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2)

omit [Fintype C] in
theorem noninjective_has_pair [LinearOrder I] {f : I → C}
    (hf : ¬ Function.Injective f) : ∃ ij ∈ pairs I, f ij.1 = f ij.2 := by
  classical
  simp only [Function.Injective] at hf
  push Not at hf
  obtain ⟨i, j, he, hn⟩ := hf
  obtain hlt | hgt := lt_or_gt_of_ne hn
  · exact ⟨(i,j), by simp [pairs, hlt], he⟩
  · exact ⟨(j,i), by simp [pairs, hgt], he.symm⟩

theorem collision_union_bound [LinearOrder I] {w : I → C → ℝ}
    (hw : ∀ i c, 0 ≤ w i c) :
    (∏ i, ∑ c, w i c) - injectiveSum w ≤
      ∑ ij ∈ pairs I, collisionSum w ij.1 ij.2 := by
  classical
  rw [← sum_assignmentWeight, injectiveSum, ← Finset.sum_sub_distrib]
  simp only [collisionSum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro f _
  have hnonneg : ∀ ij ∈ pairs I,
      0 ≤ (if f ij.1 = f ij.2 then assignmentWeight w f else 0) := by
    intro ij _
    split_ifs
    · exact assignmentWeight_nonneg hw f
    · rfl
  by_cases hf : Function.Injective f
  · simp only [hf, ↓reduceIte, sub_self]
    exact Finset.sum_nonneg hnonneg
  · simp only [hf, ↓reduceIte, sub_zero]
    obtain ⟨ij, hij, he⟩ := noninjective_has_pair hf
    simpa only [he, ↓reduceIte] using Finset.single_le_sum hnonneg hij

omit [Fintype I] [Fintype C] in

theorem prod_relative_error {J : Type u_4} (s : Finset J) (a b : J → ℝ) (e : ℝ)
    (he : 0 ≤ e) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hba : ∀ i ∈ s, b i ≤ a i)
    (herr : ∀ i ∈ s, a i - b i ≤ e * a i) :
    (∏ i ∈ s, a i) - (∏ i ∈ s, b i) ≤ (s.card : ℝ) * e * ∏ i ∈ s, a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    have hb' : ∀ i ∈ s, 0 ≤ b i := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hba' : ∀ i ∈ s, b i ≤ a i := fun i hi => hba i (Finset.mem_insert_of_mem hi)
    have ha' : ∀ i ∈ s, 0 ≤ a i := fun i hi => (hb' i hi).trans (hba' i hi)
    have hjb := hb j (Finset.mem_insert_self j s)
    have hja := hjb.trans (hba j (Finset.mem_insert_self j s))
    have h1 := mul_le_mul_of_nonneg_left
      (ih hb' hba' (fun i hi => herr i (Finset.mem_insert_of_mem hi))) hja
    have h2 := mul_le_mul_of_nonneg_right (herr j (Finset.mem_insert_self j s))
      (Finset.prod_nonneg hb')
    have h3 := mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ hb' hba')
      (mul_nonneg he hja)
    simp only [Finset.prod_insert hj, Finset.card_insert_of_notMem hj, Nat.cast_add,
      Nat.cast_one]
    nlinarith

theorem collision_error [LinearOrder I] (w v : I → C → ℝ) (d e : ℝ)
    (r : I → I → ℝ) (he : 0 ≤ e)
    (hw : ∀ i c, 0 ≤ w i c) (hwv : ∀ i c, w i c ≤ v i c)
    (hrow : ∀ i, (∑ c, v i c) - (∑ c, w i c) ≤ e * ∑ c, v i c)
    (hc : ∀ i j, i ≠ j → (∑ c, w i c * w j c) ≤ d * r i j) :
    0 ≤ (∏ i, ∑ c, v i c) - injectiveSum w ∧
    (∏ i, ∑ c, v i c) - injectiveSum w ≤
      (Fintype.card I : ℝ) * e * (∏ i, ∑ c, v i c) +
      d * ∑ ij ∈ pairs I, r ij.1 ij.2 *
        ∏ u ∈ (Finset.univ.erase ij.1).erase ij.2, ∑ c, v u c := by
  classical
  have hv : ∀ i c, 0 ≤ v i c := fun i c => (hw i c).trans (hwv i c)
  have hp : (∏ i, ∑ c, w i c) ≤ ∏ i, ∑ c, v i c :=
    Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg (fun c _ => hw i c))
      (fun i _ => Finset.sum_le_sum (fun c _ => hwv i c))
  refine ⟨sub_nonneg.mpr ((injectiveSum_le hw).trans hp), ?_⟩
  have ht := prod_relative_error (Finset.univ : Finset I)
    (fun i => ∑ c, v i c) (fun i => ∑ c, w i c) e he
    (fun i _ => Finset.sum_nonneg (fun c _ => hw i c))
    (fun i _ => Finset.sum_le_sum (fun c _ => hwv i c)) (fun i _ => hrow i)
  have hu := collision_union_bound hw
  have hc' : (∑ ij ∈ pairs I, collisionSum w ij.1 ij.2) ≤
      d * ∑ ij ∈ pairs I, r ij.1 ij.2 *
        ∏ u ∈ (Finset.univ.erase ij.1).erase ij.2, ∑ c, v u c := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ij hij
    have hne : ij.1 ≠ ij.2 := ne_of_lt (Finset.mem_filter.mp hij).2
    rw [collision_formula w hne]
    calc
      _ ≤ (d * r ij.1 ij.2) *
          ∏ u ∈ (Finset.univ.erase ij.1).erase ij.2, ∑ c, w u c :=
        mul_le_mul_of_nonneg_right (hc _ _ hne)
          (Finset.prod_nonneg (fun i _ => Finset.sum_nonneg (fun c _ => hw i c)))
      _ ≤ (d * r ij.1 ij.2) *
          ∏ u ∈ (Finset.univ.erase ij.1).erase ij.2, ∑ c, v u c := by
        apply mul_le_mul_of_nonneg_left
          (Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg (fun c _ => hw i c))
            (fun i _ => Finset.sum_le_sum (fun c _ => hwv i c)))
        exact (Finset.sum_nonneg (fun c _ => mul_nonneg (hw _ _) (hw _ _))).trans
          (hc _ _ hne)
      _ = _ := mul_assoc _ _ _
  simp only [Finset.card_univ] at ht
  linarith

omit [Fintype I] [Fintype C] in

theorem occupation_error {a d : ℝ} (ha : 0 ≤ a) (had : a ≤ d) :
    0 ≤ 1 - Real.exp (-a) ∧
    0 ≤ a - (1 - Real.exp (-a)) ∧
    a - (1 - Real.exp (-a)) ≤ a ^ 2 / 2 ∧ a ^ 2 / 2 ≤ d * a / 2 := by
  have hmono : Monotone (fun x : ℝ => 1 - x + x ^ 2 / 2 - Real.exp (-x)) := by
    apply monotone_of_hasDerivAt_nonneg (f' := fun x => x - 1 + Real.exp (-x))
    · intro x
      convert! (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add
        (((hasDerivAt_id x).pow 2).div_const 2)).sub
        (((hasDerivAt_id x).neg).exp) using 1; norm_num; ring
    · intro x
      change 0 ≤ x - 1 + Real.exp (-x)
      have h := Real.add_one_le_exp (-x)
      linarith
  have hh := hmono ha
  simp only [neg_zero, Real.exp_zero, sub_zero, zero_pow (by omega : 2 ≠ 0),
    zero_div, add_zero, sub_self] at hh
  have hlin := Real.add_one_le_exp (-a)
  have hexp := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)
  have hsq := mul_le_mul_of_nonneg_right had ha
  refine ⟨by linarith, by linarith, by linarith, by nlinarith⟩

noncomputable def slotWeight (A : I → C → Prop) (q : C → ℝ) (i : I) (c : C) : ℝ :=
  if A i c then q c else 0

theorem cell_collision_error [LinearOrder I] (A : I → C → Prop) (a : C → ℝ)
    {d : ℝ} (hd : 0 ≤ d) (ha : ∀ c, 0 ≤ a c) (had : ∀ c, a c ≤ d) :
    let v := slotWeight A a
    let w := slotWeight A (fun c => 1 - Real.exp (-a c))
    let mass := fun i => ∑ c, v i c
    let overlap := fun i j => ∑ c, if A i c ∧ A j c then a c else 0
    0 ≤ (∏ i, mass i) - injectiveSum w ∧
    (∏ i, mass i) - injectiveSum w ≤ d *
      ((Fintype.card I : ℝ) / 2 * (∏ i, mass i) +
        ∑ ij ∈ pairs I, overlap ij.1 ij.2 *
          ∏ u ∈ (Finset.univ.erase ij.1).erase ij.2, mass u) := by
  classical
  dsimp only
  have hoc := fun c => occupation_error (ha c) (had c)
  have hw : ∀ i c, 0 ≤ slotWeight A (fun c => 1 - Real.exp (-a c)) i c := by
    intro i c
    unfold slotWeight
    split_ifs
    · exact (hoc c).1
    · rfl
  have hwv : ∀ i c, slotWeight A (fun c => 1 - Real.exp (-a c)) i c ≤
      slotWeight A a i c := by
    intro i c
    unfold slotWeight
    split_ifs
    · linarith [(hoc c).2.1]
    · rfl
  have hrow : ∀ i, (∑ c, slotWeight A a i c) -
      (∑ c, slotWeight A (fun c => 1 - Real.exp (-a c)) i c) ≤
      (d / 2) * ∑ c, slotWeight A a i c := by
    intro i
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c _
    unfold slotWeight
    split_ifs
    · have h := (hoc c).2.2.1.trans (hoc c).2.2.2
      linarith
    · simp
  have hcol : ∀ i j, i ≠ j →
     (∑ c, slotWeight A (fun c => 1 - Real.exp (-a c)) i c *
       slotWeight A (fun c => 1 - Real.exp (-a c)) j c) ≤
      d * ∑ c, if A i c ∧ A j c then a c else 0 := by
    intro i j _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c _
    by_cases hi : A i c <;> by_cases hj : A j c <;>
      simp only [slotWeight, hi, hj, and_self, and_false, false_and,
        ↓reduceIte, mul_zero, zero_mul, le_refl]
    have hpa : 1 - Real.exp (-a c) ≤ a c := by linarith [(hoc c).2.1]
    calc
      _ ≤ a c * a c := mul_self_le_mul_self (hoc c).1 hpa
      _ ≤ d * a c := mul_le_mul_of_nonneg_right (had c) (ha c)
  have h := collision_error (slotWeight A (fun c => 1 - Real.exp (-a c)))
    (slotWeight A a) d (d / 2)
    (fun i j => ∑ c, if A i c ∧ A j c then a c else 0)
    (by positivity) hw hwv hrow hcol
  refine ⟨h.1, h.2.trans_eq ?_⟩
  ring

lemma injectiveSum_eq_embeddings (w : I → C → ℝ) :
    injectiveSum w = ∑ f : I ↪ C, ∏ i, w i (f i) := by
  classical
  rw [injectiveSum, ← Finset.sum_filter]
  rw [Finset.sum_subtype _ (show ∀ f : I → C, f ∈ Finset.univ.filter Function.Injective ↔ Function.Injective f by simp)]
  exact (Equiv.subtypeInjectiveEquivEmbedding I C).sum_comp
    (fun f => ∏ i, w i (f i))

omit [Fintype C] in
lemma assignmentWeight_slot (A : I → C → Prop) (p : C → ℝ) (f : I → C) :
    assignmentWeight (slotWeight A p) f =
      if ∀ i, A i (f i) then ∏ i, p (f i) else 0 := by
  classical
  by_cases h : ∀ i, A i (f i)
  · rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro i _
    exact ite_eq_left (h i)
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right hi

lemma injectiveSum_slot_eq (A : I → C → Prop) (p : C → ℝ) :
    injectiveSum (slotWeight A p) = ∑ f : I ↪ C,
      if ∀ i, A i (f i) then ∏ i, p (f i) else 0 := by
  rw [injectiveSum_eq_embeddings]
  apply Finset.sum_congr rfl
  intro f _
  exact assignmentWeight_slot A p f

end CellCounts

end OAI
