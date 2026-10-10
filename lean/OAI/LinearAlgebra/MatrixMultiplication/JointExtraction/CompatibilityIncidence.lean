import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.TypeCounts
import Mathlib.Logic.Equiv.Option

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointCompatibilityIncidence

open MatrixMultiplication.Foundation JointTypeCounts
open scoped BigOperators

attribute [local instance] Classical.propDecidable

section Actions

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (Pos A : C → Type*)
  [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

abbrev ClassPerm := ∀ c, Equiv.Perm (Pos c)

def permuteFixedWords (counts : ∀ c, A c → ℕ)
    (g : ClassPerm Pos) (w : FixedClassWords Pos A counts) :
    FixedClassWords Pos A counts :=
  fun c => ⟨(w c).val ∘ ((g c)⁻¹ : Equiv.Perm (Pos c)), fun a =>
    (wordPopulation_reindex (w c).val (g c)⁻¹ a).trans ((w c).property a)⟩

@[instance_reducible]
def fixedWordsMulAction (counts : ∀ c, A c → ℕ) :
    MulAction (ClassPerm Pos) (FixedClassWords Pos A counts) where
  smul := permuteFixedWords Pos A counts
  one_smul w := by
    funext c
    apply Subtype.ext
    funext i
    rfl
  mul_smul g h w := by
    funext c
    apply Subtype.ext
    funext i
    change (w c).val (((g * h) c)⁻¹ i) =
      (w c).val ((h c)⁻¹ ((g c)⁻¹ i))
    simp only [Pi.mul_apply, mul_inv_rev, Equiv.Perm.mul_apply]

attribute [local instance] fixedWordsMulAction

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Pos c)] [∀ c, Fintype (A c)] in
theorem fixedWordsPretransitive (counts : ∀ c, A c → ℕ) :
    MulAction.IsPretransitive (ClassPerm Pos) (FixedClassWords Pos A counts) where
  exists_smul_eq w v := by
    obtain ⟨e, he⟩ := fixedClassWords_transitive Pos A counts w v
    refine ⟨fun c => (e c)⁻¹, ?_⟩
    funext c
    apply Subtype.ext
    change (w c).val ∘ (((e c)⁻¹)⁻¹ : Equiv.Perm (Pos c)) = (v c).val
    simpa only [inv_inv] using he c

attribute [local instance] fixedWordsPretransitive

end Actions

attribute [local instance] fixedWordsMulAction fixedWordsPretransitive

section Counts

variable {P U Z A : Type*} [Fintype P] [DecidableEq U] [DecidableEq A]

def jointCount (w : P → U) (z : P → Z) (part : Z → A) (u : U) (a : A) : ℕ :=
  Fintype.card {i : P // w i = u ∧ part (z i) = a}

theorem jointCount_reindex (w : P → U) (z : P → Z) (part : Z → A)
    (e : Equiv.Perm P) (u : U) (a : A) :
    jointCount (w ∘ e) (z ∘ e) part u a = jointCount w z part u a := by
  exact Fintype.card_congr (Equiv.subtypeEquiv e fun _ => Iff.rfl)

variable [DecidableEq P] [Fintype U] [Fintype A]

omit [DecidableEq P] [Fintype A] in
theorem jointCount_sum_shapes (w : P → U) (z : P → Z) (part : Z → A) (a : A) :
    (∑ u, jointCount w z part u a) = wordPopulation (part ∘ z) a := by
  calc
    (∑ u, jointCount w z part u a) =
        ∑ u, wordPopulation (fun i : {i : P // part (z i) = a} => w i.val) u := by
      apply Finset.sum_congr rfl
      intro u _
      rw [wordPopulation_fiber]
      exact Fintype.card_congr (Equiv.subtypeEquivRight fun _ => and_comm)
    _ = wordPopulation (part ∘ z) a := wordPopulation_sum _

omit [DecidableEq P] [Fintype A] in
theorem projected_restrict_population (w : P → U) (z : P → Z) (part : Z → A)
    (d : U → Prop) (a : A) :
    wordPopulation (fun i : {i : P // d (w i)} => part (z i.val)) a =
      ∑ u : {u : U // d u}, jointCount w z part u.val a := by
  let e : {i : {i : P // d (w i)} // part (z i.val) = a} ≃
      Σ u : {u : U // d u}, {i : P // w i = u.val ∧ part (z i) = a} :=
    { toFun := fun i => ⟨⟨w i.val.val, i.val.property⟩,
        ⟨i.val.val, rfl, i.property⟩⟩
      invFun := fun i => ⟨⟨i.2.val, by
        rw [i.2.property.1]
        exact i.1.property⟩, i.2.property.2⟩
      left_inv := by intro i; rfl
      right_inv := by
        rintro ⟨⟨u, hu⟩, i, hi, ha⟩
        cases hi
        rfl }
  simpa only [wordPopulation, Fintype.card_sigma, jointCount] using Fintype.card_congr e

omit [DecidableEq P] [Fintype A] in
theorem residual_population_add_designated (w : P → U) (z : P → Z)
    (part : Z → A) (d : U → Prop) (a : A) :
    wordPopulation (fun i : {i : P // ¬d (w i)} => part (z i.val)) a +
      ∑ u : {u : U // d u}, jointCount w z part u.val a =
        wordPopulation (part ∘ z) a := by
  have hres :
      wordPopulation (fun i : {i : P // ¬d (w i)} => part (z i.val)) a =
        ∑ u : {u : U // ¬d u}, jointCount w z part u.val a := by
    convert projected_restrict_population w z part (fun u => ¬d u) a using 1 <;> congr 1
    · exact Subsingleton.elim _ _
    · ext u
      simp
  rw [hres, add_comm]
  exact (Fintype.sum_subtype_add_sum_subtype d
    (fun u => jointCount w z part u a)).trans (jointCount_sum_shapes w z part a)

omit [DecidableEq P] [Fintype A] in
theorem projected_population_fixed [Fintype Z] [DecidableEq Z]
    (z : P → Z) (counts : Z → ℕ) (hz : ∀ s, wordPopulation z s = counts s)
    (part : Z → A) (a : A) :
    wordPopulation (part ∘ z) a = ∑ s : {s : Z // part s = a}, counts s.val := by
  have h := (Fintype.card_congr
    (Equiv.sigmaSubtypeFiberEquivSubtype z
      (p := fun i => part (z i) = a) (q := fun s => part s = a)
      (fun _ => Iff.rfl))).symm
  simp only [Fintype.card_sigma] at h
  change wordPopulation (part ∘ z) a =
    ∑ s : {s : Z // part s = a}, wordPopulation z s.val at h
  simpa only [hz] using h

omit [DecidableEq P] [Fintype A] in
theorem residual_projected_window (w : P → U) (z : P → Z) (part : Z → A)
    (d : U → Prop) (counts : U → ℕ) (law : U → A → ℝ)
    (residualLaw totalTarget : A → ℝ) (χ η : ℝ) (a : A)
    (hmass : 0 < Fintype.card {i : P // ¬d (w i)})
    (htotal : |(wordPopulation (part ∘ z) a : ℝ) - totalTarget a| ≤ η)
    (hdesignated : ∀ u, d u →
      |(jointCount w z part u a : ℝ) - (counts u : ℝ) * law u a| ≤
        (counts u : ℝ) * χ)
    (hbalance : (Fintype.card {i : P // ¬d (w i)} : ℝ) * residualLaw a =
      totalTarget a - ∑ u : {u : U // d u}, (counts u.val : ℝ) * law u.val a) :
    |(wordPopulation (fun i : {i : P // ¬d (w i)} => part (z i.val)) a : ℝ) /
        Fintype.card {i : P // ¬d (w i)} - residualLaw a| ≤
      (η + (∑ u : {u : U // d u}, (counts u.val : ℝ)) * χ) /
        Fintype.card {i : P // ¬d (w i)} := by
  have hm : (0 : ℝ) < Fintype.card {i : P // ¬d (w i)} := Nat.cast_pos.mpr hmass
  have hsplit :
      (wordPopulation (fun i : {i : P // ¬d (w i)} => part (z i.val)) a : ℝ) =
        wordPopulation (part ∘ z) a -
          ∑ u : {u : U // d u}, (jointCount w z part u.val a : ℝ) := by
    have h := residual_population_add_designated w z part d a
    have h' :
        (wordPopulation (fun i : {i : P // ¬d (w i)} => part (z i.val)) a : ℝ) +
          ∑ u : {u : U // d u}, (jointCount w z part u.val a : ℝ) =
            wordPopulation (part ∘ z) a := by exact_mod_cast h
    exact eq_sub_of_add_eq h'
  have hd : |(∑ u : {u : U // d u}, (jointCount w z part u.val a : ℝ)) -
      ∑ u : {u : U // d u}, (counts u.val : ℝ) * law u.val a| ≤
        (∑ u : {u : U // d u}, (counts u.val : ℝ)) * χ := by
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun u _ => hdesignated u.val u.property)
  exact residual_window_error hm (by rwa [mul_div_cancel₀ _ hm.ne'])
    hbalance htotal hd

end Counts

section Groups

variable {P U Z A : Type*} [Fintype P] [DecidableEq P]
  [Fintype U] [DecidableEq U] [Fintype A] [DecidableEq A]

def designatedGroup (d : U → Prop) (u : U) : Option U :=
  if d u then some u else none

omit [Fintype U] [DecidableEq U] in
theorem designatedGroup_eq_some (d : U → Prop) (u v : U) :
    designatedGroup d v = some u ↔ d u ∧ v = u := by
  constructor
  · intro h
    by_cases hv : d v
    · have he : v = u := Option.some.inj (by simpa [designatedGroup, hv] using h)
      exact ⟨he ▸ hv, he⟩
    · simp [designatedGroup, hv] at h
  · rintro ⟨hu, rfl⟩
    simp [designatedGroup, hu]

omit [Fintype U] [DecidableEq U] in
theorem designatedGroup_eq_none (d : U → Prop) (v : U) :
    designatedGroup d v = none ↔ ¬d v := by
  simp [designatedGroup]

abbrev GroupPos (w : P → U) (d : U → Prop) (k : Option U) :=
  {i : P // designatedGroup d (w i) = k}

def groupProjection (w : P → U) (d : U → Prop) (k : Option U)
    (z : P → Z) (part : Z → A) : GroupPos w d k → A :=
  fun i => part (z i.val)

omit [DecidableEq P] [Fintype U] in
theorem groupPos_card_some (w : P → U) (d : U → Prop) (u : U) (hu : d u) :
    Fintype.card (GroupPos w d (some u)) = wordPopulation w u := by
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight fun i => by simp [designatedGroup_eq_some, hu]

omit [DecidableEq P] [Fintype U] [DecidableEq U] in
theorem groupPos_card_none (w : P → U) (d : U → Prop) :
    Fintype.card (GroupPos w d none) = Fintype.card {i : P // ¬d (w i)} := by
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight fun i => designatedGroup_eq_none d (w i)

omit [DecidableEq P] in
theorem restrict_card_eq_sum_population (w : P → U) (d : U → Prop) :
    Fintype.card {i : P // d (w i)} =
      ∑ u : {u : U // d u}, wordPopulation w u.val := by
  simpa only [Fintype.card_sigma, wordPopulation] using
    (Fintype.card_congr (Equiv.sigmaSubtypeFiberEquivSubtype w
      (p := fun i => d (w i)) (q := d) (fun _ => Iff.rfl))).symm

omit [DecidableEq P] [Fintype A] [Fintype U] in
theorem groupProjection_population_some (w : P → U) (d : U → Prop)
    (u : U) (hu : d u) (z : P → Z) (part : Z → A) (a : A) :
    wordPopulation (groupProjection w d (some u) z part) a =
      jointCount w z part u a := by
  apply Fintype.card_congr
  refine (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun i : P => designatedGroup d (w i) = some u)
    (fun i : P => part (z i) = a)).trans ?_
  exact Equiv.subtypeEquivRight fun i => by simp [designatedGroup_eq_some, hu]

omit [DecidableEq P] [Fintype A] [Fintype U] [DecidableEq U] in
theorem groupProjection_population_none (w : P → U) (d : U → Prop)
    (z : P → Z) (part : Z → A) (a : A) :
    wordPopulation (groupProjection w d none z part) a =
      wordPopulation (fun i : {i : P // ¬d (w i)} => part (z i.val)) a := by
  apply Fintype.card_congr
  exact (Equiv.subtypeEquiv
    (Equiv.subtypeEquivRight fun i => designatedGroup_eq_none d (w i)) fun _ => Iff.rfl)

theorem normalized_count_window {x n p χ : ℝ} (hn : 0 < n)
    (h : |x - n * p| ≤ n * χ) : |x / n - p| ≤ χ := by
  apply (mul_le_mul_iff_left₀ hn).mp
  calc
    |x / n - p| * n = |(x / n - p) * n| := by rw [abs_mul, abs_of_pos hn]
    _ = |x - n * p| := by rw [sub_mul, div_mul_cancel₀ _ hn.ne', mul_comm p n]
    _ ≤ n * χ := h
    _ = χ * n := mul_comm _ _

omit [DecidableEq P] in
theorem group_entropy_of_designated_windows
    (w : P → U) (z : P → Z) (part : Z → A) (d : U → Prop)
    (counts : U → ℕ) (hcounts : ∀ u, wordPopulation w u = counts u)
    (law : U → A → ℝ) (residualLaw totalTarget : A → ℝ)
    (χ η : ℝ) (H : Option U → ℝ) (hH : ∀ k, 0 ≤ H k)
    (htotal : ∀ a, |(wordPopulation (part ∘ z) a : ℝ) - totalTarget a| ≤ η)
    (hdesignated : ∀ u, d u → ∀ a,
      |(jointCount w z part u a : ℝ) - (counts u : ℝ) * law u a| ≤
        (counts u : ℝ) * χ)
    (hbalance : ∀ a, (Fintype.card {i : P // ¬d (w i)} : ℝ) * residualLaw a =
      totalTarget a - ∑ u : {u : U // d u}, (counts u.val : ℝ) * law u.val a)
    (hcapDesignated : ∀ u, d u → ∀ q : A → ℝ,
      (∀ a, |q a - law u a| ≤ χ) → finiteEntropy q ≤ H (some u))
    (hcapResidual : ∀ q : A → ℝ,
      (∀ a, |q a - residualLaw a| ≤
        (η + (∑ u : {u : U // d u}, (counts u.val : ℝ)) * χ) /
          Fintype.card {i : P // ¬d (w i)}) → finiteEntropy q ≤ H none)
    (k : Option U) :
    finiteEntropy (fun a => (wordPopulation (groupProjection w d k z part) a : ℝ) /
      Fintype.card (GroupPos w d k)) ≤ H k := by
  by_cases hzero : Fintype.card (GroupPos w d k) = 0
  · simpa only [hzero, Nat.cast_zero, div_zero, finiteEntropy, entropyTerm_zero,
      Finset.sum_const_zero] using hH k
  have hpos : 0 < Fintype.card (GroupPos w d k) := Nat.pos_of_ne_zero hzero
  cases k with
  | some u =>
      obtain ⟨i⟩ := Fintype.card_pos_iff.mp hpos
      have hu : d u := ((designatedGroup_eq_some d u (w i.val)).mp i.property).1
      have hm : 0 < counts u := by
        simpa only [groupPos_card_some w d u hu, hcounts u] using hpos
      apply hcapDesignated u hu
      intro a
      simp only [groupProjection_population_some w d u hu,
        groupPos_card_some w d u hu, hcounts u]
      exact normalized_count_window (Nat.cast_pos.mpr hm) (hdesignated u hu a)
  | none =>
      apply hcapResidual
      intro a
      simp only [groupProjection_population_none, groupPos_card_none]
      exact residual_projected_window w z part d counts law residualLaw totalTarget χ η a
        (by simpa only [groupPos_card_none] using hpos) (htotal a)
        (fun u hu => hdesignated u hu a) (hbalance a)

end Groups

section GroupEntropy

variable {U K A : Type*} [Fintype U] [Fintype K] [Fintype A]

def groupMass (p : U → ℝ) (group : U → K) (k : K) : ℝ :=
  ∑ u, if group u = k then p u else 0

def groupLaw (p : U → ℝ) (group : U → K) (law : U → A → ℝ)
    (k : K) (a : A) : ℝ :=
  (∑ u, if group u = k then p u * law u a else 0) / groupMass p group k

def groupedEntropy (p : U → ℝ) (group : U → K) (law : U → A → ℝ) : ℝ :=
  ∑ k, groupMass p group k * finiteEntropy (groupLaw p group law k)

omit [Fintype K] in
theorem groupMass_relabel {L : Type*} (e : K ≃ L) (p : U → ℝ)
    (group : U → K) (k : K) :
    groupMass p (e ∘ group) (e k) = groupMass p group k := by
  simp only [groupMass, Function.comp_apply, e.injective.eq_iff]

omit [Fintype A] [Fintype K] in
theorem groupLaw_relabel {L : Type*} (e : K ≃ L) (p : U → ℝ)
    (group : U → K) (law : U → A → ℝ) (k : K) :
    groupLaw p (e ∘ group) law (e k) = groupLaw p group law k := by
  funext a
  simp only [groupLaw, groupMass_relabel, Function.comp_apply, e.injective.eq_iff]

theorem groupedEntropy_relabel {L : Type*} [Fintype L] (e : K ≃ L)
    (p : U → ℝ) (group : U → K) (law : U → A → ℝ) :
    groupedEntropy p (e ∘ group) law = groupedEntropy p group law := by
  unfold groupedEntropy
  calc
    (∑ l, groupMass p (e ∘ group) l * finiteEntropy (groupLaw p (e ∘ group) law l)) =
        ∑ k, groupMass p (e ∘ group) (e k) *
          finiteEntropy (groupLaw p (e ∘ group) law (e k)) := (e.sum_comp _).symm
    _ = ∑ k, groupMass p group k * finiteEntropy (groupLaw p group law k) := by
      simp only [groupMass_relabel, groupLaw_relabel]

omit [Fintype K] in
theorem groupMass_reindex (e : U ≃ U) (p : U → ℝ) (group : U → K)
    (hp : ∀ u, p (e u) = p u) (k : K) :
    groupMass p (group ∘ e) k = groupMass p group k := by
  unfold groupMass
  calc
    (∑ u, if (group ∘ e) u = k then p u else 0) =
        ∑ u, if group (e u) = k then p (e u) else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      simp only [Function.comp_apply, hp u]
    _ = ∑ u, if group u = k then p u else 0 :=
      e.sum_comp (fun u => if group u = k then p u else 0)

omit [Fintype A] [Fintype K] in
theorem groupLaw_reindex (e : U ≃ U) (p : U → ℝ) (group : U → K)
    (law : U → A → ℝ) (hp : ∀ u, p (e u) = p u) (k : K) :
    groupLaw p (group ∘ e) (law ∘ e) k = groupLaw p group law k := by
  funext a
  unfold groupLaw
  rw [groupMass_reindex e p group hp]
  congr 1
  calc
    (∑ u, if (group ∘ e) u = k then p u * (law ∘ e) u a else 0) =
        ∑ u, if group (e u) = k then p (e u) * law (e u) a else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      simp only [Function.comp_apply, hp u]
    _ = ∑ u, if group u = k then p u * law u a else 0 :=
      e.sum_comp (fun u => if group u = k then p u * law u a else 0)

theorem groupedEntropy_reindex (e : U ≃ U) (p : U → ℝ) (group : U → K)
    (law : U → A → ℝ) (hp : ∀ u, p (e u) = p u) :
    groupedEntropy p (group ∘ e) (law ∘ e) = groupedEntropy p group law := by
  simp only [groupedEntropy, groupMass_reindex e p group hp,
    groupLaw_reindex e p group law hp]

theorem groupedEntropy_add_reindex (e : U ≃ U) (p : U → ℝ) (group : U → K)
    (law : U → A → ℝ) (hp : ∀ u, p (e u) = p u) :
    groupedEntropy p group law + groupedEntropy p (group ∘ e) (law ∘ e) =
      2 * groupedEntropy p group law := by
  rw [groupedEntropy_reindex e p group law hp]
  ring

omit [Fintype U] in
theorem designatedGroup_transport (e : U ≃ U) (d : U → Prop) :
    e.optionCongr ∘ designatedGroup (d ∘ e) = designatedGroup d ∘ e := by
  funext u
  by_cases h : d (e u) <;>
    simp [designatedGroup, Function.comp_apply, Equiv.optionCongr_apply, h]

theorem designated_groupedEntropy_reindex (e : U ≃ U) (p : U → ℝ)
    (d : U → Prop) (law : U → A → ℝ) (hp : ∀ u, p (e u) = p u) :
    groupedEntropy p (designatedGroup (d ∘ e)) (law ∘ e) =
      groupedEntropy p (designatedGroup d) law := by
  calc
    groupedEntropy p (designatedGroup (d ∘ e)) (law ∘ e) =
        groupedEntropy p (e.optionCongr ∘ designatedGroup (d ∘ e)) (law ∘ e) :=
      (groupedEntropy_relabel e.optionCongr p (designatedGroup (d ∘ e)) (law ∘ e)).symm
    _ = groupedEntropy p (designatedGroup d ∘ e) (law ∘ e) := by
      rw [designatedGroup_transport]
    _ = groupedEntropy p (designatedGroup d) law :=
      groupedEntropy_reindex e p (designatedGroup d) law hp

end GroupEntropy

section SideControls

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (Pos Shape Pair A : C → Type*)
  [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable (shapeCounts : ∀ c, Shape c → ℕ) (pairCounts : ∀ c, Pair c → ℕ)
  (part : ∀ c, Pair c → A c) (designated : ∀ c, Shape c → Prop)
  (law : ∀ c, Shape c → A c → ℝ) (χ : ℝ)
  (H : (Σ c, Option (Shape c)) → ℝ) (w : FixedClassWords Pos Shape shapeCounts)

structure SideEntropyControl where
  residualLaw : ∀ c, A c → ℝ
  totalTarget : ∀ c, A c → ℝ
  totalError : C → ℝ
  aggregate_window : ∀ c a,
    |((∑ s : {s : Pair c // part c s = a}, pairCounts c s.val : ℕ) : ℝ) -
      totalTarget c a| ≤ totalError c
  mixture_balance : ∀ c a,
    (Fintype.card {i : Pos c // ¬designated c ((w c).val i)} : ℝ) * residualLaw c a =
      totalTarget c a - ∑ u : {u : Shape c // designated c u},
        (shapeCounts c u.val : ℝ) * law c u.val a
  nonneg : ∀ g, 0 ≤ H g
  designated_entropy : ∀ c u, designated c u → ∀ q : A c → ℝ,
    (∀ a, |q a - law c u a| ≤ χ) → finiteEntropy q ≤ H ⟨c, some u⟩
  residual_entropy : ∀ c, ∀ q : A c → ℝ,
    (∀ a, |q a - residualLaw c a| ≤
      (totalError c + (∑ u : {u : Shape c // designated c u},
        (shapeCounts c u.val : ℝ)) * χ) /
          Fintype.card {i : Pos c // ¬designated c ((w c).val i)}) →
      finiteEntropy q ≤ H ⟨c, none⟩

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Pos c)] in
theorem SideEntropyControl.group_entropy
    (control : SideEntropyControl Pos Shape Pair A shapeCounts pairCounts
      part designated law χ H w)
    (z : FixedClassWords Pos Pair pairCounts)
    (hdesignated : ∀ c u, designated c u → ∀ a,
      |(jointCount (w c).val (z c).val (part c) u a : ℝ) -
        (shapeCounts c u : ℝ) * law c u a| ≤ (shapeCounts c u : ℝ) * χ)
    (g : Σ c, Option (Shape c)) :
    finiteEntropy (fun a =>
      (wordPopulation (groupProjection (w g.1).val (designated g.1) g.2
        (z g.1).val (part g.1)) a : ℝ) /
          Fintype.card (GroupPos (w g.1).val (designated g.1) g.2)) ≤ H g := by
  apply group_entropy_of_designated_windows (w g.1).val (z g.1).val (part g.1)
    (designated g.1) (shapeCounts g.1) (w g.1).property (law g.1)
    (control.residualLaw g.1) (control.totalTarget g.1) χ (control.totalError g.1)
    (fun k => H ⟨g.1, k⟩) (fun k => control.nonneg ⟨g.1, k⟩)
  · intro a
    rw [projected_population_fixed (z g.1).val (pairCounts g.1) (z g.1).property]
    exact control.aggregate_window g.1 a
  · exact hdesignated g.1
  · exact control.mixture_balance g.1
  · exact control.designated_entropy g.1
  · exact control.residual_entropy g.1

end SideControls

section Compatibility

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (Pos Shape Pair Left Right : C → Type*)
  [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]
  [∀ c, Fintype (Left c)] [∀ c, DecidableEq (Left c)]
  [∀ c, Fintype (Right c)] [∀ c, DecidableEq (Right c)]
variable (shapeCounts : ∀ c, Shape c → ℕ) (pairCounts : ∀ c, Pair c → ℕ)
  (leftPart : ∀ c, Pair c → Left c) (rightPart : ∀ c, Pair c → Right c)
  (designatedLeft designatedRight : ∀ c, Shape c → Prop)
  (leftLaw : ∀ c, Shape c → Left c → ℝ)
  (rightLaw : ∀ c, Shape c → Right c → ℝ) (χ : ℝ)

def DesignatedCompatibility (w : FixedClassWords Pos Shape shapeCounts)
    (z : FixedClassWords Pos Pair pairCounts) : Prop :=
  (∀ c u, designatedLeft c u → ∀ a,
    |(jointCount (w c).val (z c).val (leftPart c) u a : ℝ) -
      (shapeCounts c u : ℝ) * leftLaw c u a| ≤ (shapeCounts c u : ℝ) * χ) ∧
  (∀ c u, designatedRight c u → ∀ a,
    |(jointCount (w c).val (z c).val (rightPart c) u a : ℝ) -
      (shapeCounts c u : ℝ) * rightLaw c u a| ≤ (shapeCounts c u : ℝ) * χ)

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (Shape c)] [∀ c, Fintype (Pair c)]
  [∀ c, Fintype (Left c)] [∀ c, Fintype (Right c)] in
theorem designatedCompatibility_permute (g : ClassPerm Pos)
    (w : FixedClassWords Pos Shape shapeCounts)
    (z : FixedClassWords Pos Pair pairCounts) :
    DesignatedCompatibility Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ
      (permuteFixedWords Pos Shape shapeCounts g w)
      (permuteFixedWords Pos Pair pairCounts g z) ↔
    DesignatedCompatibility Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w z := by
  simp only [DesignatedCompatibility, permuteFixedWords, jointCount_reindex]

def compatibleStatisticCount (w : FixedClassWords Pos Shape shapeCounts) : ℕ :=
  Fintype.card {z : FixedClassWords Pos Pair pairCounts //
    DesignatedCompatibility Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w z}

def compatibleCandidateCount (z : FixedClassWords Pos Pair pairCounts) : ℕ :=
  Fintype.card {w : FixedClassWords Pos Shape shapeCounts //
    DesignatedCompatibility Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w z}

omit [∀ c, Fintype (Left c)] [∀ c, Fintype (Right c)] in
theorem designated_incidence_count
    (w : FixedClassWords Pos Shape shapeCounts)
    (z : FixedClassWords Pos Pair pairCounts) :
    Fintype.card (FixedClassWords Pos Shape shapeCounts) *
      compatibleStatisticCount Pos Shape Pair Left Right shapeCounts pairCounts
        leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w =
    Fintype.card (FixedClassWords Pos Pair pairCounts) *
      compatibleCandidateCount Pos Shape Pair Left Right shapeCounts pairCounts
        leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z := by
  exact invariant_incidence_count (G := ClassPerm Pos)
    (DesignatedCompatibility Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ)
    (designatedCompatibility_permute Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ) w z

omit [∀ c, Fintype (Left c)] [∀ c, Fintype (Right c)] in
theorem designated_incidence_multinomial
    (hshape : ∀ c, Fintype.card (Pos c) = ∑ u, shapeCounts c u)
    (hpair : ∀ c, Fintype.card (Pos c) = ∑ a, pairCounts c a)
    (w : FixedClassWords Pos Shape shapeCounts)
    (z : FixedClassWords Pos Pair pairCounts) :
    (∏ c, Nat.multinomial Finset.univ (shapeCounts c)) *
      compatibleStatisticCount Pos Shape Pair Left Right shapeCounts pairCounts
        leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w =
    (∏ c, Nat.multinomial Finset.univ (pairCounts c)) *
      compatibleCandidateCount Pos Shape Pair Left Right shapeCounts pairCounts
        leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z := by
  simpa only [fixedClassWords_card Pos Shape shapeCounts hshape,
    fixedClassWords_card Pos Pair pairCounts hpair] using
    designated_incidence_count Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w z

omit [∀ c, Fintype (Left c)] [∀ c, Fintype (Right c)] in
theorem compatibleCandidateCount_eq
    (w : FixedClassWords Pos Shape shapeCounts)
    (z : FixedClassWords Pos Pair pairCounts) :
    (compatibleCandidateCount Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) =
      (Fintype.card (FixedClassWords Pos Shape shapeCounts) : ℝ) *
        compatibleStatisticCount Pos Shape Pair Left Right shapeCounts pairCounts
          leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w /
        Fintype.card (FixedClassWords Pos Pair pairCounts) := by
  exact invariant_incidence_degree_eq (G := ClassPerm Pos)
    (DesignatedCompatibility Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ)
    (designatedCompatibility_permute Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ) w z

def wordEntropyBound (I A : Type*) [Fintype I] [Fintype A] (H : ℝ) : ℝ :=
  ((Fintype.card I : ℝ) + 1) ^ Fintype.card A *
    Real.exp ((Fintype.card I : ℝ) * H +
      ((Fintype.card A : ℝ) + 1) * (1 + Real.log (Fintype.card I + 1 : ℕ)))

theorem compatibleStatisticCount_le_grouped_entropy
    (w : FixedClassWords Pos Shape shapeCounts)
    (hpair : ∀ c, Function.Injective (fun s : Pair c => (leftPart c s, rightPart c s)))
    (HL HR : (Σ c, Option (Shape c)) → ℝ)
    (hL : ∀ z : FixedClassWords Pos Pair pairCounts,
      DesignatedCompatibility Pos Shape Pair Left Right shapeCounts pairCounts
        leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w z →
      ∀ g : Σ c, Option (Shape c),
        finiteEntropy (fun a =>
          (wordPopulation (groupProjection (w g.1).val (designatedLeft g.1) g.2
            (z g.1).val (leftPart g.1)) a : ℝ) /
              Fintype.card (GroupPos (w g.1).val (designatedLeft g.1) g.2)) ≤ HL g)
    (hR : ∀ z : FixedClassWords Pos Pair pairCounts,
      DesignatedCompatibility Pos Shape Pair Left Right shapeCounts pairCounts
        leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w z →
      ∀ g : Σ c, Option (Shape c),
        finiteEntropy (fun a =>
          (wordPopulation (groupProjection (w g.1).val (designatedRight g.1) g.2
            (z g.1).val (rightPart g.1)) a : ℝ) /
              Fintype.card (GroupPos (w g.1).val (designatedRight g.1) g.2)) ≤ HR g) :
    (compatibleStatisticCount Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w : ℝ) ≤
      (∏ g : Σ c, Option (Shape c), wordEntropyBound
        (GroupPos (w g.1).val (designatedLeft g.1) g.2) (Left g.1) (HL g)) *
      (∏ g : Σ c, Option (Shape c), wordEntropyBound
        (GroupPos (w g.1).val (designatedRight g.1) g.2) (Right g.1) (HR g)) := by
  let J := Σ c, Option (Shape c)
  let PL : J → Type _ := fun g => GroupPos (w g.1).val (designatedLeft g.1) g.2
  let PR : J → Type _ := fun g => GroupPos (w g.1).val (designatedRight g.1) g.2
  let EL := ∀ g : J, {v : PL g → Left g.1 //
    finiteEntropy (fun a => (wordPopulation v a : ℝ) / Fintype.card (PL g)) ≤ HL g}
  let ER := ∀ g : J, {v : PR g → Right g.1 //
    finiteEntropy (fun a => (wordPopulation v a : ℝ) / Fintype.card (PR g)) ≤ HR g}
  let Row := {z : FixedClassWords Pos Pair pairCounts //
    DesignatedCompatibility Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w z}
  let encode : Row → EL × ER := fun z =>
    (fun g => ⟨groupProjection (w g.1).val (designatedLeft g.1) g.2
      (z.val g.1).val (leftPart g.1), hL z.val z.property g⟩,
     fun g => ⟨groupProjection (w g.1).val (designatedRight g.1) g.2
      (z.val g.1).val (rightPart g.1), hR z.val z.property g⟩)
  have hinj : Function.Injective encode := by
    intro x y h
    apply Subtype.ext
    funext c
    apply Subtype.ext
    funext i
    apply hpair c
    apply Prod.ext
    · exact congrArg (fun v : EL × ER =>
        ((v.1 ⟨c, designatedGroup (designatedLeft c) ((w c).val i)⟩).val ⟨i, rfl⟩)) h
    · exact congrArg (fun v : EL × ER =>
        ((v.2 ⟨c, designatedGroup (designatedRight c) ((w c).val i)⟩).val ⟨i, rfl⟩)) h
  have hleft : (Fintype.card EL : ℝ) ≤
      ∏ g : J, wordEntropyBound (PL g) (Left g.1) (HL g) :=
    card_class_entropy_bounded_words_le PL (fun g => Left g.1) HL
  have hright : (Fintype.card ER : ℝ) ≤
      ∏ g : J, wordEntropyBound (PR g) (Right g.1) (HR g) :=
    card_class_entropy_bounded_words_le PR (fun g => Right g.1) HR
  have hcard : (Fintype.card Row : ℝ) ≤ (Fintype.card EL : ℝ) * Fintype.card ER := by
    simpa only [Fintype.card_prod, Nat.cast_mul] using
      (Nat.cast_le.mpr (Fintype.card_le_of_injective encode hinj) :
        (Fintype.card Row : ℝ) ≤ Fintype.card (EL × ER))
  exact hcard.trans (mul_le_mul hleft hright (Nat.cast_nonneg _)
    ((Nat.cast_nonneg _).trans hleft))

theorem compatibleStatisticCount_le_of_controls
    (w : FixedClassWords Pos Shape shapeCounts)
    (hpair : ∀ c, Function.Injective (fun s : Pair c => (leftPart c s, rightPart c s)))
    (HL HR : (Σ c, Option (Shape c)) → ℝ)
    (controlLeft : SideEntropyControl Pos Shape Pair Left shapeCounts pairCounts
      leftPart designatedLeft leftLaw χ HL w)
    (controlRight : SideEntropyControl Pos Shape Pair Right shapeCounts pairCounts
      rightPart designatedRight rightLaw χ HR w) :
    (compatibleStatisticCount Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w : ℝ) ≤
      (∏ g : Σ c, Option (Shape c), wordEntropyBound
        (GroupPos (w g.1).val (designatedLeft g.1) g.2) (Left g.1) (HL g)) *
      (∏ g : Σ c, Option (Shape c), wordEntropyBound
        (GroupPos (w g.1).val (designatedRight g.1) g.2) (Right g.1) (HR g)) := by
  apply compatibleStatisticCount_le_grouped_entropy Pos Shape Pair Left Right
    shapeCounts pairCounts leftPart rightPart designatedLeft designatedRight
    leftLaw rightLaw χ w hpair HL HR
  · intro z hz g
    exact SideEntropyControl.group_entropy Pos Shape Pair Left shapeCounts pairCounts
      leftPart designatedLeft leftLaw χ HL w controlLeft z hz.1 g
  · intro z hz g
    exact SideEntropyControl.group_entropy Pos Shape Pair Right shapeCounts pairCounts
      rightPart designatedRight rightLaw χ HR w controlRight z hz.2 g

theorem compatibleCandidateCount_le_of_controls
    (w : FixedClassWords Pos Shape shapeCounts)
    (z : FixedClassWords Pos Pair pairCounts)
    (hpair : ∀ c, Function.Injective (fun s : Pair c => (leftPart c s, rightPart c s)))
    (HL HR : (Σ c, Option (Shape c)) → ℝ)
    (controlLeft : SideEntropyControl Pos Shape Pair Left shapeCounts pairCounts
      leftPart designatedLeft leftLaw χ HL w)
    (controlRight : SideEntropyControl Pos Shape Pair Right shapeCounts pairCounts
      rightPart designatedRight rightLaw χ HR w) :
    (compatibleCandidateCount Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) ≤
      (Fintype.card (FixedClassWords Pos Shape shapeCounts) : ℝ) *
        ((∏ g : Σ c, Option (Shape c), wordEntropyBound
          (GroupPos (w g.1).val (designatedLeft g.1) g.2) (Left g.1) (HL g)) *
        (∏ g : Σ c, Option (Shape c), wordEntropyBound
          (GroupPos (w g.1).val (designatedRight g.1) g.2) (Right g.1) (HR g))) /
        Fintype.card (FixedClassWords Pos Pair pairCounts) := by
  rw [compatibleCandidateCount_eq Pos Shape Pair Left Right shapeCounts pairCounts
    leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w z]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left
    (compatibleStatisticCount_le_of_controls Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w hpair HL HR
      controlLeft controlRight) (Nat.cast_nonneg _)

end Compatibility

end MatrixMultiplication.JointCompatibilityIncidence

end

end OAI
