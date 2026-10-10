import OAI.Combinatorics.LowSpaceSubsetSum.Counting.MixerBalance
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.HalfOrientations

namespace OAI

/-!
# The balanced signed-layout survival event

The uniform balanced sign law is a product of uniform half choices. Averaging
the fixed-layout concentration estimate over these choices
gives the simultaneous six-half and spread event in the actual experiment.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators

theorem finiteUniformProbability_prod_average {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]
    (P : Ω → Ψ → Prop) :
    finiteUniformProbability (fun z : Ω × Ψ => P z.1 z.2) =
      (∑ y, finiteUniformProbability (fun x => P x y)) / Fintype.card Ψ := by
  classical
  simp_rw [finiteUniformProbability_eq_indicator_mean]
  simp only [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  rw [← Finset.sum_div, div_div, Finset.sum_comm]

theorem finiteUniformProbability_prod_lower {Ω Ψ : Type*}
    [Fintype Ω] [Fintype Ψ] [Nonempty Ψ] (P : Ω → Ψ → Prop) {p : ℝ}
    (hp : ∀ y, p ≤ finiteUniformProbability (fun x => P x y)) :
    p ≤ finiteUniformProbability (fun z : Ω × Ψ => P z.1 z.2) := by
  rw [finiteUniformProbability_prod_average]
  have hcard : (0 : ℝ) < Fintype.card Ψ := by exact_mod_cast Fintype.card_pos
  apply (le_div_iff₀ hcard).mpr
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun y _ => hp y)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using hsum

def baseLayoutTests {n : ℕ} (a : Fin n → ℤ) (M : Fin 3 → Finset (Fin n))
    (e : Equiv.Perm (Fin n)) (F : Finset (Fin n)) : Prop :=
  (∀ i, deficiency a (permuteSubset e (F ∩ M i)) ≤ (39 / 5000 : ℝ) * n ∧
    deficiency a (permuteSubset e (M i \ F)) ≤ (39 / 5000 : ℝ) * n) ∧
  mixerSpreadTest a (fun i => permuteSubset e (M i)) n

theorem balanced_base_layout_tests_probability {n s : ℕ} (hn : 180000000 ≤ n)
    (hs : (s : ℝ) ≤ (3 / 25 : ℝ) * n)
    (hm : ((2 * s : ℕ) : ℝ) ≤ (6 / 25 : ℝ) * n)
    (a : Fin n → ℤ) (M : Fin 3 → Finset (Fin n))
    (hM : ∀ i, (M i).card = 2 * s)
    [Nonempty (BalancedSignSubsets M s)]
    (hmean : meanDeficiency a Finset.univ s < (153 / 20000 : ℝ) * n) :
    (1 / 2 : ℝ) ≤ finiteUniformProbability
      (fun z : Equiv.Perm (Fin n) × BalancedSignSubsets M s =>
        baseLayoutTests a M z.1 z.2.val) := by
  classical
  refine finiteUniformProbability_prod_lower
    (fun (e : Equiv.Perm (Fin n)) (F : BalancedSignSubsets M s) =>
      baseLayoutTests a M e F.val) ?_
  intro F
  let A : Fin 3 → Finset (Fin n) := fun i => F.val ∩ M i
  let B : Fin 3 → Finset (Fin n) := fun i => M i \ F.val
  let H : Fin (3 + 3) → Finset (Fin n) :=
    fun i => Fin.addCases (motive := fun _ => Finset (Fin n)) A B i
  have hA : ∀ i, (A i).card = s := fun i => F.property i
  have hB : ∀ i, (B i).card = s := by
    intro i
    dsimp [B]
    rw [Finset.card_sdiff, F.property i, hM]
    omega
  have hH : ∀ i, (H i).card = s := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [H, Fin.addCases_left] using hA j
    · intro j
      simpa only [H, Fin.addCases_right] using hB j
  have h := representation_layout_tests_probability hn hs hm a H M hH hM hmean
  apply h.trans
  apply finiteUniformProbability_mono
  intro e he
  refine ⟨?_, he.2⟩
  intro i
  constructor
  · have hi := he.1 (Fin.castAdd 3 i)
    simpa only [H, Fin.addCases_left, A] using hi
  · have hi := he.1 (Fin.natAdd 3 i)
    simpa only [H, Fin.addCases_right, B] using hi

def actualLayoutTests {n : ℕ} (a : Fin n → ℤ) (M : Fin 3 → Finset (Fin n))
    (z : Equiv.Perm (Fin n) × Finset (Fin n)) : Prop :=
  (∀ i, deficiency a (z.2 ∩ permuteSubset z.1 (M i)) ≤ (39 / 5000 : ℝ) * n ∧
    deficiency a (permuteSubset z.1 (M i) \ z.2) ≤ (39 / 5000 : ℝ) * n) ∧
  mixerSpreadTest a (fun i => permuteSubset z.1 (M i)) n

theorem actualLayoutTests_base_iff {n s : ℕ} (a : Fin n → ℤ)
    (M : Fin 3 → Finset (Fin n)) (z : BalancedMixerJoint M s) :
    actualLayoutTests a M z.val ↔
      baseLayoutTests a M ((balancedMixerJointEquiv M s) z).1
        ((balancedMixerJointEquiv M s) z).2.val := by
  change actualLayoutTests a M z.val ↔
    baseLayoutTests a M z.val.1 (permuteSubset z.val.1.symm z.val.2)
  unfold actualLayoutTests baseLayoutTests
  simp only [permuteSubset_inter, permuteSubset_sdiff, ← permuteSubset_trans]
  simp

theorem balanced_actual_layout_tests_probability {n s : ℕ} (hn : 180000000 ≤ n)
    (hs : (s : ℝ) ≤ (3 / 25 : ℝ) * n)
    (hm : ((2 * s : ℕ) : ℝ) ≤ (6 / 25 : ℝ) * n)
    (a : Fin n → ℤ) (M : Fin 3 → Finset (Fin n))
    (hM : ∀ i, (M i).card = 2 * s)
    [Nonempty (BalancedSignSubsets M s)]
    (hmean : meanDeficiency a Finset.univ s < (153 / 20000 : ℝ) * n) :
    (1 / 2 : ℝ) ≤ finiteUniformProbability
      (fun z : BalancedMixerJoint M s => actualLayoutTests a M z.val) := by
  have hp : (fun z : BalancedMixerJoint M s => actualLayoutTests a M z.val) =
      (fun z => baseLayoutTests a M ((balancedMixerJointEquiv M s) z).1
        ((balancedMixerJointEquiv M s) z).2.val) := by
    funext z
    exact propext (actualLayoutTests_base_iff a M z)
  rw [hp]
  change (1 / 2 : ℝ) ≤ finiteUniformProbability
    (fun z => (fun w : Equiv.Perm (Fin n) × BalancedSignSubsets M s =>
      baseLayoutTests a M w.1 w.2.val) ((balancedMixerJointEquiv M s) z))
  exact (balanced_base_layout_tests_probability hn hs hm a M hM hmean).trans_eq
    (finiteUniformProbability_equiv (balancedMixerJointEquiv M s)
      (fun w : Equiv.Perm (Fin n) × BalancedSignSubsets M s =>
        baseLayoutTests a M w.1 w.2.val)).symm

/-- Complementation permutes the subsets having exactly half the ambient size. -/
def halfComplementEquiv (α : Type*) [Fintype α] [DecidableEq α]
    (s : ℕ) (hα : Fintype.card α = 2 * s) :
    {S : Finset α // S.card = s} ≃ {S : Finset α // S.card = s} where
  toFun S := ⟨Finset.univ \ S.val, by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, S.property, hα]
    omega⟩
  invFun S := ⟨Finset.univ \ S.val, by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, S.property, hα]
    omega⟩
  left_inv S := by apply Subtype.ext; ext x; simp
  right_inv S := by apply Subtype.ext; ext x; simp

noncomputable def orientationCoordinateEquiv {n : ℕ}
    (M : Fin 3 → Finset (Fin n)) (hdisj : ∀ i j, i ≠ j → Disjoint (M i) (M j))
    (s : ℕ) (hM : ∀ i, (M i).card = 2 * s) (b : Fin 3 → Bool)
    (k : Option (Fin 3)) :
    BalancedColorRestriction (mixerColor M) s k ≃ BalancedColorRestriction (mixerColor M) s k :=
  match k with
  | none => Equiv.refl _
  | some i => if b i then Equiv.refl _ else
      halfComplementEquiv _ s (by rw [mixerColor_card M hdisj i, hM])

noncomputable def orientBalancedSigns {n : ℕ}
    (M : Fin 3 → Finset (Fin n)) (hdisj : ∀ i j, i ≠ j → Disjoint (M i) (M j))
    (s : ℕ) (hM : ∀ i, (M i).card = 2 * s) (b : Fin 3 → Bool) :
    BalancedSignSubsets M s ≃ BalancedSignSubsets M s :=
  (balancedMixerRestrictionEquiv M hdisj s).trans
    ((Equiv.piCongrRight (orientationCoordinateEquiv M hdisj s hM b)).trans
      (balancedMixerRestrictionEquiv M hdisj s).symm)

private theorem mixer_restriction_map {n : ℕ} (M : Fin 3 → Finset (Fin n))
    (hdisj : ∀ i j, i ≠ j → Disjoint (M i) (M j)) (F : Finset (Fin n)) (i : Fin 3) :
    (F.subtype (fun x => mixerColor M x = some i)).map (Function.Embedding.subtype _) =
      F ∩ M i := by
  rw [Finset.subtype_map]
  ext x
  simp only [Finset.mem_filter, Finset.mem_inter, mixerColor_eq_some_iff M hdisj]

private theorem mixer_fiber_univ_map {n : ℕ} (M : Fin 3 → Finset (Fin n))
    (hdisj : ∀ i j, i ≠ j → Disjoint (M i) (M j)) (i : Fin 3) :
    (Finset.univ : Finset {x : Fin n // mixerColor M x = some i}).map
      (Function.Embedding.subtype _) = M i := by
  ext x
  simp only [Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coe_subtype, Subtype.exists, exists_prop]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mixerColor_eq_some_iff M hdisj y i).mp hy
  · intro hx
    exact ⟨x, (mixerColor_eq_some_iff M hdisj x i).mpr hx, rfl⟩

theorem orientBalancedSigns_selected {n : ℕ}
    (M : Fin 3 → Finset (Fin n)) (hdisj : ∀ i j, i ≠ j → Disjoint (M i) (M j))
    (s : ℕ) (hM : ∀ i, (M i).card = 2 * s) (b : Fin 3 → Bool)
    (F : BalancedSignSubsets M s) (i : Fin 3) :
    (orientBalancedSigns M hdisj s hM b F).val ∩ M i =
      orientedHalf (F.val ∩ M i) (M i \ F.val) (b i) := by
  classical
  let R := balancedMixerRestrictionEquiv M hdisj s
  have he : R (orientBalancedSigns M hdisj s hM b F) =
      (Equiv.piCongrRight (orientationCoordinateEquiv M hdisj s hM b)) (R F) := by
    simp only [orientBalancedSigns, Equiv.trans_apply, R, Equiv.apply_symm_apply]
  have hi := congrArg Subtype.val (congrFun he (some i))
  change (orientBalancedSigns M hdisj s hM b F).val.subtype
      (fun x => mixerColor M x = some i) =
    (orientationCoordinateEquiv M hdisj s hM b (some i) (R F (some i))).val at hi
  have hraw :
      ((orientBalancedSigns M hdisj s hM b F).val.subtype
        (fun x => mixerColor M x = some i)) =
      if b i then F.val.subtype (fun x => mixerColor M x = some i)
      else Finset.univ \ F.val.subtype (fun x => mixerColor M x = some i) := by
    refine hi.trans ?_
    cases hb : b i <;>
      simp only [orientationCoordinateEquiv, hb, Bool.false_eq_true, ↓reduceIte] <;> rfl
  have himage := congrArg (fun S => S.map (Function.Embedding.subtype _)) hraw
  rw [mixer_restriction_map M hdisj] at himage
  cases hb : b i
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at himage
    rw [Finset.map_sdiff, mixer_fiber_univ_map M hdisj,
      mixer_restriction_map M hdisj] at himage
    rw [himage]
    ext x
    simp [orientedHalf]
  · simpa only [hb, ↓reduceIte, mixer_restriction_map M hdisj, orientedHalf] using himage

theorem finiteUniformProbability_random_equiv {Ω B : Type*}
    [Fintype Ω] [Fintype B] [Nonempty B] (T : B → Equiv.Perm Ω) (P : Ω → Prop) :
    finiteUniformProbability (fun z : Ω × B => P (T z.2 z.1)) = finiteUniformProbability P := by
  let e : Ω × B ≃ Ω × B :=
    { toFun := fun z => (T z.2 z.1, z.2)
      invFun := fun z => ((T z.2).symm z.1, z.2)
      left_inv := by intro z; simp
      right_inv := by intro z; simp }
  exact (finiteUniformProbability_equiv e (fun z => P z.1)).trans (finiteUniformProbability_fst P)

def baseLayoutSuccess {n : ℕ} (a : Fin n → ℤ) (M : Fin 3 → Finset (Fin n))
    (e : Equiv.Perm (Fin n)) (F : Finset (Fin n)) : Prop :=
  (∀ i, deficiency a (permuteSubset e (F ∩ M i)) ≤
    min ((39 / 5000 : ℝ) * n) (deficiency a (permuteSubset e (M i)) / 2)) ∧
  mixerSpreadTest a (fun i => permuteSubset e (M i)) n

theorem balanced_base_layout_success_probability {n s : ℕ} (hn : 180000000 ≤ n)
    (hs : (s : ℝ) ≤ (3 / 25 : ℝ) * n)
    (hm : ((2 * s : ℕ) : ℝ) ≤ (6 / 25 : ℝ) * n)
    (a : Fin n → ℤ) (M : Fin 3 → Finset (Fin n))
    (hdisj : ∀ i j, i ≠ j → Disjoint (M i) (M j))
    (hM : ∀ i, (M i).card = 2 * s)
    [Nonempty (BalancedSignSubsets M s)]
    (hmean : meanDeficiency a Finset.univ s < (153 / 20000 : ℝ) * n) :
    (1 / 16 : ℝ) ≤ finiteUniformProbability
      (fun z : Equiv.Perm (Fin n) × BalancedSignSubsets M s =>
        baseLayoutSuccess a M z.1 z.2.val) := by
  classical
  let Ω := Equiv.Perm (Fin n) × BalancedSignSubsets M s
  let E : Ω → Prop := fun z => baseLayoutTests a M z.1 z.2.val
  let D : Ω → Prop := fun z => baseLayoutSuccess a M z.1 z.2.val
  let T (b : Fin 3 → Bool) : Equiv.Perm Ω :=
    Equiv.prodCongr (Equiv.refl _) (orientBalancedSigns M hdisj s hM b)
  have hgood : ∀ z, E z → ∃ b, D (T b z) := by
    rintro ⟨e, F⟩ he
    have hi (i : Fin 3) : ∃ b : Bool,
        deficiency a (orientedHalf (permuteSubset e (F.val ∩ M i))
          (permuteSubset e (M i \ F.val)) b) ≤
        min ((39 / 5000 : ℝ) * n) (deficiency a (permuteSubset e (M i)) / 2) := by
      apply exists_good_half_orientation
      · apply (Finset.disjoint_map _).mpr
        apply Finset.disjoint_left.mpr
        intro x hx hy
        exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_inter.mp hx).1
      · change (F.val ∩ M i).map e.toEmbedding ∪ (M i \ F.val).map e.toEmbedding =
          (M i).map e.toEmbedding
        rw [← Finset.map_union]
        congr 1
        ext x
        simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
        tauto
      · exact (he.1 i).1
      · exact (he.1 i).2
    let b : Fin 3 → Bool := fun i => Classical.choose (hi i)
    refine ⟨b, ?_, he.2⟩
    intro i
    have hb := Classical.choose_spec (hi i)
    change deficiency a (permuteSubset e
      ((orientBalancedSigns M hdisj s hM b F).val ∩ M i)) ≤
        min ((39 / 5000 : ℝ) * n) (deficiency a (permuteSubset e (M i)) / 2)
    rw [orientBalancedSigns_selected]
    change deficiency a (orientedHalf (permuteSubset e (F.val ∩ M i))
      (permuteSubset e (M i \ F.val)) (b i)) ≤ _ at hb
    cases hbi : b i <;> simpa only [orientedHalf, hbi, Bool.false_eq_true, ↓reduceIte] using hb
  have hjoint := finiteUniformProbability_joint_orientation E (fun z b => D (T b z)) hgood
  have hdrop : finiteUniformProbability
      (fun p : Ω × (Fin 3 → Bool) => E p.1 ∧ D (T p.2 p.1)) ≤
      finiteUniformProbability (fun p : Ω × (Fin 3 → Bool) => D (T p.2 p.1)) :=
    finiteUniformProbability_mono (fun _ h => h.2)
  have hD : finiteUniformProbability E / 8 ≤ finiteUniformProbability D :=
    hjoint.trans (hdrop.trans_eq (finiteUniformProbability_random_equiv T D))
  have hE : (1 / 2 : ℝ) ≤ finiteUniformProbability E :=
    balanced_base_layout_tests_probability hn hs hm a M hM hmean
  linarith

/-- Restricting one coordinate gives the exact balance factor in the joint law. -/
theorem finiteUniformProbability_product_restrict {Ω Ψ : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype Ψ] [Nonempty Ψ]
    (E : Ψ → Prop) [Fintype {y : Ψ // E y}] [Nonempty {y : Ψ // E y}]
    (Q : Ω → Ψ → Prop) :
    finiteUniformProbability (fun z : Ω × Ψ => E z.2 ∧ Q z.1 z.2) =
      finiteUniformProbability E *
        finiteUniformProbability (fun z : Ω × {y : Ψ // E y} => Q z.1 z.2.val) := by
  classical
  let e : {z : Ω × Ψ // E z.2 ∧ Q z.1 z.2} ≃
      {z : Ω × {y : Ψ // E y} // Q z.1 z.2.val} :=
    { toFun := fun z => ⟨(z.val.1, ⟨z.val.2, z.property.1⟩), z.property.2⟩
      invFun := fun z => ⟨(z.val.1, z.val.2.val), z.val.2.property, z.property⟩
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl }
  have hΩ : (Nat.card Ω : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hΨ : (Nat.card Ψ : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hE : (Nat.card {y : Ψ // E y} : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  simp only [finiteUniformProbability, ← Nat.card_eq_fintype_card, Nat.card_prod]
  rw [Nat.card_congr e]
  push_cast
  field_simp

/-- Independent uniform signs can be expressed in original or permuted coordinates. -/
def signLayoutEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Equiv.Perm ι × Finset ι ≃ Equiv.Perm ι × Finset ι where
  toFun z := (z.1, permuteSubset z.1 z.2)
  invFun z := (z.1, permuteSubset z.1.symm z.2)
  left_inv z := by
    apply Prod.ext
    · rfl
    change permuteSubset z.1.symm (permuteSubset z.1 z.2) = z.2
    rw [← permuteSubset_trans]
    simp
  right_inv z := by
    apply Prod.ext
    · rfl
    change permuteSubset z.1 (permuteSubset z.1.symm z.2) = z.2
    rw [← permuteSubset_trans]
    simp

def actualLayoutSuccess {n : ℕ} (a : Fin n → ℤ) (M : Fin 3 → Finset (Fin n))
    (z : Equiv.Perm (Fin n) × Finset (Fin n)) : Prop :=
  (∀ i, deficiency a (z.2 ∩ permuteSubset z.1 (M i)) ≤
    min ((39 / 5000 : ℝ) * n) (deficiency a (permuteSubset z.1 (M i)) / 2)) ∧
  mixerSpreadTest a (fun i => permuteSubset z.1 (M i)) n

theorem actualLayoutSuccess_signLayoutEquiv {n : ℕ} (a : Fin n → ℤ)
    (M : Fin 3 → Finset (Fin n)) (z : Equiv.Perm (Fin n) × Finset (Fin n)) :
    actualLayoutSuccess a M (signLayoutEquiv (Fin n) z) ↔
      baseLayoutSuccess a M z.1 z.2 := by
  change actualLayoutSuccess a M (z.1, permuteSubset z.1 z.2) ↔ _
  simp only [actualLayoutSuccess, baseLayoutSuccess, permuteSubset_inter]

/-- The complete mixer event in the actual uniform permutation and sign experiment. -/
theorem signed_layout_survival_probability {n s : ℕ} (hn : 180000000 ≤ n)
    (hs : (s : ℝ) ≤ (3 / 25 : ℝ) * n)
    (hm : ((2 * s : ℕ) : ℝ) ≤ (6 / 25 : ℝ) * n)
    (a : Fin n → ℤ) (M : Fin 3 → Finset (Fin n))
    (hdisj : ∀ i j, i ≠ j → Disjoint (M i) (M j))
    (hM : ∀ i, (M i).card = 2 * s)
    (hmean : meanDeficiency a Finset.univ s < (153 / 20000 : ℝ) * n) :
    1 / (16 * ((2 * s + 1 : ℕ) : ℝ) ^ 3) ≤ finiteUniformProbability
      (fun z : Equiv.Perm (Fin n) × Finset (Fin n) =>
        MixerBalanced (fun i => permuteSubset z.1 (M i)) s z.2 ∧
          actualLayoutSuccess a M z) := by
  classical
  let : Nonempty (BalancedSignSubsets M s) :=
    balancedSignSubsets_nonempty M hdisj s hM
  have hcond := balanced_base_layout_success_probability hn hs hm a M hdisj hM hmean
  have hbal := mixer_balance_probability_lower M hdisj s hM
  have hprod := finiteUniformProbability_product_restrict (MixerBalanced M s)
    (fun e F => baseLayoutSuccess a M e F)
  have hbase : 1 / (16 * ((2 * s + 1 : ℕ) : ℝ) ^ 3) ≤
      finiteUniformProbability (fun z : Equiv.Perm (Fin n) × Finset (Fin n) =>
        MixerBalanced M s z.2 ∧ baseLayoutSuccess a M z.1 z.2) := by
    rw [hprod]
    have hmultiply := mul_le_mul hbal hcond (by norm_num : (0 : ℝ) ≤ 1 / 16)
      (finiteUniformProbability_nonneg (MixerBalanced M s))
    calc
      _ = (1 / (2 * (s : ℝ) + 1) ^ 3) * (1 / 16) := by
        push_cast
        rw [one_div_mul_one_div]
        congr 1
        ring
      _ ≤ _ := hmultiply
  have htransport := finiteUniformProbability_equiv (signLayoutEquiv (Fin n))
    (fun z : Equiv.Perm (Fin n) × Finset (Fin n) =>
      MixerBalanced (fun i => permuteSubset z.1 (M i)) s z.2 ∧
        actualLayoutSuccess a M z)
  have hp : (fun z : Equiv.Perm (Fin n) × Finset (Fin n) =>
      MixerBalanced (fun i => permuteSubset ((signLayoutEquiv (Fin n)) z).1 (M i)) s
          ((signLayoutEquiv (Fin n)) z).2 ∧
        actualLayoutSuccess a M (signLayoutEquiv (Fin n) z)) =
      (fun z => MixerBalanced M s z.2 ∧ baseLayoutSuccess a M z.1 z.2) := by
    funext z
    apply propext
    rw [actualLayoutSuccess_signLayoutEquiv]
    change (MixerBalanced (fun i => permuteSubset z.1 (M i)) s
        (permuteSubset z.1 z.2) ∧ _) ↔ _
    rw [mixerBalanced_permute]
  rw [hp] at htransport
  exact hbase.trans_eq htransport

end LowSpaceSubsetSum

end OAI
