import OAI.Combinatorics.LowSpaceSubsetSum.Counting.BoundedSampling
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PermutationSampling
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum

namespace OAI

/-!
# Balanced random signs and conditional mixer halves

The three mixers are disjoint. Uniform global sign subsets therefore induce
independent uniform subsets on them. Conditioning each restriction to have
half the mixer size gives the exact balance probability and uniform halves.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators

variable {ι K : Type*} [DecidableEq ι] [Fintype K] [DecidableEq K]

/-- Split a finite set into its restrictions to the fibers of a finite coloring. -/
def partitionFinsetEquiv (c : ι → K) :
    Finset ι ≃ ((k : K) → Finset {x : ι // c x = k}) where
  toFun S k := S.subtype (fun x => c x = k)
  invFun S := Finset.univ.biUnion (fun k => (S k).map (Function.Embedding.subtype _))
  left_inv S := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coe_subtype, Finset.mem_subtype]
    constructor
    · rintro ⟨k, y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨c x, ⟨x, rfl⟩, hx, rfl⟩
  right_inv S := by
    funext k
    ext x
    simp only [Finset.mem_subtype, Finset.mem_biUnion, Finset.mem_univ,
      true_and, Finset.mem_map, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨j, y, hy, he⟩
      have hj : j = k := y.property.symm.trans ((congrArg c he).trans x.property)
      subst j
      have hyx : y = x := Subtype.ext he
      simpa only [hyx] using hy
    · intro hx
      exact ⟨k, x, hx, rfl⟩

theorem card_partition_profile [Fintype ι] (c : ι → K)
    (P : (k : K) → Finset {x : ι // c x = k} → Prop) :
    Nat.card {S : Finset ι // ∀ k, P k (S.subtype (fun x => c x = k))} =
      ∏ k, Nat.card {S : Finset {x : ι // c x = k} // P k S} := by
  classical
  let e := (partitionFinsetEquiv c).subtypeEquivOfSubtype
    (p := fun S => ∀ k, P k (S k))
  change Nat.card {S : Finset ι // ∀ k, P k ((partitionFinsetEquiv c) S k)} = _
  rw [Nat.card_congr e, Nat.card_congr Equiv.subtypePiEquivPi, Nat.card_pi]

/-- Balance of the three non-outside color classes. -/
def ColorBalanced (c : ι → Option (Fin 3)) (s : ℕ) (S : Finset ι) : Prop :=
  ∀ i, (S.subtype (fun x => c x = some i)).card = s

theorem colorBalanced_card [Fintype ι] (c : ι → Option (Fin 3)) (s : ℕ)
    (hsize : ∀ i, Fintype.card {x : ι // c x = some i} = 2 * s) :
    Nat.card {S : Finset ι // ColorBalanced c s S} =
      2 ^ Fintype.card {x : ι // c x = none} * ((2 * s).choose s) ^ 3 := by
  classical
  let P : (k : Option (Fin 3)) → Finset {x : ι // c x = k} → Prop :=
    fun k S => match k with
      | none => True
      | some _ => S.card = s
  have hp : (fun S : Finset ι => ColorBalanced c s S) =
      (fun S => ∀ k, P k (S.subtype (fun x => c x = k))) := by
    funext S
    apply propext
    constructor
    · intro h k
      cases k with
      | none => trivial
      | some i => exact h i
    · intro h i
      exact h (some i)
  rw [hp, card_partition_profile, Fintype.prod_option]
  simp only [P, Nat.card_eq_fintype_card, Fintype.card_subtype_true,
    Fintype.card_finset, Fintype.card_finset_len, hsize, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem central_binomial_lower (s : ℕ) :
    (2 : ℝ) ^ (2 * s) ≤ (2 * s + 1 : ℝ) * (2 * s).choose s := by
  have h : 2 ^ (2 * s) ≤ (2 * s + 1) * (2 * s).choose s := by
    rw [← Nat.sum_range_choose]
    calc
      _ ≤ ∑ _k ∈ Finset.range (2 * s + 1), (2 * s).choose s := by
        apply Finset.sum_le_sum
        intro k _
        simpa only [Nat.mul_div_cancel_left _ (by decide : 0 < 2)] using
          Nat.choose_le_middle k (2 * s)
      _ = _ := by simp
  exact_mod_cast h

theorem colorBalanced_probability [Fintype ι] (c : ι → Option (Fin 3)) (s : ℕ)
    (hsize : ∀ i, Fintype.card {x : ι // c x = some i} = 2 * s) :
    finiteUniformProbability (ColorBalanced c s) =
      (((2 * s).choose s : ℝ) / (2 : ℝ) ^ (2 * s)) ^ 3 := by
  classical
  have htotal : Fintype.card ι = Fintype.card {x : ι // c x = none} + (2 * s) * 3 := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv c), Fintype.card_sigma,
      Fintype.sum_option]
    simp only [hsize, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  simp only [finiteUniformProbability, ← Nat.card_eq_fintype_card]
  rw [colorBalanced_card c s hsize, Nat.card_eq_fintype_card, Fintype.card_finset,
    htotal, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_pow,
    Nat.cast_pow, Nat.cast_ofNat, pow_add, pow_mul]
  field_simp

theorem colorBalanced_probability_lower [Fintype ι] (c : ι → Option (Fin 3)) (s : ℕ)
    (hsize : ∀ i, Fintype.card {x : ι // c x = some i} = 2 * s) :
    1 / (2 * s + 1 : ℝ) ^ 3 ≤ finiteUniformProbability (ColorBalanced c s) := by
  rw [colorBalanced_probability c s hsize, ← one_div_pow]
  apply pow_le_pow_left₀ (by positivity)
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * s + 1) (by positivity)).mpr
  simpa only [one_mul, mul_comm] using central_binomial_lower s

/-- The index of a mixer containing an input position, or the outside category. -/
noncomputable def mixerColor (M : Fin 3 → Finset ι) (x : ι) : Option (Fin 3) :=
  if h : ∃ i, x ∈ M i then some (Classical.choose h) else none

theorem mixerColor_eq_some_iff (M : Fin 3 → Finset ι)
    (hdisj : ∀ i j, i ≠ j → Disjoint (M i) (M j)) (x : ι) (i : Fin 3) :
    mixerColor M x = some i ↔ x ∈ M i := by
  classical
  unfold mixerColor
  split_ifs with h
  · have hm := Classical.choose_spec h
    constructor
    · intro he
      have hi := Option.some.inj he
      simpa only [hi] using hm
    · intro hi
      have he : Classical.choose h = i := by
        by_contra hn
        exact Finset.disjoint_left.mp (hdisj _ _ hn) hm hi
      simp only [he]
  · constructor
    · intro he
      cases he
    · intro hi
      exact (h ⟨i, hi⟩).elim

def MixerBalanced (M : Fin 3 → Finset ι) (s : ℕ) (S : Finset ι) : Prop :=
  ∀ i, (S ∩ M i).card = s

theorem mixerColor_restriction_card (M : Fin 3 → Finset ι)
    (hdisj : ∀ i j, i ≠ j → Disjoint (M i) (M j)) (S : Finset ι) (i : Fin 3) :
    (S.subtype (fun x => mixerColor M x = some i)).card = (S ∩ M i).card := by
  classical
  rw [Finset.card_subtype]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_inter, mixerColor_eq_some_iff M hdisj]

theorem colorBalanced_mixerColor_iff (M : Fin 3 → Finset ι)
    (hdisj : ∀ i j, i ≠ j → Disjoint (M i) (M j)) (s : ℕ) (S : Finset ι) :
    ColorBalanced (mixerColor M) s S ↔ MixerBalanced M s S := by
  classical
  simp only [ColorBalanced, MixerBalanced, mixerColor_restriction_card M hdisj]

theorem mixerColor_card [Fintype ι] (M : Fin 3 → Finset ι)
    (hdisj : ∀ i j, i ≠ j → Disjoint (M i) (M j)) (i : Fin 3) :
    Fintype.card {x : ι // mixerColor M x = some i} = (M i).card := by
  classical
  let e : {x : ι // mixerColor M x = some i} ≃ (M i) :=
    Equiv.subtypeEquivRight (fun x => mixerColor_eq_some_iff M hdisj x i)
  exact (Fintype.card_congr e).trans (Fintype.card_coe (M i))

/-- Exact balance probability, independent of the locations of the three mixers. -/
theorem mixer_balance_probability [Fintype ι] (M : Fin 3 → Finset ι)
    (hdisj : ∀ i j, i ≠ j → Disjoint (M i) (M j)) (s : ℕ)
    (hsize : ∀ i, (M i).card = 2 * s) :
    finiteUniformProbability (MixerBalanced M s) =
      (((2 * s).choose s : ℝ) / (2 : ℝ) ^ (2 * s)) ^ 3 := by
  have hp : MixerBalanced M s = ColorBalanced (mixerColor M) s := by
    funext S
    exact propext (colorBalanced_mixerColor_iff M hdisj s S).symm
  rw [hp]
  apply colorBalanced_probability
  intro i
  rw [mixerColor_card M hdisj i, hsize]

/-- The inverse-cubic balance bound used before the deficiency estimates. -/
theorem mixer_balance_probability_lower [Fintype ι] (M : Fin 3 → Finset ι)
    (hdisj : ∀ i j, i ≠ j → Disjoint (M i) (M j)) (s : ℕ)
    (hsize : ∀ i, (M i).card = 2 * s) :
    1 / (2 * s + 1 : ℝ) ^ 3 ≤ finiteUniformProbability (MixerBalanced M s) := by
  have hp : MixerBalanced M s = ColorBalanced (mixerColor M) s := by
    funext S
    exact propext (colorBalanced_mixerColor_iff M hdisj s S).symm
  rw [hp]
  apply colorBalanced_probability_lower
  intro i
  rw [mixerColor_card M hdisj i, hsize]

theorem finiteUniformProbability_equiv {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]
    (e : Ω ≃ Ψ) (P : Ψ → Prop) :
    finiteUniformProbability (fun x => P (e x)) = finiteUniformProbability P := by
  classical
  simp only [finiteUniformProbability, ← Nat.card_eq_fintype_card]
  rw [Nat.card_congr (e.subtypeEquivOfSubtype (p := P)), Nat.card_congr e]

/-- Randomly permuting any independently chosen size-`s` set gives the same
uniform marginal, even when the choice of that set has additional constraints. -/
theorem permuted_family_uniform [Fintype ι] {Ξ : Type*} [Fintype Ξ] [Nonempty Ξ]
    (B : Ξ → Finset ι) (s : ℕ) (hB : ∀ ξ, (B ξ).card = s) (P : Finset ι → Prop) :
    finiteUniformProbability (fun z : Equiv.Perm ι × Ξ => P (permuteSubset z.1 (B z.2))) =
      finiteUniformProbability (fun S : ↥((Finset.univ : Finset ι).powersetCard s) => P S.val) := by
  classical
  let ξ₀ : Ξ := Classical.choice inferInstance
  let T₀ : ↥((Finset.univ : Finset ι).powersetCard s) :=
    ⟨B ξ₀, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hB ξ₀⟩⟩
  let : Nonempty ↥((Finset.univ : Finset ι).powersetCard s) := ⟨T₀⟩
  let f : Equiv.Perm ι × Ξ → ↥((Finset.univ : Finset ι).powersetCard s) :=
    fun z => ⟨permuteSubset z.1 (B z.2),
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (permuteSubset_card _ _).trans (hB _)⟩⟩
  have hf (T : ↥((Finset.univ : Finset ι).powersetCard s)) :
      Fintype.card {z // f z = T} = Fintype.card {z // f z = T₀} := by
    obtain ⟨τ, hτ⟩ := exists_permutation_of_card_eq T.val T₀.val
      ((Finset.mem_powersetCard.mp T.property).2.trans
        (Finset.mem_powersetCard.mp T₀.property).2.symm)
    have hτinv : permuteSubset τ.symm T₀.val = T.val := by
      rw [← hτ, ← permuteSubset_trans]
      simp
    let e : {z // f z = T} ≃ {z // f z = T₀} :=
      { toFun := fun z => ⟨(z.1.1.trans τ, z.1.2), by
          apply Subtype.ext
          change permuteSubset (z.1.1.trans τ) (B z.1.2) = T₀.val
          rw [permuteSubset_trans]
          have hz : permuteSubset z.1.1 (B z.1.2) = T.val := congrArg Subtype.val z.2
          rw [hz, hτ]⟩
        invFun := fun z => ⟨(z.1.1.trans τ.symm, z.1.2), by
          apply Subtype.ext
          change permuteSubset (z.1.1.trans τ.symm) (B z.1.2) = T.val
          rw [permuteSubset_trans]
          have hz : permuteSubset z.1.1 (B z.1.2) = T₀.val := congrArg Subtype.val z.2
          rw [hz, hτinv]⟩
        left_inv := fun z => by
          apply Subtype.ext
          apply Prod.ext
          · ext x
            simp
          · rfl
        right_inv := fun z => by
          apply Subtype.ext
          apply Prod.ext
          · ext x
            simp
          · rfl }
    exact Fintype.card_congr e
  exact finiteUniformProbability_map_of_constant_fibers f hf (fun S => P S.val)

@[simp] theorem permuteSubset_inter [Fintype ι] (e : Equiv.Perm ι) (S T : Finset ι) :
    permuteSubset e (S ∩ T) = permuteSubset e S ∩ permuteSubset e T :=
  Finset.map_inter S T

@[simp] theorem permuteSubset_sdiff [Fintype ι] (e : Equiv.Perm ι) (S T : Finset ι) :
    permuteSubset e (S \ T) = permuteSubset e S \ permuteSubset e T :=
  Finset.map_sdiff S T

theorem mixerBalanced_permute [Fintype ι] (M : Fin 3 → Finset ι) (s : ℕ)
    (e : Equiv.Perm ι) (F : Finset ι) :
    MixerBalanced (fun i => permuteSubset e (M i)) s (permuteSubset e F) ↔
      MixerBalanced M s F := by
  simp only [MixerBalanced, ← permuteSubset_inter, permuteSubset_card]

abbrev BalancedSignSubsets (M : Fin 3 → Finset ι) (s : ℕ) :=
  {F : Finset ι // MixerBalanced M s F}

noncomputable instance balancedSignSubsetsFintype [Fintype ι]
    (M : Fin 3 → Finset ι) (s : ℕ) : Fintype (BalancedSignSubsets M s) := Fintype.ofFinite _

abbrev BalancedMixerJoint [Fintype ι] (M : Fin 3 → Finset ι) (s : ℕ) :=
  {z : Equiv.Perm ι × Finset ι //
    MixerBalanced (fun i => permuteSubset z.1 (M i)) s z.2}

noncomputable instance balancedMixerJointFintype [Fintype ι]
    (M : Fin 3 → Finset ι) (s : ℕ) : Fintype (BalancedMixerJoint M s) := Fintype.ofFinite _

/-- Conditioning the global sign subset on mixer balance leaves the permutation
uniform and independent of the balanced sign subset in the original coordinates. -/
def balancedMixerJointEquiv [Fintype ι] (M : Fin 3 → Finset ι) (s : ℕ) :
    BalancedMixerJoint M s ≃ Equiv.Perm ι × BalancedSignSubsets M s where
  toFun z := (z.1.1, ⟨permuteSubset z.1.1.symm z.1.2, by
    apply (mixerBalanced_permute M s z.1.1 _).mp
    have he : permuteSubset z.1.1 (permuteSubset z.1.1.symm z.1.2) = z.1.2 := by
      rw [← permuteSubset_trans]
      simp
    simpa only [he] using z.2⟩)
  invFun z := ⟨(z.1, permuteSubset z.1 z.2.val),
    (mixerBalanced_permute M s z.1 z.2.val).mpr z.2.property⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change permuteSubset z.1.1 (permuteSubset z.1.1.symm z.1.2) = z.1.2
      rw [← permuteSubset_trans]
      simp
  right_inv z := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change permuteSubset z.1.symm (permuteSubset z.1 z.2.val) = z.2.val
      rw [← permuteSubset_trans]
      simp

theorem balancedSignSubsets_nonempty [Fintype ι] (M : Fin 3 → Finset ι)
    (hdisj : ∀ i j, i ≠ j → Disjoint (M i) (M j)) (s : ℕ)
    (hsize : ∀ i, (M i).card = 2 * s) : Nonempty (BalancedSignSubsets M s) := by
  have hp : 0 < finiteUniformProbability (MixerBalanced M s) :=
    lt_of_lt_of_le (by positivity) (mixer_balance_probability_lower M hdisj s hsize)
  simp only [finiteUniformProbability, ← Nat.card_eq_fintype_card] at hp
  have hden : (0 : ℝ) < Nat.card (Finset ι) := by exact_mod_cast Nat.card_pos
  have hn : 0 < Nat.card (BalancedSignSubsets M s) := by
    exact_mod_cast (div_pos_iff_of_pos_right hden).mp hp
  exact (Nat.card_pos_iff.mp hn).1

theorem conditioned_mixer_permutation_uniform [Fintype ι]
    (M : Fin 3 → Finset ι) (s : ℕ) [Nonempty (BalancedSignSubsets M s)]
    (P : Equiv.Perm ι → Prop) :
    finiteUniformProbability (fun z : BalancedMixerJoint M s => P z.val.1) =
      finiteUniformProbability P := by
  let e := balancedMixerJointEquiv M s
  calc
    _ = finiteUniformProbability (fun z : Equiv.Perm ι × BalancedSignSubsets M s => P z.1) :=
      finiteUniformProbability_equiv e (fun z => P z.1)
    _ = _ := finiteUniformProbability_fst P

theorem conditioned_selected_half_uniform [Fintype ι]
    (M : Fin 3 → Finset ι) (s : ℕ) [Nonempty (BalancedSignSubsets M s)]
    (i : Fin 3) (P : Finset ι → Prop) :
    finiteUniformProbability (fun z : BalancedMixerJoint M s =>
      P (z.val.2 ∩ permuteSubset z.val.1 (M i))) =
      finiteUniformProbability (fun S : ↥((Finset.univ : Finset ι).powersetCard s) => P S.val) := by
  let B : BalancedSignSubsets M s → Finset ι := fun F => F.val ∩ M i
  have hB : ∀ F, (B F).card = s := fun F => F.property i
  calc
    _ = finiteUniformProbability (fun z : Equiv.Perm ι × BalancedSignSubsets M s =>
        P (permuteSubset z.1 (B z.2))) := by
      have h := finiteUniformProbability_equiv (balancedMixerJointEquiv M s)
        (fun z : Equiv.Perm ι × BalancedSignSubsets M s => P (permuteSubset z.1 (B z.2)))
      convert h using 1
      congr 1
      funext z
      change P (z.val.2 ∩ permuteSubset z.val.1 (M i)) =
        P (permuteSubset z.val.1 (permuteSubset z.val.1.symm z.val.2 ∩ M i))
      rw [permuteSubset_inter]
      rw [← permuteSubset_trans]
      simp
    _ = _ := permuted_family_uniform B s hB P

theorem conditioned_complement_half_uniform [Fintype ι]
    (M : Fin 3 → Finset ι) (s : ℕ) [Nonempty (BalancedSignSubsets M s)]
    (hsize : ∀ i, (M i).card = 2 * s) (i : Fin 3) (P : Finset ι → Prop) :
    finiteUniformProbability (fun z : BalancedMixerJoint M s =>
      P (permuteSubset z.val.1 (M i) \ z.val.2)) =
      finiteUniformProbability (fun S : ↥((Finset.univ : Finset ι).powersetCard s) => P S.val) := by
  let B : BalancedSignSubsets M s → Finset ι := fun F => M i \ F.val
  have hB : ∀ F, (B F).card = s := by
    intro F
    dsimp [B]
    rw [Finset.card_sdiff, F.property i, hsize]
    omega
  calc
    _ = finiteUniformProbability (fun z : Equiv.Perm ι × BalancedSignSubsets M s =>
        P (permuteSubset z.1 (B z.2))) := by
      have h := finiteUniformProbability_equiv (balancedMixerJointEquiv M s)
        (fun z : Equiv.Perm ι × BalancedSignSubsets M s => P (permuteSubset z.1 (B z.2)))
      convert h using 1
      congr 1
      funext z
      change P (permuteSubset z.val.1 (M i) \ z.val.2) =
        P (permuteSubset z.val.1 (M i \ permuteSubset z.val.1.symm z.val.2))
      rw [permuteSubset_sdiff]
      rw [← permuteSubset_trans]
      simp
    _ = _ := permuted_family_uniform B s hB P

/-- A restriction in a mixer must have size `s`; the outside restriction is free. -/
abbrev BalancedColorRestriction (c : ι → Option (Fin 3)) (s : ℕ)
    (k : Option (Fin 3)) :=
  {S : Finset {x : ι // c x = k} // match k with
    | none => True
    | some _ => S.card = s}

noncomputable instance balancedColorRestrictionFintype [Fintype ι]
    (c : ι → Option (Fin 3)) (s : ℕ) (k : Option (Fin 3)) :
    Fintype (BalancedColorRestriction c s k) := Fintype.ofFinite _

def colorBalancedRestrictionEquiv (c : ι → Option (Fin 3)) (s : ℕ) :
    {F : Finset ι // ColorBalanced c s F} ≃
      ((k : Option (Fin 3)) → BalancedColorRestriction c s k) where
  toFun F k := ⟨F.val.subtype (fun x => c x = k), by
    cases k with
    | none => trivial
    | some i => exact F.property i⟩
  invFun f := ⟨(partitionFinsetEquiv c).symm (fun k => (f k).val), by
    intro i
    have hi := congrFun ((partitionFinsetEquiv c).apply_symm_apply
      (fun k => (f k).val)) (some i)
    change ((partitionFinsetEquiv c)
      ((partitionFinsetEquiv c).symm (fun k => (f k).val)) (some i)).card = s
    rw [hi]
    exact (f (some i)).property⟩
  left_inv F := by
    apply Subtype.ext
    exact (partitionFinsetEquiv c).symm_apply_apply F.val
  right_inv f := by
    funext k
    apply Subtype.ext
    exact congrFun ((partitionFinsetEquiv c).apply_symm_apply (fun k => (f k).val)) k

/-- The full conditional sign law is the product of the three uniform halves
and the unrestricted outside signs. -/
noncomputable def balancedMixerRestrictionEquiv (M : Fin 3 → Finset ι)
    (hdisj : ∀ i j, i ≠ j → Disjoint (M i) (M j)) (s : ℕ) :
    BalancedSignSubsets M s ≃
      ((k : Option (Fin 3)) → BalancedColorRestriction (mixerColor M) s k) :=
  (Equiv.subtypeEquivRight (fun F => (colorBalanced_mixerColor_iff M hdisj s F).symm)).trans
    (colorBalancedRestrictionEquiv (mixerColor M) s)

theorem conditioned_mixer_restrictions_uniform [Fintype ι] (M : Fin 3 → Finset ι)
    (hdisj : ∀ i j, i ≠ j → Disjoint (M i) (M j)) (s : ℕ)
    (P : ((k : Option (Fin 3)) → BalancedColorRestriction (mixerColor M) s k) → Prop) :
    finiteUniformProbability (fun F : BalancedSignSubsets M s =>
      P (balancedMixerRestrictionEquiv M hdisj s F)) = finiteUniformProbability P :=
  finiteUniformProbability_equiv (balancedMixerRestrictionEquiv M hdisj s) P

theorem conditioned_mixer_restrictions_point [Fintype ι] (M : Fin 3 → Finset ι)
    (hdisj : ∀ i j, i ≠ j → Disjoint (M i) (M j)) (s : ℕ)
    (r : (k : Option (Fin 3)) → BalancedColorRestriction (mixerColor M) s k) :
    finiteUniformProbability (fun F : BalancedSignSubsets M s =>
      balancedMixerRestrictionEquiv M hdisj s F = r) =
        ∏ k, 1 / (Fintype.card (BalancedColorRestriction (mixerColor M) s k) : ℝ) := by
  classical
  rw [conditioned_mixer_restrictions_uniform M hdisj s (fun f => f = r),
    finiteUniformProbability_eq_cardRatio]
  simp only [Fintype.card_subtype_eq, Fintype.card_pi, Nat.cast_prod,
    Finset.prod_div_distrib, Finset.prod_const_one, Nat.cast_one]

end LowSpaceSubsetSum

end OAI
