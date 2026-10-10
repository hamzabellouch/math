import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Analysis.A13IndexLemmas
import OAI.Computability.UniqueGames.Analysis.A5FrequencyTransportLemmas
import OAI.Computability.UniqueGames.Analysis.FiberEnergyLemmas
import OAI.Computability.UniqueGames.Analysis.HybridCounting
import OAI.Computability.UniqueGames.Analysis.MatrixNoiseLemmas
import OAI.Computability.UniqueGames.Analysis.MatrixRestrictions
import OAI.Computability.UniqueGames.Analysis.RestrictionLemmas
import OAI.Computability.UniqueGames.Gadgets.AdaptivePathsLemmas

namespace OAI

section

open scoped BigOperators

namespace UniqueGamesTheorem.Appendix.Globality

noncomputable def energy {N : Type*} [Fintype N] (f : N → ℝ) : ℝ :=
  𝔼 n, f n ^ 2

theorem energy_nonnegative {N : Type*} [Fintype N] (f : N → ℝ) :
    0 ≤ energy f := by
  exact Finset.expect_nonneg fun n _ => sq_nonneg (f n)

theorem sq_average_le_average_sq {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ℝ) : (𝔼 i, f i) ^ 2 ≤ 𝔼 i, f i ^ 2 := by
  simpa using Finset.expect_mul_sq_le_sq_mul_sq Finset.univ f (fun _ => (1 : ℝ))

theorem energy_average_le {I N : Type*} [Fintype I] [Nonempty I] [Fintype N]
    (f : I → N → ℝ) : energy (fun n => 𝔼 i, f i n) ≤ 𝔼 i, energy (f i) := by
  calc
    energy (fun n => 𝔼 i, f i n) ≤ 𝔼 n, 𝔼 i, f i n ^ 2 :=
      Finset.expect_le_expect fun n _ => sq_average_le_average_sq (fun i => f i n)
    _ = 𝔼 i, energy (f i) := Finset.expect_comm _ _ _

theorem energy_average_le_of_bound {I N : Type*} [Fintype I] [Nonempty I]
    [Fintype N] (f : I → N → ℝ) (η : ℝ) (h : ∀ i, energy (f i) ≤ η) :
    energy (fun n => 𝔼 i, f i n) ≤ η :=
  (energy_average_le f).trans (Finset.expect_le Finset.univ_nonempty (fun i _ => h i))

theorem energy_weighted_sum_le {I N : Type*} [Fintype I] [Fintype N]
    (w : I → ℝ) (f : I → N → ℝ) (η : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, energy (f i) ≤ η) :
    energy (fun n => ∑ i, w i * f i n) ≤ (∑ i, w i) ^ 2 * η := by
  have hsum : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
  calc
    energy (fun n => ∑ i, w i * f i n) ≤
        𝔼 n, (∑ i, w i) * ∑ i, w i * f i n ^ 2 := by
      apply Finset.expect_le_expect
      intro n _
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      · exact fun i _ => hw i
      · exact fun i _ => mul_nonneg (hw i) (sq_nonneg _)
      · intro i _
        exact le_of_eq (by ring)
    _ = (∑ i, w i) * ∑ i, w i * energy (f i) := by
      rw [← Finset.mul_expect, Finset.expect_sum_comm]
      simp_rw [← Finset.mul_expect]
      rfl
    _ ≤ (∑ i, w i) * ∑ i, w i * η := by
      apply mul_le_mul_of_nonneg_left _ hsum
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i) (hw i))
    _ = (∑ i, w i) ^ 2 * η := by rw [← Finset.sum_mul]; ring

noncomputable def restrictionEnergy {M N : Type*} [AddCommGroup M] [Fintype N]
    (f : M → ℝ) (ι : N → M) (T : M) : ℝ :=
  energy (fun n => f (T + ι n))

theorem restrictionEnergy_translate {M N : Type*} [AddCommGroup M] [Fintype N]
    (f : M → ℝ) (ι : N → M) (T a : M) :
    restrictionEnergy (fun x => f (x + a)) ι T = restrictionEnergy f ι (T + a) := by
  simp only [restrictionEnergy, add_right_comm T]

theorem restrictionEnergy_average_translate_le {I M N : Type*}
    [Fintype I] [Nonempty I] [AddCommGroup M] [Fintype N]
    (f : M → ℝ) (ι : N → M) (shifts : I → M) (η : ℝ)
    (h : ∀ T, restrictionEnergy f ι T ≤ η) (T : M) :
    restrictionEnergy (fun x => 𝔼 i, f (x + shifts i)) ι T ≤ η := by
  apply energy_average_le_of_bound (fun i n => f ((T + ι n) + shifts i)) η
  intro i
  simpa only [restrictionEnergy, add_right_comm T] using h (T + shifts i)

section BinaryLinear

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Fourier.MatrixRestrictions

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F] [Finite E] [Finite F]

def RestrictionGlobal (d : Nat) (η : ℝ) (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ (A : Submodule F2 E) (B : Submodule F2 F), order A B ≤ d →
    ∀ T : E →ₗ[F2] F, restrictionEnergy f (embed A B) T ≤ η

noncomputable def averageTranslates {I : Type*} [Fintype I]
    (shifts : I → (E →ₗ[F2] F)) (f : (E →ₗ[F2] F) → ℝ) : (E →ₗ[F2] F) → ℝ :=
  fun X => 𝔼 i, f (X + shifts i)

theorem restrictionGlobal_averageTranslates {I : Type*} [Fintype I] [Nonempty I]
    (shifts : I → (E →ₗ[F2] F)) (d : Nat) (η : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : RestrictionGlobal d η f) :
    RestrictionGlobal d η (averageTranslates shifts f) := by
  intro A B hord T
  exact restrictionEnergy_average_translate_le f (embed A B) shifts η (hf A B hord) T

theorem restrictionGlobal_neg (d : Nat) (η : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : RestrictionGlobal d η f) : RestrictionGlobal d η (fun X => -f X) := by
  intro A B hord T
  simpa only [restrictionEnergy, energy, neg_sq] using hf A B hord T

theorem restrictionGlobal_weighted_sum {I : Type*} [Fintype I]
    (w : I → ℝ) (f : I → (E →ₗ[F2] F) → ℝ) (d : Nat) (η : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, RestrictionGlobal d η (f i)) :
    RestrictionGlobal d ((∑ i, w i) ^ 2 * η) (fun X => ∑ i, w i * f i X) := by
  intro A B hord T
  exact energy_weighted_sum_le w (fun i n => f i (T + embed A B n)) η hw
    (fun i => hf i A B hord T)

theorem restrictionGlobal_three_terms (d : Nat) (η a b : ℝ)
    (f g h : (E →ₗ[F2] F) → ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : RestrictionGlobal d η f) (hg : RestrictionGlobal d η g)
    (hh : RestrictionGlobal d η h) :
    RestrictionGlobal d ((1 + a + b) ^ 2 * η)
      (fun X => f X - a * g X + b * h X) := by
  let w : Fin 3 → ℝ := fun i => if i = 0 then 1 else if i = 1 then a else b
  let fs : Fin 3 → (E →ₗ[F2] F) → ℝ := fun i =>
    if i = 0 then f else if i = 1 then (fun X => -g X) else h
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · simp [w]
    · simpa [w] using ha
    · simpa [w] using hb
  have hfs : ∀ i, RestrictionGlobal d η (fs i) := by
    intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · simpa [fs] using hf
    · simpa [fs] using restrictionGlobal_neg d η g hg
    · simpa [fs] using hh
  have hs := restrictionGlobal_weighted_sum w fs d η hw hfs
  simpa [w, fs, Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using hs

noncomputable def quadraticFilter {I : Type*} [Fintype I]
    (d : Nat) (shifts : I → (E →ₗ[F2] F)) (f : (E →ₗ[F2] F) → ℝ) :
    (E →ₗ[F2] F) → ℝ := fun X =>
  f X - ((2 : ℝ) ^ d + 2 ^ (d - 1)) * averageTranslates shifts f X +
    2 ^ (2 * d - 1) * averageTranslates shifts (averageTranslates shifts f) X

theorem restrictionGlobal_quadraticFilter {I : Type*} [Fintype I] [Nonempty I]
    (d : Nat) (η : ℝ) (shifts : I → (E →ₗ[F2] F))
    (f : (E →ₗ[F2] F) → ℝ) (hf : RestrictionGlobal d η f) :
    RestrictionGlobal d
      ((1 + ((2 : ℝ) ^ d + 2 ^ (d - 1)) + 2 ^ (2 * d - 1)) ^ 2 * η)
      (quadraticFilter d shifts f) := by
  have hg := restrictionGlobal_averageTranslates shifts d η f hf
  have hh := restrictionGlobal_averageTranslates shifts d η (averageTranslates shifts f) hg
  exact restrictionGlobal_three_terms d η _ _ f _ _
    (add_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _))
    (pow_nonneg (by norm_num) _) hf hg hh

theorem restrictionGlobal_deleted_indicator
    (H : (E →ₗ[F2] F) → Bool) (r p q : Nat) (hq : 0 < q) :
    RestrictionGlobal r ((p : ℝ) / q)
      (fun X => if UniqueGamesTheorem.Fourier.Deletion.remainder (system r) H p q X
        then (1 : ℝ) else 0) := by
  intro A B hord T
  exact remainder_restriction_sq_expect H r p q hq A B hord T

abbrev LineIndex (v : E) := F × {φ : E →ₗ[F2] F2 // φ v = 1}

noncomputable instance lineIndexFintype (v : E) : Fintype (LineIndex (F := F) v) := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype F := Fintype.ofFinite F
  letI : Fintype (E →ₗ[F2] F2) := Fintype.ofInjective
    (fun φ : E →ₗ[F2] F2 => (φ : E → F2)) DFunLike.coe_injective
  exact inferInstance

def lineShift (v : E) (p : LineIndex (F := F) v) : E →ₗ[F2] F :=
  p.2.val.smulRight p.1

noncomputable def lineAverage (v : E) (f : (E →ₗ[F2] F) → ℝ) :
    (E →ₗ[F2] F) → ℝ := averageTranslates (lineShift v) f

omit [Module F2 F] [Finite F] in
theorem lineIndex_nonempty (v : E) (hv : v ≠ 0) : Nonempty (LineIndex (F := F) v) := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F2 hv
  exact ⟨0, φ, hφ⟩

theorem restrictionGlobal_lineAverage (v : E) (hv : v ≠ 0)
    (d : Nat) (η : ℝ) (f : (E →ₗ[F2] F) → ℝ) (hf : RestrictionGlobal d η f) :
    RestrictionGlobal d η (lineAverage v f) := by
  let := lineIndex_nonempty (F := F) v hv
  exact restrictionGlobal_averageTranslates (lineShift v) d η f hf

abbrev HyperplaneIndex (ω : F →ₗ[F2] F2) := {a : F // ω a = 1} × (E →ₗ[F2] F2)

noncomputable instance hyperplaneIndexFintype (ω : F →ₗ[F2] F2) :
    Fintype (HyperplaneIndex (E := E) ω) := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype F := Fintype.ofFinite F
  letI : Fintype (E →ₗ[F2] F2) := Fintype.ofInjective
    (fun φ : E →ₗ[F2] F2 => (φ : E → F2)) DFunLike.coe_injective
  exact inferInstance

def hyperplaneShift (ω : F →ₗ[F2] F2) (p : HyperplaneIndex (E := E) ω) : E →ₗ[F2] F :=
  p.2.smulRight p.1.val

noncomputable def hyperplaneAverage (ω : F →ₗ[F2] F2)
    (f : (E →ₗ[F2] F) → ℝ) : (E →ₗ[F2] F) → ℝ :=
  averageTranslates (hyperplaneShift ω) f

omit [Finite E] [Finite F] in
theorem hyperplaneIndex_nonempty (ω : F →ₗ[F2] F2) (hω : ω ≠ 0) :
    Nonempty (HyperplaneIndex (E := E) ω) := by
  classical
  have hex : ¬ ∀ a, ω a = 0 := by
    intro h
    exact hω (LinearMap.ext h)
  obtain ⟨a, ha⟩ := not_forall.mp hex
  have hone : ω a = 1 := (scalar_cases (ω a)).resolve_left ha
  exact ⟨⟨a, hone⟩, 0⟩

theorem restrictionGlobal_hyperplaneAverage (ω : F →ₗ[F2] F2) (hω : ω ≠ 0)
    (d : Nat) (η : ℝ) (f : (E →ₗ[F2] F) → ℝ) (hf : RestrictionGlobal d η f) :
    RestrictionGlobal d η (hyperplaneAverage ω f) := by
  let := hyperplaneIndex_nonempty (E := E) ω hω
  exact restrictionGlobal_averageTranslates (hyperplaneShift ω) d η f hf

end BinaryLinear

end UniqueGamesTheorem.Appendix.Globality

end

section

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.LevelInequality
open UniqueGamesTheorem.Appendix.Globality

namespace UniqueGamesTheorem.Appendix.RankLevelFilter

attribute [local instance] Classical.propDecidable

def node : ℕ → ℝ
  | 0 => 1
  | n + 1 => node n / 2

theorem node_pos (n : ℕ) : 0 < node n := by
  induction n with
  | zero => norm_num [node]
  | succ n ih => exact div_pos ih (by norm_num)

theorem node_eq_inv_pow (n : ℕ) : node n = ((2 : ℝ) ^ n)⁻¹ := by
  induction n with
  | zero => simp [node]
  | succ n ih => rw [node, ih, pow_succ, mul_inv_rev]; ring

theorem node_add_le (i k : ℕ) : node (i + k) ≤ node i := by
  induction k with
  | zero => simp
  | succ k ih =>
    change node (i + k) / 2 ≤ node i
    linarith [node_pos (i + k)]

theorem node_antitone {i j : ℕ} (h : i ≤ j) : node j ≤ node i := by
  have he : i + (j - i) = j := by omega
  simpa only [he] using node_add_le i (j - i)

theorem node_le_one (n : ℕ) : node n ≤ 1 := by
  simpa [node] using node_add_le 0 n

theorem node_gap {j d : ℕ} (h : j < d) :
    0 < node j - node d ∧ node d ≤ node j - node d := by
  have hm := node_antitone (show j + 1 ≤ d by omega)
  change node d ≤ node j / 2 at hm
  constructor <;> linarith [node_pos d]

theorem step_coefficient_bound {j d : ℕ} (h : j < d) :
    node j / (node j - node d) + (node j - node d)⁻¹ ≤ (2 : ℝ) ^ (d + 1) := by
  have hg := node_gap h
  have he : node j / (node j - node d) + (node j - node d)⁻¹ =
      (node j + 1) / (node j - node d) := by
    simp only [div_eq_mul_inv]
    ring
  rw [he]
  calc
    _ ≤ 2 / (node j - node d) :=
      div_le_div_of_nonneg_right (by linarith [node_le_one j]) hg.1.le
    _ ≤ 2 / node d := div_le_div_of_nonneg_left (by norm_num) (node_pos d) hg.2
    _ = (2 : ℝ) ^ (d + 1) := by
      rw [node_eq_inv_pow, div_inv_eq_mul, pow_succ]
      ring

def multiplier (d k r : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, (node j - node r) / (node j - node d)

theorem multiplier_succ (d k r : ℕ) :
    multiplier d (k + 1) r =
      multiplier d k r * ((node k - node r) / (node k - node d)) := by
  simp only [multiplier, Finset.prod_range_succ]

theorem multiplier_target (d k : ℕ) (hk : k ≤ d) : multiplier d k d = 1 := by
  unfold multiplier
  apply Finset.prod_eq_one
  intro j hj
  have hjd : j < d := lt_of_lt_of_le (Finset.mem_range.mp hj) hk
  exact div_self (ne_of_gt (node_gap hjd).1)

theorem multiplier_below (d k r : ℕ) (hr : r < k) : multiplier d k r = 0 := by
  unfold multiplier
  exact Finset.prod_eq_zero_iff.mpr ⟨r, Finset.mem_range.mpr hr, by simp⟩

@[instance_reducible] def linearMapFintype {U V : Type*} [AddCommGroup U] [Module F2 U]
    [AddCommGroup V] [Module F2 V] [Finite U] [Finite V] : Fintype (U →ₗ[F2] V) := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  letI : Fintype V := Fintype.ofFinite V
  exact Fintype.ofInjective (fun φ : U →ₗ[F2] V => (φ : U → V)) DFunLike.coe_injective

section ActualLinearMaps

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in
theorem linearNoiseEigenvalue_uniform [Fintype F] (S : F →ₗ[F2] E) :
    UniqueGamesTheorem.Fourier.MatrixNoise.linearNoiseEigenvalue
      (fun _ : F => (Fintype.card F : ℝ)⁻¹) S =
        ((2 : ℝ) ^ Module.finrank F2 S.range)⁻¹ := by
  classical
  let k := (Finset.univ.filter fun v : F => S v = 0).card
  have hs : (∑ v : F, if S v = 0 then (1 : ℝ) else 0) = (k : ℝ) := by
    rw [← Finset.sum_filter]
    simp [k]
  have hc : (k : ℝ) * (2 : ℝ) ^ Module.finrank F2 S.range =
      (Fintype.card F : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ))
      (UniqueGamesTheorem.Gadget.LinearKernelCount.zero_event_finset_count_mul_pow_rank S)
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h
  have hn : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hp : (2 : ℝ) ^ Module.finrank F2 S.range ≠ 0 := pow_ne_zero _ two_ne_zero
  unfold UniqueGamesTheorem.Fourier.MatrixNoise.linearNoiseEigenvalue
  rw [← Finset.mul_sum, hs]
  apply mul_right_cancel₀ hp
  calc
    ((Fintype.card F : ℝ)⁻¹ * (k : ℝ)) * (2 : ℝ) ^ Module.finrank F2 S.range =
        (Fintype.card F : ℝ)⁻¹ * ((k : ℝ) * (2 : ℝ) ^ Module.finrank F2 S.range) :=
      mul_assoc _ _ _
    _ = (Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ) := by rw [hc]
    _ = 1 := inv_mul_cancel₀ hn
    _ = ((2 : ℝ) ^ Module.finrank F2 S.range)⁻¹ *
        (2 : ℝ) ^ Module.finrank F2 S.range := (inv_mul_cancel₀ hp).symm

variable [Finite E] [Finite F]

def rankNoise (f : (E →ₗ[F2] F) → ℝ) : (E →ₗ[F2] F) → ℝ :=
  letI : Fintype F := Fintype.ofFinite F
  letI : Fintype (E →ₗ[F2] F2) := linearMapFintype
  UniqueGamesTheorem.Fourier.MatrixNoise.linearRealNoiseOperator
    (fun _ : F => (Fintype.card F : ℝ)⁻¹) f

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem rankNoise_eq_average (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    letI : Fintype F := Fintype.ofFinite F
    letI : Fintype (E →ₗ[F2] F2) := linearMapFintype
    rankNoise f X = 𝔼 v : F, 𝔼 φ : E →ₗ[F2] F2, f (X + φ.smulRight v) := by
  classical
  dsimp [rankNoise, UniqueGamesTheorem.Fourier.MatrixNoise.linearRealNoiseOperator]
  simp only [Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  rw [← Finset.mul_sum]
  exact mul_comm _ _

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem global_average_family {I : Type*} [Fintype I] [Nonempty I]
    (f : I → (E →ₗ[F2] F) → ℝ) (d : ℕ) (η : ℝ)
    (hf : ∀ i, RestrictionGlobal d η (f i)) :
    RestrictionGlobal d η (fun X => 𝔼 i, f i X) := by
  intro A B hord T
  exact energy_average_le_of_bound (fun i N => f i (T + embed A B N)) η
    (fun i => hf i A B hord T)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem rankNoise_global (d : ℕ) (η : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : RestrictionGlobal d η f) : RestrictionGlobal d η (rankNoise f) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (E →ₗ[F2] F2) := linearMapFintype
  have he : rankNoise f =
      fun X => 𝔼 v : F, 𝔼 φ : E →ₗ[F2] F2, f (X + φ.smulRight v) := by
    funext X
    exact rankNoise_eq_average f X
  rw [he]
  apply global_average_family _ d η
  intro v
  exact restrictionGlobal_averageTranslates (fun φ : E →ₗ[F2] F2 => φ.smulRight v)
    d η f hf

omit [FiniteDimensional F2 E] in
theorem global_nonneg (d : ℕ) (η : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : RestrictionGlobal d η f) : 0 ≤ η := by
  have hord : order (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) ≤ d := by
    have hq := (⊤ : Submodule F2 F).finrank_quotient_add_finrank
    simp only [finrank_top] at hq
    have hz : Module.finrank F2 (F ⧸ (⊤ : Submodule F2 F)) = 0 := by omega
    simp [order, hz]
  exact (energy_nonnegative _).trans (hf ⊥ ⊤ hord 0)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem global_mono_bound {d : ℕ} {η ζ : ℝ} {f : (E →ₗ[F2] F) → ℝ}
    (hη : η ≤ ζ) (hf : RestrictionGlobal d η f) : RestrictionGlobal d ζ f := by
  intro A B hord T
  exact (hf A B hord T).trans hη

def step (d j : ℕ) (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) : ℝ :=
  (node j * f X - rankNoise f X) / (node j - node d)

omit [FiniteDimensional F2 E] in
theorem step_global (d j : ℕ) (hj : j < d) (η : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : RestrictionGlobal d η f) :
    RestrictionGlobal d ((2 : ℝ) ^ (2 * (d + 1)) * η) (step d j f) := by
  let a := node j / (node j - node d)
  let b := (node j - node d)⁻¹
  have ha : 0 ≤ a := div_nonneg (node_pos j).le (node_gap hj).1.le
  have hb : 0 ≤ b := inv_nonneg.mpr (node_gap hj).1.le
  let w : Fin 2 → ℝ := fun i => if i = 0 then a else b
  let fs : Fin 2 → (E →ₗ[F2] F) → ℝ := fun i =>
    if i = 0 then f else fun X => -rankNoise f X
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · simpa [w] using ha
    · simpa [w] using hb
  have hfs : ∀ i, RestrictionGlobal d η (fs i) := by
    intro i
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · simpa [fs] using hf
    · simpa [fs] using restrictionGlobal_neg d η (rankNoise f) (rankNoise_global d η f hf)
  have hs := restrictionGlobal_weighted_sum w fs d η hw hfs
  have he : (fun X => ∑ i : Fin 2, w i * fs i X) = step d j f := by
    funext X
    simp [w, fs, Fin.sum_univ_succ, step, a, b, div_eq_mul_inv]
    ring
  have hwSum : (∑ i : Fin 2, w i) = a + b := by simp [w, Fin.sum_univ_succ]
  rw [he, hwSum] at hs
  apply global_mono_bound _ hs
  have hc : a + b ≤ (2 : ℝ) ^ (d + 1) := step_coefficient_bound hj
  have hsq : (a + b) ^ 2 ≤ ((2 : ℝ) ^ (d + 1)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc)
      (show 0 ≤ (2 : ℝ) ^ (d + 1) + (a + b) by positivity)]
  have hp : ((2 : ℝ) ^ (d + 1)) ^ 2 = (2 : ℝ) ^ (2 * (d + 1)) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hp] at hsq
  exact mul_le_mul_of_nonneg_right hsq (global_nonneg d η f hf)

def iterateFilter (d : ℕ) : ℕ → ((E →ₗ[F2] F) → ℝ) → (E →ₗ[F2] F) → ℝ
  | 0, f => f
  | k + 1, f => step d k (iterateFilter d k f)

omit [FiniteDimensional F2 E] in
theorem iterateFilter_global (d k : ℕ) (hk : k ≤ d) (η : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : RestrictionGlobal d η f) :
    RestrictionGlobal d ((2 : ℝ) ^ (2 * k * (d + 1)) * η) (iterateFilter d k f) := by
  induction k with
  | zero => simpa [iterateFilter] using hf
  | succ k ih =>
    have hk' : k ≤ d := by omega
    have hs := step_global d k (by omega) _ _ (ih hk')
    have hex : 2 * (d + 1) + 2 * k * (d + 1) = 2 * (k + 1) * (d + 1) := by ring
    simpa only [iterateFilter, ← mul_assoc, ← pow_add, hex] using hs

variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem rankNoise_coeff (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (rankNoise f) S = node (frequencyRank S) * linearCoeff f S := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (E →ₗ[F2] F2) := linearMapFintype
  rw [rankNoise, UniqueGamesTheorem.Fourier.MatrixNoise.linearRealNoiseOperator_coeff,
    linearNoiseEigenvalue_uniform, node_eq_inv_pow]
  rfl

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (F →ₗ[F2] E)] in
theorem coefficient_linearCombination (a b : ℝ) (f g : (E →ₗ[F2] F) → ℝ)
    (S : F →ₗ[F2] E) :
    linearCoeff (fun X => a * f X + b * g X) S =
      a * linearCoeff f S + b * linearCoeff g S := by
  unfold linearCoeff
  simp_rw [add_mul, mul_assoc, Finset.expect_add_distrib, ← Finset.mul_expect]

theorem step_coeff (d j : ℕ) (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (step d j f) S =
      ((node j - node (frequencyRank S)) / (node j - node d)) * linearCoeff f S := by
  have he : step d j f = fun X =>
      (node j / (node j - node d)) * f X +
        (-1 / (node j - node d)) * rankNoise f X := by
    funext X
    dsimp [step]
    ring
  rw [he, coefficient_linearCombination, rankNoise_coeff]
  simp only [div_eq_mul_inv]
  ring

theorem iterateFilter_coeff (d k : ℕ) (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (iterateFilter d k f) S =
      multiplier d k (frequencyRank S) * linearCoeff f S := by
  induction k with
  | zero => simp [iterateFilter, multiplier]
  | succ k ih => rw [iterateFilter, step_coeff, ih, multiplier_succ]; ring

theorem iterateFilter_coeff_low (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (S : F →ₗ[F2] E) (hS : frequencyRank S ≤ d) :
    linearCoeff (iterateFilter d d f) S =
      if frequencyRank S = d then linearCoeff f S else 0 := by
  rw [iterateFilter_coeff]
  by_cases he : frequencyRank S = d
  · rw [he, multiplier_target d d le_rfl]
    simp
  · have hl : frequencyRank S < d := by omega
    rw [multiplier_below d d _ hl]
    simp [he]

omit [Finite E] [Finite F] in
theorem rankLevel_eq_projector (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    rankLevel d f = Derivatives.spectralProjector (fun Y => frequencyRank Y = d) f := by
  apply Derivatives.function_eq_of_linearCoeff_eq
  intro Y
  rw [linearCoeff_rankLevel, Derivatives.linearCoeff_spectralProjector]
  by_cases h : frequencyRank Y = d <;> simp [h]

theorem filtered_compression_projector (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (A : Submodule F2 E) (B : Submodule F2 F) (hord : order A B ≤ d) :
    Derivatives.spectralProjector
      (fun Y => frequencyRank (Restriction.compressFrequency A B Y) = d - order A B)
      (iterateFilter d d f) = Derivatives.hybridProjector A B (rankLevel d f) := by
  apply Derivatives.function_eq_of_linearCoeff_eq
  intro Y
  simp only [Derivatives.hybridProjector, Derivatives.linearCoeff_spectralProjector,
    linearCoeff_rankLevel]
  have hb := Level.LinearRank.compression_rank_bounds A B Y
  have hs := Level.LinearRank.hybrid_rank_loss_iff A B Y
  change frequencyRank (Restriction.compressFrequency A B Y) ≤ frequencyRank Y ∧
    frequencyRank Y ≤ frequencyRank (Restriction.compressFrequency A B Y) +
      Module.finrank F2 A + Module.finrank F2 (F ⧸ B) at hb
  change frequencyRank (Restriction.compressFrequency A B Y) + Module.finrank F2 A +
      Module.finrank F2 (F ⧸ B) = frequencyRank Y ↔ LinearIdentities.Hybrid Y A B at hs
  have ho : Module.finrank F2 A + Module.finrank F2 (F ⧸ B) ≤ d := hord
  by_cases hc : frequencyRank (Restriction.compressFrequency A B Y) = d - order A B
  · have hrle : frequencyRank Y ≤ d := by dsimp [order] at hc; omega
    rw [ite_eq_left hc, iterateFilter_coeff_low d f Y hrle]
    by_cases hr : frequencyRank Y = d
    · have hhy : LinearIdentities.Hybrid Y A B := hs.mp (by dsimp [order] at hc; omega)
      simp [hr, hhy]
    · simp [hr]
  · rw [ite_eq_right hc]
    by_cases hhy : LinearIdentities.Hybrid Y A B
    · rw [ite_eq_left hhy]
      by_cases hr : frequencyRank Y = d
      · have hl := hs.mpr hhy
        have he : frequencyRank (Restriction.compressFrequency A B Y) = d - order A B := by
          dsimp [order]
          omega
        exact (hc he).elim
      · simp [hr]
    · simp [hhy]

theorem hybridDerivative_rankLevel_eq_local_projection (d : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))] (T : E →ₗ[F2] F) (hord : order A B ≤ d) :
    Derivatives.hybridDerivative A B T (rankLevel d f) =
      rankLevel (d - order A B) (restrict (iterateFilter d d f) A B T) := by
  rw [rankLevel_eq_projector (d - order A B) (restrict (iterateFilter d d f) A B T),
    Derivatives.spectralProjector_restriction,
    filtered_compression_projector d f A B hord]
  rfl

theorem hybridDerivative_rankLevel_energy_le_strong (d : ℕ) (η : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsRestrictionGlobal f d η)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F)
    (hord : order A B ≤ d) :
    (𝔼 N, Derivatives.hybridDerivative A B T (rankLevel d f) N ^ 2) ≤
      (2 : ℝ) ^ (2 * d * (d + 1)) * η := by
  classical
  let : Finite (E ⧸ A) := Finite.of_surjective A.mkQ A.mkQ_surjective
  let : Fintype (B →ₗ[F2] (E ⧸ A)) := linearMapFintype
  have hglobal : RestrictionGlobal d η f := by
    intro A' B' horder T'
    exact hf A' B' T' horder
  have hg := iterateFilter_global d d le_rfl η f hglobal
  rw [hybridDerivative_rankLevel_eq_local_projection d f A B T hord]
  exact (rankLevel_energy_le _ _).trans (hg A B hord T)

theorem hybridDerivative_rankLevel_energy_le (d : ℕ) (η : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsRestrictionGlobal f d η)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F)
    (hord : order A B ≤ d) :
    (𝔼 N, Derivatives.hybridDerivative A B T (rankLevel d f) N ^ 2) ≤
      (2 : ℝ) ^ (10 * d * d) * η := by
  have hglobal : RestrictionGlobal d η f := by
    intro A' B' horder T'
    exact hf A' B' T' horder
  have he : 2 * d * (d + 1) ≤ 10 * d * d := by
    nlinarith [Nat.le_mul_self d]
  exact (hybridDerivative_rankLevel_energy_le_strong d η f hf A B T hord).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) he)
      (global_nonneg d η f hglobal))

end ActualLinearMaps

end UniqueGamesTheorem.Appendix.RankLevelFilter

end

end

section

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier

namespace UniqueGamesTheorem.Appendix.SelectorEnergy

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem hybridSelectorEnergy_le (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (hdegree : ∀ Y, d < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    Derivatives.hybridSelectorEnergy d f ≤
      (2 : ℝ) ^ (3 * d * d) * (𝔼 X, f X ^ 2) := by
  classical
  unfold Derivatives.hybridSelectorEnergy Derivatives.hybridProjector
  apply Derivatives.selector_energy_sum_le
  intro Y hY
  have hrank : Module.finrank F2 Y.range ≤ d := by
    by_contra hn
    exact hY (hdegree Y (Nat.lt_of_not_ge hn))
  have hc := HybridCounting.card_hybridIndex_le Y d hrank
  have hcount : Derivatives.selectorMultiplicity
      (fun s : Derivatives.HybridIndex (E := E) (F := F) d =>
        fun Y => LinearIdentities.Hybrid Y s.val.1 s.val.2) Y =
      Nat.card {s : Derivatives.HybridIndex (E := E) (F := F) d //
        LinearIdentities.Hybrid Y s.val.1 s.val.2} := by
    simp only [Derivatives.selectorMultiplicity, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  rw [hcount]
  exact_mod_cast hc

theorem hybridMomentSum_rankLevel_le (d : ℕ) (η : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : LevelInequality.IsRestrictionGlobal f d η) :
    Derivatives.hybridMomentSum d (LevelInequality.rankLevel d f) ≤
      (2 : ℝ) ^ (13 * d * d) * η * (𝔼 X, f X ^ 2) := by
  have hglobal : Globality.RestrictionGlobal d η f := by
    intro A B hord T
    exact hf A B T hord
  have hη : 0 ≤ η := RankLevelFilter.global_nonneg d η f hglobal
  have hu := Derivatives.hybridMomentSum_le_of_uniform_energy d
    (LevelInequality.rankLevel d f) ((2 : ℝ) ^ (10 * d * d) * η)
    (fun A B T h => RankLevelFilter.hybridDerivative_rankLevel_energy_le d η f hf A B T h)
  have hs := hybridSelectorEnergy_le d (LevelInequality.rankLevel d f)
    (fun Y hY => LevelInequality.rankLevel_degree_le d f Y hY)
  have hc := LevelInequality.rankLevel_energy_le d f
  have hζ : 0 ≤ (2 : ℝ) ^ (10 * d * d) * η := mul_nonneg (by positivity) hη
  have hp : (2 : ℝ) ^ (10 * d * d) * (2 : ℝ) ^ (3 * d * d) =
      (2 : ℝ) ^ (13 * d * d) := by
    rw [← pow_add]
    congr 1
    ring
  calc
    _ ≤ ((2 : ℝ) ^ (10 * d * d) * η) * Derivatives.hybridSelectorEnergy d
        (LevelInequality.rankLevel d f) := hu
    _ ≤ ((2 : ℝ) ^ (10 * d * d) * η) * ((2 : ℝ) ^ (3 * d * d) *
        (𝔼 X, LevelInequality.rankLevel d f X ^ 2)) :=
      mul_le_mul_of_nonneg_left hs hζ
    _ ≤ ((2 : ℝ) ^ (10 * d * d) * η) * ((2 : ℝ) ^ (3 * d * d) * (𝔼 X, f X ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc (by positivity)) hζ
    _ = ((2 : ℝ) ^ (10 * d * d) * (2 : ℝ) ^ (3 * d * d)) * η * (𝔼 X, f X ^ 2) := by
      ring
    _ = _ := by rw [hp]

end UniqueGamesTheorem.Appendix.SelectorEnergy

end

end

section

noncomputable section
namespace UniqueGamesTheorem.Appendix.LevelTheorem
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.LevelInequality

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

section FiniteDimensional
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

theorem rankLevel_fourth_moment_le (d : ℕ) (η : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsRestrictionGlobal f d η) :
    (𝔼 M, rankLevel d f M^4) ≤
      (2:ℝ)^(113*d*d) * η * (𝔼 M, f M^2) := by
  have ha := A5Induction.derivative_inequality d (rankLevel d f)
    (DerivativeDegree.degree_rankLevel d f)
  have hs := SelectorEnergy.hybridMomentSum_rankLevel_le d η f hf
  have hp : (2:ℝ)^(100*d^2) * (2:ℝ)^(13*d*d) = (2:ℝ)^(113*d*d) := by
    rw [← pow_add]
    congr 1
    ring
  calc
    _ ≤ (2:ℝ)^(100*d^2) * Derivatives.hybridMomentSum d (rankLevel d f) := ha
    _ ≤ (2:ℝ)^(100*d^2) * ((2:ℝ)^(13*d*d) * η * (𝔼 M, f M^2)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = ((2:ℝ)^(100*d^2) * (2:ℝ)^(13*d*d)) * η * (𝔼 M, f M^2) := by ring
    _ = _ := by rw [hp]

end FiniteDimensional

theorem theorem23 : LevelInequality.Theorem23 (E := E) (F := F) := by
  let : FiniteDimensional F2 E := Module.Finite.of_finite
  let : FiniteDimensional F2 F := Module.Finite.of_finite
  intro d _ ρ hρ _ f hf hrestricted
  have hglobal : IsRestrictionGlobal f d ρ :=
    (boolean_global_iff_density f hf d ρ).mpr hrestricted
  have hfourth := rankLevel_fourth_moment_le d ρ f hglobal
  rw [boolean_squared_norm_eq_density hf] at hfourth
  exact rankLevel_bound_of_fourth_moment d f hf ρ hρ.le hfourth

end UniqueGamesTheorem.Appendix.LevelTheorem

end

end

section

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixLevelBridge

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.LevelInequality

def levelCutoffConstant (r : Nat) (ρ : ℝ) : ℝ :=
  ∑ d ∈ Finset.range (r + 1),
    if d = 0 then ρ else (2 : ℝ) ^ (30 * d * d) * ρ ^ ((1 : ℝ) / 4)

theorem levelCutoffConstant_nonneg (r : Nat) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    0 ≤ levelCutoffConstant r ρ := by
  unfold levelCutoffConstant
  apply Finset.sum_nonneg
  intro d _
  split_ifs
  · exact hρ
  · exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      (Real.rpow_nonneg hρ _)

theorem sum_rank_le {ι : Type*} [Fintype ι] (rk : ι → Nat) (w : ι → ℝ) (r : Nat) :
    (∑ i, if rk i ≤ r then w i else 0) =
      ∑ d ∈ Finset.range (r + 1), ∑ i, if rk i = d then w i else 0 := by
  calc
    _ = ∑ i, ∑ d ∈ Finset.range (r + 1), if rk i = d then w i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simp [Finset.mem_range]
    _ = _ := Finset.sum_comm

section Unrestricted

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

def unrestrictedEquiv :
    Parameter (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) ≃ (E →ₗ[F2] F) :=
  Equiv.ofBijective (embed (⊥ : Submodule F2 E) (⊤ : Submodule F2 F))
    ⟨embed_injective ⊥ ⊤, fun X =>
      (exists_embed_iff (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) X).mpr
        ⟨bot_le, le_top⟩⟩

theorem order_bot_top : order (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) = 0 := by
  simpa [order] using
    (Module.finrank_eq_zero_of_subsingleton F2 (F ⧸ (⊤ : Submodule F2 F)))

theorem expect_unrestricted [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)]
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 A : Parameter (⊥ : Submodule F2 E) (⊤ : Submodule F2 F),
      restrict f ⊥ ⊤ 0 A) = 𝔼 X : E →ₗ[F2] F, f X := by
  apply Finset.expect_equiv (unrestrictedEquiv (E := E) (F := F))
  · intro A
    simp
  · intro A _
    change f (0 + embed ⊥ ⊤ A) = f (embed ⊥ ⊤ A)
    rw [zero_add]

end Unrestricted

section ActualLinearMaps

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def rankCutoffEnergy (r : Nat) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ S with frequencyRank S ≤ r, linearCoeff f S ^ 2

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem rankCutoffEnergy_eq_sum_exactRankMass (r : Nat) (f : (E →ₗ[F2] F) → ℝ) :
    rankCutoffEnergy r f =
      ∑ d ∈ Finset.range (r + 1), ∑ S with frequencyRank S = d, linearCoeff f S ^ 2 := by
  simpa only [rankCutoffEnergy, Finset.sum_filter] using
    sum_rank_le frequencyRank (fun S => linearCoeff f S ^ 2) r

theorem rankCutoffEnergy_eq_sum_rankLevel (r : Nat) (f : (E →ₗ[F2] F) → ℝ) :
    rankCutoffEnergy r f =
      ∑ d ∈ Finset.range (r + 1), (𝔼 X, rankLevel d f X ^ 2) := by
  simp only [rankLevel_energy, rankCutoffEnergy_eq_sum_exactRankMass]

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem frequencyRank_eq_zero_iff (S : F →ₗ[F2] E) : frequencyRank S = 0 ↔ S = 0 := by
  rw [frequencyRank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_zero_frequency (f : (E →ₗ[F2] F) → ℝ) :
    linearCoeff f (0 : F →ₗ[F2] E) = 𝔼 X, f X := by
  simp [linearCoeff, linearTraceCharacter_zero]

theorem rankZero_energy (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankLevel 0 f X ^ 2) = (𝔼 X, f X) ^ 2 := by
  rw [rankLevel_energy]
  simp [Finset.sum_filter, frequencyRank_eq_zero_iff, linearCoeff_zero_frequency]

variable [Finite E] [Finite F]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in

theorem fullSecondMoment_le_of_global (f : (E →ₗ[F2] F) → ℝ) (r : Nat) (ρ : ℝ)
    (hg : IsRestrictionGlobal f r ρ) : (𝔼 X, f X ^ 2) ≤ ρ := by
  rw [← expect_unrestricted (fun X => f X ^ 2)]
  exact hg ⊥ ⊤ 0 (by rw [order_bot_top]; exact Nat.zero_le r)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem fullMean_le_of_boolean_global (f : (E →ₗ[F2] F) → ℝ) (r : Nat) (ρ : ℝ)
    (hf : IsBoolean f) (hg : IsRestrictionGlobal f r ρ) : (𝔼 X, f X) ≤ ρ := by
  rw [← boolean_squared_norm_eq_density hf]
  exact fullSecondMoment_le_of_global f r ρ hg

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem remainder_isRestrictionGlobal_of_le
    (H : (E →ₗ[F2] F) → Bool) (r d p q : Nat) (hq : 0 < q) (hdr : d ≤ r) :
    IsRestrictionGlobal
      (fun X => if Deletion.remainder (system r) H p q X then (1 : ℝ) else 0)
      d ((p : ℝ) / q) := by
  intro W C' X horder
  exact remainder_restriction_sq_expect H r p q hq W C' (horder.trans hdr) X

theorem rankCutoffEnergy_le_of_theorem23 (h23 : Theorem23 (E := E) (F := F))
    (f : (E →ₗ[F2] F) → ℝ) (r : Nat) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hf : IsBoolean f) (hg : IsRestrictionGlobal f r ρ) :
    rankCutoffEnergy r f ≤ levelCutoffConstant r ρ * (𝔼 X, f X ^ 2) := by
  let μ := 𝔼 X, f X ^ 2
  have hμ : 0 ≤ μ := Finset.expect_nonneg (fun X _ => sq_nonneg (f X))
  have hμρ : μ ≤ ρ := fullSecondMoment_le_of_global f r ρ hg
  have hzero : (𝔼 X, rankLevel 0 f X ^ 2) ≤ ρ * μ := by
    rw [rankZero_energy, ← boolean_squared_norm_eq_density hf, pow_two]
    exact mul_le_mul_of_nonneg_right hμρ hμ
  rw [rankCutoffEnergy_eq_sum_rankLevel]
  calc
    _ ≤ ∑ d ∈ Finset.range (r + 1),
        (if d = 0 then ρ else (2 : ℝ) ^ (30 * d * d) * ρ ^ ((1 : ℝ) / 4)) * μ := by
      apply Finset.sum_le_sum
      intro d hd
      by_cases hd0 : d = 0
      · subst d
        simpa using hzero
      · have hdr : d ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
        have hgd : IsRestrictionGlobal f d ρ := by
          intro A B T horder
          exact hg A B T (horder.trans hdr)
        have hdensity := (boolean_global_iff_density f hf d ρ).mp hgd
        have hpositive := h23 d (Nat.pos_of_ne_zero hd0) ρ hρ hρ1 f hf hdensity
        simpa only [ite_eq_right hd0] using hpositive
    _ = levelCutoffConstant r ρ * μ := by
      simp only [levelCutoffConstant, Finset.sum_mul]

theorem remainder_rankCutoff_le (h23 : Theorem23 (E := E) (F := F))
    (H : (E →ₗ[F2] F) → Bool) (r p q : Nat) (hq : 0 < q)
    (hρ : (0 : ℝ) < (p : ℝ) / q) (hρ1 : (p : ℝ) / q < 1) :
    (∑ S : F →ₗ[F2] E, if Module.finrank F2 (LinearMap.range S) ≤ r then
      linearCoeff (fun X => if Deletion.remainder (system r) H p q X
        then (1 : ℝ) else 0) S ^ 2 else 0) ≤
      levelCutoffConstant r ((p : ℝ) / q) *
        (𝔼 X, (if Deletion.remainder (system r) H p q X then (1 : ℝ) else 0) ^ 2) := by
  let f : (E →ₗ[F2] F) → ℝ :=
    fun X => if Deletion.remainder (system r) H p q X then (1 : ℝ) else 0
  have hf : IsBoolean f := by
    intro X
    dsimp only [f]
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hg : IsRestrictionGlobal f r ((p : ℝ) / q) :=
    remainder_isRestrictionGlobal_of_le H r r p q hq le_rfl
  rw [← Finset.sum_filter]
  exact rankCutoffEnergy_le_of_theorem23 h23 f r ((p : ℝ) / q) hρ hρ1 hf hg

end ActualLinearMaps

end UniqueGamesTheorem.Fourier.MatrixLevelBridge

end

end

end OAI
