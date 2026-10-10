import Mathlib
import OAI.Computability.MaxCut.Games.FinalParameters
import OAI.Computability.MaxCut.Games.FiniteFieldChoice

namespace OAI

noncomputable section

namespace MaxCutGames.Gadget.StageData

open scoped BigOperators Classical
open MaxCutGames.Gadget

variable {C : Type} [AddCommGroup C] [Module (ZMod 2) C]

/-- The normalized stage's actual data, with its original finite noise choices.
Passing the inclusion explicitly avoids dependent casts of the shift carrier. -/
def toData (s : Stage (ZMod 2) C) (embed : C →ₗ[ZMod 2] s.Input)
    (hinj : Function.Injective embed)
    (hEquiv : ∀ u c, s.output (u + embed c) = s.output u + c) : ActualGadget.Data C where
  Ambient := s.Input
  ambientFintype := Fintype.ofFinite s.Input
  embed := embed
  embed_injective := hinj
  f := s.output
  equivariant := hEquiv
  NoiseIndex := s.Noise
  noiseFintype := Fintype.ofFinite s.Noise
  noise := s.noise

/-- Intrinsic count probability and uniform finite expectation are identical. -/
theorem count_probability_eq_expect {Ω : Type*} [Fintype Ω] (p : Ω → Prop) :
    Enlargement.probability p = 𝔼 x : Ω, if p x then (1 : ℚ) else 0 := by
  classical
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Enlargement.probability, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem count_probability_eq_harmonic {Ω : Type*} [Fintype Ω] (p : Ω → Prop)
    [DecidablePred p] : Enlargement.probability p = Harmonic.probability p := by
  rw [count_probability_eq_expect]
  unfold Harmonic.probability Harmonic.average
  apply Finset.expect_congr rfl
  intro x _
  split_ifs <;> rfl

theorem stabilityError_toData (s : Stage (ZMod 2) C) (embed : C →ₗ[ZMod 2] s.Input)
    (hinj : Function.Injective embed)
    (hEquiv : ∀ u c, s.output (u + embed c) = s.output u + c) :
    ActualGadget.stabilityError (toData s embed hinj hEquiv) = StageNoiseRecurrence.error s := by
  classical
  let := Fintype.ofFinite s.Input
  let := Fintype.ofFinite s.Noise
  rw [StageNoiseRecurrence.error_eq_expect]
  unfold ActualGadget.stabilityError
  change (𝔼 t : s.Input × s.Noise,
    if s.output (t.1 + s.noise t.2) = s.output t.1 then (0 : ℚ) else 1) = _
  rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  simp only [ne_eq, ite_not]

theorem stabilityError_toData_count (s : Stage (ZMod 2) C)
    [Fintype s.Input] [Fintype s.Noise] (embed : C →ₗ[ZMod 2] s.Input)
    (hinj : Function.Injective embed)
    (hEquiv : ∀ u c, s.output (u + embed c) = s.output u + c) :
    ActualGadget.stabilityError (toData s embed hinj hEquiv) =
      Enlargement.probability (fun t : s.Input × s.Noise =>
        s.output (t.1 + s.noise t.2) ≠ s.output t.1) := by
  classical
  rw [stabilityError_toData, StageNoiseRecurrence.error_eq_expect,
    count_probability_eq_expect]
  rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro u _
  apply Finset.expect_congr rfl
  intro n _
  split_ifs <;> rfl

theorem error_eq_count_probability (s : Stage (ZMod 2) C)
    [Fintype s.Input] [Fintype s.Noise] :
    StageNoiseRecurrence.error s = Enlargement.probability
      (fun t : s.Input × s.Noise => s.output (t.1 + s.noise t.2) ≠ s.output t.1) := by
  classical
  rw [StageNoiseRecurrence.error_eq_expect, count_probability_eq_expect]
  rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro u _
  apply Finset.expect_congr rfl
  intro n _
  split_ifs <;> rfl

theorem kernelError_toData_count (s : Stage (ZMod 2) C) [Fintype s.Noise]
    (embed : C →ₗ[ZMod 2] s.Input) (hinj : Function.Injective embed)
    (hEquiv : ∀ u c, s.output (u + embed c) = s.output u + c)
    {E : Type} [AddCommGroup E] [Module (ZMod 2) E] (T : s.Input →ₗ[ZMod 2] E) :
    ActualGadget.kernelError (toData s embed hinj hEquiv) T =
      Enlargement.probability (fun n : s.Noise => T (s.noise n) = 0) := by
  classical
  rw [count_probability_eq_expect]
  change StageNoiseRecurrence.average (fun n : s.Noise =>
    if T (s.noise n) = 0 then (1 : ℚ) else 0) = _
  rw [StageNoiseRecurrence.average_eq_expect]

/-- The common interface's zero-image error is exactly the complement of
the v2 nonzero-image detection probability. -/
theorem kernelError_eq_one_sub_detection (s : Stage (ZMod 2) C) [Fintype s.Noise]
    (embed : C →ₗ[ZMod 2] s.Input) (hinj : Function.Injective embed)
    (hEquiv : ∀ u c, s.output (u + embed c) = s.output u + c)
    {E : Type} [AddCommGroup E] [Module (ZMod 2) E] (T : s.Input →ₗ[ZMod 2] E) :
    ActualGadget.kernelError (toData s embed hinj hEquiv) T =
      1 - Enlargement.probability (fun n : s.Noise => T (s.noise n) ≠ 0) := by
  classical
  rw [kernelError_toData_count, count_probability_eq_expect, count_probability_eq_expect]
  calc
    (𝔼 n : s.Noise, if T (s.noise n) = 0 then (1 : ℚ) else 0) =
        𝔼 n : s.Noise, (1 - if T (s.noise n) ≠ 0 then (1 : ℚ) else 0) := by
      apply Finset.expect_congr rfl
      intro n _
      by_cases hn : T (s.noise n) = 0 <;> simp [hn]
    _ = _ := by
      rw [Finset.expect_sub_distrib, Fintype.expect_const]
      apply congrArg (fun x : ℚ => 1 - x)
      apply Finset.expect_congr rfl
      intro n _
      split_ifs <;> rfl

theorem kernelError_le_of_detection (s : Stage (ZMod 2) C) [Fintype s.Noise]
    (embed : C →ₗ[ZMod 2] s.Input) (hinj : Function.Injective embed)
    (hEquiv : ∀ u c, s.output (u + embed c) = s.output u + c)
    {E : Type} [AddCommGroup E] [Module (ZMod 2) E] (T : s.Input →ₗ[ZMod 2] E)
    (d : ℚ) (hd : d ≤ Enlargement.probability (fun n : s.Noise => T (s.noise n) ≠ 0)) :
    ActualGadget.kernelError (toData s embed hinj hEquiv) T ≤ 1 - d := by
  rw [kernelError_eq_one_sub_detection]
  exact sub_le_sub_left hd 1

end MaxCutGames.Gadget.StageData

/-!
# Constant-detection enlargement endpoint

The finite base alphabet and its rank threshold are fixed before the target
logical space. The resulting actual gadget has the same nonlinear error and
linear kernel error at most `7/8`. Only the common data and experiment interface
is reused from the old gadget namespace.
-/

namespace MaxCutGames.Gadget.EnlargementEndpoint

open scoped Classical
open Enlargement EnlargementConstruction
open MaxCutGames.Gadget

variable {B K V N : Type}
variable [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
variable [FiniteDimensional (ZMod 2) B]
variable [AddCommGroup K] [Module (ZMod 2) K] [Fintype K]
variable [FiniteDimensional (ZMod 2) K]
variable [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable [Fintype N] [Nonempty N]

def data (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0) : ActualGadget.Data K :=
  let s := productStage i hi C hC noise hdim b₀ hb₀
  StageData.toData (StageQuotient.toStage s) (StageQuotient.shift s)
    (StageQuotient.shift_injective s) (StageQuotient.output_equivariant s)

/-- Base stability and base detection suffice for the complete enlarged
gadget. Its detection error is the fixed constant `7/8`, as required by v2. -/
theorem data_satisfies (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0) (p : ℚ)
    (hchange : probability (fun z : V × N => C (z.1 + noise z.2) ≠ C z.1) ≤ p)
    (hbase : ∀ (E : Type) [AddCommGroup E] [Module (ZMod 2) E]
      (U : V →ₗ[ZMod 2] E), Function.Injective (U.comp i) →
        1 / 4 ≤ probability (fun n : N => U (noise n) ≠ 0)) :
    ActualGadget.Satisfies (data i hi C hC noise hdim b₀ hb₀) p (7 / 8)
      (Module.finrank (ZMod 2) B + 2) := by
  let s := productStage i hi C hC noise hdim b₀ hb₀
  let q := StageQuotient.toStage s
  let : Fintype (StageQuotient.Space s) := Fintype.ofFinite _
  let : Fintype q.Input := Fintype.ofFinite _
  let : Fintype q.Noise := Fintype.ofFinite _
  constructor
  · change ActualGadget.stabilityError (StageData.toData q (StageQuotient.shift s)
      (StageQuotient.shift_injective s) (StageQuotient.output_equivariant s)) ≤ p
    have heq := StageData.stabilityError_toData_count q (StageQuotient.shift s)
      (StageQuotient.shift_injective s) (StageQuotient.output_equivariant s)
    have hc := change_probability i hi C hC noise hdim b₀ hb₀
    exact heq.le.trans (hc.le.trans hchange)
  · intro E _ _ T hr
    have hd := detection_probability i hi C hC noise hdim b₀ hb₀ (hbase E) T hr
    have he := StageData.kernelError_le_of_detection q (StageQuotient.shift s)
      (StageQuotient.shift_injective s) (StageQuotient.output_equivariant s) T (1 / 8) hd
    norm_num at he
    exact he

/-- For every permitted logical space there is an actual gadget. The rank
threshold `dim B + 2` and all base data are independent of that space. -/
theorem exists_data (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0) (p : ℚ)
    (hchange : probability (fun z : V × N => C (z.1 + noise z.2) ≠ C z.1) ≤ p)
    (hbase : ∀ (E : Type) [AddCommGroup E] [Module (ZMod 2) E]
      (U : V →ₗ[ZMod 2] E), Function.Injective (U.comp i) →
        1 / 4 ≤ probability (fun n : N => U (noise n) ≠ 0)) :
    ∃ g : ActualGadget.Data K,
      ActualGadget.Satisfies g p (7 / 8) (Module.finrank (ZMod 2) B + 2) :=
  ⟨data i hi C hC noise hdim b₀ hb₀,
    data_satisfies i hi C hC noise hdim b₀ hb₀ p hchange hbase⟩

end MaxCutGames.Gadget.EnlargementEndpoint
end

namespace MaxCutGames.Gadget

open Quadratic QuadraticStageNoise
open MaxCutGames.Integration.BinaryLinear
open scoped Classical

noncomputable section

/-- Actual finite gadget data, with a rank threshold independent of the final
logical dimension and an arbitrarily small nonlinear change probability. -/
theorem exists_actual_gadget (p : ℚ) (hp : 0 < p) :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ ℓ : ℕ, r ≤ ℓ →
      ∃ g : MaxCutGames.Gadget.ActualGadget.Data (Vector ℓ),
        MaxCutGames.Gadget.ActualGadget.Satisfies g p (7 / 8) r := by
  obtain ⟨d, _hd, n, herror, hdetect⟩ := BaseConstruction.exists_base p hp
  let B := Vec (BinaryField d)
  let s := quotientStage (F := BinaryField d) n
  let : Fintype B := Fintype.ofFinite _
  let : FiniteDimensional (ZMod 2) B := Module.Finite.of_finite
  let : Fintype s.Input := Fintype.ofFinite _
  let : Fintype s.Noise := Fintype.ofFinite _
  let i : B →ₗ[ZMod 2] s.Input := s.embed
  let r := Module.finrank (ZMod 2) B + 2
  refine ⟨r, by omega, ?_⟩
  intro ℓ hℓ
  have hdim : Module.finrank (ZMod 2) B ≤
      Module.finrank (ZMod 2) (Vector ℓ) := by
    rw [finrank_vector]
    omega
  let b₀ : B := fun _ => 1
  have hb₀ : b₀ ≠ 0 := by
    intro h
    have hzero := congrFun h (0 : Fin 3)
    exact one_ne_zero hzero
  have hequiv : ∀ u (b : B), s.output (u + i b) = s.output u + b := by
    intro u b
    exact s.equivariant u b
  have hc : Enlargement.probability (fun z : s.Input × s.Noise =>
      s.output (z.1 + s.noise z.2) ≠ s.output z.1) ≤ p := by
    rw [← StageData.error_eq_count_probability s]
    exact herror
  have hb : ∀ (E : Type) [AddCommGroup E] [Module (ZMod 2) E]
      (U : s.Input →ₗ[ZMod 2] E), Function.Injective (U.comp i) →
      (1 / 4 : ℚ) ≤ Enlargement.probability (fun t => U (s.noise t) ≠ 0) := by
    intro E _ _ U hU
    have h := hdetect E U hU
    rw [StageNoiseRecurrence.average_eq_expect] at h
    refine h.trans_eq ?_
    rw [StageData.count_probability_eq_expect]
    apply Finset.expect_congr rfl
    intro t _
    by_cases ht : U (s.noise t) = 0
    · simp only [s] at ht ⊢
      simp only [ht, ne_eq, not_true_eq_false, ite_false]
    · simp only [s] at ht ⊢
      simp only [ht, ne_eq, not_false_eq_true, ite_true]
  exact EnlargementEndpoint.exists_data (B := B) (K := Vector ℓ)
    i s.embed_injective s.output hequiv s.noise hdim b₀ hb₀ p hc hb

theorem exists_split_gadget (p : ℚ) (hp : 0 < p) :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ ℓ : ℕ, r ≤ ℓ →
      ∃ d : ℕ, ∃ g : MaxCutGames.Reduction.ActualSource.SplitGadget ℓ d,
        g.stabilityError ≤ p ∧
        ∀ (P : Type) [AddCommGroup P] [Module F2 P]
          (S : MaxCutGames.Reduction.ActualSource.Ambient ℓ d →ₗ[F2] P),
          r ≤ Module.finrank F2
            (S.comp (MaxCutGames.Reduction.ActualSource.alphabetEmbedding ℓ d)).range →
          MaxCutGames.Integration.SplitGadget.kernelProbability g S ≤ 7 / 8 := by
  obtain ⟨r, hr, hg⟩ := exists_actual_gadget p hp
  refine ⟨r, hr, ?_⟩
  intro ℓ hℓ
  obtain ⟨g, hgood⟩ := hg ℓ hℓ
  exact MaxCutGames.Integration.SplitGadget.exists_split_gadget_general g hgood

end

end MaxCutGames.Gadget

end OAI
