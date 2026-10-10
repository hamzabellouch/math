import Mathlib
import OAI.Computability.DirectedFeedback.Probability.PolynomialProbability
import OAI.Computability.DirectedFeedback.Probability.Enlargement

namespace OAI

noncomputable section

namespace DFVSGames.Gadget.StageData

open scoped BigOperators Classical
open DFVSGames.Gadget

variable {C : Type} [AddCommGroup C] [Module (ZMod 2) C]

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

end DFVSGames.Gadget.StageData
end

noncomputable section

namespace DFVSGames.Gadget.EnlargementEndpoint

open scoped Classical
open Enlargement EnlargementConstruction
open DFVSGames.Gadget

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

end DFVSGames.Gadget.EnlargementEndpoint
end

namespace DFVSGames.Gadget

open Quadratic QuadraticStageNoise
open DFVSGames.Integration.BinaryLinear
open scoped Classical

noncomputable section

theorem exists_actual_gadget (p : ℚ) (hp : 0 < p) :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ ℓ : ℕ, r ≤ ℓ →
      ∃ g : DFVSGames.Gadget.ActualGadget.Data (Vector ℓ),
        DFVSGames.Gadget.ActualGadget.Satisfies g p (7 / 8) r := by
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
      ∃ d : ℕ, ∃ g : DFVSGames.Reduction.ActualSource.SplitGadget ℓ d,
        g.stabilityError ≤ p ∧
        ∀ (P : Type) [AddCommGroup P] [Module F2 P]
          (S : DFVSGames.Reduction.ActualSource.Ambient ℓ d →ₗ[F2] P),
          r ≤ Module.finrank F2
            (S.comp (DFVSGames.Reduction.ActualSource.alphabetEmbedding ℓ d)).range →
          DFVSGames.Integration.SplitGadget.kernelProbability g S ≤ 7 / 8 := by
  obtain ⟨r, hr, hg⟩ := exists_actual_gadget p hp
  refine ⟨r, hr, ?_⟩
  intro ℓ hℓ
  obtain ⟨g, hgood⟩ := hg ℓ hℓ
  exact DFVSGames.Integration.SplitGadget.exists_split_gadget_general g hgood

end

end DFVSGames.Gadget

namespace DFVSGames.Decoder.MatrixGap

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open Integration

noncomputable section

theorem parameters_of_inverse (hinverse : Inverse.Shortcode.InversePrinciple)
    (p : ℚ) (hp : 0 < p) : Nonempty (Parameters p) := by
  obtain ⟨rstar, hrstar, hgadget⟩ := Gadget.exists_split_gadget p hp
  obtain ⟨P⟩ := MatrixGapChoice.exists_inverse_parameters hinverse rstar
  obtain ⟨d, g, hstable, hkernel⟩ := hgadget P.s P.s_large
  let en := NoiseEnumeration.ofFintype g
  let T := NoiseTables.Table.ofEnumeration g en
  let gT := T.gadget g.f g.equivariant
  have hstableT : gT.stabilityError ≤ p := by
    exact (NoiseTables.Table.stabilityError_ofEnumeration g en).trans_le hstable
  have hkernelT : ∀ (Q : Type) [AddCommGroup Q] [Module F2 Q]
      (L : Ambient P.s d →ₗ[F2] Q),
      rstar ≤ Module.finrank F2 (L.comp (alphabetEmbedding P.s d)).range →
        Integration.SplitGadget.kernelProbability gT L ≤ 7 / 8 := by
    intro Q _ _ L hL
    exact (NoiseTables.Table.kernelProbability_ofEnumeration g en L).trans_le (hkernel Q L hL)
  obtain ⟨m, hm, hlarge, hβ, hβ', htv, hrate⟩ := MatrixGapChoice.exists_cube P d
  refine ⟨{
    k := m ^ 3
    s := P.s
    d := d
    k_pos := Nat.succ_le_iff.mpr (pow_pos hm _)
    s_pos := hrstar.trans P.s_large
    T := T
    f := g.f
    equivariant := g.equivariant
    stability := hstableT
    sound := ?_ }⟩
  intro S hdistinct hopt
  apply address_value_le_of_semantic_acceptance S (m ^ 3) T g.f g.equivariant
  intro labeling
  apply le_of_lt
  by_contra hnot
  have haccept : (99 : ℚ) / 100 ≤ TableKeysGame.acceptanceProbability S (m ^ 3) gT labeling :=
    le_of_not_gt hnot
  have hgood := P.advice (m ^ 3) hlarge S d gT labeling
    (fun L hL => hkernelT (ActualHomogeneous.E (m ^ 3)) L hL) haccept
  exact ActualMatrixContradiction.contradiction S labeling P.α
    (ActualGoodRows.goodRowMass rstar P.s P.r) (1 / (m : ℝ) ^ 2)
    P.positive P.trivial_small hβ hβ' hgood htv hrate hdistinct hopt

end
end DFVSGames.Decoder.MatrixGap

namespace DFVSGames.Appendix.Restriction

def isum {α : Type} : List α → (α → Int) → Int
  | [], _ => 0
  | a :: as, f => f a + isum as f

theorem isum_congr {α : Type} (as : List α) (f g : α → Int)
    (h : ∀ a, f a = g a) : isum as f = isum as g := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [isum, h, ih]

theorem isum_zero {α : Type} (as : List α) : isum as (fun _ => 0) = 0 := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [isum, ih, Int.zero_add]

theorem isum_add {α : Type} (as : List α) (f g : α → Int) :
    isum as (fun a => f a + g a) = isum as f + isum as g := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [isum, ih]; omega

theorem isum_mul_left {α : Type} (as : List α) (c : Int) (f : α → Int) :
    isum as (fun a => c * f a) = c * isum as f := by
  induction as with
  | nil => simp only [isum, Int.mul_zero]
  | cons a as ih => simp only [isum, ih, Int.mul_add]

theorem isum_mul_right {α : Type} (as : List α) (f : α → Int) (c : Int) :
    isum as (fun a => f a * c) = isum as f * c := by
  induction as with
  | nil => simp only [isum, Int.zero_mul]
  | cons a as ih => simp only [isum, ih, Int.add_mul]

theorem isum_const {α : Type} (as : List α) (c : Int) :
    isum as (fun _ => c) = (as.length : Int) * c := by
  induction as with
  | nil => simp only [isum, List.length_nil, Int.natCast_zero, Int.zero_mul]
  | cons a as ih =>
    simp only [isum, ih, List.length_cons, Int.natCast_add, Int.natCast_one,
      Int.add_mul, Int.one_mul]
    omega

theorem isum_swap {α β : Type} (as : List α) (bs : List β) (f : α → β → Int) :
    isum as (fun a => isum bs (f a)) = isum bs (fun b => isum as (fun a => f a b)) := by
  induction as with
  | nil => simp only [isum, isum_zero]
  | cons a as ih => simp only [isum, isum_add, ih]

theorem isum_map {α β : Type} (as : List α) (g : α → β) (f : β → Int) :
    isum (as.map g) f = isum as (fun a => f (g a)) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, isum, ih]

theorem isum_perm {α : Type} {as bs : List α} (h : as.Perm bs) (f : α → Int) :
    isum as f = isum bs f := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [isum, ih]
  | swap a b as => simp only [isum]; omega
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

def binarySign (b : Bool) : Int := if b then -1 else 1

theorem binarySign_xor (a b : Bool) :
    binarySign (a.xor b) = binarySign a * binarySign b := by
  cases a <;> cases b <;> decide

theorem binary_character_restriction {M N Y Z : Type}
    (translate : M → N → M) (compress : Y → Z)
    (ambientPair : Y → M → Bool) (restrictedPair : Z → N → Bool)
    (traceCompatibility : ∀ y t n,
      ambientPair y (translate t n) = (ambientPair y t).xor (restrictedPair (compress y) n))
    (y : Y) (t : M) (n : N) :
    binarySign (ambientPair y (translate t n)) =
      binarySign (ambientPair y t) * binarySign (restrictedPair (compress y) n) := by
  rw [traceCompatibility, binarySign_xor]

theorem coefficient_merging {M N Y Z : Type} [DecidableEq Z]
    (ys : List Y) (ns : List N) (translate : M → N → M) (compress : Y → Z)
    (ambient : Y → M → Int) (restricted : Z → N → Int) (coeff : Y → Int)
    (compatibility : ∀ y t n,
      ambient y (translate t n) = ambient y t * restricted (compress y) n)
    (orthogonality : ∀ y z,
      isum ns (fun n => restricted (compress y) n * restricted z n) =
        if compress y = z then (ns.length : Int) else 0)
    (t : M) (z : Z) :
    isum ns (fun n =>
      isum ys (fun y => coeff y * ambient y (translate t n)) * restricted z n) =
    (ns.length : Int) *
      isum ys (fun y => if compress y = z then coeff y * ambient y t else 0) := by
  calc
    _ = isum ns (fun n => isum ys (fun y =>
        (coeff y * ambient y t) *
          (restricted (compress y) n * restricted z n))) := by
      apply isum_congr
      intro n
      rw [← isum_mul_right]
      apply isum_congr
      intro y
      rw [compatibility]
      simp only [Int.mul_assoc]
    _ = isum ys (fun y => isum ns (fun n =>
        (coeff y * ambient y t) *
          (restricted (compress y) n * restricted z n))) := isum_swap ns ys _
    _ = isum ys (fun y => (coeff y * ambient y t) *
        (if compress y = z then (ns.length : Int) else 0)) := by
      apply isum_congr
      intro y
      rw [isum_mul_left, orthogonality]
    _ = isum ys (fun y => (ns.length : Int) *
        (if compress y = z then coeff y * ambient y t else 0)) := by
      apply isum_congr
      intro y
      split <;> simp_all only [Int.mul_comm, Int.mul_zero]
    _ = _ := isum_mul_left ys _ _

theorem restriction_average {M N : Type}
    (ms : List M) (ns : List N) (translate : M → N → M)
    (translationPermutes : ∀ n, (ms.map (fun t => translate t n)).Perm ms)
    (observable : M → Int) :
    isum ms (fun t => isum ns (fun n => observable (translate t n))) =
      (ns.length : Int) * isum ms observable := by
  rw [isum_swap]
  calc
    _ = isum ns (fun _ => isum ms observable) := by
      apply isum_congr
      intro n
      rw [← isum_map]
      exact isum_perm (translationPermutes n) observable
    _ = _ := isum_const ns _

theorem bool_translation_perm (n : Bool) :
    ([false, true].map (fun t => t.xor n)).Perm [false, true] := by
  cases n
  · exact List.Perm.refl _
  · exact List.Perm.swap false true []

theorem bool_restriction_average (ns : List Bool) (observable : Bool → Int) :
    isum [false, true] (fun t => isum ns (fun n => observable (t.xor n))) =
      (ns.length : Int) * isum [false, true] observable :=
  restriction_average [false, true] ns Bool.xor bool_translation_perm observable

theorem bool_character_compatibility (y t n : Bool) :
    binarySign (y && (t.xor n)) = binarySign (y && t) * binarySign (y && n) := by
  cases y <;> cases t <;> cases n <;> decide

theorem bool_character_orthogonality (y z : Bool) :
    isum [false, true] (fun n => binarySign (y && n) * binarySign (z && n)) =
      if y = z then (2 : Int) else 0 := by
  cases y <;> cases z <;> decide

theorem bool_coefficient_merging (coeff : Bool → Int) (t z : Bool) :
    isum [false, true] (fun n =>
      isum [false, true] (fun y => coeff y * binarySign (y && (t.xor n))) *
        binarySign (z && n)) =
      2 * (coeff z * binarySign (z && t)) := by
  have h := coefficient_merging [false, true] [false, true] Bool.xor id
    (fun y t => binarySign (y && t)) (fun y n => binarySign (y && n))
    coeff bool_character_compatibility bool_character_orthogonality t z
  cases z <;> simpa [isum] using h

end DFVSGames.Appendix.Restriction

noncomputable section

namespace DFVSGames.Appendix.Restriction

open scoped BigOperators
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier
attribute [local instance] Classical.propDecidable

theorem real_translation_average {G N : Type*} [AddCommGroup G] [Fintype G]
    [Fintype N] [Nonempty N] (embed : N → G) (observable : G → ℝ) :
    (𝔼 t, 𝔼 n, observable (t + embed n)) = 𝔼 t, observable t := by
  rw [Finset.expect_comm]
  calc
    _ = 𝔼 _n : N, 𝔼 t, observable t := by
      apply Finset.expect_congr rfl
      intro n _
      exact Fintype.expect_equiv (Equiv.addRight (embed n)) _ _ (fun _ => rfl)
    _ = _ := Finset.expect_const Finset.univ_nonempty _

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

def compressFrequency (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) : B →ₗ[F2] (E ⧸ A) :=
  A.mkQ.comp (Y.comp B.subtype)

omit [FiniteDimensional F2 E] in

theorem linear_trace_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (N : DFVSGames.Fourier.MatrixRestrictions.Parameter A B) :
    linearTracePair (DFVSGames.Fourier.MatrixRestrictions.embed A B N) Y =
      linearTracePair N (compressFrequency A B Y) := by
  unfold linearTracePair DFVSGames.Fourier.MatrixRestrictions.embed compressFrequency
  simp only [LinearMap.comp_assoc]
  rw [LinearMap.trace_comp_comm']
  simp only [LinearMap.comp_assoc]

omit [FiniteDimensional F2 E] in

theorem linear_character_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (T : E →ₗ[F2] F)
    (N : DFVSGames.Fourier.MatrixRestrictions.Parameter A B) :
    linearTraceCharacter Y (T + DFVSGames.Fourier.MatrixRestrictions.embed A B N) =
      linearTraceCharacter Y T * linearTraceCharacter (compressFrequency A B Y) N := by
  simp only [linearTraceCharacter_apply, linearTracePair_add_left,
    linear_trace_restriction, DFVSGames.Fourier.MatrixCharacters.binarySign_add]

omit [FiniteDimensional F2 E] in
theorem real_character_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (T : E →ₗ[F2] F)
    (N : DFVSGames.Fourier.MatrixRestrictions.Parameter A B) :
    (linearTraceCharacter Y (T + DFVSGames.Fourier.MatrixRestrictions.embed A B N)).re =
      (linearTraceCharacter Y T).re * (linearTraceCharacter (compressFrequency A B Y) N).re := by
  rw [linear_character_restriction, Complex.mul_re]
  simp only [linearTraceCharacter_apply,
    DFVSGames.Fourier.MatrixCharacters.binarySign_im, mul_zero, sub_zero]

variable [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in

theorem linear_restriction_average (A : Submodule F2 E) (B : Submodule F2 F)
    (h : (E →ₗ[F2] F) → ℝ) :
    (𝔼 T, 𝔼 N, DFVSGames.Fourier.MatrixRestrictions.restrict h A B T N) = 𝔼 T, h T :=
  real_translation_average (DFVSGames.Fourier.MatrixRestrictions.embed A B) h

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in

theorem linear_restriction_moment_average (A : Submodule F2 E) (B : Submodule F2 F)
    (h : (E →ₗ[F2] F) → ℝ) (p : ℝ) :
    (𝔼 T, 𝔼 N, |DFVSGames.Fourier.MatrixRestrictions.restrict h A B T N| ^ p) =
      𝔼 T, |h T| ^ p :=
  real_translation_average (DFVSGames.Fourier.MatrixRestrictions.embed A B)
    (fun T => |h T| ^ p)

variable [Fintype (F →ₗ[F2] E)]

theorem linear_coefficient_merging (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) (Z : B →ₗ[F2] (E ⧸ A)) :
    linearCoeff (DFVSGames.Fourier.MatrixRestrictions.restrict f A B T) Z =
      ∑ Y : F →ₗ[F2] E,
        if compressFrequency A B Y = Z then linearCoeff f Y * (linearTraceCharacter Y T).re
        else 0 := by
  classical
  have hexpansion : DFVSGames.Fourier.MatrixRestrictions.restrict f A B T =
      ∑ Y : F →ₗ[F2] E,
        (linearCoeff f Y * (linearTraceCharacter Y T).re) •
          (fun N => (linearTraceCharacter (compressFrequency A B Y) N).re) := by
    funext N
    change f (T + DFVSGames.Fourier.MatrixRestrictions.embed A B N) = _
    rw [← linear_fourier_inversion f (T + DFVSGames.Fourier.MatrixRestrictions.embed A B N)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro Y _
    rw [real_character_restriction]
    ring
  rw [hexpansion, linearCoeff_sum]
  apply Finset.sum_congr rfl
  intro Y _
  rw [linearCoeff_smul, linearCoeff_character]
  by_cases h : compressFrequency A B Y = Z
  · simp [h]
  · simp [h, Ne.symm h]

end DFVSGames.Appendix.Restriction
end

namespace DFVSGames.Appendix.Level

def rankFilter (d r : Nat) (selected : Bool) : Rat :=
  if selected then 1 else
    (((2 : Rat) ^ r - 2 ^ d) * (2 ^ r - 2 ^ (d - 1))) / ((2 : Rat) ^ r) ^ 2

theorem filter_polynomial_algebra (q x y : Rat) (hq : q ≠ 0) :
    (q - x) * (q - y) / q ^ 2 = 1 - (x + y) / q + x * y / q ^ 2 := by
  grind

theorem rankFilter_selected (d r : Nat) : rankFilter d r true = 1 := by
  simp [rankFilter]

theorem rankFilter_zero_at_d (d : Nat) : rankFilter d d false = 0 := by
  simp only [rankFilter, Bool.false_eq_true, ↓reduceIte]
  grind

theorem rankFilter_zero_at_pred (d : Nat) : rankFilter d (d - 1) false = 0 := by
  simp only [rankFilter, Bool.false_eq_true, ↓reduceIte]
  grind

theorem only_two_source_ranks {d r s : Nat} (hd : 1 ≤ d)
    (hlo : s ≤ r) (hhi : r ≤ s + 1) (hs : s + 1 = d) :
    r = d ∨ r = d - 1 := by
  omega

theorem rank_filter_character {d r s : Nat} (hd : 1 ≤ d)
    (selected : Bool) (c : Rat)
    (hlo : s ≤ r) (hhi : r ≤ s + 1)
    (hselected : selected = true → r = s + 1) :
    (if selected then if r = d then c else 0 else 0) =
      (if s + 1 = d then rankFilter d r selected * c else 0) := by
  cases selected with
  | true =>
    have hr := hselected rfl
    simp [rankFilter, hr]
  | false =>
    by_cases hs : s + 1 = d
    · have hr := only_two_source_ranks hd hlo hhi hs
      rcases hr with hr | hr
      · simp [hs, hr, rankFilter_zero_at_d]
      · simp [hs, hr, rankFilter_zero_at_pred]
    · simp [hs]

def mergedCoefficient {α : Type} (indices : List α)
    (phase coefficient : α → Rat) : Rat :=
  (indices.map (fun x => phase x * coefficient x)).sum

theorem rank_filter_commutes_with_merge {α : Type} (indices : List α)
    (d : Nat) (hd : 1 ≤ d) (rank restrictedRank : α → Nat)
    (selected : α → Bool) (phase coefficient : α → Rat)
    (hlo : ∀ x, restrictedRank x ≤ rank x)
    (hhi : ∀ x, rank x ≤ restrictedRank x + 1)
    (hselected : ∀ x, selected x = true → rank x = restrictedRank x + 1) :
    mergedCoefficient indices phase
        (fun x => if selected x then if rank x = d then coefficient x else 0 else 0) =
      mergedCoefficient indices phase
        (fun x => if restrictedRank x + 1 = d
          then rankFilter d (rank x) (selected x) * coefficient x else 0) := by
  unfold mergedCoefficient
  congr 1
  apply List.map_congr_left
  intro x _
  exact congrArg (fun c : Rat => phase x * c)
    (rank_filter_character hd (selected x) (coefficient x) (hlo x) (hhi x)
      (hselected x))

theorem higher_ranks_cannot_contaminate {d r s : Nat}
    (hhi : r ≤ s + 1) (hr : d < r) : s + 1 ≠ d := by
  omega

theorem iterated_globality_exponent {d k : Nat} (hd : 1 ≤ d) (hk : k ≤ d) :
    2 * k + 4 * k * d - 2 * k * (k - 1) ≤ 10 * d * d := by
  have hkd : k * d ≤ d * d := Nat.mul_le_mul_right d hk
  have hdd : d ≤ d * d := by
    have := Nat.mul_le_mul_left d hd
    simpa using this
  have hbasic : 2 * k + 4 * k * d ≤ 6 * d * d := by
    grind
  grind

theorem successor_le_two_pow (d : Nat) : d + 1 ≤ 2 ^ d := by
  induction d with
  | zero => decide
  | succ d ih =>
    rw [Nat.pow_succ]
    omega

theorem selector_multiplicity_bound {d count : Nat} (hd : 1 ≤ d)
    (hcount : count ≤ (d + 1) ^ 2 * 2 ^ (d * d)) :
    count ≤ 2 ^ (3 * d * d) := by
  have hs := Nat.pow_le_pow_left (successor_le_two_pow d) 2
  have hdd : d ≤ d * d := by
    have := Nat.mul_le_mul_left d hd
    simpa using this
  calc
    count ≤ (d + 1) ^ 2 * 2 ^ (d * d) := hcount
    _ ≤ (2 ^ d) ^ 2 * 2 ^ (d * d) := Nat.mul_le_mul_right _ hs
    _ = 2 ^ (d * 2 + d * d) := by rw [← Nat.pow_mul, ← Nat.pow_add]
    _ ≤ 2 ^ (3 * d * d) := Nat.pow_le_pow_right (by decide) (by grind)

theorem final_exponent_slack (d : Nat) : 113 * d * d ≤ 4 * (30 * d * d) := by
  grind

end DFVSGames.Appendix.Level

namespace DFVSGames.Appendix.Level.LinearRank

open Module LinearMap
attribute [local instance] Classical.propDecidable

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V] [FiniteDimensional K W] [FiniteDimensional K V]

def compress (A : Submodule K V) (B : Submodule K W) (Y : W →ₗ[K] V) :
    B →ₗ[K] V ⧸ A := A.mkQ.comp (Y.comp B.subtype)

theorem finrank_comap_subtype_le (A B : Submodule K V) :
    finrank K (A.comap B.subtype) ≤ finrank K A := by
  rw [← Submodule.finrank_map_subtype_eq B (A.comap B.subtype),
    Submodule.map_comap_subtype]
  exact Submodule.finrank_mono inf_le_right

theorem quotient_rank_bounds (A : Submodule K V) (Y : W →ₗ[K] V) :
    finrank K (range (A.mkQ.comp Y)) ≤ finrank K (range Y) ∧
      finrank K (range Y) ≤ finrank K (range (A.mkQ.comp Y)) + finrank K A := by
  have h := (A.mkQ.comp (range Y).subtype).finrank_range_add_finrank_ker
  have hr : range (A.mkQ.comp (range Y).subtype) = range (A.mkQ.comp Y) := by
    simp only [range_comp, Submodule.range_subtype]
  rw [hr, ker_comp, Submodule.ker_mkQ] at h
  have hk := finrank_comap_subtype_le A (range Y)
  omega

omit [FiniteDimensional K V] in
theorem quotient_rank_selected (A : Submodule K V) (Y : W →ₗ[K] V)
    (hA : A ≤ range Y) :
    finrank K (range (A.mkQ.comp Y)) + finrank K A = finrank K (range Y) := by
  have h := (A.mkQ.comp (range Y).subtype).finrank_range_add_finrank_ker
  have hr : range (A.mkQ.comp (range Y).subtype) = range (A.mkQ.comp Y) := by
    simp only [range_comp, Submodule.range_subtype]
  rw [hr, ker_comp, Submodule.ker_mkQ,
    (Submodule.comapSubtypeEquivOfLe hA).finrank_eq] at h
  exact h

omit [FiniteDimensional K V] in
theorem domain_rank_bounds (B : Submodule K W) (Y : W →ₗ[K] V) :
    finrank K (range (Y.comp B.subtype)) ≤ finrank K (range Y) ∧
      finrank K (range Y) ≤
        finrank K (range (Y.comp B.subtype)) + finrank K (W ⧸ B) := by
  have h₁ := (Y.comp B.subtype).finrank_range_add_finrank_ker
  have h₂ := Y.finrank_range_add_finrank_ker
  have h₃ := B.finrank_quotient_add_finrank
  rw [ker_comp] at h₁
  have hk := finrank_comap_subtype_le (ker Y) B
  have hr : finrank K (range (Y.comp B.subtype)) ≤ finrank K (range Y) := by
    apply Submodule.finrank_mono
    exact LinearMap.range_comp_le_range _ _
  omega

omit [FiniteDimensional K V] in
theorem domain_rank_selected (B : Submodule K W) (Y : W →ₗ[K] V)
    (hB : ker Y ≤ B) :
    finrank K (range (Y.comp B.subtype)) + finrank K (W ⧸ B) =
      finrank K (range Y) := by
  have h₁ := (Y.comp B.subtype).finrank_range_add_finrank_ker
  have h₂ := Y.finrank_range_add_finrank_ker
  have h₃ := B.finrank_quotient_add_finrank
  rw [ker_comp, (Submodule.comapSubtypeEquivOfLe hB).finrank_eq] at h₁
  omega

omit [FiniteDimensional K V] in

theorem hybrid_rank_loss (A : Submodule K V) (B : Submodule K W)
    (Y : W →ₗ[K] V) (hA : A ≤ range Y) (hB : A.comap Y ≤ B) :
    finrank K (range (compress A B Y)) + finrank K A + finrank K (W ⧸ B) =
      finrank K (range Y) := by
  have hquot := quotient_rank_selected A Y hA
  have hdom := domain_rank_selected B (A.mkQ.comp Y) (by
    simpa only [ker_comp, Submodule.ker_mkQ] using hB)
  have hc : (A.mkQ.comp Y).comp B.subtype = compress A B Y := rfl
  rw [hc] at hdom
  omega

theorem finrank_comap_subtype_eq_iff (A B : Submodule K V) :
    finrank K (A.comap B.subtype) = finrank K A ↔ A ≤ B := by
  constructor
  · intro h
    have hdim := Submodule.finrank_map_subtype_eq B (A.comap B.subtype)
    rw [Submodule.map_comap_subtype, h] at hdim
    have heq : B ⊓ A = A := Submodule.eq_of_le_of_finrank_eq inf_le_right hdim
    calc
      A = B ⊓ A := heq.symm
      _ ≤ B := inf_le_left
  · intro h
    exact (Submodule.comapSubtypeEquivOfLe h).finrank_eq

theorem quotient_rank_equality_iff (A : Submodule K V) (Y : W →ₗ[K] V) :
    finrank K (range (A.mkQ.comp Y)) + finrank K A = finrank K (range Y) ↔
      A ≤ range Y := by
  constructor
  · intro heq
    have hn := (A.mkQ.comp (range Y).subtype).finrank_range_add_finrank_ker
    have hr : range (A.mkQ.comp (range Y).subtype) = range (A.mkQ.comp Y) := by
      simp only [range_comp, Submodule.range_subtype]
    rw [hr, ker_comp, Submodule.ker_mkQ] at hn
    apply (finrank_comap_subtype_eq_iff A (range Y)).mp
    omega
  · exact quotient_rank_selected A Y

omit [FiniteDimensional K V] in
theorem domain_rank_equality_iff (B : Submodule K W) (Y : W →ₗ[K] V) :
    finrank K (range (Y.comp B.subtype)) + finrank K (W ⧸ B) =
      finrank K (range Y) ↔ ker Y ≤ B := by
  constructor
  · intro heq
    have h₁ := (Y.comp B.subtype).finrank_range_add_finrank_ker
    have h₂ := Y.finrank_range_add_finrank_ker
    have h₃ := B.finrank_quotient_add_finrank
    rw [ker_comp] at h₁
    apply (finrank_comap_subtype_eq_iff (ker Y) B).mp
    omega
  · exact domain_rank_selected B Y

theorem compression_rank_bounds (A : Submodule K V) (B : Submodule K W)
    (Y : W →ₗ[K] V) :
    finrank K (range (compress A B Y)) ≤ finrank K (range Y) ∧
      finrank K (range Y) ≤
        finrank K (range (compress A B Y)) + finrank K A + finrank K (W ⧸ B) := by
  have hq := quotient_rank_bounds A Y
  have hd := domain_rank_bounds B (A.mkQ.comp Y)
  have hc : (A.mkQ.comp Y).comp B.subtype = compress A B Y := rfl
  rw [hc] at hd
  omega

theorem hybrid_rank_loss_iff (A : Submodule K V) (B : Submodule K W)
    (Y : W →ₗ[K] V) :
    finrank K (range (compress A B Y)) + finrank K A + finrank K (W ⧸ B) =
      finrank K (range Y) ↔ A ≤ range Y ∧ A.comap Y ≤ B := by
  constructor
  · intro heq
    have hq := quotient_rank_bounds A Y
    have hd := domain_rank_bounds B (A.mkQ.comp Y)
    have hc : (A.mkQ.comp Y).comp B.subtype = compress A B Y := rfl
    rw [hc] at hd
    constructor
    · apply (quotient_rank_equality_iff A Y).mp
      omega
    · have he : finrank K (range ((A.mkQ.comp Y).comp B.subtype)) +
          finrank K (W ⧸ B) = finrank K (range (A.mkQ.comp Y)) := by
        rw [hc]
        omega
      have hk := (domain_rank_equality_iff B (A.mkQ.comp Y)).mp he
      simpa only [ker_comp, Submodule.ker_mkQ] using hk
  · rintro ⟨hA, hB⟩
    exact hybrid_rank_loss A B Y hA hB

theorem line_rank_filter (A : Submodule K V) (Y : W →ₗ[K] V)
    (hline : finrank K A = 1) (d : Nat) (hd : 1 ≤ d) (c : Rat) :
    (if A ≤ range Y then
      if finrank K (range Y) = d then c else 0 else 0) =
      (if finrank K (range (A.mkQ.comp Y)) + 1 = d then
        DFVSGames.Appendix.Level.rankFilter d (finrank K (range Y))
          (decide (A ≤ range Y)) * c else 0) := by
  classical
  have hb := quotient_rank_bounds A Y
  have hhi : finrank K (range Y) ≤ finrank K (range (A.mkQ.comp Y)) + 1 := by
    simpa only [hline] using hb.2
  have hs : decide (A ≤ range Y) = true →
      finrank K (range Y) = finrank K (range (A.mkQ.comp Y)) + 1 := by
    intro h
    have hl := quotient_rank_selected A Y (of_decide_eq_true h)
    omega
  simpa only [decide_eq_true_eq] using
    DFVSGames.Appendix.Level.rank_filter_character hd (decide (A ≤ range Y)) c hb.1 hhi hs

omit [FiniteDimensional K V] in

theorem hyperplane_rank_filter (B : Submodule K W) (Y : W →ₗ[K] V)
    (hhyperplane : finrank K (W ⧸ B) = 1) (d : Nat) (hd : 1 ≤ d) (c : Rat) :
    (if ker Y ≤ B then
      if finrank K (range Y) = d then c else 0 else 0) =
      (if finrank K (range (Y.comp B.subtype)) + 1 = d then
        DFVSGames.Appendix.Level.rankFilter d (finrank K (range Y))
          (decide (ker Y ≤ B)) * c else 0) := by
  classical
  have hb := domain_rank_bounds B Y
  have hhi : finrank K (range Y) ≤ finrank K (range (Y.comp B.subtype)) + 1 := by
    simpa only [hhyperplane] using hb.2
  have hs : decide (ker Y ≤ B) = true →
      finrank K (range Y) = finrank K (range (Y.comp B.subtype)) + 1 := by
    intro h
    have hl := domain_rank_selected B Y (of_decide_eq_true h)
    omega
  simpa only [decide_eq_true_eq] using
    DFVSGames.Appendix.Level.rank_filter_character hd (decide (ker Y ≤ B)) c hb.1 hhi hs

end DFVSGames.Appendix.Level.LinearRank

end OAI
