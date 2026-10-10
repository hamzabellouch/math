import Mathlib
import OAI.Computability.DirectedFeedback.Games.ActualAdviceStochasticBridge

namespace OAI

namespace DFVSGames.Integration.FinalParameters

open DFVSGames.Soundness.RepetitionUpper

def rho (r s : Nat) : ℚ := (1 / 2 : ℚ) ^ (s - (r + 1))
def levelConstant (r : Nat) : ℚ := (r + 1 : ℚ) * 2 ^ (30 * r ^ 2)
def alpha (δ : ℚ) (s : Nat) : ℚ := δ / (8 * (2 : ℚ) ^ s * 2 ^ (s ^ 2))
def beta (r s : Nat) : ℚ := rho r s / 2 * (1 / 2 : ℚ) ^ (r * s)
def theta (δ : ℚ) (r s : Nat) : ℚ := alpha δ s * beta r s
def repetitionRate : ℚ := 1 - 1 / (100000 * 192 ^ 3)

theorem levelConstant_pos (r : Nat) : 0 < levelConstant r := by
  unfold levelConstant
  positivity

theorem rho_pos (r s : Nat) : 0 < rho r s := by
  unfold rho
  positivity

theorem theta_pos {δ : ℚ} (hδ : 0 < δ) (r s : Nat) : 0 < theta δ r s := by
  unfold theta alpha beta
  have := rho_pos r s
  positivity

theorem repetitionRate_bounds : 0 ≤ repetitionRate ∧ repetitionRate < 1 := by
  norm_num [repetitionRate]

theorem exists_symbol_dimension (r : Nat) {δ : ℚ} (hδ : 0 < δ) :
    ∃ s : Nat, r + 1 < s ∧ ∃ u : ℚ,
      0 < u ∧ u ^ 4 = rho r s ∧ levelConstant r * u ≤ δ / 8 := by
  have hA := levelConstant_pos r
  have ht : 0 < δ / (8 * levelConstant r) := by positivity
  obtain ⟨n, hn, hsmall⟩ := exists_power_lt (1 / 2 : ℚ)
    (δ / (8 * levelConstant r)) (by norm_num) (by norm_num) ht
  refine ⟨r + 1 + 4 * n, by omega, (1 / 2 : ℚ) ^ n, by positivity, ?_, ?_⟩
  · unfold rho
    rw [Nat.add_sub_cancel_left, ← pow_mul]
    congr 1
    omega
  · have hbound : (1 / 2 : ℚ) ^ n * (8 * levelConstant r) < δ :=
      (lt_div_iff₀ (by positivity)).mp hsmall
    linarith

theorem exists_repetition_and_dimension (L q : Nat) {θ : ℚ}
    (hθ : 0 < θ) (hq : 0 < q) :
    ∃ t k : Nat, 0 < t ∧ t ≤ k ∧
      (1 - zeroProbability L * (1 - repetitionRate)) ^ t < decoderThreshold θ q ∧
      16 * (t : ℚ) ^ 2 * 2 ^ (t * L) ≤ (k : ℚ) * θ ^ 2 := by
  obtain ⟨t, ht, hrep⟩ := exists_repetition_length L q repetitionRate θ
    repetitionRate_bounds.1 repetitionRate_bounds.2 hθ hq
  let B : ℚ := 16 * (t : ℚ) ^ 2 * 2 ^ (t * L)
  obtain ⟨n, hn, hlarge⟩ := exists_pos_nat_gt (B / θ ^ 2)
  refine ⟨t, t + n, ht, by omega, hrep, ?_⟩
  have hnlarge : B < (n : ℚ) * θ ^ 2 :=
    (div_lt_iff₀ (by positivity)).mp hlarge
  have ht0 : 0 ≤ (t : ℚ) * θ ^ 2 := by positivity
  dsimp [B] at hnlarge
  simp only [Nat.cast_add]
  nlinarith

def gamma (ε : ℚ) (k : Nat) : ℚ := ε / (4 * (k : ℚ))

theorem gamma_bounds {ε : ℚ} {k : Nat}
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) (hk : 0 < k) :
    0 < gamma ε k ∧ gamma ε k < 1 / 8 := by
  have hk1 : (1 : ℚ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  unfold gamma
  constructor
  · positivity
  · apply (div_lt_iff₀ (by positivity)).2
    linarith

theorem exists_source_error {γ : ℚ} (hγ : 0 < γ) :
    ∃ n : Nat, 0 < n ∧ 0 < (1 / 2 : ℚ) ^ n ∧
      (1 / 2 : ℚ) ^ n ≤ 1 / 16 ∧ (1 / 2 : ℚ) ^ n ≤ γ / 4 := by
  have hm : 0 < min (1 / 16 : ℚ) (γ / 4) := by positivity
  obtain ⟨n, hn, hs⟩ := exists_power_lt (1 / 2 : ℚ)
    (min (1 / 16 : ℚ) (γ / 4)) (by norm_num) (by norm_num) hm
  exact ⟨n, hn, by positivity, le_of_lt (lt_min_iff.mp hs).1,
    le_of_lt (lt_min_iff.mp hs).2⟩

theorem exists_parameters (r : Nat) {ε δ : ℚ}
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) (hδ : 0 < δ) :
    ∃ s : Nat, r + 1 < s ∧ ∃ u : ℚ,
      0 < u ∧ u ^ 4 = rho r s ∧ levelConstant r * u ≤ δ / 8 ∧
      ∀ L : Nat, ∃ t k n : Nat,
        0 < t ∧ t ≤ k ∧
        (1 - zeroProbability L * (1 - repetitionRate)) ^ t <
          decoderThreshold (theta δ r s) (2 ^ s) ∧
        16 * (t : ℚ) ^ 2 * 2 ^ (t * L) ≤ (k : ℚ) * (theta δ r s) ^ 2 ∧
        0 < gamma ε k ∧ gamma ε k < 1 / 8 ∧
        0 < n ∧ 0 < (1 / 2 : ℚ) ^ n ∧
        (1 / 2 : ℚ) ^ n ≤ 1 / 16 ∧
        (1 / 2 : ℚ) ^ n ≤ gamma ε k / 4 := by
  obtain ⟨s, hs, u, hu, hroot, hlevel⟩ := exists_symbol_dimension r hδ
  refine ⟨s, hs, u, hu, hroot, hlevel, ?_⟩
  intro L
  obtain ⟨t, k, ht, htk, hrep, hcomp⟩ :=
    exists_repetition_and_dimension L (2 ^ s) (theta_pos hδ r s) (by positivity)
  have hk : 0 < k := lt_of_lt_of_le ht htk
  have hγ := gamma_bounds hε hεhalf hk
  obtain ⟨n, hn, hξ, hξ16, hξγ⟩ := exists_source_error hγ.1
  exact ⟨t, k, n, ht, htk, hrep, hcomp, hγ.1, hγ.2, hn, hξ, hξ16, hξγ⟩

theorem completeness_budget {ε : ℚ} {k : Nat} (hk : 0 < k) :
    (k : ℚ) * gamma ε k + (ε / 2) / 2 = ε / 2 := by
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  unfold gamma
  field_simp
  ring

end DFVSGames.Integration.FinalParameters

namespace DFVSGames.Gadget.ActualGadget

abbrev F2 := ZMod 2

structure Data (C : Type) [AddCommGroup C] [Module F2 C] where
  Ambient : Type
  [ambientAddCommGroup : AddCommGroup Ambient]
  [ambientModule : Module F2 Ambient]
  [ambientFintype : Fintype Ambient]
  embed : C →ₗ[F2] Ambient
  embed_injective : Function.Injective embed
  f : Ambient → C
  equivariant : ∀ x c, f (x + embed c) = f x + c
  NoiseIndex : Type
  [noiseFintype : Fintype NoiseIndex]
  [noiseNonempty : Nonempty NoiseIndex]
  noise : NoiseIndex → Ambient

attribute [instance] Data.ambientAddCommGroup Data.ambientModule Data.ambientFintype
attribute [instance] Data.noiseFintype Data.noiseNonempty

variable {C : Type} [AddCommGroup C] [Module F2 C]

noncomputable def failureIndicator (g : Data C) (sample : g.Ambient × g.NoiseIndex) : ℚ := by
  classical
  exact if g.f (sample.1 + g.noise sample.2) = g.f sample.1 then 0 else 1

noncomputable def stabilityError (g : Data C) : ℚ :=
  Finset.univ.expect (failureIndicator g)

noncomputable def kernelIndicator (g : Data C) {P : Type}
    [AddCommGroup P] [Module F2 P] (S : g.Ambient →ₗ[F2] P) (i : g.NoiseIndex) : ℚ := by
  classical
  exact if S (g.noise i) = 0 then 1 else 0

noncomputable def kernelError (g : Data C) {P : Type}
    [AddCommGroup P] [Module F2 P] (S : g.Ambient →ₗ[F2] P) : ℚ :=
  Finset.univ.expect (kernelIndicator g S)

theorem stabilityError_nonneg (g : Data C) : 0 ≤ stabilityError g := by
  classical
  apply Finset.expect_nonneg
  intro sample _
  unfold failureIndicator
  split <;> decide

theorem stabilityError_le_one (g : Data C) : stabilityError g ≤ 1 := by
  classical
  apply Finset.expect_le Finset.univ_nonempty
  intro sample _
  unfold failureIndicator
  split <;> decide

theorem kernelError_nonneg (g : Data C) {P : Type}
    [AddCommGroup P] [Module F2 P] (S : g.Ambient →ₗ[F2] P) : 0 ≤ kernelError g S := by
  classical
  apply Finset.expect_nonneg
  intro i _
  unfold kernelIndicator
  split <;> decide

theorem kernelError_le_one (g : Data C) {P : Type}
    [AddCommGroup P] [Module F2 P] (S : g.Ambient →ₗ[F2] P) : kernelError g S ≤ 1 := by
  classical
  apply Finset.expect_le Finset.univ_nonempty
  intro i _
  unfold kernelIndicator
  split <;> decide

def leaf (C : Type) [AddCommGroup C] [Module F2 C] [Fintype C] : Data C where
  Ambient := C
  embed := LinearMap.id
  embed_injective := Function.injective_id
  f := id
  equivariant := by intro x c; rfl
  NoiseIndex := C
  noise := id

def Satisfies (g : Data C) (ζ ν : ℚ) (r : Nat) : Prop :=
  stabilityError g ≤ ζ ∧
  ∀ (P : Type) [AddCommGroup P] [Module F2 P] (S : g.Ambient →ₗ[F2] P),
    r ≤ Module.finrank F2 (S.comp g.embed).range → kernelError g S ≤ ν

def StableNonlinearDispersion : Prop :=
  ∀ ζ ν : ℚ, 0 < ζ → ζ < 1 → 0 < ν → ν < 1 →
    ∃ r : Nat, 1 ≤ r ∧
      ∀ s : Nat, r ≤ s →
        ∃ g : Data (DFVSGames.Integration.BinaryLinear.Vector s), Satisfies g ζ ν r

end DFVSGames.Gadget.ActualGadget

namespace DFVSGames.Reduction.ActualSource

open DFVSGames.Integration.BinaryLinear

structure Source where
  «variables» : Nat
  occurrences : Nat
  nonempty : 0 < occurrences
  equation : Fin occurrences → CloneGap.Equation (Fin «variables»)

def Source.sourceList (S : Source) : List (CloneGap.Equation (Fin S.«variables»)) :=
  List.ofFn S.equation

def Source.ofList {n : Nat} (es : List (CloneGap.Equation (Fin n)))
    (hne : es ≠ []) : Source where
  «variables» := n
  occurrences := es.length
  nonempty := List.length_pos_iff.mpr hne
  equation := es.get

@[simp] theorem Source.sourceList_ofList {n : Nat}
    (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) :
    (Source.ofList es hne).sourceList = es := by
  exact List.ofFn_getElem

@[simp] theorem Source.sourceList_length (S : Source) :
    S.sourceList.length = S.occurrences := by simp [Source.sourceList]

theorem Source.sourceList_nonempty (S : Source) : S.sourceList ≠ [] := by
  intro h
  have hp := S.nonempty
  have hn := S.sourceList_length
  rw [h] at hn
  simp only [List.length_nil] at hn
  omega

instance sourceIndexNonempty (S : Source) : Nonempty (Fin S.occurrences) :=
  ⟨⟨0, S.nonempty⟩⟩

def Source.satisfied (S : Source) (A : Fin S.«variables» → Bool)
    (i : Fin S.occurrences) : Bool := CloneGap.satisfied (S.equation i) A

def Source.failure (S : Source) (A : Fin S.«variables» → Bool) : ℚ :=
  Finset.univ.expect (fun i => if S.satisfied A i then (0 : ℚ) else 1)

def Source.DistinctNames (S : Source) : Prop :=
  ∀ i, (S.equation i).first ≠ (S.equation i).second ∧
    (S.equation i).first ≠ (S.equation i).third ∧
    (S.equation i).second ≠ (S.equation i).third

abbrev Alphabet (s : Nat) := DFVSGames.Integration.BinaryLinear.Vector s
abbrev Ambient (s d : Nat) := Alphabet s × DFVSGames.Integration.BinaryLinear.Vector d

def alphabetEmbedding (s d : Nat) : Alphabet s →ₗ[F2] Ambient s d :=
  LinearMap.inl F2 (Alphabet s) (DFVSGames.Integration.BinaryLinear.Vector d)

@[simp] theorem alphabetEmbedding_apply (s d : Nat) (c : Alphabet s) :
    alphabetEmbedding s d c = (c, 0) := rfl

structure SplitGadget (s d : Nat) where
  f : Ambient s d → Alphabet s
  equivariant : ∀ (x : Ambient s d) (c : Alphabet s), f (x + (c, 0)) = f x + c
  NoiseIndex : Type
  noiseFintype : Fintype NoiseIndex
  noiseNonempty : Nonempty NoiseIndex
  noise : NoiseIndex → Ambient s d

attribute [instance] SplitGadget.noiseFintype SplitGadget.noiseNonempty

def SplitGadget.stabilityError {s d : Nat} (g : SplitGadget s d) : ℚ :=
  Finset.univ.expect (fun xv : Ambient s d × g.NoiseIndex =>
    if g.f (xv.1 + g.noise xv.2) = g.f xv.1 then (0 : ℚ) else 1)

def SplitGadget.kernelError {s d p : Nat} (g : SplitGadget s d)
    (S : Ambient s d →ₗ[F2] DFVSGames.Integration.BinaryLinear.Vector p) : ℚ :=
  Finset.univ.expect (fun i => if S (g.noise i) = 0 then (1 : ℚ) else 0)

theorem SplitGadget.stabilityError_nonneg {s d : Nat} (g : SplitGadget s d) :
    0 ≤ g.stabilityError := by
  apply Finset.expect_nonneg
  intro x _
  split <;> norm_num

theorem SplitGadget.stabilityError_le_one {s d : Nat} (g : SplitGadget s d) :
    g.stabilityError ≤ 1 := by
  apply Finset.expect_le Finset.univ_nonempty
  intro x _
  split <;> norm_num

end DFVSGames.Reduction.ActualSource

namespace DFVSGames.Integration.SplitGadget

open BinaryLinear

variable {R : Type} [AddCommGroup R] [Module F2 R] [FiniteDimensional F2 R]

theorem exists_split_equiv {s : Nat} (e : Vector s →ₗ[F2] R)
    (he : Function.Injective e) :
    ∃ d : Nat, ∃ φ : R ≃ₗ[F2] (Vector s × Vector d),
      ∀ c, φ (e c) = (c, 0) := by
  obtain ⟨U, hU⟩ := e.range.exists_isCompl
  let er := LinearEquiv.ofInjective e he
  let eu := (Module.finBasis F2 U).equivFun
  let split := e.range.prodEquivOfIsCompl U hU
  refine ⟨Module.finrank F2 U, split.symm.trans (er.symm.prodCongr eu), ?_⟩
  intro c
  change (er.symm.prodCongr eu) (split.symm (e c)) = (c, 0)
  have hc : split.symm (e c) = (er c, 0) :=
    e.range.prodEquivOfIsCompl_symm_apply_left U hU (er c)
  rw [hc]
  simp

open DFVSGames.Gadget.ActualGadget (Data stabilityError failureIndicator kernelError Satisfies)
open DFVSGames.Reduction.ActualSource

noncomputable def kernelProbability {s d : Nat} (g : SplitGadget s d)
    {P : Type} [AddCommGroup P] [Module F2 P]
    (S : Ambient s d →ₗ[F2] P) : ℚ := by
  classical
  exact Finset.univ.expect (fun i => if S (g.noise i) = 0 then (1 : ℚ) else 0)

theorem kernelProbability_eq_kernelError {s d p : Nat} (g : SplitGadget s d)
    (S : Ambient s d →ₗ[F2] Vector p) :
    kernelProbability g S = g.kernelError S := by
  unfold kernelProbability SplitGadget.kernelError
  congr 1
  funext i
  by_cases h : S (g.noise i) = 0 <;> simp_all

noncomputable def transport {s d : Nat} (g : Data (Vector s))
    (φ : g.Ambient ≃ₗ[F2] Ambient s d)
    (he : ∀ c, φ (g.embed c) = (c, 0)) : SplitGadget s d where
  f x := g.f (φ.symm x)
  equivariant x c := by
    have hc : φ.symm (c, 0) = g.embed c := by rw [← he c]; simp
    rw [map_add, hc]
    exact g.equivariant (φ.symm x) c
  NoiseIndex := g.NoiseIndex
  noiseFintype := g.noiseFintype
  noiseNonempty := g.noiseNonempty
  noise i := φ (g.noise i)

theorem transport_stabilityError {s d : Nat} (g : Data (Vector s))
    (φ : g.Ambient ≃ₗ[F2] Ambient s d)
    (he : ∀ c, φ (g.embed c) = (c, 0)) :
    (transport g φ he).stabilityError = stabilityError g := by
  classical
  apply Fintype.expect_equiv (φ.symm.toEquiv.prodCongr (Equiv.refl g.NoiseIndex))
  intro x
  simp [transport, failureIndicator, map_add]

theorem transport_kernelError {s d p : Nat} (g : Data (Vector s))
    (φ : g.Ambient ≃ₗ[F2] Ambient s d)
    (he : ∀ c, φ (g.embed c) = (c, 0))
    (S : Ambient s d →ₗ[F2] Vector p) :
    (transport g φ he).kernelError S = kernelError g (S.comp φ.toLinearMap) := by
  unfold SplitGadget.kernelError kernelError Gadget.ActualGadget.kernelIndicator
  congr 1
  funext i
  by_cases h : S (φ (g.noise i)) = 0 <;> simp_all [transport]

theorem transport_symbol_map {s d : Nat} (g : Data (Vector s))
    (φ : g.Ambient ≃ₗ[F2] Ambient s d)
    (he : ∀ c, φ (g.embed c) = (c, 0))
    {P : Type} [AddCommGroup P] [Module F2 P]
    (S : Ambient s d →ₗ[F2] P) :
    (S.comp φ.toLinearMap).comp g.embed = S.comp (alphabetEmbedding s d) := by
  apply LinearMap.ext
  intro c
  change S (φ (g.embed c)) = S (c, 0)
  rw [he]

theorem transport_kernelProbability {s d : Nat} (g : Data (Vector s))
    (φ : g.Ambient ≃ₗ[F2] Ambient s d)
    (he : ∀ c, φ (g.embed c) = (c, 0))
    {P : Type} [AddCommGroup P] [Module F2 P]
    (S : Ambient s d →ₗ[F2] P) :
    kernelProbability (transport g φ he) S =
      kernelError g (S.comp φ.toLinearMap) := by
  rfl

theorem transport_satisfies {s d : Nat} (g : Data (Vector s))
    (φ : g.Ambient ≃ₗ[F2] Ambient s d)
    (he : ∀ c, φ (g.embed c) = (c, 0))
    {ζ ν : ℚ} {r : Nat} (hg : Satisfies g ζ ν r) :
    (transport g φ he).stabilityError ≤ ζ ∧
      ∀ p (S : Ambient s d →ₗ[F2] Vector p),
        r ≤ Module.finrank F2 (S.comp (alphabetEmbedding s d)).range →
        (transport g φ he).kernelError S ≤ ν := by
  constructor
  · rw [transport_stabilityError]
    exact hg.1
  · intro p S hS
    rw [transport_kernelError g φ he S]
    apply hg.2 (Vector p) (S.comp φ.toLinearMap)
    rwa [transport_symbol_map g φ he S]

theorem exists_split_gadget {s : Nat} (g : Data (Vector s))
    {ζ ν : ℚ} {r : Nat} (hg : Satisfies g ζ ν r) :
    ∃ d : Nat, ∃ h : SplitGadget s d,
      h.stabilityError ≤ ζ ∧
      ∀ p (S : Ambient s d →ₗ[F2] Vector p),
        r ≤ Module.finrank F2 (S.comp (alphabetEmbedding s d)).range →
        h.kernelError S ≤ ν := by
  obtain ⟨d, φ, he⟩ := exists_split_equiv g.embed g.embed_injective
  exact ⟨d, transport g φ he, transport_satisfies g φ he hg⟩

theorem exists_split_gadget_general {s : Nat} (g : Data (Vector s))
    {ζ ν : ℚ} {r : Nat} (hg : Satisfies g ζ ν r) :
    ∃ d : Nat, ∃ h : SplitGadget s d,
      h.stabilityError ≤ ζ ∧
      ∀ (P : Type) [AddCommGroup P] [Module F2 P]
        (S : Ambient s d →ₗ[F2] P),
        r ≤ Module.finrank F2 (S.comp (alphabetEmbedding s d)).range →
        kernelProbability h S ≤ ν := by
  obtain ⟨d, φ, he⟩ := exists_split_equiv g.embed g.embed_injective
  refine ⟨d, transport g φ he, ?_, ?_⟩
  · rw [transport_stabilityError]
    exact hg.1
  · intro P _ _ S hS
    rw [transport_kernelProbability g φ he S]
    apply hg.2 P (S.comp φ.toLinearMap)
    rwa [transport_symbol_map g φ he S]

end DFVSGames.Integration.SplitGadget

namespace DFVSGames.Integration.RealBounds

open BinaryLinear FinalParameters

theorem rho_eq_two_div_pow {r s : Nat} (hs : r + 1 ≤ s) :
    rho r s = 2 / (2 : ℚ) ^ (s - r) := by
  have hn : s - r = (s - (r + 1)) + 1 := by omega
  unfold rho
  rw [hn, pow_succ, div_pow, one_pow]
  field_simp

theorem rho_real_eq_two_div_pow {r s : Nat} (hs : r + 1 ≤ s) :
    (rho r s : ℝ) = 2 / (2 : ℝ) ^ (s - r) := by
  simpa using congrArg (fun q : ℚ => (q : ℝ)) (rho_eq_two_div_pow hs)

theorem beta_eq_div (r s : Nat) :
    beta r s = rho r s / (2 * (2 : ℚ) ^ (r * s)) := by
  unfold beta
  rw [div_pow, one_pow]
  ring

theorem theta_real_product (δ : ℚ) (r s : Nat) :
    (theta δ r s : ℝ) =
      ((δ : ℝ) / (8 * (2 : ℝ) ^ s * 2 ^ (s * s))) *
        ((rho r s : ℝ) / (2 * (2 : ℝ) ^ (r * s))) := by
  simp [theta, alpha, beta_eq_div, pow_two]

theorem fourth_root_as_rpow {u ρ : ℚ} (hu : 0 < u) (hfour : u ^ 4 = ρ) :
    (ρ : ℝ) ^ (1 / 4 : ℝ) = (u : ℝ) := by
  have hpow : (u : ℝ) ^ 4 = (ρ : ℝ) := by exact_mod_cast hfour
  have hu' : (0 : ℝ) ≤ u := by exact_mod_cast (le_of_lt hu)
  rw [← hpow, one_div]
  exact Real.pow_rpow_inv_natCast hu' (by decide : (4 : Nat) ≠ 0)

theorem exists_symbol_dimension_real (r : Nat) {δ : ℚ} (hδ : 0 < δ) :
    ∃ s : Nat, r + 1 < s ∧
      (levelConstant r : ℝ) * (rho r s : ℝ) ^ (1 / 4 : ℝ) ≤ (δ : ℝ) / 8 := by
  obtain ⟨s, hs, u, hu, hfour, hbound⟩ := exists_symbol_dimension r hδ
  refine ⟨s, hs, ?_⟩
  rw [fourth_root_as_rpow hu hfour]
  exact_mod_cast hbound

theorem kernelProbability_real {s d : Nat}
    (g : DFVSGames.Reduction.ActualSource.SplitGadget s d)
    {P : Type} [AddCommGroup P] [Module F2 P] [DecidableEq P]
    (S : (Vector s × Vector d) →ₗ[F2] P) :
    (SplitGadget.kernelProbability g S : ℝ) =
      Finset.univ.expect (fun i => if S (g.noise i) = 0 then (1 : ℝ) else 0) := by
  classical
  unfold SplitGadget.kernelProbability
  simp only [Finset.expect_eq_sum_div_card, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : S (g.noise i) = 0 <;> simp [h]

theorem kernelProbability_real_le {s d : Nat}
    (g : DFVSGames.Reduction.ActualSource.SplitGadget s d)
    {P : Type} [AddCommGroup P] [Module F2 P] [DecidableEq P]
    (S : (Vector s × Vector d) →ₗ[F2] P) {ν : ℚ}
    (h : SplitGadget.kernelProbability g S ≤ ν) :
    Finset.univ.expect (fun i => if S (g.noise i) = 0 then (1 : ℝ) else 0) ≤ (ν : ℝ) := by
  classical
  rw [← kernelProbability_real g S]
  exact_mod_cast h

theorem comparison_square_budget {t k L : Nat} {θ : ℚ} (hk : 0 < k)
    (h : 16 * (t : ℚ) ^ 2 * 2 ^ (t * L) ≤ (k : ℚ) * θ ^ 2) :
    ((t : ℝ) ^ 2 / (k : ℝ)) * 2 ^ (t * L) ≤ ((θ : ℝ) / 4) ^ 2 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h' : 16 * (t : ℝ) ^ 2 * 2 ^ (t * L) ≤ (k : ℝ) * (θ : ℝ) ^ 2 := by
    exact_mod_cast h
  rw [div_mul_eq_mul_div, div_le_iff₀ hk']
  nlinarith

end DFVSGames.Integration.RealBounds

namespace DFVSGames.Soundness.ActualMapComparison
open LinearMapDensity PartnerProjection PartnerSampling

theorem actual_partner_expectation_comparison {k t : ℕ}
    (hk : 0 < k) (htk : t ≤ k) (rhs : Fin k → Bool)
    {R : Type} [AddCommGroup R] [Module (ZMod 2) R] [FiniteDimensional (ZMod 2) R]
    [Fintype (SourcePoint rhs →ₗ[ZMod 2] R)]
    [∀ p : Partner k t, Fintype (PartnerPoint rhs (active p) →ₗ[ZMod 2] R)]
    (H : (SourcePoint rhs →ₗ[ZMod 2] R) → ℝ) (hH : ∀ M, |H M| ≤ 1) :
    |uniformMean (fun p : Partner k t =>
        uniformMean (fun B : PartnerPoint rhs (active p) →ₗ[ZMod 2] R =>
          H (B.comp (PartnerLinear.projection rhs (active p) (slots p))))) - uniformMean H| ≤
      Real.sqrt (((t : ℝ)^2 / k) * (2 : ℝ)^(Module.finrank (ZMod 2) R * t)) := by
  let : Nonempty (Partner k t) := partner_nonempty htk
  have hsecond :
      uniformMean (fun M : SourcePoint rhs →ₗ[ZMod 2] R =>
        (mixtureDensity (kernel (t := t) rhs) M)^2) ≤
      1 + ((t : ℝ)^2 / k) * (2 : ℝ)^(Module.finrank (ZMod 2) R * t) := by
    rw [mixtureDensity_second_moment]
    exact kernel_overlap_weight_le hk htk rhs (Module.finrank (ZMod 2) R)
  have hc := ExpectationComparison.bounded_test_expectation_comparison
    Finset.univ Finset.univ_nonempty (mixtureDensity (R := R) (kernel (t := t) rhs)) H
    (((t : ℝ)^2 / k) * (2 : ℝ)^(Module.finrank (ZMod 2) R * t))
    (mixtureDensity_mean (R := R) (kernel (t := t) rhs)) hsecond (fun M _ => hH M)
  rw [mixture_pullback_uniformMean
    (fun p : Partner k t => PartnerLinear.projection rhs (active p) (slots p))
    (fun p => PartnerLinear.projection_surjective rhs (active p) (slots p)) H]
  have hkernel : kernel (t := t) rhs =
      (fun p : Partner k t => (PartnerLinear.projection rhs (active p) (slots p)).ker) := rfl
  rw [hkernel] at hc
  simpa only [uniformMean, mul_comm] using hc

theorem actual_partner_expectation_comparison_dimension {k t L : ℕ}
    (hk : 0 < k) (htk : t ≤ k) (rhs : Fin k → Bool)
    {R : Type} [AddCommGroup R] [Module (ZMod 2) R] [FiniteDimensional (ZMod 2) R]
    [Fintype (SourcePoint rhs →ₗ[ZMod 2] R)]
    [∀ p : Partner k t, Fintype (PartnerPoint rhs (active p) →ₗ[ZMod 2] R)]
    (H : (SourcePoint rhs →ₗ[ZMod 2] R) → ℝ) (hH : ∀ M, |H M| ≤ 1)
    (hm : Module.finrank (ZMod 2) R ≤ L) :
    |uniformMean (fun p : Partner k t =>
        uniformMean (fun B : PartnerPoint rhs (active p) →ₗ[ZMod 2] R =>
          H (B.comp (PartnerLinear.projection rhs (active p) (slots p))))) - uniformMean H| ≤
      Real.sqrt (((t : ℝ)^2 / k) * (2 : ℝ)^(t * L)) := by
  have he : Module.finrank (ZMod 2) R * t ≤ t * L := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right t hm
  have hp : (2 : ℝ)^(Module.finrank (ZMod 2) R * t) ≤ (2 : ℝ)^(t*L) :=
    pow_le_pow_right₀ (by norm_num) he
  exact (actual_partner_expectation_comparison hk htk rhs H hH).trans
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hp
      (div_nonneg (sq_nonneg (t : ℝ)) (Nat.cast_nonneg k))))

theorem actual_partner_expectation_quarter {k t L : ℕ} {θ : ℚ}
    (hk : 0 < k) (htk : t ≤ k) (rhs : Fin k → Bool)
    {R : Type} [AddCommGroup R] [Module (ZMod 2) R] [FiniteDimensional (ZMod 2) R]
    [Fintype (SourcePoint rhs →ₗ[ZMod 2] R)]
    [∀ p : Partner k t, Fintype (PartnerPoint rhs (active p) →ₗ[ZMod 2] R)]
    (H : (SourcePoint rhs →ₗ[ZMod 2] R) → ℝ) (hH : ∀ M, |H M| ≤ 1)
    (hm : Module.finrank (ZMod 2) R ≤ L) (hθ : 0 ≤ θ)
    (budget : 16 * (t : ℚ)^2 * 2^(t*L) ≤ (k : ℚ)*θ^2) :
    |uniformMean (fun p : Partner k t =>
        uniformMean (fun B : PartnerPoint rhs (active p) →ₗ[ZMod 2] R =>
          H (B.comp (PartnerLinear.projection rhs (active p) (slots p))))) - uniformMean H| ≤
      (θ : ℝ) / 4 :=
  (actual_partner_expectation_comparison_dimension hk htk rhs H hH hm).trans
    (ExpectationComparison.comparison_error_le_quarter _ _ (by exact_mod_cast hθ)
      (Integration.RealBounds.comparison_square_budget hk budget))

end DFVSGames.Soundness.ActualMapComparison

namespace DFVSGames.Soundness.ActualMapComparison

def sourcePrecomposeEquiv {A E R : Type}
    [AddCommGroup A] [Module (ZMod 2) A] [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup R] [Module (ZMod 2) R] (e : A ≃ₗ[ZMod 2] E) :
    (E →ₗ[ZMod 2] R) ≃ (A →ₗ[ZMod 2] R) where
  toFun M := M.comp e.toLinearMap
  invFun M := M.comp e.symm.toLinearMap
  left_inv M := by
    apply LinearMap.ext
    intro x
    change M (e (e.symm x)) = M x
    rw [e.apply_symm_apply]
  right_inv M := by
    apply LinearMap.ext
    intro x
    change M (e.symm (e x)) = M x
    rw [e.symm_apply_apply]

theorem uniformMean_sourcePrecompose {A E R : Type}
    [AddCommGroup A] [Module (ZMod 2) A] [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup R] [Module (ZMod 2) R]
    [Fintype (A →ₗ[ZMod 2] R)] [Fintype (E →ₗ[ZMod 2] R)]
    (e : A ≃ₗ[ZMod 2] E) (H : (E →ₗ[ZMod 2] R) → ℝ) :
    LinearMapDensity.uniformMean (fun M : A →ₗ[ZMod 2] R =>
      H (M.comp e.symm.toLinearMap)) = LinearMapDensity.uniformMean H := by
  simpa only [LinearMapDensity.uniformMean] using
    (Fintype.expect_equiv (sourcePrecomposeEquiv e).symm
      (fun M : A →ₗ[ZMod 2] R => H (M.comp e.symm.toLinearMap)) H (fun _ => rfl))

theorem actual_partner_expectation_quarter_equiv {k t L : ℕ} {θ : ℚ}
    (hk : 0 < k) (htk : t ≤ k) (rhs : Fin k → Bool)
    {R E : Type} [AddCommGroup R] [Module (ZMod 2) R] [FiniteDimensional (ZMod 2) R]
    [AddCommGroup E] [Module (ZMod 2) E]
    [Fintype (PartnerProjection.SourcePoint rhs →ₗ[ZMod 2] R)]
    [Fintype (E →ₗ[ZMod 2] R)]
    [∀ p : PartnerSampling.Partner k t,
      Fintype (PartnerProjection.PartnerPoint rhs (PartnerSampling.active p) →ₗ[ZMod 2] R)]
    (e : PartnerProjection.SourcePoint rhs ≃ₗ[ZMod 2] E)
    (H : (E →ₗ[ZMod 2] R) → ℝ) (hH : ∀ M, |H M| ≤ 1)
    (hm : Module.finrank (ZMod 2) R ≤ L) (hθ : 0 ≤ θ)
    (budget : 16 * (t : ℚ)^2 * 2^(t*L) ≤ (k : ℚ) * θ^2) :
    |LinearMapDensity.uniformMean (fun p : PartnerSampling.Partner k t =>
        LinearMapDensity.uniformMean (fun B :
          PartnerProjection.PartnerPoint rhs (PartnerSampling.active p) →ₗ[ZMod 2] R =>
          H (B.comp ((PartnerLinear.projection rhs (PartnerSampling.active p)
            (PartnerSampling.slots p)).comp e.symm.toLinearMap)))) -
      LinearMapDensity.uniformMean H| ≤ (θ : ℝ) / 4 := by
  let Hcanon : (PartnerProjection.SourcePoint rhs →ₗ[ZMod 2] R) → ℝ :=
    fun M => H (M.comp e.symm.toLinearMap)
  have hcanon := actual_partner_expectation_quarter hk htk rhs Hcanon
    (fun M => hH (M.comp e.symm.toLinearMap)) hm hθ budget
  have hmean : LinearMapDensity.uniformMean Hcanon = LinearMapDensity.uniformMean H :=
    uniformMean_sourcePrecompose e H
  rw [hmean] at hcanon
  simpa only [Hcanon, LinearMap.comp_assoc] using hcanon

end DFVSGames.Soundness.ActualMapComparison

namespace DFVSGames.Soundness.RawTargetLaw

open scoped BigOperators
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Reduction
open PartnerProjection PartnerMapCoordinates RawPartnerTarget

theorem partnerProjection_congr_slots {k : Nat} (rhs : Fin k → Bool)
    (J : Finset (Fin k)) (slot slot' : Fin k → Slot)
    (agree : ∀ j ∈ J, slot j = slot' j) :
    PartnerLinear.projection rhs (activeOf J) slot =
      PartnerLinear.projection rhs (activeOf J) slot' := by
  apply PartnerFullSampling.projection_eq_of_slots_eq_on_active
  intro j hj
  exact agree j (by simpa [activeOf] using hj)

theorem rawProjection_congr_slots {k : Nat} (rhs : Fin k → Bool)
    (J : Finset (Fin k)) (slot slot' : Fin k → Slot)
    (agree : ∀ j ∈ J, slot j = slot' j) :
    RawPartnerTarget.rawProjection rhs J slot =
      RawPartnerTarget.rawProjection rhs J slot' := by
  unfold RawPartnerTarget.rawProjection
  rw [partnerProjection_congr_slots rhs J slot slot' agree]

theorem precompose_rawProjection {k : Nat} (rhs : Fin k → Bool)
    (J : Finset (Fin k)) (slot : Fin k → Slot)
    {R : Type} [AddCommGroup R] [Module F2 R]
    (M : RawPoint J →ₗ[F2] R) :
    (M.comp (pointEquiv rhs J).toLinearMap).comp
        ((PartnerLinear.projection rhs (activeOf J) slot).comp
          (PartnerLinear.sourceLinearEquiv rhs).symm.toLinearMap) =
      M.comp (RawPartnerTarget.rawProjection rhs J slot) := by
  simp only [RawPartnerTarget.rawProjection, LinearMap.comp_assoc]

theorem partner_row_column_expectation {k : Nat} (rhs : Fin k → Bool)
    (J : Finset (Fin k)) (slot : Fin k → Slot)
    {D C : Type} [AddCommGroup D] [Module F2 D] [AddCommGroup C] [Module F2 C]
    [Fintype (PartnerPoint rhs (activeOf J) →ₗ[F2] D)]
    [Fintype (PartnerPoint rhs (activeOf J) →ₗ[F2] C)]
    [Fintype (RawPoint J →ₗ[F2] D)] [Fintype (RawPoint J →ₗ[F2] C)]
    (H : (ActualHomogeneous.E k →ₗ[F2] D) →
      (ActualHomogeneous.E k →ₗ[F2] C) → ℝ) :
    (𝔼 Z : PartnerPoint rhs (activeOf J) →ₗ[F2] D,
      𝔼 X : PartnerPoint rhs (activeOf J) →ₗ[F2] C,
        let pi := (PartnerLinear.projection rhs (activeOf J) slot).comp
          (PartnerLinear.sourceLinearEquiv rhs).symm.toLinearMap
        H (Z.comp pi) (X.comp pi)) =
    (𝔼 Z : RawPoint J →ₗ[F2] D, 𝔼 X : RawPoint J →ₗ[F2] C,
      H (Z.comp (RawPartnerTarget.rawProjection rhs J slot))
        (X.comp (RawPartnerTarget.rawProjection rhs J slot))) := by
  symm
  apply Fintype.expect_equiv
    (ActualMapComparison.sourcePrecomposeEquiv (R := D) (pointEquiv rhs J))
  intro Z
  apply Fintype.expect_equiv
    (ActualMapComparison.sourcePrecomposeEquiv (R := C) (pointEquiv rhs J))
  intro X
  change H (Z.comp (RawPartnerTarget.rawProjection rhs J slot))
      (X.comp (RawPartnerTarget.rawProjection rhs J slot)) =
    H ((Z.comp (pointEquiv rhs J).toLinearMap).comp
        ((PartnerLinear.projection rhs (activeOf J) slot).comp
          (PartnerLinear.sourceLinearEquiv rhs).symm.toLinearMap))
      ((X.comp (pointEquiv rhs J).toLinearMap).comp
        ((PartnerLinear.projection rhs (activeOf J) slot).comp
          (PartnerLinear.sourceLinearEquiv rhs).symm.toLinearMap))
  simp only [precompose_rawProjection]

end DFVSGames.Soundness.RawTargetLaw

namespace DFVSGames.Soundness.UniformPartition
open scoped BigOperators
noncomputable section

def mean {Ω : Type} [Fintype Ω] (g : Ω → ℝ) : ℝ :=
  (∑ ω, g ω) / Fintype.card Ω

theorem mean_equiv {Ω Γ : Type} [Fintype Ω] [Fintype Γ]
    (e : Ω ≃ Γ) (g : Γ → ℝ) : mean (fun ω => g (e ω)) = mean g := by
  unfold mean
  rw [e.sum_comp, Fintype.card_congr e]

def fiberSum {Ω H : Type} [Fintype Ω] [DecidableEq H]
    (f : Ω → H) (h : H) (g : Ω → ℝ) : ℝ :=
  ∑ ω, if f ω = h then g ω else 0

def fiberSize {Ω H : Type} [Fintype Ω] [DecidableEq H]
    (f : Ω → H) (h : H) : ℝ := fiberSum f h (fun _ => 1)

theorem fiberSize_eq_card {Ω H : Type} [Fintype Ω] [DecidableEq H]
    (f : Ω → H) (h : H) :
    fiberSize f h = ((Finset.univ.filter (fun ω => f ω = h)).card : ℝ) := by
  classical
  unfold fiberSize fiberSum
  rw [← Finset.sum_filter]
  simp

theorem sum_fiberSum {Ω H : Type} [Fintype Ω] [Fintype H] [DecidableEq H]
    (f : Ω → H) (g : Ω → ℝ) :
    (∑ h, fiberSum f h g) = ∑ ω, g ω := by
  unfold fiberSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp

theorem fiberSize_mul {Ω H : Type} [Fintype Ω] [DecidableEq H]
    (f : Ω → H) (b : H → ℝ) (h : H) :
    fiberSize f h * b h = fiberSum f h (fun ω => b (f ω)) := by
  unfold fiberSize fiberSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : f ω = h <;> simp [hω]

theorem fiberSize_pos {Ω H : Type} [Fintype Ω] [DecidableEq H]
    (f : Ω → H) (h : H) (hh : ∃ ω, f ω = h) : 0 < fiberSize f h := by
  classical
  obtain ⟨ω, hω⟩ := hh
  rw [fiberSize_eq_card]
  have hc : 0 < (Finset.univ.filter (fun ω => f ω = h)).card :=
    Finset.card_pos.mpr ⟨ω, by simp [hω]⟩
  exact_mod_cast hc

theorem fiberSize_mul_conditional {Ω H : Type} [Fintype Ω] [DecidableEq H]
    (f : Ω → H) (g : Ω → ℝ) (h : H) :
    fiberSize f h * (fiberSum f h g / fiberSize f h) = fiberSum f h g := by
  classical
  by_cases hh : ∃ ω, f ω = h
  · have hn : fiberSize f h ≠ 0 := ne_of_gt (fiberSize_pos f h hh)
    field_simp [hn]
  · have hz : ∀ ω, f ω ≠ h := fun ω hω => hh ⟨ω, hω⟩
    simp [fiberSize, fiberSum, hz]

theorem total_mean {Ω H : Type} [Fintype Ω] [Fintype H] [DecidableEq H]
    (f : Ω → H) (g : Ω → ℝ) :
    mean g = mean (fun ω => fiberSum f (f ω) g / fiberSize f (f ω)) := by
  let b : H → ℝ := fun h => fiberSum f h g / fiberSize f h
  change mean g = mean (fun ω => b (f ω))
  unfold mean
  apply congrArg (fun x : ℝ => x / (Fintype.card Ω : ℝ))
  calc
    (∑ ω, g ω) = ∑ h, fiberSum f h g := (sum_fiberSum f g).symm
    _ = ∑ h, fiberSize f h * b h := by
      apply Finset.sum_congr rfl
      intro h _
      exact (fiberSize_mul_conditional f g h).symm
    _ = ∑ h, fiberSum f h (fun ω => b (f ω)) := by
      apply Finset.sum_congr rfl
      intro h _
      exact fiberSize_mul f b h
    _ = ∑ ω, b (f ω) := sum_fiberSum f (fun ω => b (f ω))

theorem mean_mono {Ω : Type} [Fintype Ω] {g g' : Ω → ℝ}
    (h : ∀ ω, g ω ≤ g' ω) : mean g ≤ mean g' := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ => h ω)) (Nat.cast_nonneg _)

theorem mean_le_partition_bound {Ω H : Type}
    [Fintype Ω] [Fintype H] [DecidableEq H]
    (f : Ω → H) (g : Ω → ℝ) (bound : H → ℝ)
    (hlocal : ∀ h, (∃ ω, f ω = h) →
      fiberSum f h g / fiberSize f h ≤ bound h) :
    mean g ≤ mean (fun ω => bound (f ω)) := by
  calc
    mean g = mean (fun ω => fiberSum f (f ω) g / fiberSize f (f ω)) := total_mean f g
    _ ≤ mean (fun ω => bound (f ω)) := mean_mono (fun ω => hlocal (f ω) ⟨ω,rfl⟩)

theorem fiber_conditional_eq_subtype_mean {Ω H : Type}
    [Fintype Ω] [DecidableEq H] (f : Ω → H) (h : H) (g : Ω → ℝ) :
    fiberSum f h g / fiberSize f h =
      mean (fun ω : {ω // f ω = h} => g ω.val) := by
  classical
  simp only [fiberSum, fiberSize, mean]
  congr 1
  · rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun ω => by simp) g
  · rw [← Finset.sum_filter]
    simp [Fintype.card_subtype]

end
end DFVSGames.Soundness.UniformPartition

end OAI
