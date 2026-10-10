import Mathlib
import OAI.Computability.MaxCut.Encoding.MatrixCoordinates
import OAI.Computability.MaxCut.Games.RowErasureConcentration

namespace OAI

namespace MaxCutGames.Decoder.ActualGoodRows

open Integration.BinaryLinear Reduction ActualSource
open Inverse Inverse.RowErasure
open Inverse.Shortcode (Mat HasAffineSlice)
open scoped BigOperators Classical

noncomputable section

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

def table (S : Source) (k s d : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (U : ActualGame.Question S k) (T : ActualHomogeneous.E k →ₗ[F2] Vector d)
    (M : Mat s (1 + 2 * k)) : Vector s :=
  TableKeysGame.unfolded S k s d labeling
    (U, ((MatrixCoordinates.mapEquiv k s).symm M).prod T)

theorem table_acceptance (S : Source) (k s d : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (U : ActualGame.Question S k) (T : ActualHomogeneous.E k →ₗ[F2] Vector d) :
    Shortcode.equalityAcceptance (table S k s d labeling U T) =
      ActualSpectral.fiberAcceptance S k s d labeling U T := by
  unfold table
  rw [← MatrixCoordinates.shortcodeAcceptance_eq k s
    (fun M : ActualHomogeneous.E k →ₗ[F2] Vector s =>
      TableKeysGame.unfolded S k s d labeling (U, M.prod T))]
  unfold ActualSpectral.fiberAcceptance SurrogateFibers.shortcodeAcceptance
  apply Finset.expect_congr (by ext M; simp only [Finset.mem_univ])
  intro M _
  apply Finset.expect_congr (by ext a; simp only [Finset.mem_univ])
  intro a _
  apply Finset.expect_congr (by ext l; simp only [Finset.mem_univ])
  intro l _
  rfl

/-- The row-advice probability in actual matrix coordinates. In particular,
dependent rows of `A` are sampled with their full multiplicity. -/
def adviceMass (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ) : ℝ :=
  𝔼 U : ActualGame.Question S k,
    𝔼 T : ActualHomogeneous.E k →ₗ[F2] Vector d,
      RowErasure.adviceMass
        ((RowErasureMatrix.family s (1 + 2 * k) r).goodAt (table S k s d labeling U T) α)

def goodRowMass (rstar s r : ℕ) : ℝ :=
  10 * ActualSpectral.eta rstar ^ 2 / (2 : ℝ) ^ (s * r)

theorem goodRowMass_pos (rstar s r : ℕ) : 0 < goodRowMass rstar s r := by
  unfold goodRowMass
  have h := ActualSpectral.eta_pos rstar
  positivity

theorem exists_actual_advice_threshold (rstar : ℕ) (α : ℝ)
    (hα : 0 < α) (hαone : α ≤ 1) (s r : ℕ)
    (hr : r < s) (halphabet : 1 / (2 : ℝ) ^ s ≤ α / 8) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (∀ f : Mat s (1 + 2 * k) → Vector s,
        ActualSpectral.eta rstar ≤ Shortcode.equalityAcceptance f → HasAffineSlice f α r) →
      ∀ (S : Source) (d : ℕ) (g : SplitGadget s d)
        (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)),
        (∀ L : Ambient s d →ₗ[F2] ActualHomogeneous.E k,
          rstar ≤ Module.finrank F2 (L.comp (alphabetEmbedding s d)).range →
          Integration.SplitGadget.kernelProbability g L ≤ 7 / 8) →
        (99 : ℚ) / 100 ≤ TableKeysGame.acceptanceProbability S k g labeling →
        goodRowMass rstar s r ≤ adviceMass S k s d r labeling α := by
  obtain ⟨m₀, hm₀⟩ := RowErasureMatrix.exists_contextual_advice_threshold
    (ActualSpectral.eta rstar) α (ActualSpectral.eta_pos rstar) hα hαone
    s r hr halphabet
  refine ⟨m₀, ?_⟩
  intro k hk hinverse S d g labeling hkernel haccept
  let Q := ActualGame.Question S k × (ActualHomogeneous.E k →ₗ[F2] Vector d)
  let f : Q → Mat s (1 + 2 * k) → Vector s :=
    fun q => table S k s d labeling q.1 q.2
  have hcontext : 10 * ActualSpectral.eta rstar ≤
      uniformMass (fun q : Q => 4 * ActualSpectral.eta rstar ≤
        Shortcode.equalityAcceptance (f q)) := by
    have h := ActualSpectral.actual_good_fiber_mass S k g labeling rstar hkernel haccept
    dsimp only [Q, f]
    unfold uniformMass
    rw [ActualSpectral.expect_prod]
    simpa only [indicator, table_acceptance] using h
  have h := hm₀ (1 + 2 * k) (by omega) hinverse Q f hcontext
  dsimp only [Q, f] at h
  rw [ActualSpectral.expect_prod] at h
  simpa only [goodRowMass, adviceMass] using h

end
end MaxCutGames.Decoder.ActualGoodRows

namespace MaxCutGames.Decoder.ConstantSelection

open MaxCutGames.Foundations.Information
open SparseLaw

noncomputable section

/-- Probability of actual visible data carrying a transferred witness. -/
def visibleMass (α g₀ : ℝ) (ell r : ℕ) : ℝ :=
  α * g₀ / (8 * (2 : ℝ) ^ (ell * r))

/-- Independent private decoding success on a transferred witness. -/
def conditionalMass (α : ℝ) (ell r : ℕ) : ℝ :=
  (α / 8) ^ 2 / (2 : ℝ) ^ (ell * r) / (2 : ℝ) ^ r

def decodingMass (α g₀ : ℝ) (ell r : ℕ) : ℝ :=
  visibleMass α g₀ ell r * conditionalMass α ell r

/-- The whole-table TV budget includes the coefficient of both compared
events in the witness-margin inequality. -/
def variationBudget (α g₀ : ℝ) (ell r : ℕ) : ℝ :=
  visibleMass α g₀ ell r / (1 + α / 4)

theorem visibleMass_pos {α g₀ : ℝ} (hα : 0 < α) (hg₀ : 0 < g₀)
    (ell r : ℕ) : 0 < visibleMass α g₀ ell r := by
  unfold visibleMass
  positivity

theorem conditionalMass_pos {α : ℝ} (hα : 0 < α) (ell r : ℕ) :
    0 < conditionalMass α ell r := by
  unfold conditionalMass
  positivity

theorem decodingMass_pos {α g₀ : ℝ} (hα : 0 < α) (hg₀ : 0 < g₀)
    (ell r : ℕ) : 0 < decodingMass α g₀ ell r :=
  mul_pos (visibleMass_pos hα hg₀ ell r) (conditionalMass_pos hα ell r)

theorem variationBudget_pos {α g₀ : ℝ} (hα : 0 < α) (hg₀ : 0 < g₀)
    (ell r : ℕ) : 0 < variationBudget α g₀ ell r := by
  exact div_pos (visibleMass_pos hα hg₀ ell r) (by positivity)

theorem variationBudget_suffices {α g₀ ε : ℝ} (hα : 0 < α) (ell r : ℕ)
    (hε : ε ≤ variationBudget α g₀ ell r) :
    (1 + α / 4) * ε ≤ α * g₀ * (1 / (2 : ℝ) ^ (ell * r)) / 8 := by
  have hd : 0 < 1 + α / 4 := by positivity
  have h := (le_div_iff₀ hd).mp hε
  calc
    (1 + α / 4) * ε = ε * (1 + α / 4) := mul_comm _ _
    _ ≤ visibleMass α g₀ ell r := h
    _ = α * g₀ * (1 / (2 : ℝ) ^ (ell * r)) / 8 := by
      unfold visibleMass
      ring

/-- Exponential clean-mask decay persists after increasing the cube root. -/
theorem cube_exponential_antitone {m n : ℕ} (hmn : m ≤ n)
    {N : ℝ} (hN : 0 < N) :
    Real.exp (-(n : ℝ) / (3600 * N)) ≤
      Real.exp (-(m : ℝ) / (3600 * N)) := by
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact neg_le_neg (by exact_mod_cast hmn)

/-- One tuple length meets the sparse-law and repetition requirements, while
exceeding any independent inverse/erasure dimension threshold. -/
theorem exists_simultaneous_cube (V : Type*) [Fintype V] [Zero V] [DecidableEq V]
    {N ε γ : ℝ} (hN : 1 ≤ N) (hε : 0 < ε) (hγ : 0 < γ) (lower : ℕ) :
    ∃ m : ℕ, lower ≤ m ∧ 0 < m ∧
      totalVariation
        (independentWeights (mixture (1 / (m : ℝ) ^ 2) (singletonPairWeights V)) (m ^ 3))
        (uniformWeights (Fin (m ^ 3) → V × V)) ≤ ε ∧
      (1 - ((1 / (m : ℝ) ^ 2) / N) / 3600) ^ (m ^ 3) < γ := by
  obtain ⟨m₀, hm₀, hexp⟩ := Clean.exists_cube_exponential_lt
    (show 0 < N by linarith) hγ
  obtain ⟨m, hlarge, hm, htv⟩ := exists_cubeSlope_totalVariation_le V ε hε
    (max lower m₀)
  have hbase : m₀ ≤ m := (le_max_right _ _).trans hlarge
  refine ⟨m, (le_max_left _ _).trans hlarge, hm, htv, ?_⟩
  have hdecay := (Clean.cube_mask_rate_le_exp (Nat.succ_le_iff.mpr hm) hN).trans
    (cube_exponential_antitone hbase (by linarith : 0 < N))
  have hbeta : (1 / (m : ℝ)) ^ 2 = 1 / (m : ℝ) ^ 2 := by ring
  rw [hbeta] at hdecay
  exact hdecay.trans_lt hexp

/-- All scalar requirements for the final decoding contradiction can be met
after the fixed alphabet and inverse parameters have been chosen. -/
theorem exists_matrix_cube (V : Type*) [Fintype V] [Zero V] [DecidableEq V]
    {α g₀ : ℝ} (hα : 0 < α) (hg₀ : 0 < g₀)
    (ell r dimW lower : ℕ) :
    ∃ m : ℕ, lower ≤ m ∧ 0 < m ∧
      totalVariation
        (independentWeights (mixture (1 / (m : ℝ) ^ 2) (singletonPairWeights V)) (m ^ 3))
        (uniformWeights (Fin (m ^ 3) → V × V)) ≤ variationBudget α g₀ ell r ∧
      (1 - ((1 / (m : ℝ) ^ 2) / (2 : ℝ) ^ (dimW + r)) / 3600) ^ (m ^ 3) <
        decodingMass α g₀ ell r := by
  exact exists_simultaneous_cube V (one_le_pow₀ (by norm_num))
    (variationBudget_pos hα hg₀ ell r) (decodingMass_pos hα hg₀ ell r) lower

end
end MaxCutGames.Decoder.ConstantSelection

namespace MaxCutGames.Decoder.MatrixGapChoice

open Integration.BinaryLinear Reduction ActualSource
open Inverse.Shortcode (Mat HasAffineSlice InversePrinciple equalityAcceptance)

noncomputable section

/-- Fixed dimensions, density and sparse mask for one logical alphabet.
The remaining gadget codimension may be arbitrary when choosing the cube. -/
structure InverseParameters (rstar : ℕ) where
  α : ℝ
  positive : 0 < α
  bounded : α ≤ 1
  r : ℕ
  s : ℕ
  s_large : rstar ≤ s
  r_small : r < s
  trivial_small : 1 / (2 : ℝ) ^ (s - r) < α / 8
  tupleThreshold : ℕ
  inverse : ∀ k : ℕ, tupleThreshold ≤ k →
    ∀ f : Mat s (1 + 2 * k) → Vector s,
      ActualSpectral.eta rstar ≤ equalityAcceptance f → HasAffineSlice f α r
  advice : ∀ k : ℕ, tupleThreshold ≤ k →
    ∀ (S : Source) (d : ℕ) (g : SplitGadget s d)
      (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)),
      (∀ L : Ambient s d →ₗ[F2] ActualHomogeneous.E k,
        rstar ≤ Module.finrank F2 (L.comp (alphabetEmbedding s d)).range →
        Integration.SplitGadget.kernelProbability g L ≤ 7 / 8) →
      (99 : ℚ) / 100 ≤ TableKeysGame.acceptanceProbability S k g labeling →
      ActualGoodRows.goodRowMass rstar s r ≤ ActualGoodRows.adviceMass S k s d r labeling α

theorem eta_lt_one (rstar : ℕ) : ActualSpectral.eta rstar < 1 := by
  have hp : (1 : ℝ) ≤ 2 ^ rstar := one_le_pow₀ (by norm_num)
  have hi : 1 / (2 : ℝ) ^ rstar ≤ 1 := by
    exact (div_le_one (by positivity)).mpr hp
  unfold ActualSpectral.eta
  rw [← one_div]
  linarith

theorem exists_inverse_parameters (hinverse : InversePrinciple) (rstar : ℕ) :
    Nonempty (InverseParameters rstar) := by
  obtain ⟨α, hα, hαone, r, _hr, s₀, hinv⟩ :=
    hinverse (ActualSpectral.eta rstar) (ActualSpectral.eta_pos rstar) (eta_lt_one rstar)
  obtain ⟨s, hs, hrs, hsmall, _htiny⟩ := DimensionSelection.exists_logical_dimension
    hα (ActualSpectral.eta_pos rstar) r (max rstar s₀)
  have hsstar : rstar ≤ s := (le_max_left _ _).trans hs
  have hs₀ : s₀ ≤ s := (le_max_right _ _).trans hs
  obtain ⟨m₀, hm₀⟩ := hinv s hs₀
  have halphabet : 1 / (2 : ℝ) ^ s ≤ α / 8 := by
    have hp : (2 : ℝ) ^ (s - r) ≤ 2 ^ s :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le s r)
    exact (one_div_le_one_div_of_le (by positivity) hp).trans hsmall.le
  obtain ⟨k₀, hk₀⟩ := ActualGoodRows.exists_actual_advice_threshold
    rstar α hα hαone s r hrs halphabet
  let threshold := max m₀ k₀
  have hi (k : ℕ) (hk : threshold ≤ k) :
      ∀ f : Mat s (1 + 2 * k) → Vector s,
        ActualSpectral.eta rstar ≤ equalityAcceptance f → HasAffineSlice f α r := by
    apply hm₀ (1 + 2 * k)
    have hm : m₀ ≤ k := (le_max_left _ _).trans hk
    omega
  refine ⟨{
    α := α
    positive := hα
    bounded := hαone
    r := r
    s := s
    s_large := hsstar
    r_small := hrs
    trivial_small := hsmall
    tupleThreshold := threshold
    inverse := hi
    advice := ?_ }⟩
  intro k hk S d g labeling hkernel haccept
  exact hk₀ k ((le_max_right _ _).trans hk) (hi k hk) S d g labeling hkernel haccept

/-- After all fixed dimensions are known, the cube simultaneously exceeds the
inverse threshold, reduces full-table variation, and beats the decoder mass. -/
theorem exists_cube {rstar : ℕ} (P : InverseParameters rstar) (d : ℕ) :
    ∃ m : ℕ, 0 < m ∧ P.tupleThreshold ≤ m ^ 3 ∧
      0 ≤ 1 / (m : ℝ) ^ 2 ∧ 1 / (m : ℝ) ^ 2 ≤ 1 ∧
      Foundations.Information.totalVariation
        (SparseLaw.independentWeights
          (SparseLaw.mixture (1 / (m : ℝ) ^ 2)
            (SparseLaw.singletonPairWeights (Ambient P.s d))) (m ^ 3))
        (SparseLaw.uniformWeights (Fin (m ^ 3) → Ambient P.s d × Ambient P.s d)) ≤
          ConstantSelection.variationBudget P.α (ActualGoodRows.goodRowMass rstar P.s P.r) P.s P.r ∧
      (1 - ((1 / (m : ℝ) ^ 2) / (2 : ℝ) ^ (d + P.r)) / 3600) ^ (m ^ 3) <
        ConstantSelection.decodingMass P.α (ActualGoodRows.goodRowMass rstar P.s P.r) P.s P.r := by
  obtain ⟨m, hlarge, hm, htv, hrate⟩ := ConstantSelection.exists_matrix_cube (Ambient P.s d)
    P.positive (ActualGoodRows.goodRowMass_pos rstar P.s P.r) P.s P.r d P.tupleThreshold
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.succ_le_iff.mpr hm)
  have hmsq : (1 : ℝ) ≤ (m : ℝ) ^ 2 := one_le_pow₀ hmreal
  refine ⟨m, hm, hlarge.trans (Nat.le_self_pow (by decide : (3 : ℕ) ≠ 0) m),
    by positivity, ?_, htv, hrate⟩
  exact (div_le_one (by positivity)).mpr hmsq

end
end MaxCutGames.Decoder.MatrixGapChoice

end OAI
