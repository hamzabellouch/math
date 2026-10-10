import Mathlib
import OAI.Computability.DirectedFeedback.Games.AffineWitnessNormalization

namespace OAI

namespace DFVSGames.Inverse.RowErasureMatrix

open DFVSGames.Inverse.Shortcode
open DFVSGames.Inverse.RowErasure
open DFVSGames.Inverse.RowErasureDescriptions
open scoped BigOperators

noncomputable section

theorem exists_replacement_of_budget {ell m r : ℕ}
    (B : Mat ell m → Prop) (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (halphabet : 1 / (2 ^ ell : ℝ) ≤ α / 8)
    (hbudget : (2 : ℝ) ^ ((2 * r + 1) * (ell + m)) *
      Real.exp (-(α ^ 2 * (2 : ℝ) ^ ((ell - r) * (m - r))) / 32) < 1) :
    ∃ replacement : Mat ell m → Vector ell,
      ∀ d : Description ell m r, ((family ell m r).points d).Nonempty →
        (family ell m r).randomizedAgreement B replacement d < α / 4 := by
  let ρ := Real.exp (-(α ^ 2 * (2 : ℝ) ^ ((ell - r) * (m - r))) / 32)
  apply (family ell m r).exists_erasure_of_probability_bound B α ρ
  · intro d
    by_cases hne : ((family ell m r).points d).Nonempty
    · have htail := (family ell m r).randomizedAgreement_probability_le B α hα hαone
        (by simpa only [card_vector, Nat.cast_pow, Nat.cast_ofNat] using halphabet) d
      have hcardNat := d.toSlice.pow_dimension_le_card r le_rfl le_rfl hne
      have hcard : (2 : ℝ) ^ ((ell - r) * (m - r)) ≤
          (((family ell m r).points d).card : ℝ) := by
        exact_mod_cast hcardNat
      apply htail.trans
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hcard (sq_nonneg α)
      linarith
    · simpa [uniformMass, indicator, hne] using (Real.exp_pos
        (-(α ^ 2 * (2 : ℝ) ^ ((ell - r) * (m - r))) / 32)).le
  · simpa only [card_description, Nat.cast_pow, Nat.cast_ofNat] using hbudget

theorem advice_mass_ge_of_inverse_and_budget {ell m r : ℕ}
    (f : Mat ell m → Vector ell) (η α : ℝ) (hη : 0 < η)
    (hα : 0 < α) (hαone : α ≤ 1)
    (halphabet : 1 / (2 ^ ell : ℝ) ≤ α / 8)
    (haccept : 4 * η ≤ Shortcode.equalityAcceptance f)
    (inverse : ∀ g : Mat ell m → Vector ell,
      η ≤ Shortcode.equalityAcceptance g → HasAffineSlice g α r)
    (hbudget : (2 : ℝ) ^ ((2 * r + 1) * (ell + m)) *
      Real.exp (-(α ^ 2 * (2 : ℝ) ^ ((ell - r) * (m - r))) / 32) < 1) :
    η / (2 ^ (ell * r) : ℝ) ≤ adviceMass ((family ell m r).goodAt f α) := by
  exact advice_mass_ge_of_inverse_and_erasure f η α hη hα haccept inverse
    (exists_replacement_of_budget ((family ell m r).erasedUnion f α)
      α hα hαone halphabet hbudget)

end
end DFVSGames.Inverse.RowErasureMatrix

namespace DFVSGames.Inverse.RowErasure

open Filter
open scoped Topology

theorem eventually_log_unionBound_neg (α : ℝ) (hα : 0 < α)
    (ell r : ℕ) (hr : r < ell) :
    ∀ᶠ m : ℕ in atTop,
      (((2 * r + 1) * (ell + m) : ℕ) : ℝ) * Real.log 2 -
        α ^ 2 * (2 : ℝ) ^ ((ell - r) * (m - r)) / 32 < 0 := by
  let C : ℝ := (2 * r + 1 : ℕ)
  let D : ℝ := (ell + r : ℕ)
  have hzero : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [pow_zero] using
      (tendsto_pow_const_div_const_pow_of_one_lt 0 (show (1 : ℝ) < 2 by norm_num))
  have hone : Tendsto (fun n : ℕ => (n : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [pow_one] using
      (tendsto_pow_const_div_const_pow_of_one_lt 1 (show (1 : ℝ) < 2 by norm_num))
  have hlim' : Tendsto
      (fun n : ℕ => (C * Real.log 2) * (D * (1 / (2 : ℝ) ^ n) +
        (n : ℝ) / (2 : ℝ) ^ n)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      ((hzero.const_mul D).add hone).const_mul (C * Real.log 2)
  have hlim : Tendsto
      (fun n : ℕ => C * (D + (n : ℝ)) * Real.log 2 / (2 : ℝ) ^ n)
      atTop (𝓝 0) := by
    convert hlim' using 1
    ext n
    ring
  have hpos : 0 < α ^ 2 / 32 := by positivity
  have hsmall : ∀ᶠ n : ℕ in atTop,
      C * (D + (n : ℝ)) * Real.log 2 / (2 : ℝ) ^ n < α ^ 2 / 32 :=
    hlim.eventually (gt_mem_nhds hpos)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  apply eventually_atTop.2
  refine ⟨N + r, ?_⟩
  intro m hm
  have hrm : r ≤ m := by omega
  have hn : N ≤ m - r := by omega
  have hmcast : (m : ℝ) = (r : ℝ) + ((m - r : ℕ) : ℝ) := by
    exact_mod_cast (show m = r + (m - r) by omega)
  have hcast : (((2 * r + 1) * (ell + m) : ℕ) : ℝ) =
      C * (D + ((m - r : ℕ) : ℝ)) := by
    dsimp [C, D]
    push_cast
    rw [hmcast]
    ring
  have hlinear := (div_lt_iff₀ (show (0 : ℝ) < 2 ^ (m - r) by positivity)).1
    (hN (m - r) hn)
  have hexponent : m - r ≤ (ell - r) * (m - r) := by
    have h := Nat.mul_le_mul_right (m - r) (show 1 ≤ ell - r by omega)
    simpa only [one_mul] using h
  have hpower : (2 : ℝ) ^ (m - r) ≤ 2 ^ ((ell - r) * (m - r)) :=
    pow_le_pow_right₀ (by norm_num) hexponent
  have hproduct := mul_le_mul_of_nonneg_left hpower hpos.le
  rw [hcast]
  nlinarith

theorem eventually_unionBound_lt_one (α : ℝ) (hα : 0 < α)
    (ell r : ℕ) (hr : r < ell) :
    ∀ᶠ m : ℕ in atTop,
      (2 : ℝ) ^ ((2 * r + 1) * (ell + m)) *
        Real.exp (-(α ^ 2) * (2 : ℝ) ^ ((ell - r) * (m - r)) / 32) < 1 := by
  filter_upwards [eventually_log_unionBound_neg α hα ell r hr] with m hm
  have hpositive : (0 : ℝ) < 2 ^ ((2 * r + 1) * (ell + m)) := by positivity
  calc
    (2 : ℝ) ^ ((2 * r + 1) * (ell + m)) *
        Real.exp (-(α ^ 2) * (2 : ℝ) ^ ((ell - r) * (m - r)) / 32) =
        Real.exp ((((2 * r + 1) * (ell + m) : ℕ) : ℝ) * Real.log 2 -
          α ^ 2 * (2 : ℝ) ^ ((ell - r) * (m - r)) / 32) := by
      rw [← Real.exp_log hpositive, ← Real.exp_add, Real.log_pow]
      congr 1
      ring
    _ < 1 := Real.exp_lt_one_iff.mpr hm

theorem exists_unionBound_threshold (α : ℝ) (hα : 0 < α)
    (ell r : ℕ) (hr : r < ell) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → r ≤ m ∧
      (2 : ℝ) ^ ((2 * r + 1) * (ell + m)) *
        Real.exp (-(α ^ 2) * (2 : ℝ) ^ ((ell - r) * (m - r)) / 32) < 1 := by
  exact eventually_atTop.1 ((eventually_ge_atTop r).and
    (eventually_unionBound_lt_one α hα ell r hr))

end DFVSGames.Inverse.RowErasure

namespace DFVSGames.Inverse.RowErasureMatrix

open DFVSGames.Inverse.Shortcode
open DFVSGames.Inverse.RowErasure
open DFVSGames.Inverse.RowErasureDescriptions
open scoped BigOperators

noncomputable section

theorem exists_erasure_threshold (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (ell r : ℕ) (hr : r < ell) (halphabet : 1 / (2 ^ ell : ℝ) ≤ α / 8) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ B : Mat ell m → Prop,
        ∃ replacement : Mat ell m → Vector ell,
          ∀ d : Description ell m r, ((family ell m r).points d).Nonempty →
            (family ell m r).randomizedAgreement B replacement d < α / 4 := by
  obtain ⟨m₀, hm₀⟩ := exists_unionBound_threshold α hα ell r hr
  refine ⟨m₀, ?_⟩
  intro m hm B
  apply exists_replacement_of_budget B α hα hαone halphabet
  simpa only [neg_mul] using (hm₀ m hm).2

theorem exists_fixed_context_advice_threshold (η α : ℝ)
    (hη : 0 < η) (hα : 0 < α) (hαone : α ≤ 1)
    (ell r : ℕ) (hr : r < ell) (halphabet : 1 / (2 ^ ell : ℝ) ≤ α / 8) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      (∀ g : Mat ell m → Vector ell,
        η ≤ Shortcode.equalityAcceptance g → HasAffineSlice g α r) →
      ∀ f : Mat ell m → Vector ell,
        4 * η ≤ Shortcode.equalityAcceptance f →
          η / (2 ^ (ell * r) : ℝ) ≤ adviceMass ((family ell m r).goodAt f α) := by
  obtain ⟨m₀, hm₀⟩ := exists_erasure_threshold α hα hαone ell r hr halphabet
  refine ⟨m₀, ?_⟩
  intro m hm inverse f haccept
  exact advice_mass_ge_of_inverse_and_erasure f η α hη hα haccept inverse
    (hm₀ m hm ((family ell m r).erasedUnion f α))

theorem exists_contextual_advice_threshold (η α : ℝ)
    (hη : 0 < η) (hα : 0 < α) (hαone : α ≤ 1)
    (ell r : ℕ) (hr : r < ell) (halphabet : 1 / (2 ^ ell : ℝ) ≤ α / 8) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      (∀ g : Mat ell m → Vector ell,
        η ≤ Shortcode.equalityAcceptance g → HasAffineSlice g α r) →
      ∀ (Q : Type) [Fintype Q] (f : Q → Mat ell m → Vector ell),
        10 * η ≤ uniformMass (fun q => 4 * η ≤ Shortcode.equalityAcceptance (f q)) →
          10 * η ^ 2 / (2 ^ (ell * r) : ℝ) ≤
            Finset.univ.expect (fun q => adviceMass ((family ell m r).goodAt (f q) α)) := by
  obtain ⟨m₀, hm₀⟩ := exists_erasure_threshold α hα hαone ell r hr halphabet
  refine ⟨m₀, ?_⟩
  intro m hm inverse Q _ f hcontext
  have hlocal : ∀ q : Q, 4 * η ≤ Shortcode.equalityAcceptance (f q) →
      η ≤ uniformMass (goodUnion ((family ell m r).goodAt (f q) α)) := by
    intro q hq
    exact (family ell m r).union_mass_ge_of_inverse_and_erasure
      left right (f q) η α hη hα
      (by simpa only [acceptance_eq] using hq)
      left_uniform right_uniform (described_inverse α η inverse)
      (hm₀ m hm ((family ell m r).erasedUnion (f q) α))
  have h := advice_average_ge_ten_eta_sq_div_card
    (fun q => 4 * η ≤ Shortcode.equalityAcceptance (f q))
    (fun q => (family ell m r).goodAt (f q) α) η hη.le hcontext hlocal
  simpa only [card_rowMap, Nat.cast_pow, Nat.cast_ofNat] using h

end
end DFVSGames.Inverse.RowErasureMatrix

namespace DFVSGames.Decoder.ActualGoodRows

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
end DFVSGames.Decoder.ActualGoodRows

namespace DFVSGames.Decoder.ConstantSelection

open DFVSGames.Foundations.Information
open SparseLaw

noncomputable section

def visibleMass (α g₀ : ℝ) (ell r : ℕ) : ℝ :=
  α * g₀ / (8 * (2 : ℝ) ^ (ell * r))

def conditionalMass (α : ℝ) (ell r : ℕ) : ℝ :=
  (α / 8) ^ 2 / (2 : ℝ) ^ (ell * r) / (2 : ℝ) ^ r

def decodingMass (α g₀ : ℝ) (ell r : ℕ) : ℝ :=
  visibleMass α g₀ ell r * conditionalMass α ell r

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

theorem cube_exponential_antitone {m n : ℕ} (hmn : m ≤ n)
    {N : ℝ} (hN : 0 < N) :
    Real.exp (-(n : ℝ) / (3600 * N)) ≤
      Real.exp (-(m : ℝ) / (3600 * N)) := by
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact neg_le_neg (by exact_mod_cast hmn)

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
end DFVSGames.Decoder.ConstantSelection

namespace DFVSGames.Decoder.MatrixGapChoice

open Integration.BinaryLinear Reduction ActualSource
open Inverse.Shortcode (Mat HasAffineSlice InversePrinciple equalityAcceptance)

noncomputable section

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
end DFVSGames.Decoder.MatrixGapChoice

namespace DFVSGames.Inverse.RowErasure

noncomputable section

variable {X Y A S D : Type*}

def SliceFamily.chosenDescription (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) : D :=
  Classical.choose hgood

theorem SliceFamily.chosenDescription_spec (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) :
    F.rowMap (F.chosenDescription f α a s hgood) = a ∧
      F.rowValue (F.chosenDescription f α a s hgood) = s ∧
      (F.points (F.chosenDescription f α a s hgood)).Nonempty ∧
      α / 2 ≤ F.agreement f (F.chosenDescription f α a s hgood) :=
  Classical.choose_spec hgood

theorem SliceFamily.chosenDescription_congr (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) {a a' : A} {s s' : S}
    (hgood : F.GoodAdvice f α a s) (hgood' : F.GoodAdvice f α a' s')
    (ha : a = a') (hs : s = s') :
    F.chosenDescription f α a s hgood =
      F.chosenDescription f α a' s' hgood' := by
  subst a'
  subst s'
  rfl

def SliceFamily.selectedDescription (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) : Option D := by
  classical
  exact if hgood : F.GoodAdvice f α a s then
    some (F.chosenDescription f α a s hgood) else none

theorem SliceFamily.selectedDescription_of_good (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) :
    F.selectedDescription f α a s = some (F.chosenDescription f α a s hgood) := by
  simp only [SliceFamily.selectedDescription, dite_eq_left hgood]

theorem SliceFamily.good_of_selectedDescription (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) {d : D}
    (hselected : F.selectedDescription f α a s = some d) :
    F.GoodAdvice f α a s := by
  classical
  by_contra hgood
  simp only [SliceFamily.selectedDescription, dite_eq_right hgood] at hselected
  cases hselected

theorem SliceFamily.selectedDescription_spec (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) {d : D}
    (hselected : F.selectedDescription f α a s = some d) :
    F.rowMap d = a ∧ F.rowValue d = s ∧ (F.points d).Nonempty ∧
      α / 2 ≤ F.agreement f d := by
  have hgood := F.good_of_selectedDescription f α a s hselected
  rw [F.selectedDescription_of_good f α a s hgood] at hselected
  have hd := Option.some.inj hselected
  rw [← hd]
  exact F.chosenDescription_spec f α a s hgood

theorem SliceFamily.selectedDescription_congr (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) {a a' : A} {s s' : S}
    (ha : a = a') (hs : s = s') :
    F.selectedDescription f α a s = F.selectedDescription f α a' s' := by
  subst a'
  subst s'
  rfl

def SliceFamily.selectedEvent (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) : Prop :=
  ∃ d, F.selectedDescription f α a (F.advice a x) = some d ∧ x ∈ F.points d

def SliceFamily.selectedMatch (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) : Prop :=
  ∃ d, F.selectedDescription f α a (F.advice a x) = some d ∧
    x ∈ F.points d ∧ f x = F.target d x

theorem SliceFamily.selectedEvent_iff_of_advice (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) (x : X) (hx : F.advice a x = s) :
    F.selectedEvent f α a x ↔ x ∈ F.points (F.chosenDescription f α a s hgood) := by
  unfold SliceFamily.selectedEvent
  rw [hx, F.selectedDescription_of_good f α a s hgood]
  constructor
  · rintro ⟨d, hd, hmem⟩
    have he := Option.some.inj hd
    simpa only [he] using hmem
  · intro hmem
    exact ⟨_, rfl, hmem⟩

theorem SliceFamily.selectedMatch_iff_of_advice (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) (x : X) (hx : F.advice a x = s) :
    F.selectedMatch f α a x ↔
      x ∈ F.points (F.chosenDescription f α a s hgood) ∧
        f x = F.target (F.chosenDescription f α a s hgood) x := by
  unfold SliceFamily.selectedMatch
  rw [hx, F.selectedDescription_of_good f α a s hgood]
  constructor
  · rintro ⟨d, hd, hmem, hmatch⟩
    have he := Option.some.inj hd
    simpa only [he] using And.intro hmem hmatch
  · rintro ⟨hmem, hmatch⟩
    exact ⟨_, rfl, hmem, hmatch⟩

theorem SliceFamily.selectedEvent_good (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X)
    (hx : F.selectedEvent f α a x) : F.goodAt f α a x := by
  obtain ⟨d, hd, _⟩ := hx
  exact F.good_of_selectedDescription f α a (F.advice a x) hd

theorem SliceFamily.selectedMatch_event (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X)
    (hx : F.selectedMatch f α a x) : F.selectedEvent f α a x := by
  obtain ⟨d, hd, hmem, _⟩ := hx
  exact ⟨d, hd, hmem⟩

end
end DFVSGames.Inverse.RowErasure

namespace DFVSGames.Inverse.RowErasure.SelectionPartition

open scoped BigOperators Classical

noncomputable section

variable {X S : Type*} [Fintype X] [Fintype S]

def fiber (observe : X → S) (s : S) : Finset X :=
  Finset.univ.filter fun x => observe x = s

def event (observe : X → S) (good : S → Prop) (chosen : S → Finset X)
    (x : X) : Prop :=
  good (observe x) ∧ x ∈ chosen (observe x)

def matchEvent (observe : X → S) (good : S → Prop) (chosen : S → Finset X)
    (hit : S → X → Prop) (x : X) : Prop :=
  event observe good chosen x ∧ hit (observe x) x

theorem expect_le_expect_of_fiber_sum_le (observe : X → S) (f g : X → ℝ)
    (hle : ∀ s, (∑ x ∈ fiber observe s, f x) ≤ ∑ x ∈ fiber observe s, g x) :
    Finset.univ.expect f ≤ Finset.univ.expect g := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [← Finset.sum_fiberwise Finset.univ observe f,
    ← Finset.sum_fiberwise Finset.univ observe g]
  exact Finset.sum_le_sum fun s _ => hle s

omit [Fintype S] in

theorem sum_event_mul_fiber (observe : X → S) (good : S → Prop)
    (chosen : S → Finset X)
    (support : ∀ s x, x ∈ chosen s → observe x = s)
    (s : S) (hgood : good s) (w : X → ℝ) :
    (∑ x ∈ fiber observe s, indicator (event observe good chosen x) * w x) =
      ∑ x ∈ chosen s, w x := by
  have hsub : chosen s ⊆ fiber observe s := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, support s x hx⟩
  calc
    _ = ∑ x ∈ fiber observe s, if x ∈ chosen s then w x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      have hobs : observe x = s := (Finset.mem_filter.mp hx).2
      simp [event, indicator, hobs, hgood, ite_mul]
    _ = ∑ x ∈ chosen s, if x ∈ chosen s then w x else 0 := by
      exact (Finset.sum_subset hsub (by
        intro x _ hx
        simp only [ite_eq_right hx])).symm
    _ = ∑ x ∈ chosen s, w x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact ite_eq_left hx

omit [Fintype S] in
theorem sum_event_fiber (observe : X → S) (good : S → Prop)
    (chosen : S → Finset X)
    (support : ∀ s x, x ∈ chosen s → observe x = s)
    (s : S) (hgood : good s) :
    (∑ x ∈ fiber observe s, indicator (event observe good chosen x)) =
      ((chosen s).card : ℝ) := by
  simpa using sum_event_mul_fiber observe good chosen support s hgood (fun _ => 1)

omit [Fintype S] in
theorem sum_match_fiber (observe : X → S) (good : S → Prop)
    (chosen : S → Finset X)
    (support : ∀ s x, x ∈ chosen s → observe x = s)
    (hit : S → X → Prop) (s : S) (hgood : good s) :
    (∑ x ∈ fiber observe s, indicator (matchEvent observe good chosen hit x)) =
      ∑ x ∈ chosen s, indicator (hit s x) := by
  calc
    _ = ∑ x ∈ fiber observe s,
        indicator (event observe good chosen x) * indicator (hit s x) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hobs : observe x = s := (Finset.mem_filter.mp hx).2
      by_cases hevent : event observe good chosen x <;>
        by_cases hhit : hit s x <;>
        simp [matchEvent, indicator, hevent, hobs, hhit]
    _ = ∑ x ∈ chosen s, indicator (hit s x) :=
      sum_event_mul_fiber observe good chosen support s hgood (fun x => indicator (hit s x))

theorem mass_event_ge (observe : X → S) (good : S → Prop)
    (chosen : S → Finset X)
    (support : ∀ s x, x ∈ chosen s → observe x = s)
    (c : ℝ)
    (hsize : ∀ s, good s →
      c * ((fiber observe s).card : ℝ) ≤ ((chosen s).card : ℝ)) :
    c * uniformMass (fun x => good (observe x)) ≤
      uniformMass (event observe good chosen) := by
  unfold uniformMass
  rw [Finset.mul_expect]
  apply expect_le_expect_of_fiber_sum_le observe
  intro s
  by_cases hgood : good s
  · rw [sum_event_fiber observe good chosen support s hgood]
    calc
      (∑ x ∈ fiber observe s, c * indicator (good (observe x))) =
          c * ((fiber observe s).card : ℝ) := by
        calc
          _ = ∑ _x ∈ fiber observe s, c := by
            apply Finset.sum_congr rfl
            intro x hx
            have hobs : observe x = s := (Finset.mem_filter.mp hx).2
            simp [indicator, hobs, hgood]
          _ = _ := by simp [mul_comm]
      _ ≤ _ := hsize s hgood
  · have hz : ∀ x ∈ fiber observe s,
        indicator (good (observe x)) = 0 ∧
          indicator (event observe good chosen x) = 0 := by
      intro x hx
      have hobs : observe x = s := (Finset.mem_filter.mp hx).2
      simp [indicator, event, hobs, hgood]
    have hleft : (∑ x ∈ fiber observe s, c * indicator (good (observe x))) = 0 :=
      Finset.sum_eq_zero fun x hx => by rw [(hz x hx).1, mul_zero]
    have hright : (∑ x ∈ fiber observe s, indicator (event observe good chosen x)) = 0 :=
      Finset.sum_eq_zero fun x hx => (hz x hx).2
    rw [hleft, hright]

theorem mass_match_ge (observe : X → S) (good : S → Prop)
    (chosen : S → Finset X)
    (support : ∀ s x, x ∈ chosen s → observe x = s)
    (hit : S → X → Prop) (β : ℝ)
    (hmatch : ∀ s, good s →
      β * ((chosen s).card : ℝ) ≤ ∑ x ∈ chosen s, indicator (hit s x)) :
    β * uniformMass (event observe good chosen) ≤
      uniformMass (matchEvent observe good chosen hit) := by
  unfold uniformMass
  rw [Finset.mul_expect]
  apply expect_le_expect_of_fiber_sum_le observe
  intro s
  by_cases hgood : good s
  · rw [← Finset.mul_sum, sum_event_fiber observe good chosen support s hgood,
      sum_match_fiber observe good chosen support hit s hgood]
    exact hmatch s hgood
  · have hz : ∀ x ∈ fiber observe s,
        indicator (event observe good chosen x) = 0 ∧
          indicator (matchEvent observe good chosen hit x) = 0 := by
      intro x hx
      have hobs : observe x = s := (Finset.mem_filter.mp hx).2
      simp [indicator, event, matchEvent, hobs, hgood]
    have hleft : (∑ x ∈ fiber observe s, β * indicator (event observe good chosen x)) = 0 :=
      Finset.sum_eq_zero fun x hx => by rw [(hz x hx).1, mul_zero]
    have hright :
        (∑ x ∈ fiber observe s, indicator (matchEvent observe good chosen hit x)) = 0 :=
      Finset.sum_eq_zero fun x hx => (hz x hx).2
    rw [hleft, hright]

end
end DFVSGames.Inverse.RowErasure.SelectionPartition

end OAI
