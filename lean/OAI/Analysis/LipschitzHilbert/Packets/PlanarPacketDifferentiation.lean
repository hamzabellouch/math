import OAI.Analysis.LipschitzHilbert.Fourier.FiniteBandDerivative
import OAI.Analysis.LipschitzHilbert.Packets.LinePacketReplacement

namespace OAI

/-! Exact vertical derivatives of packet syntheses. Coefficients stay
fixed during differentiation, including when they are analyzing integrals. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def planarPacketBand (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (j : Fin N) (k : κ) (x y : ℝ) : ℂ :=
  ∑ i, coeff j i k * wave j i k y x

omit [Fintype κ] in
theorem planarPacketBand_hasDerivAt (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (j : Fin N) (k : κ) (x y : ℝ)
    (hw : ∀ i, DifferentiableAt ℝ (fun t => wave j i k t x) y) :
    HasDerivAt (planarPacketBand coeff wave j k x)
      (∑ i, coeff j i k * deriv (fun t => wave j i k t x) y) y := by
  apply HasDerivAt.fun_sum
  intro i _
  exact (hw i).hasDerivAt.const_mul _

omit [Fintype κ] in
theorem planarPacketBand_covariant (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (frequency : κ → ℝ)
    (j : Fin N) (k : κ) (x y : ℝ)
    (hw : ∀ i, DifferentiableAt ℝ (fun t => wave j i k t x) y) :
    deriv (planarPacketBand coeff wave j k x) y -
      (frequency k:ℂ)*Complex.I*planarPacketBand coeff wave j k x y =
    planarPacketBand coeff
      (fun j i k t s => deriv (fun z => wave j i k z s) t -
        (frequency k:ℂ)*Complex.I*wave j i k t s) j k x y := by
  rw [(planarPacketBand_hasDerivAt coeff wave j k x y hw).deriv]
  unfold planarPacketBand
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

def planarPacketInterval (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (a b : ℕ) (x y : ℝ) : EuclideanSpace ℂ κ :=
  bandIntervalSignal (fun j k => planarPacketBand coeff wave j k x) a b y

omit [Fintype κ] in
theorem planarPacketInterval_smul (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (s : ℝ) (a b : ℕ) (x y : ℝ) :
    planarPacketInterval coeff (fun j i k t z => (s:ℂ)*wave j i k t z) a b x y =
      s • planarPacketInterval coeff wave a b x y := by
  have hs (j : Fin N) (k : κ) :
      planarPacketBand coeff (fun j i k t z => (s:ℂ)*wave j i k t z) j k x y =
        (s:ℂ)*planarPacketBand coeff wave j k x y := by
    simp only [planarPacketBand, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hp (n : ℕ) (k : κ) :
      scalarBandPartial (fun j => planarPacketBand coeff
        (fun j i k t z => (s:ℂ)*wave j i k t z) j k x) n y =
      (s:ℂ)*scalarBandPartial (fun j => planarPacketBand coeff wave j k x) n y := by
    simp only [scalarBandPartial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp only [hs, mul_zero]
  ext k
  change _ = (s:ℂ)*(_-_)
  simp only [planarPacketInterval, bandIntervalSignal, WithLp.ofLp_toLp, hp, mul_sub]

theorem planarPacketInterval_covariant (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (frequency : κ → ℝ)
    (a b : ℕ) (x y : ℝ)
    (hw : ∀ j i k t, DifferentiableAt ℝ (fun z => wave j i k z x) t) :
    covariantSignal frequency (fun k t => planarPacketInterval coeff wave a b x t k) y =
    planarPacketInterval coeff
      (fun j i k t s => deriv (fun z => wave j i k z s) t -
        (frequency k:ℂ)*Complex.I*wave j i k t s) a b x y := by
  unfold planarPacketInterval
  rw [bandIntervalSignal_covariant _ _ _ _ _ (fun j k =>
    (planarPacketBand_hasDerivAt coeff wave j k x y (fun i => hw j i k y)).differentiableAt)]
  congr 1
  funext j k t
  exact planarPacketBand_covariant coeff wave frequency j k x t
    (fun i => hw j i k t)

theorem planarPacketInterval_eq_partial_difference
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (P : LinePacketFamily N κ ι)
    (y : ℝ) (hc : ∀ j i, coeff j i = P.coeff j i)
    (hw : ∀ j i k x, wave j i k y x = P.wave j i k x) (a b : ℕ) (x : ℝ) :
    planarPacketInterval coeff wave a b x y =
      hilbertPartialBandSum P.packets b x - hilbertPartialBandSum P.packets a x := by
  have hs (j : Fin N) (k : κ) : planarPacketBand coeff wave j k x y = P.packets j k x := by
    simp only [planarPacketBand, hc, hw, LinePacketFamily.packets, packetSynthesis_apply]
  ext k
  simp only [planarPacketInterval, bandIntervalSignal, WithLp.ofLp_toLp,
    WithLp.ofLp_sub, Pi.sub_apply, hilbertPartialBandSum, scalarBandPartial,
    partialBandSum, hs]

theorem planarPacketInterval_norm_le
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (P : LinePacketFamily N κ ι)
    (y : ℝ) (hc : ∀ j i, coeff j i = P.coeff j i)
    (hw : ∀ j i k x, wave j i k y x = P.wave j i k x)
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ N) (x : ℝ) :
    ‖planarPacketInterval coeff wave a b x y‖ ≤ P.variation x := by
  rw [planarPacketInterval_eq_partial_difference coeff wave P y hc hw]
  exact increment_le_cubicVariation (fun n => hilbertPartialBandSum P.packets n x) N a b hab hb

theorem planarPacketInterval_covariant_norm_le
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (P : LinePacketFamily N κ ι)
    (frequency : κ → ℝ) (y : ℝ) (hc : ∀ j i, coeff j i = P.coeff j i)
    (hw : ∀ j i k x, deriv (fun t => wave j i k t x) y -
      (frequency k:ℂ)*Complex.I*wave j i k y x = P.wave j i k x)
    (hd : ∀ j i k x t, DifferentiableAt ℝ (fun z => wave j i k z x) t)
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ N) (x : ℝ) :
    ‖covariantSignal frequency (fun k t => planarPacketInterval coeff wave a b x t k) y‖ ≤
      P.variation x := by
  rw [planarPacketInterval_covariant coeff wave frequency a b x y (fun j i k => hd j i k x)]
  exact planarPacketInterval_norm_le coeff _ P y hc hw a b hab hb x

theorem planarPacketInterval_scaled_covariant_norm_le
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (P : LinePacketFamily N κ ι)
    (frequency : κ → ℝ) (s y : ℝ) (hs : 0 ≤ s)
    (hc : ∀ j i, coeff j i = P.coeff j i)
    (hw : ∀ j i k x, (s:ℂ)*(deriv (fun t => wave j i k t x) y -
      (frequency k:ℂ)*Complex.I*wave j i k y x) = P.wave j i k x)
    (hd : ∀ j i k x t, DifferentiableAt ℝ (fun z => wave j i k z x) t)
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ N) (x : ℝ) :
    s*‖covariantSignal frequency (fun k t => planarPacketInterval coeff wave a b x t k) y‖ ≤
      P.variation x := by
  have h := planarPacketInterval_norm_le coeff
    (fun j i k t z => (s:ℂ)*(deriv (fun u => wave j i k u z) t -
      (frequency k:ℂ)*Complex.I*wave j i k t z)) P y hc hw a b hab hb x
  rw [planarPacketInterval_smul, ← planarPacketInterval_covariant coeff wave frequency a b x y
    (fun j i k => hd j i k x), norm_smul, Real.norm_eq_abs, abs_of_nonneg hs] at h
  exact h

end LipschitzHilbert

end

end OAI
