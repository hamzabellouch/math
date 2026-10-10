import OAI.Analysis.LipschitzHilbert.Fourier.DemodulatedVertical
import OAI.Analysis.LipschitzHilbert.Estimates.ThresholdSynthesis

namespace OAI

/-! Vertical differentiation commutes with the actual finite band sums.
The covariant derivative uses the same carrier in every band of a fixed
coordinate, so no carrier-frequency factor is lost. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

def scalarBandPartial {N : ℕ} (F : Fin N → ℝ → ℂ) (n : ℕ) (y : ℝ) : ℂ :=
  ∑ j, if j.val < n then F j y else 0

theorem scalarBandPartial_hasDerivAt {N : ℕ} (F : Fin N → ℝ → ℂ)
    (n : ℕ) (y : ℝ) (hF : ∀ j, DifferentiableAt ℝ (F j) y) :
    HasDerivAt (scalarBandPartial F n)
      (scalarBandPartial (fun j => deriv (F j)) n y) y := by
  apply HasDerivAt.fun_sum
  intro j _
  by_cases hj : j.val < n
  · simpa only [hj, ite_true] using (hF j).hasDerivAt
  · simpa only [hj, ite_false] using (hasDerivAt_const y (0:ℂ))

theorem scalarBandPartial_covariant {N : ℕ} (F : Fin N → ℝ → ℂ)
    (n : ℕ) (frequency y : ℝ) (hF : ∀ j, DifferentiableAt ℝ (F j) y) :
    deriv (scalarBandPartial F n) y - (frequency:ℂ)*Complex.I*scalarBandPartial F n y =
      scalarBandPartial (fun j t => deriv (F j) t-(frequency:ℂ)*Complex.I*F j t) n y := by
  rw [(scalarBandPartial_hasDerivAt F n y hF).deriv]
  unfold scalarBandPartial
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

def bandIntervalSignal {N : ℕ} {κ : Type*} (F : Fin N → κ → ℝ → ℂ)
    (a b : ℕ) (y : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => scalarBandPartial (fun j => F j k) b y -
    scalarBandPartial (fun j => F j k) a y)

theorem bandIntervalSignal_covariant {N : ℕ} {κ : Type*} [Fintype κ]
    (F : Fin N → κ → ℝ → ℂ) (a b : ℕ) (frequency : κ → ℝ) (y : ℝ)
    (hF : ∀ j k, DifferentiableAt ℝ (F j k) y) :
    covariantSignal frequency (fun k t => bandIntervalSignal F a b t k) y =
      bandIntervalSignal (fun j k t => deriv (F j k) t-
        (frequency k:ℂ)*Complex.I*F j k t) a b y := by
  ext k
  change deriv (fun t => scalarBandPartial (fun j => F j k) b t -
      scalarBandPartial (fun j => F j k) a t) y -
      (frequency k:ℂ)*Complex.I*(scalarBandPartial (fun j => F j k) b y -
        scalarBandPartial (fun j => F j k) a y) = _
  have hd := (scalarBandPartial_hasDerivAt (fun j => F j k) b y (fun j => hF j k)).sub
    (scalarBandPartial_hasDerivAt (fun j => F j k) a y (fun j => hF j k))
  change HasDerivAt (fun t => scalarBandPartial (fun j => F j k) b t -
    scalarBandPartial (fun j => F j k) a t) _ y at hd
  rw [hd.deriv]
  have hb := scalarBandPartial_covariant (fun j => F j k) b (frequency k) y (fun j => hF j k)
  have ha := scalarBandPartial_covariant (fun j => F j k) a (frequency k) y (fun j => hF j k)
  change _ = scalarBandPartial _ b y - scalarBandPartial _ a y
  rw [← hb, ← ha]
  rw [(scalarBandPartial_hasDerivAt (fun j => F j k) b y (fun j => hF j k)).deriv,
    (scalarBandPartial_hasDerivAt (fun j => F j k) a y (fun j => hF j k)).deriv]
  ring

theorem bandIntervalSignal_norm_le {N : ℕ} {κ : Type*} [Fintype κ]
    (F : Fin N → κ → ℝ → ℂ) (a b : ℕ) (hab : a ≤ b) (hb : b ≤ N) (y : ℝ) :
    ‖bandIntervalSignal F a b y‖ ≤ cubicVariation
      (fun n => (WithLp.toLp 2 (fun k => scalarBandPartial (fun j => F j k) n y) :
        EuclideanSpace ℂ κ)) N := by
  have heq : bandIntervalSignal F a b y =
      WithLp.toLp 2 (fun k => scalarBandPartial (fun j => F j k) b y) -
      WithLp.toLp 2 (fun k => scalarBandPartial (fun j => F j k) a y) := by
    ext k
    rfl
  rw [heq]
  exact increment_le_cubicVariation (fun n => (WithLp.toLp 2
    (fun k => scalarBandPartial (fun j => F j k) n y) : EuclideanSpace ℂ κ)) N a b hab hb

end LipschitzHilbert

end

end OAI
