import OAI.Analysis.LipschitzHilbert.Packets.PlanarPacketDifferentiation
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! Joint continuity and local square integrability for actual packet
interval sums and their covariant derivatives. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

omit [Fintype κ] in
theorem planarPacketBand_continuous (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ)
    (hw : ∀ j i k, Continuous (fun z : ℝ × ℝ => wave j i k z.1 z.2))
    (j : Fin N) (k : κ) :
    Continuous (fun z : ℝ × ℝ => planarPacketBand coeff wave j k z.2 z.1) := by
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (hw j i k))

omit [Fintype κ] in
theorem planarPacketPartial_continuous (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ)
    (hw : ∀ j i k, Continuous (fun z : ℝ × ℝ => wave j i k z.1 z.2)) (n : ℕ) :
    Continuous (fun z : ℝ × ℝ => (WithLp.toLp 2 (fun k =>
      scalarBandPartial (fun j => planarPacketBand coeff wave j k z.2) n z.1) :
        EuclideanSpace ℂ κ)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
  apply continuous_pi
  intro k
  apply continuous_finsetSum
  intro j _
  by_cases hj : j.val < n
  · simpa only [hj, ite_true] using planarPacketBand_continuous coeff wave hw j k
  · simpa only [hj, ite_false] using (continuous_const : Continuous (fun _ : ℝ × ℝ => (0:ℂ)))

theorem planarPacketInterval_continuous (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ)
    (hw : ∀ j i k, Continuous (fun z : ℝ × ℝ => wave j i k z.1 z.2)) (a b : ℕ) :
    Continuous (fun z : ℝ × ℝ => planarPacketInterval coeff wave a b z.2 z.1) := by
  convert (planarPacketPartial_continuous coeff wave hw b).sub
    (planarPacketPartial_continuous coeff wave hw a) using 1
  ext z k
  rfl

theorem lineFamily_variation_continuous (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (P : ℝ → LinePacketFamily N κ ι)
    (hw : ∀ j i k, Continuous (fun z : ℝ × ℝ => wave j i k z.1 z.2))
    (hcoeff : ∀ y j i, coeff j i = (P y).coeff j i)
    (hwave : ∀ y j i k x, wave j i k y x = (P y).wave j i k x) :
    Continuous (fun z : ℝ × ℝ => (P z.1).variation z.2) := by
  have heq (z : ℝ × ℝ) (n : ℕ) :
      hilbertPartialBandSum (P z.1).packets n z.2 =
        WithLp.toLp 2 (fun k => scalarBandPartial
          (fun j => planarPacketBand coeff wave j k z.2) n z.1) := by
    ext k
    simp only [hilbertPartialBandSum, WithLp.ofLp_toLp, partialBandSum,
      scalarBandPartial, LinePacketFamily.packets, packetSynthesis_apply,
      planarPacketBand, hcoeff z.1, hwave z.1]
  simp_rw [LinePacketFamily.variation, heq]
  exact continuous_cubicVariation _ (planarPacketPartial_continuous coeff wave hw) N

theorem planarPacketInterval_memLp (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ)
    (hw : ∀ j i k, Continuous (fun z : ℝ × ℝ => wave j i k z.1 z.2))
    (a b : ℕ) (x lower upper : ℝ) :
    MemLp (planarPacketInterval coeff wave a b x) 2 (volume.restrict (Icc lower upper)) := by
  have hplane := planarPacketInterval_continuous coeff wave hw a b
  have hc := hplane.comp (f := fun y : ℝ => (y,x))
    (continuous_id.prodMk continuous_const)
  change Continuous (planarPacketInterval coeff wave a b x) at hc
  exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    (hc.norm.pow 2).continuousOn.integrableOn_Icc

omit [Fintype κ] in
theorem planarPacketInterval_component_differentiable
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (a b : ℕ) (x y : ℝ) (k : κ)
    (hd : ∀ j i, DifferentiableAt ℝ (fun t => wave j i k t x) y) :
    DifferentiableAt ℝ (fun t => planarPacketInterval coeff wave a b x t k) y := by
  change DifferentiableAt ℝ (fun t =>
    scalarBandPartial (fun j => planarPacketBand coeff wave j k x) b t -
    scalarBandPartial (fun j => planarPacketBand coeff wave j k x) a t) y
  have hb (n : ℕ) := (scalarBandPartial_hasDerivAt
    (fun j => planarPacketBand coeff wave j k x) n y (fun j =>
      (planarPacketBand_hasDerivAt coeff wave j k x y (hd j)).differentiableAt)).differentiableAt
  exact (hb b).sub (hb a)

theorem planarPacketInterval_covariant_memLp
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (frequency : κ → ℝ)
    (hd : ∀ j i k x t, DifferentiableAt ℝ (fun z => wave j i k z x) t)
    (hD : ∀ j i k, Continuous (fun z : ℝ × ℝ =>
      deriv (fun t => wave j i k t z.2) z.1 - (frequency k:ℂ)*Complex.I*wave j i k z.1 z.2))
    (a b : ℕ) (x lower upper : ℝ) :
    MemLp (covariantSignal frequency (fun k t => planarPacketInterval coeff wave a b x t k))
      2 (volume.restrict (Icc lower upper)) := by
  let D := fun j i k t s => deriv (fun z => wave j i k z s) t -
    (frequency k:ℂ)*Complex.I*wave j i k t s
  have heq : covariantSignal frequency (fun k t => planarPacketInterval coeff wave a b x t k) =
      fun y => planarPacketInterval coeff D a b x y := by
    funext y
    exact planarPacketInterval_covariant coeff wave frequency a b x y (fun j i k => hd j i k x)
  have hDc : ∀ j i k, Continuous (fun z : ℝ × ℝ => D j i k z.1 z.2) := hD
  rw [heq]
  exact planarPacketInterval_memLp coeff D hDc a b x lower upper

end LipschitzHilbert

end

end OAI
