import OAI.Analysis.LipschitzHilbert.Estimates.TopLatticeDecay
import OAI.Analysis.LipschitzHilbert.Estimates.TopFamilyException
import OAI.Analysis.LipschitzHilbert.Estimates.SlicedIntegral

namespace OAI

/-! Transfer the global lattice neighborhood bound to physical slope
coordinates and the exact top weight, with an exponential area bound. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert

def topAreaPrefactor (K : ℝ) : ℝ := 4*K^2*(4*Real.pi)^2

theorem topAreaPrefactor_pos (K : ℝ) (hK : 0 < K) : 0 < topAreaPrefactor K := by
  unfold topAreaPrefactor
  positivity

theorem slope_top_neighborhood {ι E : Type*} [NormedAddCommGroup E]
    (T : SlopeBox) (K A J L : ℝ) (d : ℕ) (hK : 0 < K) (hA : 0 ≤ A)
    (F : ι → ℝ → ℝ → E)
    (hlocal : ∀ n : ℕ, 1 ≤ n → ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
      (volume.prod volume) bad ≤ (1/4:ℝ≥0∞)^n*
        (2*ENNReal.ofReal (K*T.length)*ENNReal.ofReal (2*(K*T.width)))*
          ENNReal.ofReal ((4*Real.pi)^2) ∧
      ∀ i x y v, |v| ≤ K*T.width → (x,y) ∉ bad →
        ‖F i x (y+v)‖ ≤ A*(n:ℝ)*
          boxVariationWeight (packetBoxIndex T.x (T.y-T.slope*T.x)
            (K*T.length) (K*T.width) x y)^(8*d)) :
    let n := topExceptionMoment (topAreaPrefactor K) J L
    ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
      (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*T.area) ∧
      ∀ i z v, |v| ≤ K*T.width → z ∉ bad →
        ‖F i z.1 ((z.2-T.slope*z.1)+v)‖ ≤
          (A*(n:ℝ)*5^(8*d))*(T.weight K (d:ℝ) z)^8 := by
  dsimp only
  let n := topExceptionMoment (topAreaPrefactor K) J L
  obtain ⟨bad,hbad,harea,hpoint⟩ := hlocal n (topExceptionMoment_pos _ _ _)
  let physical := slopeShear T.slope '' bad
  have hphysical : MeasurableSet physical := (slopeShear T.slope).measurableSet_image.mpr hbad
  have hmeasure : (volume.prod volume) physical = (volume.prod volume) bad := by
    have h := (slopeShear_measurePreserving T.slope).measure_preimage_equiv physical
    rw [show (slopeShear T.slope) ⁻¹' physical = bad from
      Equiv.preimage_image _ _] at h
    exact h.symm
  have hfactor :
      (2*ENNReal.ofReal (K*T.length)*ENNReal.ofReal (2*(K*T.width)))*
        ENNReal.ofReal ((4*Real.pi)^2) =
      ENNReal.ofReal (topAreaPrefactor K)*ENNReal.ofReal T.area := by
    have hl := T.length_pos
    have hw := T.width_pos
    have htwo : (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) := by norm_num
    rw [htwo, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*(K*T.length)),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*(K*T.length)*(2*(K*T.width))),
      ← ENNReal.ofReal_mul (topAreaPrefactor_pos K hK).le]
    congr 1
    unfold topAreaPrefactor SlopeBox.area
    ring
  have hexp : (1/4:ℝ≥0∞)^n*ENNReal.ofReal (topAreaPrefactor K) ≤
      ENNReal.ofReal (Real.exp (-J*L)) := by
    have h := ENNReal.ofReal_le_ofReal
      (prefactor_quarter_successor_bound (topAreaPrefactor K) (J*L) (topAreaPrefactor_pos K hK))
    rw [ENNReal.ofReal_mul (topAreaPrefactor_pos K hK).le,
      ENNReal.ofReal_pow (by norm_num)] at h
    have hq : ENNReal.ofReal (1/4:ℝ) = (1/4:ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    rw [hq, show -(J*L) = -J*L by ring] at h
    simpa only [n, topExceptionMoment, mul_comm] using h
  refine ⟨physical,hphysical,?_,?_⟩
  · rw [hmeasure]
    rw [mul_assoc, hfactor] at harea
    calc
      _ ≤ ((1/4:ℝ≥0∞)^n*ENNReal.ofReal (topAreaPrefactor K))*ENNReal.ofReal T.area := by
        simpa only [mul_assoc] using harea
      _ ≤ ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal T.area := mul_le_mul' hexp le_rfl
      _ = _ := (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
  · intro i z v hv hout
    have hcoord : (z.1,z.2-T.slope*z.1) ∉ bad := by
      intro hin
      apply hout
      refine ⟨(z.1,z.2-T.slope*z.1),hin,?_⟩
      simp [slopeShear]
    have hp := hpoint i z.1 (z.2-T.slope*z.1) v hv hcoord
    have hdecay := T.lattice_decay_le_weight K hK d z
    exact hp.trans (by
      have h := mul_le_mul_of_nonneg_left hdecay (mul_nonneg hA (Nat.cast_nonneg n))
      simpa only [mul_assoc] using h)

end LipschitzHilbert

end

end OAI
