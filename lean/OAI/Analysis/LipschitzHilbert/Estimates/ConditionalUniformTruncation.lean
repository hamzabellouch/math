import OAI.Analysis.LipschitzHilbert.Geometry.ConditionalUnitDirection
import OAI.Analysis.LipschitzHilbert.Geometry.DirectionDilation

namespace OAI

/-! The uniform sharp-truncation estimate at reciprocal Lipschitz scale.
The explicit radius is deliberately smaller than the allowed absolute
radius; the operator constant is independent of both cutoffs and the field. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LipschitzHilbert
open PacketRepresentation

theorem conditional_uniform_truncation (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (hReassembly : BandToFullInput) :
    ∃ C : ℝ, 0<C ∧ ∀ K : ℝ≥0, 0<K → ∀ epsilon R : ℝ,
      0<epsilon → epsilon≤R → R≤1/(1000000*(K:ℝ)) →
      ∀ v : Plane → Plane, LipschitzWith K v → (∀ x, ‖v x‖=1) →
      ∀ f : SchwartzMap Plane ℂ,
        eLpNorm (shortTransform v epsilon R f) 2 volume≤ENNReal.ofReal (C*‖f.toLp 2 volume‖) := by
  obtain ⟨C,hC,hbound⟩ := conditional_unit_small_lipschitz hVariation hLL hH hReassembly
  refine ⟨C,hC,?_⟩
  intro K hK epsilon R he heR hR v hv hunit f
  have hKr : 0<(K:ℝ) := hK
  let L : ℝ := 100*(K:ℝ)
  have hL : 0<L := by positivity
  have hLR : L*R≤1/10000 := by
    have h := (le_div_iff₀ (by positivity : 0<1000000*(K:ℝ))).mp hR
    dsimp only [L]
    nlinarith
  have hbd := hbound (L*epsilon) (L*R) (mul_pos hL he)
    (mul_le_mul_of_nonneg_left heR hL.le) hLR (rescaleField L v)
    (rescaleField_lipschitz_small hK hv) (rescaleField_unit v hunit)
    (rescaleSchwartz L hL.ne' f)
  rw [shortTransform_dilation L hL.ne' v epsilon R f] at hbd
  have hfcont : Continuous (shortTransform v epsilon R f) :=
    shortTransform_continuous hv.continuous f.continuous he heR
  have hmg : MemLp (fun x => shortTransform v epsilon R f (L⁻¹ • x)) 2 volume :=
    hbd.trans_lt (by simp)
  have hmf : MemLp (shortTransform v epsilon R f) 2 volume :=
    (memLp_two_comp_smul_iff _ hfcont L⁻¹ (inv_ne_zero hL.ne')).mp hmg
  have hs := toLp_norm_comp_smul _ hfcont hmf L⁻¹ (inv_pos.mpr hL)
  rw [inv_inv] at hs
  have hn := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hbd
  rw [ENNReal.toReal_ofReal (mul_nonneg hC.le (norm_nonneg _)),rescaleSchwartz_norm L hL f] at hn
  have hn' : ‖hmg.toLp (fun x => shortTransform v epsilon R f (L⁻¹ • x))‖≤
      C*(L*‖f.toLp 2 volume‖) := by
    rw [Lp.norm_toLp]
    exact hn
  rw [hs] at hn'
  have hnorm : ‖hmf.toLp (shortTransform v epsilon R f)‖≤C*‖f.toLp 2 volume‖ := by
    nlinarith
  rw [←Lp.enorm_toLp hmf,←ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hnorm

end LipschitzHilbert

end

end OAI
