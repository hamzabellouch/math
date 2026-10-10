import OAI.Analysis.LipschitzHilbert.Fourier.SchwartzConjugation
import OAI.Analysis.LipschitzHilbert.Estimates.ShortL2Operator

namespace OAI

/-! Conjugation is an isometric real-linear involution of complex L2. -/
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
namespace LipschitzHilbert
variable {X : Type*} [MeasurableSpace X]

def l2Conj (mu : Measure X) : Lp ℂ 2 mu →L[ℝ] Lp ℂ 2 mu :=
  Complex.conjCLE.toContinuousLinearMap.compLpL 2 mu

theorem l2Conj_coe (mu : Measure X) (f : Lp ℂ 2 mu) :
    l2Conj mu f=ᵐ[mu] fun x => conj (f x) :=
  Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL f

theorem l2Conj_norm (mu : Measure X) (f : Lp ℂ 2 mu) : ‖l2Conj mu f‖=‖f‖ := by
  rw [Lp.norm_def,Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.memLp _).aestronglyMeasurable (Lp.memLp _).aestronglyMeasurable
  filter_upwards [l2Conj_coe mu f] with x hx
  rw [hx,Complex.norm_conj]

theorem l2Conj_involutive (mu : Measure X) (f : Lp ℂ 2 mu) : l2Conj mu (l2Conj mu f)=f := by
  apply Lp.ext
  filter_upwards [l2Conj_coe mu (l2Conj mu f),l2Conj_coe mu f] with x hx hx'
  rw [hx,hx']
  exact star_star (f x)

theorem l2Conj_onSchwartz (f : SchwartzMap (ℝ×ℝ) ℂ) :
    l2Conj PacketRepresentation.planeMeasure (f.toLp 2 PacketRepresentation.planeMeasure)=
      (schwartzConj f).toLp 2 PacketRepresentation.planeMeasure := by
  apply Lp.ext
  filter_upwards [l2Conj_coe PacketRepresentation.planeMeasure (f.toLp 2 PacketRepresentation.planeMeasure),
    (f.memLp 2 PacketRepresentation.planeMeasure).coeFn_toLp,
    ((schwartzConj f).memLp 2 PacketRepresentation.planeMeasure).coeFn_toLp] with x hx hfx hcx
  change (f.toLp 2 PacketRepresentation.planeMeasure) x=f x at hfx
  change ((schwartzConj f).toLp 2 PacketRepresentation.planeMeasure) x=schwartzConj f x at hcx
  rw [hx,hfx,hcx,schwartzConj_apply]

theorem l2_maps_eq_onSchwartz
    (T S : Lp ℂ 2 PacketRepresentation.planeMeasure →L[ℝ] Lp ℂ 2 PacketRepresentation.planeMeasure)
    (h : ∀ f : SchwartzMap (ℝ×ℝ) ℂ,
      T (f.toLp 2 PacketRepresentation.planeMeasure)=S (f.toLp 2 PacketRepresentation.planeMeasure)) : T=S := by
  apply DFunLike.coe_injective
  apply T.continuous.ext_on (SchwartzMap.denseRange_toLpCLM (F:=ℂ)
    (by norm_num : (2:ℝ≥0∞)≠⊤)) S.continuous
  rintro _ ⟨f,rfl⟩
  exact h f

end LipschitzHilbert

end

end OAI
