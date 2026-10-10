import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialMellinIdentity

namespace OAI

/-! A concrete nonnegative radial test supported in [2,4]. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaRadialTent (v : ℝ) : ℝ := max 0 (1-|v-3|)

lemma cubicThetaRadialTent_nonneg (v : ℝ) : 0≤cubicThetaRadialTent v :=
  le_max_left _ _

lemma cubicThetaRadialTent_continuous : Continuous cubicThetaRadialTent := by
  unfold cubicThetaRadialTent
  fun_prop

lemma cubicThetaRadialTent_compact : HasCompactSupport cubicThetaRadialTent := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (2:ℝ) 4))
  intro v hv
  have hp : 0<1-|v-3| := by
    by_contra hn
    exact hv (max_eq_left (le_of_not_gt hn))
  have h := abs_lt.mp (show |v-3|<1 by linarith)
  constructor <;> linarith

def cubicThetaRadialTestWeight : C_c(ℝ,ℂ) where
  toFun v := (cubicThetaRadialTent v:ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp cubicThetaRadialTent_continuous
  hasCompactSupport' := cubicThetaRadialTent_compact.comp_left
    (g:=fun x : ℝ => (x:ℂ)) (by simp)

lemma cubicThetaRadialTestWeight_apply (v : ℝ) :
    cubicThetaRadialTestWeight v=(cubicThetaRadialTent v:ℂ) := rfl

lemma cubicThetaPositive_setIntegral {a x : ℝ} {f : ℝ → ℝ}
    (hc : ContinuousOn f (Ioi a)) (hi : IntegrableOn f (Ioi a))
    (hn : ∀ t∈Ioi a, 0≤f t) (hx : a<x) (hp : 0<f x) :
    0<∫ t in Ioi a, f t := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_mem measurableSet_Ioi).mono (fun t ht => hn t ht)) hi).mpr
  have ho := hc.isOpen_inter_preimage isOpen_Ioi (isOpen_Ioi : IsOpen (Ioi (0:ℝ)))
  have hpos := ho.measure_pos (μ:=volume) ⟨x,hx,hp⟩
  apply lt_of_lt_of_le hpos
  apply measure_mono
  intro t ht
  exact ⟨ne_of_gt ht.2,ht.1⟩

end CubicFirstMoment

end

end OAI
