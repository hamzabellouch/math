import Mathlib
import OAI.Geometry.PrescribedPotential.DeterminantOrder
import OAI.Geometry.PrescribedPotential.GlobalSobolev
import OAI.Geometry.PrescribedPotential.VolumePath

namespace OAI

/-! Volume Normalization. -/

section

 

noncomputable section
open Matrix Filter Set Topology
open scoped ComplexOrder Classical ContDiff
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
namespace SmoothRealFunction

lemma negative_hessian_posSemidef_at_globalMax (φ : SmoothRealFunction A) {x : X}
    (hx : ∀ y, φ.value y ≤ φ.value x) (i : Fin A.count) (hi : x ∈ (A.chart i).source) :
    (-φ.hessian i (A.chart i x)).PosSemidef := by
  have hs := (φ.smooth i).contDiffAt
    ((A.chart i).open_target.mem_nhds ((A.chart i).mapsTo hi))
  have hm : IsLocalMax (φ.localExpression i) (A.chart i x) := by
    apply Filter.Eventually.of_forall
    intro z
    simpa [localExpression, (A.chart i).left_inv hi] using hx ((A.chart i).symm z)
  exact EllipticKernel.negative_potentialMatrix_posSemidef_at_localMax hs hm

lemma hessian_posSemidef_at_globalMin (φ : SmoothRealFunction A) {x : X}
    (hx : ∀ y, φ.value x ≤ φ.value y) (i : Fin A.count) (hi : x ∈ (A.chart i).source) :
    (φ.hessian i (A.chart i x)).PosSemidef := by
  have hm : ∀ y, (φ.realSMul (-1)).value y ≤ (φ.realSMul (-1)).value x := by
    intro y
    change -1 * φ.value y ≤ -1 * φ.value x
    linarith [hx y]
  have hp := (φ.realSMul (-1)).negative_hessian_posSemidef_at_globalMax hm i hi
  simpa [hessian_realSMul] using hp
end SmoothRealFunction
namespace KaehlerMetric

lemma logRatio_deform_nonpos_at_globalMax (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (hp : g.PositivePotential φ) {x : X} (hx : ∀ y, φ.value y ≤ φ.value x) :
    (g.logRatio (g.deform φ hp)).value x ≤ 0 := by
  obtain ⟨i,hi⟩ := A.covers x
  have hz := (A.chart i).mapsTo hi
  have hd : (g.matrix i (A.chart i x) + φ.hessian i (A.chart i x)).det.re ≤
      (g.matrix i (A.chart i x)).det.re := by
    apply MongeAmpere.det_re_mono (hp i _ hz)
    simpa only [sub_add_cancel_left] using φ.negative_hessian_posSemidef_at_globalMax hx i hi
  change g.logRatioValue (g.deform φ hp) x ≤ 0
  rw [g.logRatioValue_local _ i hi]
  apply sub_nonpos.mpr
  apply Real.log_le_log ((g.deform φ hp).volumeCoefficient_pos i hz)
  exact hd

lemma logRatio_deform_nonneg_at_globalMin (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (hp : g.PositivePotential φ) {x : X} (hx : ∀ y, φ.value x ≤ φ.value y) :
    0 ≤ (g.logRatio (g.deform φ hp)).value x := by
  obtain ⟨i,hi⟩ := A.covers x
  have hz := (A.chart i).mapsTo hi
  have hd := MongeAmpere.det_re_add_posSemidef _ _ (g.positive i _ hz)
    (φ.hessian_posSemidef_at_globalMin hx i hi)
  change 0 ≤ g.logRatioValue (g.deform φ hp) x
  rw [g.logRatioValue_local _ i hi]
  apply sub_nonneg.mpr
  exact Real.log_le_log (g.volumeCoefficient_pos i hz) hd
end KaehlerMetric

 

theorem volumePath_scalar_bound [CompactSpace X] [Nonempty X]
    (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    {t b : ℝ} {φ : SmoothRealFunction A} (ht : t ∈ Icc 0 1)
    (hsol : SolvesVolumePath g h t φ b) :
    |b| ≤ ‖(⟨(prescribedForcing g h).value, (prescribedForcing g h).continuous⟩ : C(X,ℝ))‖ := by
  let F : C(X,ℝ) := ⟨(prescribedForcing g h).value, (prescribedForcing g h).continuous⟩
  obtain ⟨hp,he⟩ := hsol
  have hbound (x : X) : |t * (prescribedForcing g h).value x| ≤ ‖F‖ := by
    rw [abs_mul, abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)).trans (by
      simpa [F, Real.norm_eq_abs] using F.norm_coe_le_norm x)
  obtain ⟨x,_,hx⟩ := isCompact_univ.exists_isMaxOn univ_nonempty φ.continuous.continuousOn
  obtain ⟨y,_,hy⟩ := isCompact_univ.exists_isMinOn univ_nonempty φ.continuous.continuousOn
  have hmax := g.logRatio_deform_nonpos_at_globalMax φ hp (fun z => hx (mem_univ z))
  have hmin := g.logRatio_deform_nonneg_at_globalMin φ hp (fun z => hy (mem_univ z))
  rw [he x] at hmax
  rw [he y] at hmin
  obtain ⟨hlx,hux⟩ := abs_le.mp (hbound x)
  obtain ⟨hly,huy⟩ := abs_le.mp (hbound y)
  apply abs_le.mpr
  constructor <;> linarith
end Anticanonical.SourceSmooth

end
end

end OAI
