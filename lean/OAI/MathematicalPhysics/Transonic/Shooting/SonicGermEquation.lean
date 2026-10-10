import OAI.MathematicalPhysics.Transonic.Shooting.Family
import OAI.MathematicalPhysics.Transonic.Shooting.EulerCoordinates

namespace OAI

section
noncomputable section
namespace SepticProfile.SonicShooting
open Set SourceFamily
open scoped ContDiff

def Family.width (F : Family) : ℝ := 1-endRadius F.e

def Family.germArc (F : Family) (p : Parameter) (z : ℝ) : ℝ := F.germ.realFunction p (z-1)

lemma Family.width_pos (F : Family) : 0<F.width :=
  sub_pos.mpr (endRadius_bounds F.e_pos F.e_lt).2
lemma Family.width_small (F : Family) : F.width<1/100 := by
  have h := (endRadius_bounds F.e_pos F.e_lt).1
  unfold Family.width; linarith
lemma Family.width_eq (F : Family) : F.width=|SourceEuler.changeOfVariable (1/500) F.e| := by
  have h : SourceEuler.changeOfVariable (1/500) F.e<0 := by
    have hh := (endRadius_bounds F.e_pos F.e_lt).2
    unfold endRadius at hh
    linarith
  rw [abs_of_neg h]
  unfold Family.width endRadius
  ring
lemma Family.width_radius (F : Family) : F.width<F.germ.radius := by
  rw [F.width_eq]
  exact F.e_radius

lemma Family.germArc_analytic (F : Family) (p : Parameter) {z : ℝ}
    (hz : |z-1|<F.germ.radius) : AnalyticAt ℝ (F.germArc p) z := by
  exact (F.germ.real_analytic p hz).comp (f:=fun z:ℝ => z-1) (analyticAt_id.sub analyticAt_const)

lemma Family.germArc_equation (F : Family) (p : Parameter) {z : ℝ}
    (hz : |z-1|<F.germ.radius) :
    AxisBarriers.D (sig p) z (F.germArc p z)*deriv (F.germArc p) z=
      AxisBarriers.N (kap p) z (F.germArc p z) := by
  have hd := (F.germ.real_analytic p hz).differentiableAt.hasDerivAt.comp
    (h:=fun z:ℝ => z-1) z ((hasDerivAt_id z).sub_const 1)
  change HasDerivAt (F.germArc p) _ _ at hd
  have he := F.germ.real_equation p hz
  have hder : deriv (F.germArc p) z=deriv (F.germ.realFunction p) (z-1) := by
    simpa only [mul_one,Family.germArc,Function.comp_def] using hd.deriv
  dsimp [AxisBarriers.N,AxisBarriers.D,Family.germArc]
  rw [hder]
  simpa only [show 1+(z-1)=z by ring] using he

lemma Family.germArc_value (F : Family) (p : Parameter) : F.germArc p 1=1 := by
  simp [Family.germArc,UniformGerm.realFunction,F.germ.value]

lemma Family.germArc_slope (F : Family) (p : Parameter) :
    deriv (F.germArc p) 1=slp p := by
  have hd := (F.germ.real_analytic p (x:=0) (by simpa using F.germ.radius_pos)).differentiableAt.hasDerivAt
  have hd' := hd.comp_of_eq (h:=fun z:ℝ => z-1) 1 ((hasDerivAt_id (1:ℝ)).sub_const 1) (by ring)
  change HasDerivAt (F.germArc p) _ _ at hd'
  have he : deriv (F.germ.realFunction p) 0=slp p := by
    rw [F.germ.real_derivative p (by simpa using F.germ.radius_pos)]
    simpa using congrArg Complex.re (F.germ.slope p)
  simpa only [he,mul_one,Family.germArc,Function.comp_def] using hd'.deriv

lemma Family.germArc_split (F : Family) (p : Parameter) (z : ℝ) :
    F.germArc p z=1+(z-1)*(F.germ.V p ((z-1:ℝ):ℂ)).re := by
  unfold Family.germArc UniformGerm.realFunction
  rw [F.germ.split]
  simp only [Complex.add_re,Complex.one_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]

lemma Family.germArc_positive (F : Family) (p : Parameter) {z : ℝ}
    (hz : |z-1|≤F.width) : 0<F.germArc p z := by
  have hh := F.germ_window p (z-1) (by rwa [← F.width_eq])
  exact hh.1

lemma Family.germArc_below (F : Family) (p : Parameter) {z : ℝ}
    (hz : z ∈ Ico (endRadius F.e) 1) : F.germArc p z ∈ Ioo (0:ℝ) 1 := by
  have hwd : |z-1|≤F.width := by
    rw [abs_of_neg (by linarith [hz.2])]
    unfold Family.width
    linarith [hz.1]
  refine ⟨F.germArc_positive p hwd,?_⟩
  have hv := (F.germ_window p (z-1) (by rwa [← F.width_eq])).2
  rw [F.germArc_split]
  have hm : (z-1)*(F.germ.V p ((z-1:ℝ):ℂ)).re<0 :=
    mul_neg_of_neg_of_pos (sub_neg.mpr hz.2) (by linarith)
  linarith

lemma Family.germArc_above (F : Family) (p : Parameter) {z : ℝ}
    (hz : z ∈ Ioc (1:ℝ) (1+F.width)) : 1<F.germArc p z := by
  have hwd : |z-1|≤F.width := by
    rw [abs_of_pos (sub_pos.mpr hz.1)]
    linarith [hz.2]
  have hv := (F.germ_window p (z-1) (by rwa [← F.width_eq])).2
  rw [F.germArc_split]
  have hm : 0<(z-1)*(F.germ.V p ((z-1:ℝ):ℂ)).re :=
    mul_pos (sub_pos.mpr hz.1) (by linarith)
  linarith

end SepticProfile.SonicShooting

end
end

end OAI
