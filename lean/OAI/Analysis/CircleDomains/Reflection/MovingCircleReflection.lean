import OAI.Analysis.CircleDomains.Reflection.AnnularReflectionInjection

namespace OAI

/-! Reflection into a moving target circle. The unnormalized bound does
not divide by its radius, so it remains useful along degenerating disks. -/
open Set Function Filter Metric Complex
open scoped Topology ComplexConjugate
noncomputable section
namespace CircleDomainRigidity

def circleReflectionExtension (c:ℂ) (r:ℝ) (f:ℂ → ℂ) (z:ℂ) : ℂ :=
  c+(r:ℂ)*annularCircleReflect (fun w => (f w-c)/(r:ℂ)) z

lemma circleReflectionExtension_outer {c z:ℂ} {r:ℝ} {f:ℂ → ℂ}
    (hr:0<r) (hz:1≤‖z‖) : circleReflectionExtension c r f z=f z := by
  have hrc : (r:ℂ)≠0 := by exact_mod_cast hr.ne'
  rw [circleReflectionExtension,annularCircleReflect,ite_eq_left hz]
  field_simp
  ring

lemma normalized_circle_norm (c:ℂ) {r:ℝ} (hr:0<r) (w:ℂ) :
    ‖(w-c)/(r:ℂ)‖=‖w-c‖/r := by
  simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]

lemma circleReflectionExtension_differentiableOn {U:Set ℂ} {f:ℂ → ℂ} {c:ℂ} {r:ℝ}
    (hr:0<r) (hU:IsOpen U) (hz:∀z∈U,z≠0)
    (hs:∀z∈U,unitCircleReflection z∈U)
    (hc:ContinuousOn f (U∩{z | 1≤‖z‖}))
    (hd:∀z∈U,1<‖z‖ → DifferentiableAt ℂ f z)
    (ho:∀z∈U,1≤‖z‖ → r≤‖f z-c‖)
    (hb:∀z∈U,‖z‖=1 → ‖f z-c‖=r) :
    DifferentiableOn ℂ (circleReflectionExtension c r f) U := by
  let g := fun z => (f z-c)/(r:ℂ)
  have hg : ContinuousOn g (U∩{z | 1≤‖z‖}) := (hc.sub continuousOn_const).div_const _
  have hgd : ∀z∈U,1<‖z‖ → DifferentiableAt ℂ g z :=
    fun z hzU hzn => ((hd z hzU hzn).sub_const c).div_const _
  have hgn : ∀z∈U,1≤‖z‖ → g z≠0 := by
    intro z hzU hzn
    apply norm_pos_iff.mp
    change 0<‖(f z-c)/(r:ℂ)‖
    rw [normalized_circle_norm c hr]
    exact div_pos (hr.trans_le (ho z hzU hzn)) hr
  have hgb : ∀z∈U,‖z‖=1 → ‖g z‖=1 := by
    intro z hzU hzn
    change ‖(f z-c)/(r:ℂ)‖=1
    rw [normalized_circle_norm c hr,hb z hzU hzn,div_self hr.ne']
  exact (differentiableOn_const c).add ((differentiableOn_const (r:ℂ)).mul
    (differentiableOn_annularCircleReflect hU hz hs hg hgd hgn hgb))

lemma circleReflectionExtension_norm_le {U:Set ℂ} {f:ℂ → ℂ} {c:ℂ} {r M:ℝ}
    (hr:0<r) (hz:∀z∈U,z≠0) (hs:∀z∈U,unitCircleReflection z∈U)
    (hM:‖c‖+r≤M)
    (hf:∀z∈U,1≤‖z‖ → r≤‖f z-c‖ ∧ ‖f z‖≤M)
    {z:ℂ} (hzU:z∈U) : ‖circleReflectionExtension c r f z‖≤M := by
  by_cases hzo : 1≤‖z‖
  · rw [circleReflectionExtension_outer hr hzo]
    exact (hf z hzU hzo).2
  · let g := fun w => (f w-c)/(r:ℂ)
    have hge : 1≤‖g (unitCircleReflection z)‖ := by
      change 1≤‖(f (unitCircleReflection z)-c)/(r:ℂ)‖
      rw [normalized_circle_norm c hr]
      exact (one_le_div hr).mpr
        (hf _ (hs z hzU) (unitCircleReflection_outer (hz z hzU) (lt_of_not_ge hzo).le)).1
    have hinner : ‖annularCircleReflect g z‖≤1 := by
      rw [annularCircleReflect,ite_eq_right hzo,unitCircleReflection_norm]
      exact (inv_le_one₀ (zero_lt_one.trans_le hge)).mpr hge
    change ‖c+(r:ℂ)*annularCircleReflect g z‖≤M
    calc
      _ ≤ ‖c‖+‖(r:ℂ)*annularCircleReflect g z‖ := norm_add_le _ _
      _ = ‖c‖+r*‖annularCircleReflect g z‖ := by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
      _ ≤ ‖c‖+r := by nlinarith
      _ ≤ M := hM

end CircleDomainRigidity

end

end OAI
