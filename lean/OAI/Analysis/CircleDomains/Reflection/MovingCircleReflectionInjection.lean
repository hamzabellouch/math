import OAI.Analysis.CircleDomains.Reflection.MovingCircleReflection

namespace OAI

/-! Injectivity of the actual unnormalized reflection in a moving circle. -/
open Set Function Filter Metric Complex
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma injOn_circleReflectionExtension {U:Set ℂ} {f:ℂ→ℂ} {c:ℂ} {r:ℝ}
    (hr:0<r) (hz:∀z∈U,z≠0) (hs:∀z∈U,unitCircleReflection z∈U)
    (hi:InjOn f (U∩{z | 1≤‖z‖}))
    (ho:∀z∈U,1<‖z‖ → r<‖f z-c‖)
    (hb:∀z∈U,‖z‖=1 → ‖f z-c‖=r) :
    InjOn (circleReflectionExtension c r f) U := by
  let g := fun z => (f z-c)/(r:ℂ)
  have hrc : (r:ℂ)≠0 := by exact_mod_cast hr.ne'
  have hgi : InjOn g (U∩{z | 1≤‖z‖}) := by
    intro z hzU w hwU he
    apply hi hzU hwU
    have he' := congrArg (fun v:ℂ => v*(r:ℂ)) he
    change (f z-c)/(r:ℂ)*(r:ℂ)=(f w-c)/(r:ℂ)*(r:ℂ) at he'
    rw [div_mul_cancel₀ _ hrc,div_mul_cancel₀ _ hrc] at he'
    exact sub_left_injective he'
  have hgo : ∀z∈U,1<‖z‖ → 1<‖g z‖ := by
    intro z hzU hzn
    change 1<‖(f z-c)/(r:ℂ)‖
    rw [normalized_circle_norm c hr]
    exact (one_lt_div hr).mpr (ho z hzU hzn)
  have hgb : ∀z∈U,‖z‖=1 → ‖g z‖=1 := by
    intro z hzU hzn
    change ‖(f z-c)/(r:ℂ)‖=1
    rw [normalized_circle_norm c hr,hb z hzU hzn,div_self hr.ne']
  intro z hzU w hwU he
  apply injOn_annularCircleReflect hz hs hgi hgo hgb hzU hwU
  change c+(r:ℂ)*annularCircleReflect g z=c+(r:ℂ)*annularCircleReflect g w at he
  exact mul_left_cancel₀ hrc (add_left_cancel he)

end CircleDomainRigidity

end

end OAI
