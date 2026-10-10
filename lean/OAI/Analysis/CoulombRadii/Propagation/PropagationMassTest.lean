import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.PropagationDatumRegularity
import OAI.Analysis.CoulombRadii.ThomasFermi.CountTestFlux

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma PropagationInvariant.mass_test {B C r Z L : ℝ} {u μ p : Position → ℝ}
    (d : PropagationInvariant B C r Z L u μ p) (hr : 0<r)
    (hμ : Integrable μ) (hp : Integrable p)
    {φ : Position → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφn : ∀ x,0≤φ x) (hone : ∀ x,‖x‖≤r → φ x=1) :
    (∫ x,cutoffReaction r (fun y => Z*coulombKernel y+u y) x*φ x) ≤
      4*Real.pi*(Z-(∫ x in Metric.ball 0 r,μ x)+(∫ x,p x))+
        (∫ x,(Z*coulombKernel x+u x)*coordinateLaplacian φ x) := by
  let m : Position → ℝ := (Metric.ball (0:Position) r).indicator μ
  have him : Integrable m := hμ.indicator measurableSet_ball
  have hmp : ∀ x,m x*φ x=m x := by
    intro x
    by_cases hx : ‖x‖<r
    · simp only [m,Set.indicator_of_mem (show x∈Metric.ball (0:Position) r by simpa using hx),hone x hx.le,mul_one]
    · simp [m,show x∉Metric.ball (0:Position) r by simpa using hx]
  have hpp : ∀ x,p x*φ x=p x := by
    intro x
    by_cases hx : ‖x‖<r
    · rw [hone x hx.le,mul_one]
    · rw [d.error_support x (le_of_not_gt hx),zero_mul]
  have hic := integrable_mul_test_on
    ((cutoffReaction_offset_locallyIntegrable (Z:=Z) hr d.continuous_offset).locallyIntegrableOn univ)
    hφ.continuous hc (subset_univ _)
  have he : (fun x => propagationRHS r ‖x‖ (μ x) (p x) (Z*coulombKernel x+u x)*φ x)=
      fun x => 4*Real.pi*(m x-p x)+cutoffReaction r (fun y => Z*coulombKernel y+u y) x*φ x := by
    funext x
    rw [propagationRHS_eq,add_mul,propagationCoreSource,mul_assoc,sub_mul,hpp]
    have hh : (if ‖x‖<r then μ x else 0)=m x := by
      simp only [m,Set.indicator,Metric.mem_ball,dist_zero_right]
    rw [hh,hmp]
  have hicore : Integrable (fun x => 4*Real.pi*(m x-p x)) := (him.sub hp).const_mul (4*Real.pi)
  have H := d.weak φ hφ hc (subset_univ _) hφn
  rw [hone 0 (by simpa using hr.le),he,
    integral_add hicore hic,
    integral_const_mul,integral_sub him hp] at H
  have hm : (∫ x,m x)=∫ x in Metric.ball 0 r,μ x := integral_indicator measurableSet_ball
  rw [hm] at H
  linarith only [H]

end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma propagation_shell_volume {r : ℝ} (hr : 0<r) :
    (volume : Measure Position).real (Metric.ball 0 (2*r) \ Metric.ball 0 r)=
      (28*Real.pi/3)*r^3 := by
  rw [measureReal_sdiff (Metric.ball_subset_ball (by linarith)) measurableSet_ball,
    Coulomb.volume_real_ball_three _ (by positivity),Coulomb.volume_real_ball_three _ hr.le]
  ring

lemma propagationBarrier_shell_lower {B r : ℝ} (hB : 0≤B) (hr : 0<r)
    {x : Position} (hx : r≤‖x‖) (hx' : ‖x‖≤2*r) :
    (7*B/128)/r^4≤propagationBarrier B r x := by
  have hd := hr.trans_le hx
  calc
    _=((7/8:ℝ)*B)/(2*r)^4 := by ring
    _≤((7/8:ℝ)*B)/‖x‖^4 := div_le_div_of_nonneg_left (by positivity)
      (pow_pos hd 4) (pow_le_pow_left₀ hd.le hx' 4)
    _≤_ := (propagationBarrier_two_sided hB hr hx).1

lemma PropagationInvariant.reaction_shell_test {B C r Z L R : ℝ} {u μ p : Position → ℝ}
    (d : PropagationInvariant B C r Z L u μ p) (hr : 0<r) (hB : 0≤B)
    (hR : 2*r≤R) :
    (tfReaction (7*B/128)*(28*Real.pi/3))/r^3≤
      ∫ x,cutoffReaction r (fun y => Z*coulombKernel y+u y) x*Coulomb.countTest 0 R x := by
  let F := fun x => cutoffReaction r (fun y => Z*coulombKernel y+u y) x*Coulomb.countTest 0 R x
  let A : Set Position := Metric.ball 0 (2*r) \ Metric.ball 0 r
  have hRp : 0<R := (by positivity : (0:ℝ)<2*r).trans_le hR
  have hi : Integrable F := integrable_mul_test_on
    ((cutoffReaction_offset_locallyIntegrable (Z:=Z) hr d.continuous_offset).locallyIntegrableOn univ)
    (Coulomb.countTest_smooth 0 R).continuous (Coulomb.countTest_compact 0 hRp) (subset_univ _)
  have hn : ∀ x,0≤F x := by
    intro x
    apply mul_nonneg _ (Coulomb.countTest_nonneg 0 R x)
    unfold cutoffReaction Set.indicator
    split_ifs
    · exact tfReaction_nonneg _
    · exact le_rfl
  have hAf : volume A<⊤ := lt_of_le_of_lt (measure_mono sdiff_subset) Metric.isBounded_ball.measure_lt_top
  have : IsFiniteMeasure (volume.restrict A) := ⟨by simpa using hAf⟩
  have hb : ∀ x∈A,tfReaction (7*B/128)/r^6≤F x := by
    intro x hx
    have hl : r≤‖x‖ := le_of_not_gt (by simpa using hx.2)
    have hu : ‖x‖<2*r := by simpa using hx.1
    have Hone := Coulomb.countTest_one (0:Position) hRp
      (show ‖x-0‖≤R by simpa using hu.le.trans hR)
    change _≤cutoffReaction r (fun y => Z*coulombKernel y+u y) x*Coulomb.countTest 0 R x
    rw [Hone,mul_one]
    simp only [cutoffReaction,Set.indicator_of_mem (show x∈{x : Position | r≤‖x‖} from hl)]
    rw [←tfReaction_div_fourth _ hr]
    exact tfReaction_monotone ((propagationBarrier_shell_lower hB hr hl hu.le).trans (d.caps x hl).1)
  have H := integral_mono_ae (integrable_const (tfReaction (7*B/128)/r^6)) hi.integrableOn
    (ae_restrict_of_forall_mem (measurableSet_ball.diff measurableSet_ball) hb)
  rw [setIntegral_const] at H
  have Hvol : (volume : Measure Position).real A=(28*Real.pi/3)*r^3 := propagation_shell_volume hr
  rw [Hvol,smul_eq_mul] at H
  have he : (28*Real.pi/3)*r^3*(tfReaction (7*B/128)/r^6)=
      (tfReaction (7*B/128)*(28*Real.pi/3))/r^3 := by field_simp
  rw [he] at H
  exact H.trans (setIntegral_le_integral hi (Eventually.of_forall hn))

theorem PropagationInvariant.charge_deficit {B C r Z L : ℝ} {u μ p : Position → ℝ}
    (d : PropagationInvariant B C r Z L u μ p) (hr : 0<r) (hB : 0≤B) (hC : 0≤C)
    (hμ : Integrable μ) (hp : Integrable p) :
    (tfReaction (7*B/128)*(28*Real.pi/3))/(4*Real.pi*r^3)≤
      Z-(∫ x in Metric.ball 0 r,μ x)+(∫ x,p x) := by
  let D := Z-(∫ x in Metric.ball 0 r,μ x)+(∫ x,p x)
  let I := ∫ x,|coordinateLaplacian Coulomb.cutSeed x|
  have he : ∀ᶠ R : ℝ in atTop,
      (tfReaction (7*B/128)*(28*Real.pi/3))/r^3≤4*Real.pi*D+C*I/R^3 := by
    filter_upwards [eventually_ge_atTop (2*r)] with R hR
    have hRp : 0<R := (by positivity : (0:ℝ)<2*r).trans_le hR
    have hrR : r≤R := (by linarith : r≤2*r).trans hR
    have h1 := d.reaction_shell_test hr hB hR
    have h2 := d.mass_test hr hμ hp (Coulomb.countTest_smooth 0 R) (Coulomb.countTest_compact 0 hRp)
      (Coulomb.countTest_nonneg 0 R) (fun x hx => Coulomb.countTest_one 0 hRp (by simpa using hx.trans hrR))
    have h3 := countTest_pairing_bound (F:=fun x => Z*coulombKernel x+u x)
      ((measurable_const.mul measurable_coulombKernel).add d.continuous_offset.measurable) hC hRp
      (fun x hx => by
        have H := d.caps x (hrR.trans hx)
        rw [abs_of_nonneg (((by positivity : (0:ℝ)≤(7/8:ℝ)*B/‖x‖^4).trans
          (propagationBarrier_two_sided hB hr (hrR.trans hx)).1).trans H.1)]
        exact H.2)
    exact h1.trans (h2.trans (add_le_add le_rfl ((le_abs_self _).trans h3)))
  have ht : Tendsto (fun R : ℝ => 4*Real.pi*D+C*I/R^3) atTop (𝓝 (4*Real.pi*D)) := by
    have H : Tendsto (fun R : ℝ => R⁻¹^3) atTop (𝓝 (0:ℝ)) := by simpa using (tendsto_inv_atTop_zero (𝕜:=ℝ)).pow 3
    convert (tendsto_const_nhds (x:=C*I)).mul H |>.const_add (4*Real.pi*D) using 1 <;>
      simp [div_eq_mul_inv,inv_pow]
  have H := ge_of_tendsto ht he
  apply (div_le_iff₀ (by positivity : 0<4*Real.pi*r^3)).mpr
  have HH := (div_le_iff₀ (pow_pos hr 3)).mp H
  nlinarith only [HH]

lemma propagationDeficit_coefficient_pos {B : ℝ} (hB : 0<B) :
    0<(tfReaction (7*B/128)*(28*Real.pi/3))/(4*Real.pi) := by
  unfold tfReaction kTF
  positivity

end NeutralAtom
end

end

end OAI
