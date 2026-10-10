import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.H1VectorL2
import OAI.Analysis.CoulombRadii.RandomFields.ExteriorIMS

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb
def bindingCut (r:ℝ) (l:Fin 2) : Space → ℝ := radialCut 0 r (Equiv.swap 0 1 l)
lemma bindingCut_smooth (r:ℝ) (l:Fin 2) : ContDiff ℝ ∞ (bindingCut r l) := radialCut_smooth ..
lemma bindingCut_partition (r:ℝ) (z:Space) : ∑ l,bindingCut r l z^2=1 := by
  rw [show (∑ l,bindingCut r l z^2)=∑ l,radialCut 0 r l z^2 from Equiv.sum_comp (Equiv.swap (0:Fin 2) 1) (fun l => radialCut 0 r l z^2)]
  exact radialCut_partition 0 r z
lemma bindingCut_derivative {r:ℝ} (hr:0<r) (l:Fin 2) (b:Fin 3) (z:Space) :
    |fderiv ℝ (bindingCut r l) z (EuclideanSpace.single b 1)| ≤ radialCutCoefficient/r :=
  radialCut_derivative_bound 0 hr _ b z
lemma bindingCut_attraction (Z:ℕ) (hZ:1 ≤ Z) {r:ℝ} (hr:0<r) (z:Space) (hz:bindingCut r 0 z≠0) :
    attraction (atom Z hZ) z ≤ (Z:ℝ)/r := by
  have hn:r < ‖z‖ := by
    by_contra hh
    apply hz
    simpa [bindingCut] using radialCut_core_zero 0 hr z (by simpa using le_of_not_gt hh)
  have ha:attraction (atom Z hZ) z=(Z:ℝ)*‖z‖⁻¹ := by simp [attraction,atom,coulombKernel]
  rw [ha,div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (inv_le_inv₀ (hr.trans hn) hr |>.mpr hn.le) (Nat.cast_nonneg Z)

def bindingLocalized {n:ℕ} (u:H1Vector n) {r:ℝ} (hr:0<r) (p:Fin n → Fin 2) : H1Vector n :=
  u.labelCut (bindingCut r) (bindingCut_smooth r) (bindingCut_partition r) (radialCutCoefficient/r)
    (div_nonneg radialCutCoefficient_pos.le hr.le) (bindingCut_derivative hr) p

def configurationBox (n:ℕ) (r:ℝ) : Set (Configuration n) := {x | ∀ i,‖position x i‖ ≤ 2*r}
lemma configurationBox_measurable (n:ℕ) (r:ℝ) : MeasurableSet (configurationBox n r) := by
  simpa only [configurationBox,ofPred_forall,positionCLM_apply] using
    MeasurableSet.iInter (fun i:Fin n => (isClosed_le (positionCLM i).continuous.norm (continuous_const (y:=2*r))).measurableSet)
lemma configurationBox_finite (n:ℕ) {r:ℝ} (hr:0<r) : volume (configurationBox n r)≠(⊤:ℝ≥0∞) := by
  have hs:configurationBox n r ⊆ Metric.closedBall 0 (Real.sqrt (3*(n:ℝ))*(2*r)) := by
    intro x hx
    rw [Metric.mem_closedBall,dist_zero_right]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (by positivity))).mp
    rw [mul_pow,Real.sq_sqrt (by positivity),EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _a:Fin n × Fin 3,(2*r)^2 := by
        apply Finset.sum_le_sum
        intro a _
        have ha:‖x a‖ ≤ 2*r := (PiLp.norm_apply_le (position x a.1) a.2).trans (hx a.1)
        exact pow_le_pow_left₀ (norm_nonneg _) ha 2
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]; ring
  exact ne_top_of_le_ne_top
    ((isCompact_closedBall (0:Configuration n) (Real.sqrt (3*(n:ℝ))*(2*r))).measure_lt_top.ne)
    (measure_mono hs)

lemma bindingLocalized_value_outside {n:ℕ} (u:H1Vector n) {r:ℝ} (hr:0<r)
    (s:Spins n) (x:Configuration n) (hx:x∉configurationBox n r) :
    (bindingLocalized u hr (fun _ => 1)).value s x=0 := by
  have hi:∃ i,2*r < ‖position x i‖ := by simpa only [configurationBox,mem_ofPred_eq,not_forall,not_le] using hx
  obtain ⟨i,hi⟩:=hi
  have ht:tensorCut (bindingCut r) (fun _ : Fin n => 1) x=0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa [bindingCut] using radialCut_out_zero 0 hr (position x i) (by simpa using hi.le)
  change (tensorCut (bindingCut r) (fun _ : Fin n => 1) x:ℂ)*u.value s x=0
  rw [ht,Complex.ofReal_zero,zero_mul]

lemma bindingLocalized_norm_le {n:ℕ} (u:H1Vector n) {r:ℝ} (hr:0<r)
    (s:Spins n) (x:Configuration n) :
    ‖(bindingLocalized u hr (fun _ => 1)).value s x‖^2 ≤ ‖u.value s x‖^2 := by
  change ‖(tensorCut (bindingCut r) (fun _ : Fin n => 1) x:ℂ)*u.value s x‖^2 ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow]
  have h:=pow_le_pow_left₀ (abs_nonneg _) (tensorCut_abs_le_one (bindingCut r) (bindingCut_partition r) (fun _ : Fin n => 1) x) 2
  simpa using mul_le_mul_of_nonneg_right h (sq_nonneg ‖u.value s x‖)

lemma binding_loss_controls_cut {n:ℕ} (u:H1Vector n) {r:ℝ} (hr:0<r) (s:Spins n) :
    ‖cutL2 (configurationBox n r)ᶜ (configurationBox_measurable n r).compl (u.valueL2 s)‖^2 ≤
      mass u-mass (bindingLocalized u hr (fun _ => 1)) := by
  let v:=bindingLocalized u hr (fun _ => 1)
  have hd(t:Spins n):Integrable (fun x => ‖u.value t x‖^2-‖v.value t x‖^2) :=
    ((u.value_L2 t).integrable_norm_pow (by norm_num)).sub ((v.value_L2 t).integrable_norm_pow (by norm_num))
  have hn(t:Spins n)(x:Configuration n):0 ≤ ‖u.value t x‖^2-‖v.value t x‖^2 := sub_nonneg.mpr (bindingLocalized_norm_le u hr t x)
  have he:mass u-mass v=∑ t,∫ x,‖u.value t x‖^2-‖v.value t x‖^2 := by
    simp only [mass,integral_sub ((u.value_L2 _).integrable_norm_pow (by norm_num)) ((v.value_L2 _).integrable_norm_pow (by norm_num)),Finset.sum_sub_distrib]
  rw [he]
  apply le_trans _ (Finset.single_le_sum (f:=fun t:Spins n => ∫ x,‖u.value t x‖^2-‖v.value t x‖^2)
    (fun t _ => integral_nonneg (hn t)) (Finset.mem_univ s))
  rw [l2_norm_sq_integral]
  apply integral_mono_ae
  · exact (Lp.memLp _).integrable_norm_pow (by norm_num)
  · exact hd s
  filter_upwards [cutL2_ae (configurationBox n r)ᶜ (configurationBox_measurable n r).compl (u.valueL2 s),u.valueL2_ae s] with x hx hu
  rw [hx]
  by_cases h:x∈configurationBox n r
  · simp only [mem_compl_iff,h,not_true_eq_false,not_false_eq_true,indicator_of_notMem,norm_zero,zero_pow (by decide : 2≠0)]
    exact hn s x
  · rw [indicator_of_mem h,hu,show v.value s x=0 from bindingLocalized_value_outside u hr s x h]
    simp

lemma binding_loss_bound (Z:ℕ) (hZ:1 ≤ Z) {n:ℕ} (hn:0<n) (u:H1Vector n) (ha:Antisymmetric u)
    {r:ℝ} (hr:0<r) (E P:ℝ) (hE:(E:EReal) ≤ sectorFormBottom (atom Z hZ) n)
    (hP:(P:EReal) ≤ sectorFormBottom (atom Z hZ) (n-1)) :
    (P-E)*(mass u-mass (bindingLocalized u hr (fun _ => 1))) ≤
      form (atom Z hZ) u-E*mass u+
        (3*(n:ℝ)*(radialCutCoefficient/r)^2+(n:ℝ)*((Z:ℝ)/r))*mass u :=
  binary_cut_loss_bound Z hZ hn u ha _ _ _ _ _ _ _ (by positivity) (bindingCut_attraction Z hZ hr) E P hE hP
end Coulomb
end

end

end OAI
