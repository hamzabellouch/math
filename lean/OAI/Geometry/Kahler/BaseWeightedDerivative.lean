import OAI.Geometry.Kahler.BaseDensityDefinitions

namespace OAI

universe uKahler11626_1 uKahler11629_1 uKahler11634_1 uKahler11642_1 uKahler11661_1 uKahler11675_1 uKahler11691_1 uKahler11701_1 uKahler11718_1 uKahler11754_1 uKahler11763_1 uKahler11780_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma bounded_half_plane {f : ℂ → ℂ} {C M : ℝ}
    (hd : DiffContOnCl ℂ f {z | 0 < z.re})
    (hb : ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ M)
    (hboundary : ∀ x : ℝ, ‖f ((x:ℂ)*Complex.I)‖ ≤ C)
    {z : ℂ} (hz : 0 ≤ z.re) : ‖f z‖ ≤ C := by
  apply PhragmenLindelof.right_half_plane_of_bounded_on_real hd _ _ hboundary hz
  · refine ⟨0,by norm_num,0,Asymptotics.IsBigO.of_bound M ?_⟩
    apply eventually_inf_principal.mpr
    exact Eventually.of_forall (fun z hz => by simpa using hb z (le_of_lt hz))
  · apply isBoundedUnder_of_eventually_le (a := M)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    exact hb x (by simpa using hx)

def expSum {ι : Type uKahler11626_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (z : ℂ) : ℂ :=
  ∑ i ∈ s, a i * Complex.exp (Complex.I*(w i:ℂ)*z)

lemma expSum_differentiable {ι : Type uKahler11629_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) :
    Differentiable ℂ (expSum s a w) := by
  unfold expSum
  fun_prop

private def dampedSum {ι : Type uKahler11634_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  (∑ i ∈ s, a i * Complex.exp (-((2:ℝ)+w i:ℝ)*z))/(1+z)^N

private lemma half_plane_norm_one_add {z : ℂ} (hz : 0 ≤ z.re) : 1 ≤ ‖1+z‖ := by
  have h := Complex.re_le_norm (1+z)
  simp only [Complex.add_re,Complex.one_re] at h
  linarith

private lemma dampedSum_bound {ι : Type uKahler11642_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (N : ℕ)
    (hw : ∀ i ∈ s, -2 ≤ w i) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖dampedSum s a w N z‖ ≤ ∑ i ∈ s, ‖a i‖ := by
  unfold dampedSum
  rw [norm_div,norm_pow]
  apply (div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one (half_plane_norm_one_add hz)) N)).mpr
  have he : ∀ i ∈ s, ‖Complex.exp (-((2:ℝ)+w i:ℝ)*z)‖ ≤ 1 := by
    intro i hi
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simpa only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.neg_im,Complex.ofReal_im,neg_zero,zero_mul,sub_zero] using
      mul_nonpos_of_nonpos_of_nonneg (show -(2+w i) ≤ 0 by linarith [hw i hi]) hz
  calc
    ‖∑ i ∈ s, a i * Complex.exp (-((2:ℝ)+w i:ℝ)*z)‖ ≤ ∑ i ∈ s, ‖a i‖*1 := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun i hi => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (he i hi) (norm_nonneg _))
    _ = ∑ i ∈ s, ‖a i‖ := by simp
    _ ≤ (∑ i ∈ s, ‖a i‖)*‖1+z‖^N := le_mul_of_one_le_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (one_le_pow₀ (half_plane_norm_one_add hz))

private lemma dampedSum_diffCont {ι : Type uKahler11661_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (N : ℕ) :
    DiffContOnCl ℂ (dampedSum s a w N) {z | 0 < z.re} := by
  have hnum : Differentiable ℂ (fun z : ℂ => ∑ i ∈ s, a i * Complex.exp (-((2:ℝ)+w i:ℝ)*z)) := by
    fun_prop
  have hn : ∀ z : ℂ, 0 ≤ z.re → (1+z)^N ≠ 0 := by
    intro z hz
    apply pow_ne_zero
    exact norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (half_plane_norm_one_add hz))
  constructor
  · intro z hz
    exact ((hnum z).div (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (1+z)^N) z) (hn z (le_of_lt hz))).differentiableWithinAt
  · rw [Complex.closure_setOfPred_lt_re]
    exact hnum.continuous.continuousOn.div ((continuous_const.add continuous_id).pow N).continuousOn hn

private lemma dampedSum_eq {ι : Type uKahler11675_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (N : ℕ) (z : ℂ) :
    dampedSum s a w N z = Complex.exp (-2*z)*expSum s a w (Complex.I*z)/(1+z)^N := by
  unfold dampedSum expSum
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_left_comm,mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  have hi2 := Complex.I_sq
  calc
    -(2+(w i:ℂ))*z = -2*z + Complex.I^2*(w i:ℂ)*z := by rw [hi2]; ring
    _ = _ := by ring

private lemma dampedSum_imag_norm {ι : Type uKahler11691_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (N : ℕ) (x : ℝ) :
    ‖dampedSum s a w N ((x:ℂ)*Complex.I)‖ = ‖expSum s a w (-x)‖/‖1+(x:ℂ)*Complex.I‖^N := by
  rw [dampedSum_eq,norm_div,norm_mul,norm_pow]
  have he : Complex.I*((x:ℂ)*Complex.I) = -(x:ℂ) := by calc
    _ = (x:ℂ)*Complex.I^2 := by ring
    _ = _ := by rw [Complex.I_sq]; ring
  rw [he,Complex.norm_exp]
  have hr : (-2*((x:ℂ)*Complex.I)).re = 0 := by simp [Complex.mul_re,Complex.mul_im]
  rw [hr,Real.exp_zero,one_mul]

private lemma dampedSum_boundary {ι : Type uKahler11701_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (N : ℕ)
    {B : ℝ} (hB : 0 ≤ B)
    (hg : ∀ x : ℝ, ‖expSum s a w x‖ ≤ B*(1+|x|)^N) (x : ℝ) :
    ‖dampedSum s a w N ((x:ℂ)*Complex.I)‖ ≤ B*2^N := by
  rw [dampedSum_imag_norm]
  have hn := half_plane_norm_one_add (z := (x:ℂ)*Complex.I) (by simp)
  have hd : ‖1+(x:ℂ)*Complex.I‖ > 0 := lt_of_lt_of_le zero_lt_one hn
  apply (div_le_iff₀ (pow_pos hd N)).mpr
  have him := Complex.abs_im_le_norm (1+(x:ℂ)*Complex.I)
  simp only [Complex.add_im,Complex.one_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,
    Complex.ofReal_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] at him
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|x|) (show 1+|x| ≤ 2*‖1+(x:ℂ)*Complex.I‖ by linarith) N
  have hb := hg (-x)
  rw [abs_neg,Complex.ofReal_neg] at hb
  apply hb.trans
  simpa only [mul_pow,mul_assoc] using mul_le_mul_of_nonneg_left hp hB

private lemma expSum_upper_bound {ι : Type uKahler11718_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (N : ℕ)
    (hw : ∀ i ∈ s, -2 ≤ w i) {B : ℝ} (hB : 0 ≤ B)
    (hg : ∀ x : ℝ, ‖expSum s a w x‖ ≤ B*(1+|x|)^N)
    {z : ℂ} (hz : 0 ≤ z.im) (hz1 : ‖z‖ ≤ 1) :
    ‖expSum s a w z‖ ≤ B*4^N*Real.exp 2 := by
  let v := -Complex.I*z
  have hv : v.re = z.im := by simp [v,Complex.mul_re]
  have hv0 : 0 ≤ v.re := by rwa [hv]
  have hv1 : ‖v‖ ≤ 1 := by simpa [v,norm_mul] using hz1
  have hvz : Complex.I*v = z := by
    dsimp [v]
    calc
      _ = -Complex.I^2*z := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  have hb := bounded_half_plane (dampedSum_diffCont s a w N)
    (fun z hz => dampedSum_bound s a w N hw hz) (dampedSum_boundary s a w N hB hg) hv0
  rw [dampedSum_eq,norm_div,norm_mul,norm_pow,hvz,Complex.norm_exp] at hb
  have he : (-2*v).re = -2*z.im := by simp [Complex.mul_re,hv]
  rw [he] at hb
  have hd := half_plane_norm_one_add hv0
  have hdp : 0 < ‖1+v‖^N := pow_pos (lt_of_lt_of_le zero_lt_one hd) N
  have hb' := (div_le_iff₀ hdp).mp hb
  have hh := mul_le_mul_of_nonneg_left hb' (Real.exp_pos (2*z.im)).le
  have hexp : Real.exp (2*z.im)*Real.exp (-2*z.im) = 1 := by rw [← Real.exp_add]; convert Real.exp_zero using 1; ring_nf
  rw [← mul_assoc,hexp,one_mul] at hh
  have hv2 : ‖1+v‖ ≤ 2 := by have := norm_add_le (1:ℂ) v; simp only [norm_one] at this; linarith
  have hp : ‖1+v‖^N ≤ 2^N := pow_le_pow_left₀ (norm_nonneg _) hv2 N
  have hei : Real.exp (2*z.im) ≤ Real.exp 2 := by
    apply Real.exp_le_exp.mpr
    have hm := Complex.im_le_norm z
    linarith
  apply hh.trans
  calc
    _ ≤ Real.exp 2*((B*2^N)*2^N) := mul_le_mul hei (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc B,← mul_pow]; norm_num; ring

lemma expSum_neg_frequencies {ι : Type uKahler11754_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (z : ℂ) :
    expSum s a (fun i => -w i) z = expSum s a w (-z) := by
  unfold expSum
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  push_cast
  ring

lemma expSum_disk_bound {ι : Type uKahler11763_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (N : ℕ)
    (hw : ∀ i ∈ s, |w i| ≤ 2) {B : ℝ} (hB : 0 ≤ B)
    (hg : ∀ x : ℝ, ‖expSum s a w x‖ ≤ B*(1+|x|)^N)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖expSum s a w z‖ ≤ B*4^N*Real.exp 2 := by
  by_cases him : 0 ≤ z.im
  · exact expSum_upper_bound s a w N (fun i hi => (abs_le.mp (hw i hi)).1) hB hg him hz
  · have hw' : ∀ i ∈ s, -2 ≤ -w i := fun i hi => by linarith [(abs_le.mp (hw i hi)).2]
    have hg' : ∀ x : ℝ, ‖expSum s a (fun i => -w i) x‖ ≤ B*(1+|x|)^N := by
      intro x
      rw [expSum_neg_frequencies]
      simpa only [Complex.ofReal_neg,abs_neg] using hg (-x)
    have hh := expSum_upper_bound s a (fun i => -w i) N hw' hB hg'
      (z := -z) (by simpa using (le_of_not_ge him)) (by simpa using hz)
    simpa only [expSum_neg_frequencies,neg_neg] using hh

lemma expSum_second_derivative_bound {ι : Type uKahler11780_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (N : ℕ)
    (hw : ∀ i ∈ s, |w i| ≤ 2) {B : ℝ} (hB : 0 ≤ B)
    (hg : ∀ x : ℝ, ‖expSum s a w x‖ ≤ B*(1+|x|)^N) :
    ‖iteratedDeriv 2 (expSum s a w) 0‖ ≤ 2*B*4^N*Real.exp 2 := by
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := (0:ℂ)) 2 (by norm_num : (0:ℝ)<1)
    (expSum_differentiable s a w).diffContOnCl (fun z hz => expSum_disk_bound s a w N hw hB hg
      (show ‖z‖ ≤ 1 by simpa only [Metric.mem_sphere,dist_zero_right] using le_of_eq hz))
  convert hh using 1; norm_num; ring

end PinchedHartogs.BaseConstruction

end

end OAI
