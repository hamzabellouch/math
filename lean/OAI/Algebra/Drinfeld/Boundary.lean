import OAI.Algebra.Drinfeld.BraidExp

namespace OAI

noncomputable section

section
namespace RealDeligneDrinfeld.BraidInsertionSum
open DeligneDrinfeld.CategoryExp
attribute [local instance] LieRing.ofAssociativeRing
variable {I : Type*} (N : ℕ) (s : Finset I) (q : I → L) (n : I → ℕ)
  (hqn : ∀ i,q i∈Ln (n i))
 theorem loop_x : (free N s q n hqn).D 0 0 (FreeCutoffCategory.j N x)=0 := by
  rw [free,DeligneDrinfeld.CategoryExp.sum_apply]
  apply Finset.sum_eq_zero
  intro i _hi
  rw [FreeCutoffCategory.loop_j]
  rw [DeligneDrinfeld.CategoryGauge.loop_apply]
  change FreeCutoffCategory.j N (derivation (q i) x+⁅(0:L),x⁆)=0
  rw [derivation_apply,D_x,zero_lie,add_zero,map_zero]
 theorem loop_y : (free N s q n hqn).D 0 0 (FreeCutoffCategory.j N y)=
    FreeCutoffCategory.j N y*FreeCutoffCategory.j N (∑ i∈s,q i)-
      FreeCutoffCategory.j N (∑ i∈s,q i)*FreeCutoffCategory.j N y := by
  rw [free,DeligneDrinfeld.CategoryExp.sum_apply,map_sum,Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [FreeCutoffCategory.loop_j]
  rw [DeligneDrinfeld.CategoryGauge.loop_apply]
  change FreeCutoffCategory.j N (derivation (q i) y+⁅(0:L),y⁆)=_
  rw [derivation_apply,D_y,zero_lie,add_zero,LieHom.map_lie,Ring.lie_def]
end RealDeligneDrinfeld.BraidInsertionSum

namespace RealDeligneDrinfeld.KZLogDifference
open DeligneDrinfeld DeligneDrinfeld.KZRealLog DeligneDrinfeld.KZComparison
open BraidInsertionSum
variable {I : Type*} (N : ℕ) (s : Finset I) (q : I → L) (n : I → ℕ)
  (hqn : ∀ i,q i∈Ln (n i)) (hn : ∀ i,2<n i)
 theorem difference (k : ℕ)
    (hq : KZComparison.value N-FreeCutoffCategory.j N (∑ i∈s,q i)∈FreeCutoffCategory.F N k)
    (m : ℕ) (a : FreeCutoffCategory.Q N) (ha : a∈FreeCutoffCategory.F N m) :
    KZRealLog.D N false true a-(free N s q n hqn).D 0 1 a∈FreeCutoffCategory.F N (m+k) := by
  rw [KZRealLog.edge_formula,BraidInsertionSum.edge_formula]
  apply TangentialCutoff.difference_mem N (KZRealLog.D N false false) ((free N s q n hqn).D 0 0)
      (KZComparison.value N) (FreeCutoffCategory.j N (∑ i∈s,q i))
      (fun a b => (KZRealLog.data N).comp false false false b a) (fun a b => (free N s q n hqn).comp 0 0 0 b a)
      ((KZRealLog.data N).one false) ((free N s q n hqn).one 0)
  · exact KZRealLog.loop_x N
  · simpa only [x,FreeCutoffCategory.j_of] using BraidInsertionSum.loop_x N s q n hqn
  · exact KZRealLog.loop_false_y N
  · simpa only [y,FreeCutoffCategory.j_of] using BraidInsertionSum.loop_y N s q n hqn
  · exact hq
  · exact ha
 include hn in
 theorem exponential (k : ℕ)
    (hq : KZComparison.value N-FreeCutoffCategory.j N (∑ i∈s,q i)∈FreeCutoffCategory.F N k) :
    (negative N:FreeCutoffCategory.Q N)-CategoryExp.act (free N s q n hqn) 0 1 (positive N)-
      (KZComparison.value N-FreeCutoffCategory.j N (∑ i∈s,q i))∈FreeCutoffCategory.F N (k+1) := by
  have hh := CategoryExp.exp_difference_unit (CutoffCategory.filtration ∅ N)
    (KZRealLog.D N false true) ((free N s q n hqn).D 0 1) k
    (KZRealLog.raises N false true) (free_raises N s q n hqn hn 0 1)
    (difference N s q n hqn k hq) (positive_weight N)
  rw [KZRealLog.exp_comparison,KZRealLog.value,BraidInsertionSum.unit] at hh
  exact hh
end RealDeligneDrinfeld.KZLogDifference

end

namespace DeligneDrinfeld.PoleEstimate

section
open MeasureTheory Set intervalIntegral

lemma continuousOn_inv {a b : ℝ} (ha : 0<a) : ContinuousOn (fun t : ℝ => t⁻¹) (Icc a b) :=
  continuousOn_id.inv₀ (fun _ ht => ne_of_gt (ha.trans_le ht.1))

lemma integral_inv_sq {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ t in a..b,(t⁻¹)^2)=a⁻¹-b⁻¹ := by
  have hi : IntervalIntegrable (fun t : ℝ => (t⁻¹)^2) volume a b :=
    ((continuousOn_inv ha).pow 2).intervalIntegrable_of_Icc hab
  have hd (t : ℝ) (ht : t∈uIcc a b) : HasDerivAt (fun t : ℝ => -t⁻¹) ((t⁻¹)^2) t := by
    rw [uIcc_of_le hab] at ht
    have h := ((hasDerivAt_id t).inv (ne_of_gt (ha.trans_le ht.1))).neg
    convert! h using 1
    simp [div_eq_mul_inv,inv_pow]
  have h := integral_eq_sub_of_hasDerivAt hd hi
  linarith

lemma integral_inv_sq_le {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ t in a..b,(t⁻¹)^2)≤a⁻¹ := by
  rw [integral_inv_sq ha hab]
  exact sub_le_self _ (inv_nonneg.mpr (ha.le.trans hab))

lemma integral_inv_le {a b : ℝ} (ha : 0<a) (hab : a≤b) (hb : b≤1) :
    (∫ t in a..b,t⁻¹)≤-Real.log a := by
  rw [integral_inv_of_pos ha (ha.trans_le hab),Real.log_div (ne_of_gt (ha.trans_le hab)) (ne_of_gt ha)]
  have h : Real.log b≤0 := Real.log_nonpos (ha.le.trans hab) hb
  linarith

lemma abs_inv_add_sub_inv_le {t δ : ℝ} (ht : 0<t) (hδ : 0≤δ) :
    |(t+δ)⁻¹-t⁻¹|≤δ*(t⁻¹)^2 := by
  have htd : 0<t+δ := by linarith
  have horder : (t+δ)⁻¹≤t⁻¹ := inv_anti₀ ht (by linarith)
  rw [abs_of_nonpos (sub_nonpos.mpr horder)]
  have he : -((t+δ)⁻¹-t⁻¹)=δ*t⁻¹*(t+δ)⁻¹ := by
    field_simp
    ring
  rw [he]
  calc
    _ ≤ δ*t⁻¹*t⁻¹ := mul_le_mul_of_nonneg_left horder (mul_nonneg hδ (inv_nonneg.mpr ht.le))
    _ = _ := by ring

lemma abs_inv_sub_sub_inv_le {t δ : ℝ} (ht : 0<t) (hδ : 0≤δ) (hd : 2*δ≤t) :
    |(t-δ)⁻¹-t⁻¹|≤2*δ*(t⁻¹)^2 := by
  have htd : 0<t-δ := by linarith
  have horder : t⁻¹≤(t-δ)⁻¹ := inv_anti₀ htd (by linarith)
  rw [abs_of_nonneg (sub_nonneg.mpr horder)]
  have he : (t-δ)⁻¹-t⁻¹=δ*t⁻¹*(t-δ)⁻¹ := by
    field_simp
    ring
  have hbound : (t-δ)⁻¹≤2*t⁻¹ := by
    calc
      _ ≤ (t/2)⁻¹ := inv_anti₀ (by linarith) (by linarith)
      _ = 2*t⁻¹ := by field_simp
  rw [he]
  calc
    _ ≤ δ*t⁻¹*(2*t⁻¹) := mul_le_mul_of_nonneg_left hbound (mul_nonneg hδ (inv_nonneg.mpr ht.le))
    _ = _ := by ring

lemma integral_abs_inv_add_sub_inv_le {a b δ : ℝ} (ha : 0<a) (hab : a≤b) (hδ : 0≤δ) :
    (∫ t in a..b,|(t+δ)⁻¹-t⁻¹|)≤δ*a⁻¹ := by
  have hc : ContinuousOn (fun t : ℝ => |(t+δ)⁻¹-t⁻¹|) (Icc a b) :=
    (((continuousOn_id.add continuousOn_const).inv₀
      (fun t ht => ne_of_gt (show 0<t+δ by linarith [ht.1]))).sub (continuousOn_inv ha)).abs
  have hi : IntervalIntegrable (fun t : ℝ => δ*(t⁻¹)^2) volume a b :=
    (continuousOn_const.mul ((continuousOn_inv ha).pow 2)).intervalIntegrable_of_Icc hab
  calc
    _ ≤ ∫ t in a..b,δ*(t⁻¹)^2 := integral_mono_on hab (hc.intervalIntegrable_of_Icc hab) hi
      (fun t ht => abs_inv_add_sub_inv_le (ha.trans_le ht.1) hδ)
    _ = δ*(∫ t in a..b,(t⁻¹)^2) := integral_const_mul _ _
    _ ≤ δ*a⁻¹ := mul_le_mul_of_nonneg_left (integral_inv_sq_le ha hab) hδ

lemma integral_abs_inv_sub_sub_inv_le {a b δ : ℝ} (ha : 0<a) (hab : a≤b)
    (hδ : 0≤δ) (hd : 2*δ≤a) :
    (∫ t in a..b,|(t-δ)⁻¹-t⁻¹|)≤2*δ*a⁻¹ := by
  have hc : ContinuousOn (fun t : ℝ => |(t-δ)⁻¹-t⁻¹|) (Icc a b) :=
    (((continuousOn_id.sub continuousOn_const).inv₀
      (fun t ht => ne_of_gt (show 0<t-δ by linarith [ht.1]))).sub (continuousOn_inv ha)).abs
  have hi : IntervalIntegrable (fun t : ℝ => 2*δ*(t⁻¹)^2) volume a b :=
    (continuousOn_const.mul ((continuousOn_inv ha).pow 2)).intervalIntegrable_of_Icc hab
  calc
    _ ≤ ∫ t in a..b,2*δ*(t⁻¹)^2 := integral_mono_on hab (hc.intervalIntegrable_of_Icc hab) hi
      (fun t ht => abs_inv_sub_sub_inv_le (ha.trans_le ht.1) hδ (hd.trans ht.1))
    _ = 2*δ*(∫ t in a..b,(t⁻¹)^2) := integral_const_mul _ _
    _ ≤ 2*δ*a⁻¹ := mul_le_mul_of_nonneg_left (integral_inv_sq_le ha hab) (by positivity)

end

open MeasureTheory Set intervalIntegral FinitePicard KZCollar
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

omit [NormedAlgebra ℝ A] in
theorem integralNorm_add_le {f g : ℝ → A} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b) :
    integralNorm (fun t => f t+g t) a b ≤ integralNorm f a b+integralNorm g a b := by
  calc
    _  ≤  ∫ t in a..b,‖f t‖+‖g t‖ := integral_mono_on hab (hf.add hg).norm (hf.norm.add hg.norm)
      (fun _ _ => norm_add_le _ _)
    _ = _ := intervalIntegral.integral_add hf.norm hg.norm

lemma scalar_right_inv_continuous {a b : ℝ} (hb : b<1) :
    ContinuousOn (fun t : ℝ => (t-1)⁻¹) (Icc a b) :=
  (continuousOn_id.sub continuousOn_const).inv₀
    (fun t ht => ne_of_lt (show t-1<0 by linarith [ht.2]))

lemma integral_right_inv_abs {a b : ℝ} (ha : 0<a) (hab : a ≤ b) (hb : b<1) :
    (∫ t in a..b,|(t-1)⁻¹|) ≤ -Real.log (1-b) := by
  have he : (fun t : ℝ => |(t-1)⁻¹|)=fun t => |(1-t)⁻¹| := by
    funext t
    rw [show t-1=-(1-t) by ring,inv_neg,abs_neg]
  rw [he,integral_comp_sub_left (fun t : ℝ => |t⁻¹|) 1]
  have hba : 1-b ≤ 1-a := by linarith
  have he' : (∫ t in (1-b)..(1-a),|t⁻¹|)=∫ t in (1-b)..(1-a),t⁻¹ := by
    apply integral_congr
    intro t ht
    rw [uIcc_of_le hba] at ht
    exact abs_of_nonneg (inv_nonneg.mpr (by linarith [ht.1]))
  rw [he']
  exact integral_inv_le (by linarith) hba (by linarith)

theorem bulkForm_mass {X Y : A} {a b : ℝ} (ha : 0<a) (hab : a ≤ b) (hb : b<1) :
    integralNorm (bulkForm X Y) a b ≤ ‖X‖*(-Real.log a)+‖Y‖*(-Real.log (1-b)) := by
  have hc0 := continuousOn_inv (b:=b) ha
  have hc1 := scalar_right_inv_continuous (a:=a) hb
  have hi0 : IntervalIntegrable (fun t : ℝ => t⁻¹ • X) volume a b := (hc0.smul (continuousOn_const (c:=X))).intervalIntegrable_of_Icc hab
  have hi1 : IntervalIntegrable (fun t : ℝ => (t-1)⁻¹ • Y) volume a b := (hc1.smul (continuousOn_const (c:=Y))).intervalIntegrable_of_Icc hab
  have h0 : integralNorm (fun t : ℝ => t⁻¹ • X) a b ≤ ‖X‖*(-Real.log a) := by
    unfold integralNorm
    simp only [norm_smul,Real.norm_eq_abs]
    rw [intervalIntegral.integral_mul_const]
    have he : (∫ t in a..b,|t⁻¹|)=∫ t in a..b,t⁻¹ := by
      apply integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      exact abs_of_nonneg (inv_nonneg.mpr (ha.le.trans ht.1))
    rw [he,mul_comm]
    exact mul_le_mul_of_nonneg_left (integral_inv_le ha hab hb.le) (norm_nonneg _)
  have h1 : integralNorm (fun t : ℝ => (t-1)⁻¹ • Y) a b ≤ ‖Y‖*(-Real.log (1-b)) := by
    unfold integralNorm
    simp only [norm_smul,Real.norm_eq_abs]
    rw [intervalIntegral.integral_mul_const,mul_comm]
    exact mul_le_mul_of_nonneg_left (integral_right_inv_abs ha hab hb) (norm_nonneg _)
  exact (integralNorm_add_le hab hi0 hi1).trans (add_le_add h0 h1)

def shiftedBulk (X Y U V : A) (δ t : ℝ) : A :=
  bulkForm X Y t+((t+δ)⁻¹-t⁻¹) • U+((t+δ-1)⁻¹-(t-1)⁻¹) • V

lemma right_shift_abs (δ t : ℝ) :
    |(t+δ-1)⁻¹-(t-1)⁻¹|=|((1-t)-δ)⁻¹-(1-t)⁻¹| := by
  rw [show t+δ-1=-((1-t)-δ) by ring,show t-1=-(1-t) by ring,inv_neg,inv_neg,neg_sub_neg,abs_sub_comm]

lemma integral_right_shift {a b δ : ℝ} (hab : a ≤ b) (hb : b<1) (hδ : 0 ≤ δ) (hd : 2*δ ≤ 1-b) :
    (∫ t in a..b,|(t+δ-1)⁻¹-(t-1)⁻¹|) ≤ 2*δ*(1-b)⁻¹ := by
  simp_rw [right_shift_abs]
  rw [integral_comp_sub_left (fun t => |(t-δ)⁻¹-t⁻¹|) 1]
  exact integral_abs_inv_sub_sub_inv_le (by linarith) (by linarith) hδ hd

lemma shiftedBulk_continuous (X Y U V : A) {a b δ : ℝ}
    (ha : 0<a) (hb : b<1) (hδ : 0 ≤ δ) (hd : 2*δ ≤ 1-b) :
    ContinuousOn (shiftedBulk X Y U V δ) (Icc a b) := by
  have h0 := continuousOn_inv (b:=b) ha
  have h1 := scalar_right_inv_continuous (a:=a) hb
  have h2 : ContinuousOn (fun t : ℝ => (t+δ)⁻¹) (Icc a b) :=
    (continuousOn_id.add continuousOn_const).inv₀
      (fun t ht => ne_of_gt (show 0<t+δ by linarith [ht.1]))
  have h3 : ContinuousOn (fun t : ℝ => (t+δ-1)⁻¹) (Icc a b) :=
    ((continuousOn_id.add continuousOn_const).sub continuousOn_const).inv₀
      (fun t ht => ne_of_lt (show t+δ-1<0 by linarith [ht.2]))
  exact (((h0.smul continuousOn_const).add (h1.smul continuousOn_const)).add
    ((h2.sub h0).smul continuousOn_const)).add ((h3.sub h1).smul continuousOn_const)

lemma shiftedBulk_error_mass {X Y U V : A} {a b δ : ℝ}
    (ha : 0<a) (hab : a ≤ b) (hb : b<1) (hδ : 0 ≤ δ) (hd : 2*δ ≤ 1-b) :
    integralNorm (fun t => shiftedBulk X Y U V δ t-bulkForm X Y t) a b ≤
      ‖U‖*(δ*a⁻¹)+‖V‖*(2*δ*(1-b)⁻¹) := by
  have h0 := continuousOn_inv (b:=b) ha
  have h1 := scalar_right_inv_continuous (a:=a) hb
  have h2 : ContinuousOn (fun t : ℝ => (t+δ)⁻¹) (Icc a b) :=
    (continuousOn_id.add continuousOn_const).inv₀
      (fun t ht => ne_of_gt (show 0<t+δ by linarith [ht.1]))
  have h3 : ContinuousOn (fun t : ℝ => (t+δ-1)⁻¹) (Icc a b) :=
    ((continuousOn_id.add continuousOn_const).sub continuousOn_const).inv₀
      (fun t ht => ne_of_lt (show t+δ-1<0 by linarith [ht.2]))
  have he : (fun t => shiftedBulk X Y U V δ t-bulkForm X Y t)=
      (fun t => ((t+δ)⁻¹-t⁻¹) • U+((t+δ-1)⁻¹-(t-1)⁻¹) • V) := by
    funext t
    unfold shiftedBulk
    abel
  rw [he]
  calc
    _  ≤  integralNorm (fun t => ((t+δ)⁻¹-t⁻¹) • U) a b+
        integralNorm (fun t => ((t+δ-1)⁻¹-(t-1)⁻¹) • V) a b :=
      integralNorm_add_le hab (((h2.sub h0).smul continuousOn_const).intervalIntegrable_of_Icc hab)
        (((h3.sub h1).smul continuousOn_const).intervalIntegrable_of_Icc hab)
    _ = ‖U‖*(∫ t in a..b,|(t+δ)⁻¹-t⁻¹|)+‖V‖*(∫ t in a..b,|(t+δ-1)⁻¹-(t-1)⁻¹|) := by
      simp only [integralNorm,norm_smul,Real.norm_eq_abs,intervalIntegral.integral_mul_const]
      ring
    _  ≤  _ := add_le_add
      (mul_le_mul_of_nonneg_left (integral_abs_inv_add_sub_inv_le ha hab hδ) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (integral_right_shift hab hb hδ hd) (norm_nonneg _))

end DeligneDrinfeld.PoleEstimate

namespace DeligneDrinfeld.FourCollar
open MeasureTheory Set Filter FinitePicard KZCollar RegularSingular
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def form (a b d e f : A) (x y vx vy : ℝ) : A :=
  (vx/x) • a+(vy/y) • b+((vy-vx)/(y-x)) • d+
    (vx/(x-1)) • e+(vy/(y-1)) • f

def cx : Fin 5 → ℝ → ℝ := ![(fun s => s^2),(fun s => s),
  (fun s => 1-s-s^2),(fun s => s^2),(fun s => 1-s)]
def cy : Fin 5 → ℝ → ℝ := ![(fun s => s),(fun s => s+s^2),
  (fun s => 1-s),(fun s => 1-s^2),(fun s => 1-s^2)]
def vx : Fin 5 → ℝ → ℝ := ![(fun s => 2*s),(fun _ => 1),
  (fun s => -1-2*s),(fun s => 2*s),(fun _ => -1)]
def vy : Fin 5 → ℝ → ℝ := ![(fun _ => 1),(fun s => 1+2*s),
  (fun _ => -1),(fun s => -2*s),(fun s => -2*s)]

def residue (a b d e f : A) : Fin 5 → A :=
  ![2 • a+b+d,a+b+2 • d,f+e+2 • d,2 • a+2 • f,2 • f+e+d]

def remainder (a b d e f : A) : Fin 5 → ℝ → A :=
  ![(fun s => -((1-s)⁻¹) • (d+f)-(2*s/(1-s^2)) • e),
    (fun s => (1+s)⁻¹ • b-(1-s)⁻¹ • e-((1+2*s)/(1-s-s^2)) • f),
    (fun s => (1+s)⁻¹ • e-(1-s)⁻¹ • b-((1+2*s)/(1-s-s^2)) • a),
    (fun s => -(2*s/(1-s^2)) • (b+e)-(4*s/(1-2*s^2)) • d),
    (fun s => -((1-s)⁻¹) • (d+a)-(2*s/(1-s^2)) • b)]

omit [NormedRing A] [NormedAlgebra ℝ A] in
theorem coordinates_derivative (i : Fin 5) (s : ℝ) :
    HasDerivAt (cx i) (vx i s) s ∧ HasDerivAt (cy i) (vy i s) s := by
  have hd : HasDerivAt (fun t : ℝ => t) 1 s := hasDerivAt_id s
  have hc (c : ℝ) : HasDerivAt (fun _ : ℝ => c) 0 s := hasDerivAt_const s c
  have hp : HasDerivAt (fun s : ℝ => s^2) (2*s) s := by
    convert! hd.pow 2 using 1; norm_num
  fin_cases i
  · change HasDerivAt (fun s : ℝ => s^2) (2*s) s ∧ HasDerivAt id 1 s
    exact ⟨hp,hd⟩
  · change HasDerivAt id 1 s ∧ HasDerivAt (fun s : ℝ => s+s^2) (1+2*s) s
    exact ⟨hd,hd.add hp⟩
  · change HasDerivAt (fun s : ℝ => 1-s-s^2) (-1-2*s) s ∧ HasDerivAt (fun s : ℝ => 1-s) (-1) s
    exact ⟨by simpa using! ((hc 1).sub hd).sub hp,by simpa using! (hc 1).sub hd⟩
  · change HasDerivAt (fun s : ℝ => s^2) (2*s) s ∧ HasDerivAt (fun s : ℝ => 1-s^2) (-2*s) s
    exact ⟨hp,by simpa using! (hc 1).sub hp⟩
  · change HasDerivAt (fun s : ℝ => 1-s) (-1) s ∧ HasDerivAt (fun s : ℝ => 1-s^2) (-2*s) s
    exact ⟨by simpa using! (hc 1).sub hd,by simpa using! (hc 1).sub hp⟩

omit [NormedRing A] [NormedAlgebra ℝ A] in
theorem scalar_nonzero {s : ℝ} (hs : s∈Icc 0 (1/4)) :
    1-s≠0 ∧ 1+s≠0 ∧ 1-s^2≠0 ∧ 1-s-s^2≠0 ∧ 1-2*s^2≠0 := by
  have hsq : s^2≤1/16 := by nlinarith [hs.1,hs.2,sq_nonneg (s-1/4)]
  exact ⟨by linarith [hs.2],by linarith [hs.1],by linarith,
    by linarith [hs.2],by linarith⟩

omit [NormedRing A] [NormedAlgebra ℝ A] in
theorem chamber (i : Fin 5) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    0<cx i s ∧ cx i s<cy i s ∧ cy i s<1 := by
  have hsq : s^2≤1/16 := by nlinarith [hs.1,hs.2,sq_nonneg (s-1/4)]
  have hss : s^2<s := by nlinarith [hs.1,hs.2]
  fin_cases i
  · change 0<s^2 ∧ s^2<s ∧ s<1
    exact ⟨sq_pos_of_pos hs.1,hss,by linarith [hs.2]⟩
  · change 0<s ∧ s<s+s^2 ∧ s+s^2<1
    exact ⟨hs.1,by nlinarith [sq_pos_of_pos hs.1],by nlinarith [hs.2]⟩
  · change 0<1-s-s^2 ∧ 1-s-s^2<1-s ∧ 1-s<1
    exact ⟨by linarith [hs.2],by nlinarith [sq_pos_of_pos hs.1],by linarith [hs.1]⟩
  · change 0<s^2 ∧ s^2<1-s^2 ∧ 1-s^2<1
    exact ⟨sq_pos_of_pos hs.1,by linarith,by nlinarith [sq_pos_of_pos hs.1]⟩
  · change 0<1-s ∧ 1-s<1-s^2 ∧ 1-s^2<1
    exact ⟨by nlinarith [hs.1,hs.2,sq_pos_of_pos hs.1],
    by nlinarith [hs.1,hs.2,sq_pos_of_pos hs.1],by nlinarith [hs.1,hs.2,sq_pos_of_pos hs.1]⟩

theorem form_collar (a b d e f : A) (i : Fin 5) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    form a b d e f (cx i s) (cy i s) (vx i s) (vy i s)=
      s⁻¹ • residue a b d e f i+remainder a b d e f i s := by
  obtain ⟨h1,hp,h2,h3,h4⟩ := scalar_nonzero ⟨hs.1.le,hs.2⟩
  have h0 : s≠0 := ne_of_gt hs.1
  have hss : s-s^2≠0 := by nlinarith [hs.1,hs.2]
  have hsp : s+s^2≠0 := by nlinarith [hs.1,sq_nonneg s]
  have hm : s-1≠0 := sub_ne_zero.mpr (by linarith [hs.2])
  have hs2 : s^2-1≠0 := by exact sub_ne_zero.mpr (sub_ne_zero.mp h2).symm
  have hn3 : -1+s+s^2≠0 := by intro h; apply h3; linarith
  have hnsp : -s-s^2≠0 := by intro h; apply hsp; linarith
  have hn4 : 1-s^2*2≠0 := by intro h; apply h4; linarith
  have hnp : -1-s≠0 := by intro h; apply hp; linarith
  fin_cases i
  · change form a b d e f (s^2) s (2*s) 1=
      s⁻¹ • (2 • a+b+d)+(-((1-s)⁻¹) • (d+f)-(2*s/(1-s^2)) • e)
    unfold form
    match_scalars <;> field_simp [h0,h1,hp,h2,h3,h4,hss,hsp,hm,hs2,hn3,hnsp,hn4] <;> ring
  · change form a b d e f s (s+s^2) 1 (1+2*s)=
      s⁻¹ • (a+b+2 • d)+((1+s)⁻¹ • b-(1-s)⁻¹ • e-((1+2*s)/(1-s-s^2)) • f)
    unfold form
    match_scalars <;> field_simp [h0,h1,hp,h2,h3,h4,hss,hsp,hm,hs2,hn3,hnsp,hn4] <;> first | ring1 | (ring_nf; field_simp [h0,hn3,hnsp,hn4,hnp]; ring)
  · change form a b d e f (1-s-s^2) (1-s) (-1-2*s) (-1)=
      s⁻¹ • (f+e+2 • d)+((1+s)⁻¹ • e-(1-s)⁻¹ • b-((1+2*s)/(1-s-s^2)) • a)
    unfold form
    match_scalars <;> field_simp [h0,h1,hp,h2,h3,h4,hss,hsp,hm,hs2,hn3,hnsp,hn4] <;> first | ring1 | (ring_nf; field_simp [h0,hn3,hnsp,hn4,hnp]; ring)
  · change form a b d e f (s^2) (1-s^2) (2*s) (-2*s)=
      s⁻¹ • (2 • a+2 • f)+(-(2*s/(1-s^2)) • (b+e)-(4*s/(1-2*s^2)) • d)
    unfold form
    match_scalars <;> field_simp [h0,h1,hp,h2,h3,h4,hss,hsp,hm,hs2,hn3,hnsp,hn4] <;> first | ring1 | (ring_nf; field_simp [h0,hn3,hnsp,hn4,hnp]; ring)
  · change form a b d e f (1-s) (1-s^2) (-1) (-2*s)=
      s⁻¹ • (2 • f+e+d)+(-((1-s)⁻¹) • (d+a)-(2*s/(1-s^2)) • b)
    unfold form
    match_scalars <;> field_simp [h0,h1,hp,h2,h3,h4,hss,hsp,hm,hs2,hn3,hnsp,hn4] <;> ring

 theorem remainder_continuous (a b d e f : A) (i : Fin 5) :
    ContinuousOn (remainder a b d e f i) (Icc 0 (1/4)) := by
  have h1 : ContinuousOn (fun s : ℝ => (1-s)⁻¹) (Icc 0 (1/4)) :=
    (continuousOn_const.sub continuousOn_id).inv₀ (fun s hs => (scalar_nonzero hs).1)
  have hp : ContinuousOn (fun s : ℝ => (1+s)⁻¹) (Icc 0 (1/4)) :=
    (continuousOn_const.add continuousOn_id).inv₀ (fun s hs => (scalar_nonzero hs).2.1)
  have h2 : ContinuousOn (fun s : ℝ => 2*s/(1-s^2)) (Icc 0 (1/4)) :=
    (continuousOn_const.mul continuousOn_id).div (continuousOn_const.sub (continuousOn_id.pow 2))
      (fun s hs => (scalar_nonzero hs).2.2.1)
  have h3 : ContinuousOn (fun s : ℝ => (1+2*s)/(1-s-s^2)) (Icc 0 (1/4)) :=
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).div
      ((continuousOn_const.sub continuousOn_id).sub (continuousOn_id.pow 2))
      (fun s hs => (scalar_nonzero hs).2.2.2.1)
  have h4 : ContinuousOn (fun s : ℝ => 4*s/(1-2*s^2)) (Icc 0 (1/4)) :=
    (continuousOn_const.mul continuousOn_id).div
      (continuousOn_const.sub (continuousOn_const.mul (continuousOn_id.pow 2)))
      (fun s hs => (scalar_nonzero hs).2.2.2.2)
  fin_cases i
  all_goals norm_num only [remainder,Fin.reduceFinMk,Matrix.cons_val_zero,Matrix.cons_val_succ]
  · exact ((h1.neg).smul continuousOn_const).sub (h2.smul continuousOn_const)
  · exact ((hp.smul continuousOn_const).sub (h1.smul continuousOn_const)).sub (h3.smul continuousOn_const)
  · exact ((hp.smul continuousOn_const).sub (h1.smul continuousOn_const)).sub (h3.smul continuousOn_const)
  · exact ((h2.neg).smul continuousOn_const).sub (h4.smul continuousOn_const)
  · exact ((h1.neg).smul continuousOn_const).sub (h2.smul continuousOn_const)

variable (F : NilpotentFiltration A) {a b d e f : A}
  (ha : a∈F.space 1) (hb : b∈F.space 1) (hd : d∈F.space 1)
  (he : e∈F.space 1) (hf : f∈F.space 1)

include ha hb hd he hf

theorem residue_mem (i : Fin 5) : residue a b d e f i∈F.space 1 := by
  fin_cases i
  · exact (F.space 1).add_mem ((F.space 1).add_mem ((F.space 1).nsmul_mem ha _) hb) hd
  · exact (F.space 1).add_mem ((F.space 1).add_mem ha hb) ((F.space 1).nsmul_mem hd _)
  · exact (F.space 1).add_mem ((F.space 1).add_mem hf he) ((F.space 1).nsmul_mem hd _)
  · exact (F.space 1).add_mem ((F.space 1).nsmul_mem ha _) ((F.space 1).nsmul_mem hf _)
  · exact (F.space 1).add_mem ((F.space 1).add_mem ((F.space 1).nsmul_mem hf _) he) hd

theorem remainder_mem (i : Fin 5) (s : ℝ) : remainder a b d e f i s∈F.space 1 := by
  fin_cases i
  · exact (F.space 1).sub_mem ((F.space 1).smul_mem _ ((F.space 1).add_mem hd hf))
      ((F.space 1).smul_mem _ he)
  · exact (F.space 1).sub_mem ((F.space 1).sub_mem ((F.space 1).smul_mem _ hb)
      ((F.space 1).smul_mem _ he)) ((F.space 1).smul_mem _ hf)
  · exact (F.space 1).sub_mem ((F.space 1).sub_mem ((F.space 1).smul_mem _ he)
      ((F.space 1).smul_mem _ hb)) ((F.space 1).smul_mem _ ha)
  · exact (F.space 1).sub_mem ((F.space 1).smul_mem _ ((F.space 1).add_mem hb he))
      ((F.space 1).smul_mem _ hd)
  · exact (F.space 1).sub_mem ((F.space 1).smul_mem _ ((F.space 1).add_mem hd ha))
      ((F.space 1).smul_mem _ hb)

def normalized (i : Fin 5) : ℝ → A :=
  RegularSingular.solution F (residue a b d e f i) (remainder a b d e f i)

variable [CompleteSpace A] [FiniteDimensional ℝ A]

theorem normalized_derivative (i : Fin 5) {s : ℝ} (hs : s∈Ioo 0 (1/4)) :
    HasDerivAt (normalized F (a:=a) (b:=b) (d:=d) (e:=e) (f:=f) i)
      (form a b d e f (cx i s) (cy i s) (vx i s) (vy i s)*normalized F (a:=a) (b:=b) (d:=d) (e:=e) (f:=f) i s) s := by
  rw [form_collar a b d e f i ⟨hs.1,hs.2.le⟩]
  exact solution_derivative F (residue_mem F ha hb hd he hf i)
    (remainder_mem F ha hb hd he hf i) (remainder_continuous a b d e f i) hs

omit [FiniteDimensional ℝ A] in
theorem normalized_limit (i : Fin 5) :
    Tendsto (fun s => gauge (-residue a b d e f i) s*normalized F (a:=a) (b:=b) (d:=d) (e:=e) (f:=f) i s)
      (𝓝[>] 0) (𝓝 (1:A)) :=
  solution_limit F (residue_mem F ha hb hd he hf i) (by norm_num : (0:ℝ)<1/4)
    (remainder_continuous a b d e f i)

theorem normalized_isUnit (i : Fin 5) (s : ℝ) :
    IsUnit (normalized F (a:=a) (b:=b) (d:=d) (e:=e) (f:=f) i s) :=
  solution_isUnit F (residue_mem F ha hb hd he hf i) (remainder_mem F ha hb hd he hf i) s

end DeligneDrinfeld.FourCollar

namespace DeligneDrinfeld.BCBoundary

section
open MeasureTheory Set Filter Asymptotics FinitePicard KZCollar PowerAsymptotic PoleEstimate
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def endpoint (s : ℝ) : ℝ := 1-s-s^2

theorem interval_bounds {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    s ≤ endpoint s ∧ endpoint s<1 ∧ 2*s^2 ≤ 1-endpoint s := by
  have hsq : s^2 ≤ 1/16 := by nlinarith [hs.1,hs.2,sq_nonneg (s-1/4)]
  simp only [endpoint]
  exact ⟨by nlinarith [hs.1,hs.2],by nlinarith [hs.1],by nlinarith [hs.1,hs.2]⟩

theorem form_eq (a b d e f : A) (s t : ℝ) :
    FourCollar.form a b d e f t (t+s^2) 1 1=shiftedBulk (a+b) (e+f) b f (s^2) t := by
  simp only [FourCollar.form,shiftedBulk,bulkForm,one_div,sub_self,zero_div,zero_smul,add_zero,
    smul_add,sub_smul]
  abel

theorem error_bound (X Y U V : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    integralNorm (fun t => shiftedBulk X Y U V (s^2) t-bulkForm X Y t) s (endpoint s) ≤
      (‖U‖+2*‖V‖)*s := by
  obtain ⟨hab,hb,hd⟩ := interval_bounds hs
  have h := shiftedBulk_error_mass (X:=X) (Y:=Y) (U:=U) (V:=V) hs.1 hab hb (sq_nonneg s) hd
  have he : s^2*s⁻¹=s := by field_simp
  have hgap : s ≤ 1-endpoint s := by dsimp [endpoint]; nlinarith [sq_nonneg s]
  have hr : (1-endpoint s)⁻¹ ≤ s⁻¹ := inv_anti₀ hs.1 hgap
  have he2 : 2*s^2*(1-endpoint s)⁻¹ ≤ 2*s := by
    calc
      _ ≤ 2*s^2*s⁻¹ := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = 2*s := by rw [mul_assoc,he]
  calc
    _ ≤ ‖U‖*(s^2*s⁻¹)+‖V‖*(2*s^2*(1-endpoint s)⁻¹) := h
    _ ≤ ‖U‖*s+‖V‖*(2*s) := by rw [he]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left he2 (norm_nonneg V))
    _ = _ := by ring

theorem bulk_bound (X Y : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    integralNorm (bulkForm X Y) s (endpoint s) ≤ (‖X‖+‖Y‖)*(-Real.log s) := by
  obtain ⟨hab,hb,hd⟩ := interval_bounds hs
  have hh : -Real.log (1-endpoint s) ≤ -Real.log s := by
    apply neg_le_neg
    exact Real.log_le_log hs.1 (by dsimp [endpoint]; nlinarith [sq_nonneg s])
  calc
    _ ≤ ‖X‖*(-Real.log s)+‖Y‖*(-Real.log (1-endpoint s)) := bulkForm_mass hs.1 hab hb
    _ ≤ ‖X‖*(-Real.log s)+‖Y‖*(-Real.log s) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hh (norm_nonneg Y))
    _ = _ := by ring

def mass (X Y U V : A) (s : ℝ) : ℝ :=
  (‖X‖+‖Y‖)*(-Real.log s)+(‖U‖+2*‖V‖)*s

omit [NormedAlgebra ℝ A] in
theorem mass_subpower (X Y U V : A) : Subpower (mass X Y U V) := by
  have hl : Subpower (fun s : ℝ => -Real.log s) := by
    simpa only [pow_one,neg_one_mul] using (const_subpower (-1:ℝ)).mul (log_pow_subpower 1)
  exact ((const_subpower _).mul hl).add (continuousAt_subpower (continuousAt_const.mul continuousAt_id))

theorem perturbation (X Y U V : A) (N : ℕ) :
    PowerSmall (fun s => transport (shiftedBulk X Y U V (s^2)) s N (endpoint s)-
      transport (bulkForm X Y) s N (endpoint s)) := by
  apply transport_perturbation_powerSmall (L:=mass X Y U V)
    (E:=fun s => (‖U‖+2*‖V‖)*s) _ (mass_subpower X Y U V) (linear_powerSmall _) N
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0:ℝ)<1/4)] with s hs
  obtain ⟨hab,hb,hd⟩ := interval_bounds hs
  have hcΩ := shiftedBulk_continuous X Y U V hs.1 hb (sq_nonneg s) hd
  have hcΘ := (bulkForm_continuous X Y).mono (show Icc s (endpoint s)⊆Ioo 0 1 from
    fun t ht => ⟨hs.1.trans_le ht.1,ht.2.trans_lt hb⟩)
  have hiΩ : IntervalIntegrable (shiftedBulk X Y U V (s^2)) volume s (endpoint s) := hcΩ.intervalIntegrable_of_Icc hab
  have hiΘ : IntervalIntegrable (bulkForm X Y) volume s (endpoint s) := hcΘ.intervalIntegrable_of_Icc hab
  have hE : 0 ≤ (‖U‖+2*‖V‖)*s := mul_nonneg (by positivity) hs.1.le
  have hlog : 0 ≤ -Real.log s := neg_nonneg.mpr (Real.log_nonpos hs.1.le (by linarith [hs.2]))
  have hbase : 0 ≤ (‖X‖+‖Y‖)*(-Real.log s) := mul_nonneg (by positivity) hlog
  have he := error_bound X Y U V hs
  have hΘ := bulk_bound X Y hs
  have hΩ : integralNorm (shiftedBulk X Y U V (s^2)) s (endpoint s) ≤ mass X Y U V s := by
    have h := integralNorm_add_le hab hiΘ (hiΩ.sub hiΘ)
    have hf : (fun t => bulkForm X Y t+(shiftedBulk X Y U V (s^2) t-bulkForm X Y t))=
        shiftedBulk X Y U V (s^2) := by funext t; abel
    rw [hf] at h
    exact h.trans (add_le_add hΘ he)
  exact ⟨hab,hiΩ,hiΘ,add_nonneg hbase hE,hE,hΩ,hΘ.trans (le_add_of_nonneg_right hE),he⟩

end

open Set Filter FinitePicard KZCollar PowerAsymptotic PoleEstimate
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]

theorem shared_residue_cancel {X Y Z : A} {N : ℕ} (hZ : Z^(N+1)=0)
    (hZX : Commute Z X) (hZY : Commute Z Y) (a b s : ℝ) :
    gauge (-(Y+Z)) s*transport (bulkForm X Y) a N b*gauge (X+Z) s =
      gauge (-Y) s*transport (bulkForm X Y) a N b*gauge X s := by
  have ht := transport_commute Z (fun t : ℝ => (hZX.smul_right (t⁻¹)).add_right (hZY.smul_right ((t-1)⁻¹))) a N b
  have hg := gauge_commute hZ ht.symm s
  change Commute (transport (bulkForm X Y) a N b) (gauge Z s) at hg
  have hy : gauge (-(Y+Z)) s=gauge (-Y) s*gauge (-Z) s := by
    rw [neg_add,gauge_add_of_commute]; exact hZY.symm.neg_left.neg_right
  have hx : gauge (X+Z) s=gauge Z s*gauge X s := by
    rw [add_comm,gauge_add_of_commute hZX]
  rw [hy,hx]
  calc
    _ = gauge (-Y) s*(gauge (-Z) s*(transport (bulkForm X Y) a N b*gauge Z s))*gauge X s := by simp only [mul_assoc]
    _ = gauge (-Y) s*(gauge (-Z) s*(gauge Z s*transport (bulkForm X Y) a N b))*gauge X s := by rw [hg.eq]
    _ = _ := by rw [←mul_assoc (gauge (-Z) s),gauge_neg_mul,one_mul]

omit [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem gap_tendsto : Tendsto (fun s : ℝ => s+s^2) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [zero_pow (by omega : 2≠0),zero_add] using h.add (h.pow 2)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact add_pos_of_pos_of_nonneg hs (sq_nonneg s)

theorem bulk_limit (F : NilpotentFiltration A) {X Y : A}
    (hX : X∈F.space 1) (hY : Y∈F.space 1) :
    Tendsto (fun s => gauge (-Y) s*transport (bulkForm X Y) s F.cutoff (endpoint s)*gauge X s)
      (𝓝[>] 0) (𝓝 (associator F X Y)) := by
  have h := (gauge_ratio_limit Y).mul (regularizedBulk_two_limit F hX hY tendsto_id gap_tendsto)
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change 0<s at hs
  have hg : gauge Y (1+s)*gauge (-Y) (s+s^2)=gauge (-Y) s := by
    rw [show s+s^2=(1+s)*s by ring,gauge_mul_scale _ (by linarith) hs.ne',←mul_assoc,gauge_mul_neg,one_mul]
  simp only [←mul_assoc]
  rw [hg,show 1-(s+s^2)=endpoint s by dsimp [endpoint]; ring]
  rfl

theorem limit (F : NilpotentFiltration A) {X Y Z : A} (U V : A)
    (hX : X∈F.space 1) (hY : Y∈F.space 1) (hZ : Z∈F.space 1)
    (hZX : Commute Z X) (hZY : Commute Z Y) :
    Tendsto (fun s => gauge (-(Y+Z)) s*
      transport (shiftedBulk X Y U V (s^2)) s F.cutoff (endpoint s)*gauge (X+Z) s)
      (𝓝[>] 0) (𝓝 (associator F X Y)) := by
  have hl := normalized_perturbation_limit (perturbation X Y U V F.cutoff)
    (gauge_subpower (pow_cutoff_eq_zero F ((F.space 1).neg_mem ((F.space 1).add_mem hY hZ))))
    (gauge_subpower (pow_cutoff_eq_zero F ((F.space 1).add_mem hX hZ)))
  have hb := bulk_limit F hX hY
  have he (s : ℝ) := shared_residue_cancel (pow_cutoff_eq_zero F hZ) hZX hZY s (endpoint s) s
  have hb' : Tendsto (fun s => gauge (-(Y+Z)) s*transport (bulkForm X Y) s F.cutoff (endpoint s)*gauge (X+Z) s)
      (𝓝[>] 0) (𝓝 (associator F X Y)) := hb.congr (fun s => (he s).symm)
  simpa only [zero_add,sub_add_cancel] using! hl.add hb'

end DeligneDrinfeld.BCBoundary

namespace DeligneDrinfeld.KZRectangle
open MeasureTheory Set Filter FinitePicard LogRectangle
open scoped Topology
attribute [local instance] LieRing.ofAssociativeRing
variable {K A : Type*} [NontriviallyNormedField K] [NormedAlgebra ℝ K]
  [NormedRing A] [NormedAlgebra K A] [NormedAlgebra ℝ A] [IsScalarTower ℝ K A]

def edges : Fin 6 → Fin 4×Fin 4 := ![(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
def dif (z : Fin 4 → K) (i : Fin 6) : K := z (edges i).1-z (edges i).2

def chords (j : GenericBraid.T K (Fin 4) →ₗ⁅K⁆ A) (i : Fin 6) : A :=
  j (GenericBraid.t (edges i).1 (edges i).2)

omit [NormedAlgebra ℝ K] [NormedAlgebra ℝ A] [IsScalarTower ℝ K A] in
theorem form_eq (j : GenericBraid.T K (Fin 4) →ₗ⁅K⁆ A) (z v : Fin 4 → K) :
    form (chords j) (dif z) (dif v)=j (KZFlat.connection z v) := by
  simp only [form,Fin.sum_univ_succ,KZFlat.connection,KZFlat.combine,KZFlat.coefficients,
    KZFlat.dlog,dif,chords,edges,map_add,map_smul]
  norm_num only [Fin.reduceFinMk,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.isValue,
    Fin.succ_zero_eq_one,Fin.succ_one_eq_two,Fin.zero_eta,Fin.mk_one]
  simp only [Fin.sum_univ_zero,add_zero]
  abel

omit [NormedAlgebra ℝ K] [NormedAlgebra ℝ A] [IsScalarTower ℝ K A] in
theorem form_commute (j : GenericBraid.T K (Fin 4) →ₗ⁅K⁆ A)
    (z v w : Fin 4 → K) (hz : Function.Injective z) :
    Commute (form (chords j) (dif z) (dif v)) (form (chords j) (dif z) (dif w)) := by
  rw [form_eq,form_eq]
  have h := congrArg j (KZFlat.flat z v w hz)
  rw [j.map_lie,map_zero] at h
  exact sub_eq_zero.mp h

omit [NormedRing A] [NormedAlgebra K A] [NormedAlgebra ℝ K] [NormedAlgebra ℝ A]
  [IsScalarTower ℝ K A] in
theorem dif_ne_zero (z : Fin 4 → K) (hz : Function.Injective z) (i : Fin 6) : dif z i≠0 := by
  apply sub_ne_zero.mpr (hz.ne _)
  fin_cases i <;> decide

variable [CompleteSpace A] [FiniteDimensional ℝ A]

theorem transport_derivative (F : NilpotentFiltration A)
    (j : GenericBraid.T K (Fin 4) →ₗ⁅K⁆ A)
    {z zs zt zst : ℝ → ℝ → Fin 4 → K} {a b u v s : ℝ}
    (hab : a≤b) (huv : u≤v)
    (hc : ∀ i (r : K),r • chords j i∈F.space 1)
    (hz : ∀ i,ContinuousOn (fun w : ℝ×ℝ => z w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (hs : ∀ i,ContinuousOn (fun w : ℝ×ℝ => zs w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (ht : ∀ i,ContinuousOn (fun w : ℝ×ℝ => zt w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (hst : ∀ i,ContinuousOn (fun w : ℝ×ℝ => zst w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (hn : ∀ s∈Icc u v,∀ t∈Icc a b,Function.Injective (z s t))
    (hDsz : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun s => z s t i) (zs s t i) s)
    (hDszt : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun s => zt s t i) (zst s t i) s)
    (hDtz : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun t => z s t i) (zt s t i) t)
    (hDtzs : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun t => zs s t i) (zst s t i) t)
    (hss : s∈Ioo u v) :
    HasDerivAt (fun s => transport (fun t => j (KZFlat.connection (z s t) (zt s t))) a F.cutoff b)
      (j (KZFlat.connection (z s b) (zs s b))*transport (fun t => j (KZFlat.connection (z s t) (zt s t))) a F.cutoff b-
        transport (fun t => j (KZFlat.connection (z s t) (zt s t))) a F.cutoff b*j (KZFlat.connection (z s a) (zs s a))) s := by
  simp only [←form_eq]
  apply LogRectangle.transport_derivative F (chords j) (z:=fun s t => dif (z s t))
    (zt:=fun s t => dif (zt s t)) (zs:=fun s t => dif (zs s t))
    (zst:=fun s t => dif (zst s t)) hab huv hc
  · intro i
    exact (hz _).sub (hz _)
  · intro i
    exact (hs _).sub (hs _)
  · intro i
    exact (ht _).sub (ht _)
  · intro i
    exact (hst _).sub (hst _)
  · intro s hs t ht i
    exact dif_ne_zero _ (hn s hs t ht) i
  · intro s hs t ht i
    exact (hDsz s hs t ht _).sub (hDsz s hs t ht _)
  · intro s hs t ht i
    exact (hDszt s hs t ht _).sub (hDszt s hs t ht _)
  · intro s hs t ht i
    exact (hDtz s hs t ht _).sub (hDtz s hs t ht _)
  · intro s hs t ht i
    exact (hDtzs s hs t ht _).sub (hDtzs s hs t ht _)
  · intro t ht
    exact form_commute j _ _ _ (hn s ⟨hss.1.le,hss.2.le⟩ t ht)
  · exact hss

theorem transport_homotopy (F : NilpotentFiltration A)
    (j : GenericBraid.T K (Fin 4) →ₗ⁅K⁆ A)
    {z zs zt zst : ℝ → ℝ → Fin 4 → K} {a b u v p q : ℝ}
    (hab : a≤b) (huv : u<v)
    (hc : ∀ i (r : K),r • chords j i∈F.space 1)
    (hz : ∀ i,ContinuousOn (fun w : ℝ×ℝ => z w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (hs : ∀ i,ContinuousOn (fun w : ℝ×ℝ => zs w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (ht : ∀ i,ContinuousOn (fun w : ℝ×ℝ => zt w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (hst : ∀ i,ContinuousOn (fun w : ℝ×ℝ => zst w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (hn : ∀ s∈Icc u v,∀ t∈Icc a b,Function.Injective (z s t))
    (hDsz : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun s => z s t i) (zs s t i) s)
    (hDszt : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun s => zt s t i) (zst s t i) s)
    (hDtz : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun t => z s t i) (zt s t i) t)
    (hDtzs : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun t => zs s t i) (zst s t i) t)
    (ha : ∀ s∈Ioo u v,zs s a=0) (hb : ∀ s∈Ioo u v,zs s b=0)
    (hp : p∈Icc u v) (hq : q∈Icc u v) :
    transport (fun t => j (KZFlat.connection (z p t) (zt p t))) a F.cutoff b=
      transport (fun t => j (KZFlat.connection (z q t) (zt q t))) a F.cutoff b := by
  simp only [←form_eq]
  apply LogRectangle.transport_constant F (chords j) (p:=p) (q:=q) (z:=fun s t => dif (z s t))
    (zt:=fun s t => dif (zt s t)) (zs:=fun s t => dif (zs s t))
    (zst:=fun s t => dif (zst s t)) hab huv hc
  · intro i
    exact (hz _).sub (hz _)
  · intro i
    exact (hs _).sub (hs _)
  · intro i
    exact (ht _).sub (ht _)
  · intro i
    exact (hst _).sub (hst _)
  · intro s hs t ht i
    exact dif_ne_zero _ (hn s hs t ht) i
  · intro s hs t ht i
    exact (hDsz s hs t ht _).sub (hDsz s hs t ht _)
  · intro s hs t ht i
    exact (hDszt s hs t ht _).sub (hDszt s hs t ht _)
  · intro s hs t ht i
    exact (hDtz s hs t ht _).sub (hDtz s hs t ht _)
  · intro s hs t ht i
    exact (hDtzs s hs t ht _).sub (hDtzs s hs t ht _)
  · intro s hs t ht
    exact form_commute j _ _ _ (hn s ⟨hs.1.le,hs.2.le⟩ t ht)
  · intro s hs
    ext i
    simp [dif,ha s hs]
  · intro s hs
    ext i
    simp [dif,hb s hs]
  · exact hp
  · exact hq

end DeligneDrinfeld.KZRectangle

namespace DeligneDrinfeld.StraightKZ
open MeasureTheory Set Filter FinitePicard KZRectangle LogRectangle
open scoped Topology
attribute [local instance] LieRing.ofAssociativeRing
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def segment (p q : Fin 4 → ℝ) (t : ℝ) (i : Fin 4) : ℝ := (1-t)*p i+t*q i

def velocity (p q : Fin 4 → ℝ) (i : Fin 4) : ℝ := q i-p i

@[simp] theorem segment_zero (p q : Fin 4 → ℝ) : segment p q 0=p := by
  ext i; simp [segment]
@[simp] theorem segment_one (p q : Fin 4 → ℝ) : segment p q 1=q := by
  ext i; simp [segment]

theorem segment_strictMono {p q : Fin 4 → ℝ} (hp : StrictMono p) (hq : StrictMono q)
    {t : ℝ} (ht : t∈Icc 0 1) : StrictMono (segment p q t) := by
  intro i k hik
  dsimp [segment]
  have h0 := hp hik
  have h1 := hq hik
  have h := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr h0.le)
  have hh := mul_nonneg ht.1 (sub_nonneg.mpr h1.le)
  by_cases htp : 0<t
  · have hpos := mul_pos htp (sub_pos.mpr h1)
    nlinarith
  · have htz : t=0 := le_antisymm (not_lt.mp htp) ht.1
    simpa only [htz,sub_zero,one_mul,zero_mul,add_zero] using h0

theorem segment_derivative (p q : Fin 4 → ℝ) (t : ℝ) (i : Fin 4) :
    HasDerivAt (fun t => segment p q t i) (velocity p q i) t := by
  have h : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id t
  convert! (((hasDerivAt_const t (1:ℝ)).sub h).mul_const (p i)).add (h.mul_const (q i)) using 1
  dsimp [velocity]
  ring

def connection (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A) (p q : Fin 4 → ℝ) (t : ℝ) : A :=
  j (KZFlat.connection (segment p q t) (velocity p q))

def fundamental (F : NilpotentFiltration A) (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
    (p q : Fin 4 → ℝ) : A := transport (connection j p q) 0 F.cutoff 1

lemma connection_mem (F : NilpotentFiltration A) (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
    (hc : ∀ i,chords j i∈F.space 1) (z v : Fin 4 → ℝ) : j (KZFlat.connection z v)∈F.space 1 := by
  rw [←form_eq]
  exact (F.space 1).sum_mem (fun i hi => (F.space 1).smul_mem _ (hc i))

lemma zero_connection (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A) (p : Fin 4 → ℝ) :
    j (KZFlat.connection p 0)=0 := by
  rw [←form_eq]
  simp [form,dif]

variable [CompleteSpace A] [FiniteDimensional ℝ A]

omit [CompleteSpace A] in
theorem fundamental_isUnit (F : NilpotentFiltration A)
    (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A) (hc : ∀ i,chords j i∈F.space 1) (p q : Fin 4 → ℝ) :
    IsUnit (fundamental F j p q) :=
  transport_isUnit F (fun _ => connection_mem F j hc _ _) _ _ _

theorem fundamental_derivative (F : NilpotentFiltration A)
    (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A) (hc : ∀ i,chords j i∈F.space 1)
    {p : Fin 4 → ℝ} {q q' : ℝ → Fin 4 → ℝ} {a b s : ℝ}
    (hp : StrictMono p) (hq : ∀ s∈Icc a b,StrictMono (q s))
    (hqc : ∀ i,ContinuousOn (fun s => q s i) (Icc a b))
    (hqc' : ∀ i,ContinuousOn (fun s => q' s i) (Icc a b))
    (hqd : ∀ s∈Ioo a b,∀ i,HasDerivAt (fun s => q s i) (q' s i) s)
    (hs : s∈Ioo a b) :
    HasDerivAt (fun s => fundamental F j p (q s))
      (j (KZFlat.connection (q s) (q' s))*fundamental F j p (q s)) s := by
  have hab : a≤b := le_trans hs.1.le hs.2.le
  have hq2 (i : Fin 4) : ContinuousOn (fun w : ℝ×ℝ => q w.1 i) (Icc a b ×ˢ Icc 0 1) :=
    (hqc i).comp continuous_fst.continuousOn (fun w hw => hw.1)
  have hq2' (i : Fin 4) : ContinuousOn (fun w : ℝ×ℝ => q' w.1 i) (Icc a b ×ˢ Icc 0 1) :=
    (hqc' i).comp continuous_fst.continuousOn (fun w hw => hw.1)
  have h := KZRectangle.transport_derivative F j (z:=fun s t => segment p (q s) t)
    (zt:=fun s _ => velocity p (q s)) (zs:=fun s t i => t*q' s i)
    (zst:=fun s _ => q' s) (by norm_num : (0:ℝ)≤1) hab
    (fun i r => (F.space 1).smul_mem r (hc i))
    (fun i => ((continuousOn_const.sub continuous_snd.continuousOn).mul continuousOn_const).add
      (continuous_snd.continuousOn.mul (hq2 i)))
    (fun i => continuous_snd.continuousOn.mul (hq2' i))
    (fun i => (hq2 i).sub continuousOn_const) (fun i => hq2' i)
    (fun v hv t ht => (segment_strictMono hp (hq v hv) ht).injective)
    (fun v hv t ht i => by
      simpa only [segment,Pi.add_apply,zero_add] using! (hasDerivAt_const v ((1-t)*p i)).add ((hqd v hv i).const_mul t))
    (fun v hv t ht i => by
      simpa [velocity] using! (hqd v hv i).sub_const (p i))
    (fun v hv t ht i => segment_derivative p (q v) t i)
    (fun v hv t ht i => by
      simpa using! (hasDerivAt_id t).mul_const (q' v i)) hs
  have hzero : (fun i => (0:ℝ)*q' s i)=(0:Fin 4 → ℝ) := by ext; simp
  have hone : (fun i => (1:ℝ)*q' s i)=q' s := by ext; simp
  simpa only [segment_zero,segment_one,hzero,hone,zero_connection,mul_zero,sub_zero,
    fundamental,StraightKZ.connection] using! h

end DeligneDrinfeld.StraightKZ

end

end OAI
