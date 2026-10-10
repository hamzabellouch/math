import OAI.Analysis.LiebThirring.QuadraticForms

namespace OAI


noncomputable section
namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set
open scoped Topology

/-- C¹ representatives of real H¹, with the L² inner product (not the H¹ norm). -/
def c1L2Submodule : Submodule ℝ ((ℝ → ℝ) × (ℝ → ℝ)) where
  carrier := {u | MemLp u.1 2 volume ∧ MemLp u.2 2 volume ∧ Continuous u.2 ∧
    ∀ x, HasDerivAt u.1 (u.2 x) x}
  zero_mem' := ⟨by simp,by simp,continuous_zero,fun x ↦ hasDerivAt_const x 0⟩
  add_mem' := by
    rintro u v ⟨hu,hu',hc,hd⟩ ⟨hv,hv',hvc,hvd⟩
    exact ⟨hu.add hv,hu'.add hv',hc.add hvc,fun x ↦ (hd x).add (hvd x)⟩
  smul_mem' := by
    rintro c u ⟨hu,hu',hc,hd⟩
    exact ⟨hu.const_smul c,hu'.const_smul c,continuous_const.smul hc,
      fun x ↦ (hd x).const_smul c⟩

def C1L2 : Type := ↥c1L2Submodule
instance : AddCommGroup C1L2 := inferInstanceAs (AddCommGroup ↥c1L2Submodule)
instance : Module ℝ C1L2 := inferInstanceAs (Module ℝ ↥c1L2Submodule)
namespace C1L2

def val (u : C1L2) : ℝ → ℝ := u.1.1
def grad (u : C1L2) : ℝ → ℝ := u.1.2
lemma val_memLp (u : C1L2) : MemLp u.val 2 volume := u.property.1
lemma grad_memLp (u : C1L2) : MemLp u.grad 2 volume := u.property.2.1
lemma grad_continuous (u : C1L2) : Continuous u.grad := u.property.2.2.1
lemma hasDerivAt (u : C1L2) (x : ℝ) : HasDerivAt u.val (u.grad x) x := u.property.2.2.2 x
lemma continuous (u : C1L2) : Continuous u.val := continuous_iff_continuousAt.mpr (fun x ↦ (u.hasDerivAt x).continuousAt)

def toLp : C1L2 →ₗ[ℝ] Lp ℝ 2 (volume : Measure ℝ) where
  toFun u := u.val_memLp.toLp u.val
  map_add' u v := u.val_memLp.toLp_add v.val_memLp
  map_smul' c u := u.val_memLp.toLp_const_smul c

lemma toLp_injective : Function.Injective toLp := by
  intro u v h
  have ha : u.val =ᵐ[volume] v.val := (MemLp.toLp_eq_toLp_iff u.val_memLp v.val_memLp).mp h
  have hv : u.val = v.val := MeasureTheory.Measure.eq_of_ae_eq ha u.continuous v.continuous
  apply Subtype.ext
  apply Prod.ext
  · exact hv
  · funext x
    exact ((hv ▸ u.hasDerivAt x) : HasDerivAt v.val (u.grad x) x).unique (v.hasDerivAt x)

instance : NormedAddCommGroup C1L2 := NormedAddCommGroup.induced C1L2 (Lp ℝ 2 (volume : Measure ℝ)) toLp toLp_injective
instance : InnerProductSpace ℝ C1L2 := InnerProductSpace.induced toLp

@[simp] lemma val_zero (x : ℝ) : (0 : C1L2).val x = 0 := rfl
@[simp] lemma grad_zero (x : ℝ) : (0 : C1L2).grad x = 0 := rfl
@[simp] lemma val_add (u v : C1L2) (x : ℝ) : (u+v).val x = u.val x+v.val x := rfl
@[simp] lemma grad_add (u v : C1L2) (x : ℝ) : (u+v).grad x = u.grad x+v.grad x := rfl
@[simp] lemma val_smul (c : ℝ) (u : C1L2) (x : ℝ) : (c • u).val x = c*u.val x := rfl
@[simp] lemma grad_smul (c : ℝ) (u : C1L2) (x : ℝ) : (c • u).grad x = c*u.grad x := rfl

lemma inner_eq_integral (u v : C1L2) : inner ℝ u v = ∫ x, u.val x*v.val x := by
  change inner ℝ (toLp u) (toLp v) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [u.val_memLp.coeFn_toLp,v.val_memLp.coeFn_toLp] with x hx hy
  change (toLp v) x*(toLp u) x = u.val x*v.val x
  rw [show (toLp u) x = u.val x from hx,show (toLp v) x = v.val x from hy,mul_comm]

end C1L2
end SharpLiebThirring.SobolevProof
namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set
lemma locallyIntegrable_intervalIntegrable {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  (intervalIntegrable_iff').mpr (hf.integrableOn_isCompact isCompact_uIcc)
end SharpLiebThirring.SobolevProof
namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff
namespace C1L2

lemma contDiff (u : C1L2) : ContDiff ℝ 1 u.val := by
  rw [contDiff_one_iff_deriv]
  exact ⟨fun x ↦ (u.hasDerivAt x).differentiableAt,
    by convert u.grad_continuous using 1; ext x; exact (u.hasDerivAt x).deriv⟩

lemma ac (u : C1L2) (a b : ℝ) : AbsolutelyContinuousOnInterval u.val a b :=
  u.contDiff.contDiffOn.absolutelyContinuousOnInterval

@[simp] lemma deriv_val (u : C1L2) : deriv u.val = u.grad := funext (fun x ↦ (u.hasDerivAt x).deriv)

/-- Exact integrated real eigen-equation; no regularity of W beyond local L¹. -/
def IsEigen (W : ℝ → ℝ) (k : ℝ) (u : C1L2) : Prop :=
  ∀ a b, u.grad b-u.grad a = ∫ x in a..b, (k^2-W x)*u.val x

lemma eigen_integrable {W : ℝ → ℝ} (hW : LocallyIntegrable W volume)
    (k : ℝ) (u : C1L2) : LocallyIntegrable (fun x ↦ (k^2-W x)*u.val x) volume :=
  ((locallyIntegrable_const (c := k^2)).sub hW).mul_continuous u.continuous

def eigenSubmodule {W : ℝ → ℝ} (hW : LocallyIntegrable W volume) (k : ℝ) : Submodule ℝ C1L2 where
  carrier := {u | u.IsEigen W k}
  zero_mem' := by intro a b; simp
  add_mem' := by
    intro u v hu hv a b
    simp only [val_add,grad_add,mul_add]
    rw [intervalIntegral.integral_add
      (locallyIntegrable_intervalIntegrable (eigen_integrable hW k u) a b)
      (locallyIntegrable_intervalIntegrable (eigen_integrable hW k v) a b),← hu a b,← hv a b]
    ring
  smul_mem' := by
    intro c u hu a b
    simp only [val_smul,grad_smul]
    simp_rw [mul_left_comm (k^2-_)]
    rw [intervalIntegral.integral_const_mul,← hu a b]
    ring

lemma IsEigen.grad_ac {W : ℝ → ℝ} {k : ℝ} {u : C1L2}
    (hu : u.IsEigen W k) (hW : LocallyIntegrable W volume) (a b : ℝ) :
    AbsolutelyContinuousOnInterval u.grad a b := by
  have hh : u.grad = fun x ↦ u.grad a+∫ t in a..x, (k^2-W t)*u.val t := by
    funext x; linarith [hu a x]
  rw [hh]
  exact ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ ↦ u.grad a)).contDiffOn.absolutelyContinuousOnInterval).add
    ((locallyIntegrable_intervalIntegrable (eigen_integrable hW k u) a b).absolutelyContinuousOnInterval_intervalIntegral (by simp))

lemma IsEigen.grad_deriv {W : ℝ → ℝ} {k : ℝ} {u : C1L2}
    (hu : u.IsEigen W k) (hW : LocallyIntegrable W volume) :
    ∀ᵐ x, deriv u.grad x = (k^2-W x)*u.val x := by
  have hh : u.grad = fun x ↦ u.grad 0+∫ t in (0 : ℝ)..x, (k^2-W t)*u.val t := by
    funext x; linarith [hu 0 x]
  have hd := LocallyIntegrable.ae_hasDerivAt_integral (eigen_integrable hW k u)
  filter_upwards [hd] with x hx
  rw [hh]
  exact ((hx 0).const_add (u.grad 0)).deriv

lemma IsEigen.weak_interval {W : ℝ → ℝ} {k a b : ℝ} {u : C1L2}
    (hu : u.IsEigen W k) (hW : LocallyIntegrable W volume) (v : C1L2)
    (ha : v.val a = 0) (hb : v.val b = 0) :
    (∫ x in a..b, u.grad x*v.grad x) = -(∫ x in a..b, (k^2-W x)*u.val x*v.val x) := by
  have h := (hu.grad_ac hW a b).integral_mul_deriv_eq_deriv_mul (v.ac a b)
  rw [v.deriv_val,ha,hb,mul_zero,mul_zero,sub_self,zero_sub] at h
  rw [h]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hu.grad_deriv hW] with x hx _
  rw [hx]

lemma IsEigen.weak_compact {W : ℝ → ℝ} {k : ℝ} {u : C1L2}
    (hu : u.IsEigen W k) (hW : LocallyIntegrable W volume) (v : C1L2)
    (hvc : HasCompactSupport v.val) :
    (∫ x, u.grad x*v.grad x) = -(∫ x, (k^2-W x)*u.val x*v.val x) := by
  obtain ⟨R,hR,hzero⟩ := hvc.exists_pos_le_norm
  have hvd : v.grad = deriv v.val := v.deriv_val.symm
  have hi1 : Function.support (fun x ↦ u.grad x*v.grad x) ⊆ Ioc (-(R+1)) (R+1) := by
    intro x hx
    have hxs : x ∈ tsupport v.val :=
      tsupport_deriv_subset (subset_tsupport (deriv v.val) (by
        rw [← hvd]; exact (mul_ne_zero_iff.mp hx).2))
    have hRp : tsupport v.val ⊆ closedBall (0 : ℝ) R := by
      apply closure_minimal _ isClosed_closedBall
      intro x hx
      simp only [mem_closedBall,dist_zero_right,Real.norm_eq_abs]
      exact le_of_lt (lt_of_not_ge (fun h ↦ hx (hzero x h)))
    have hxR := hRp hxs
    simp only [mem_closedBall,dist_zero_right,Real.norm_eq_abs,abs_le] at hxR
    constructor <;> linarith [hxR.1,hxR.2]
  have hi2 : Function.support (fun x ↦ (k^2-W x)*u.val x*v.val x) ⊆ Ioc (-(R+1)) (R+1) := by
    intro x hx
    have hxR : |x| < R := lt_of_not_ge (fun hh ↦ (mul_ne_zero_iff.mp hx).2 (hzero x hh))
    rw [abs_lt] at hxR
    constructor <;> linarith [hxR.1,hxR.2]
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hi1,
    ← intervalIntegral.integral_eq_integral_of_support_subset hi2]
  exact hu.weak_interval hW v (hzero _ (by rw [Real.norm_eq_abs,abs_neg,abs_of_pos (by linarith)]; linarith))
    (hzero _ (by rw [Real.norm_eq_abs,abs_of_pos (by linarith)]; linarith))

end C1L2
end SharpLiebThirring.SobolevProof
namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set Filter
open scoped Topology ContDiff

lemma cutoffDerivative_compact (n : ℕ) : HasCompactSupport (cutoffDerivative n) := by
  have hh : cutoffDerivative n = deriv (cutoff n) := funext (fun x ↦ (cutoff_hasDerivAt n x).deriv.symm)
  rw [hh]
  exact (cutoff_compact n).deriv

namespace C1L2

def cut (n : ℕ) (u : C1L2) : C1L2 :=
  ⟨⟨fun x ↦ cutoff n x*u.val x,fun x ↦ cutoffDerivative n x*u.val x+cutoff n x*u.grad x⟩,
    ⟨(((cutoff_contDiff n).continuous).mul u.continuous).memLp_of_hasCompactSupport
      ((cutoff_compact n).mul_right),
    (((cutoffDerivative_continuous n).mul u.continuous).add
      (((cutoff_contDiff n).continuous).mul u.grad_continuous)).memLp_of_hasCompactSupport
      (((cutoffDerivative_compact n).mul_right).add ((cutoff_compact n).mul_right)),
    ((cutoffDerivative_continuous n).mul u.continuous).add
      (((cutoff_contDiff n).continuous).mul u.grad_continuous),
    fun x ↦ (cutoff_hasDerivAt n x).mul (u.hasDerivAt x)⟩⟩

@[simp] lemma cut_val (n : ℕ) (u : C1L2) (x : ℝ) : (u.cut n).val x = cutoff n x*u.val x := rfl
@[simp] lemma cut_grad (n : ℕ) (u : C1L2) (x : ℝ) :
    (u.cut n).grad x = cutoffDerivative n x*u.val x+cutoff n x*u.grad x := rfl
lemma cut_compact (n : ℕ) (u : C1L2) : HasCompactSupport (u.cut n).val := (cutoff_compact n).mul_right

def cutMap (n : ℕ) : C1L2 →ₗ[ℝ] C1L2 where
  toFun := cut n
  map_add' u v := by
    apply Subtype.ext
    apply Prod.ext <;> funext x
    · change cutoff n x*(u.val x+v.val x) = cutoff n x*u.val x+cutoff n x*v.val x
      ring
    · change cutoffDerivative n x*(u.val x+v.val x)+cutoff n x*(u.grad x+v.grad x) =
        (cutoffDerivative n x*u.val x+cutoff n x*u.grad x)+
          (cutoffDerivative n x*v.val x+cutoff n x*v.grad x)
      ring
  map_smul' c u := by
    apply Subtype.ext
    apply Prod.ext <;> funext x
    · change cutoff n x*(c*u.val x) = c*(cutoff n x*u.val x)
      ring
    · change cutoffDerivative n x*(c*u.val x)+cutoff n x*(c*u.grad x) =
        c*(cutoffDerivative n x*u.val x+cutoff n x*u.grad x)
      ring

lemma integrable_val_mul (u v : C1L2) : Integrable (fun x ↦ u.val x*v.val x) :=
  u.val_memLp.integrable_mul v.val_memLp
lemma integrable_grad_mul (u v : C1L2) : Integrable (fun x ↦ u.grad x*v.grad x) :=
  u.grad_memLp.integrable_mul v.grad_memLp

lemma integral_real_multiplier_tendsto {a : ℕ → ℝ → ℝ} {l : ℝ} {g : ℝ → ℝ}
    (hg : Integrable g) (ha : ∀ n, AEStronglyMeasurable (a n))
    {D : ℝ} (hD : ∀ n x, |a n x| ≤ D)
    (hl : ∀ x, Tendsto (fun n ↦ a n x) atTop (𝓝 l)) :
    Tendsto (fun n ↦ ∫ x, a n x*g x) atTop (𝓝 (l*∫ x, g x)) := by
  rw [← integral_const_mul]
  apply tendsto_integral_of_dominated_convergence (fun x ↦ D*|g x|)
  · exact fun n ↦ (ha n).mul hg.aestronglyMeasurable
  · exact hg.abs.const_mul D
  · intro n; exact ae_of_all _ (fun x ↦ by rw [Real.norm_eq_abs,abs_mul]; exact mul_le_mul_of_nonneg_right (hD n x) (abs_nonneg _))
  · exact ae_of_all _ (fun x ↦ (hl x).mul_const _)

lemma cutoff_inner_tendsto (u v : C1L2) :
    Tendsto (fun n ↦ inner ℝ (u.cut n) (v.cut n)) atTop (𝓝 (inner ℝ u v)) := by
  simp_rw [inner_eq_integral,cut_val,show ∀ (n : ℕ) (x : ℝ),
    cutoff n x*u.val x*(cutoff n x*v.val x) = cutoff n x^2*(u.val x*v.val x) by intros; ring]
  simpa only [one_mul] using integral_real_multiplier_tendsto (l := 1) (a := fun n x ↦ cutoff n x^2) (u.integrable_val_mul v)
    (fun n ↦ ((cutoff_contDiff n).continuous.pow 2).aestronglyMeasurable)
    (D := 1) (fun n x ↦ by
      rw [abs_pow]; have h := cutoff_bound n x; nlinarith [abs_nonneg (cutoff n x)])
    (fun x ↦ by simpa using (cutoff_tendsto x).pow 2)

end C1L2
end SharpLiebThirring.SobolevProof
namespace SharpLiebThirring.SobolevProof.C1L2
open MeasureTheory Set Filter
open scoped Topology ContDiff

def energy (W : ℝ → ℝ) (u v : C1L2) : ℝ :=
  (∫ x, u.grad x*v.grad x)-(∫ x, W x*u.val x*v.val x)

lemma energy_symm (W : ℝ → ℝ) (u v : C1L2) : energy W u v = energy W v u := by
  unfold energy
  congr 1 <;> apply integral_congr_ae <;> exact ae_of_all _ (fun _ ↦ by ring)

lemma integrable_potential {W : ℝ → ℝ} (hW : LocallyIntegrable W volume) (u v : C1L2)
    (hv : HasCompactSupport v.val) : Integrable (fun x ↦ W x*u.val x*v.val x) :=
  (hW.mul_continuous u.continuous).integrable_smul_right_of_hasCompactSupport v.continuous hv

private lemma cut_energy_algebra (c d u v du dv k w : ℝ) :
    (d*u+c*du)*(d*v+c*dv)-w*(c*u)*(c*v) =
      (du*(d*(c*v)+c*(d*v+c*dv))+(k^2-w)*u*(c*(c*v)))+
        -k^2*((c*u)*(c*v))+d^2*(u*v)+(c*d)*(u*dv-du*v) := by ring

lemma cut_error_integrable (u v : C1L2) (n : ℕ) :
    Integrable (fun x ↦ cutoffDerivative n x^2*(u.val x*v.val x)) := by
  obtain ⟨D,hD,hDb⟩ := cutoffDerivative_uniform_bound
  apply (u.integrable_val_mul v).bdd_mul
    (((cutoffDerivative_continuous n).pow 2).aestronglyMeasurable) (c := D^2)
  exact ae_of_all _ (fun x ↦ by
    rw [Real.norm_eq_abs,Pi.pow_apply,abs_pow]
    nlinarith [hDb n x,abs_nonneg (cutoffDerivative n x)])

lemma cut_cross_integrable (u v : C1L2) (n : ℕ) :
    Integrable (fun x ↦ (cutoff n x*cutoffDerivative n x)*(u.val x*v.grad x-u.grad x*v.val x)) :=
  (((cutoff_contDiff n).continuous.mul (cutoffDerivative_continuous n)).mul
    ((u.continuous.mul v.grad_continuous).sub (u.grad_continuous.mul v.continuous))).integrable_of_hasCompactSupport
    (((cutoff_compact n).mul_right).mul_right)

lemma cut_weak_integrable {W : ℝ → ℝ} (hW : LocallyIntegrable W volume) (k : ℝ)
    (u v : C1L2) (n : ℕ) :
    Integrable (fun x ↦ (k^2-W x)*u.val x*((v.cut n).cut n).val x) :=
  ((locallyIntegrable_const (c := k^2)).sub hW).mul_continuous u.continuous |>.integrable_smul_right_of_hasCompactSupport
    ((v.cut n).cut n).continuous ((v.cut n).cut_compact n)

lemma cut_weak_zero {W : ℝ → ℝ} {k : ℝ} {u : C1L2}
    (hu : u.IsEigen W k) (hW : LocallyIntegrable W volume) (v : C1L2) (n : ℕ) :
    (∫ x, u.grad x*((v.cut n).cut n).grad x+(k^2-W x)*u.val x*((v.cut n).cut n).val x) = 0 := by
  rw [integral_add (u.integrable_grad_mul _) (cut_weak_integrable hW k u v n),
    hu.weak_compact hW _ ((v.cut n).cut_compact n)]
  ring

lemma cut_energy_identity {W : ℝ → ℝ} {k : ℝ} {u : C1L2}
    (hu : u.IsEigen W k) (hW : LocallyIntegrable W volume) (v : C1L2) (n : ℕ) :
    energy W (u.cut n) (v.cut n) = -k^2*inner ℝ (u.cut n) (v.cut n)+
      (∫ x, cutoffDerivative n x^2*(u.val x*v.val x))+
      (∫ x, (cutoff n x*cutoffDerivative n x)*(u.val x*v.grad x-u.grad x*v.val x)) := by
  let z := (v.cut n).cut n
  have hiw := cut_weak_integrable hW k u v n
  have hig := u.integrable_grad_mul z
  have hiz : Integrable (fun x ↦ u.grad x*z.grad x+(k^2-W x)*u.val x*z.val x) := hig.add hiw
  have hzero := cut_weak_zero hu hW v n
  have hpair := (u.cut n).integrable_val_mul (v.cut n)
  have hi3 := cut_error_integrable u v n
  have hic := cut_cross_integrable u v n
  rw [energy,inner_eq_integral,← integral_const_mul,
    ← integral_sub ((u.cut n).integrable_grad_mul (v.cut n)) (integrable_potential hW _ _ (v.cut_compact n))]
  calc
    _ = (∫ x, u.grad x*z.grad x+(k^2-W x)*u.val x*z.val x) +
      (∫ x, -k^2*((u.cut n).val x*(v.cut n).val x))+
      (∫ x, cutoffDerivative n x^2*(u.val x*v.val x))+
      (∫ x, (cutoff n x*cutoffDerivative n x)*(u.val x*v.grad x-u.grad x*v.val x)) := by
      have h1 := integral_add hiz (hpair.const_mul (-k^2))
      have h2 := integral_add (hiz.add (hpair.const_mul (-k^2))) hi3
      have h3 := integral_add ((hiz.add (hpair.const_mul (-k^2))).add hi3) hic
      simp only [Pi.add_apply] at h1 h2 h3
      rw [← h1, ← h2, ← h3]
      apply integral_congr_ae
      exact ae_of_all _ (fun x ↦ by simp only [z,cut_val,cut_grad]; exact cut_energy_algebra _ _ _ _ _ _ _ _)
    _ = _ := by rw [hzero,zero_add]

lemma cut_energy_tendsto {W : ℝ → ℝ} {k : ℝ} {u : C1L2}
    (hu : u.IsEigen W k) (hW : LocallyIntegrable W volume) (v : C1L2) :
    Tendsto (fun n ↦ energy W (u.cut n) (v.cut n)) atTop (𝓝 (-k^2*inner ℝ u v)) := by
  obtain ⟨D,hD,hDb⟩ := cutoffDerivative_uniform_bound
  have hd : Tendsto (fun n ↦ ∫ x, cutoffDerivative n x^2*(u.val x*v.val x)) atTop (𝓝 0) := by
    simpa only [zero_mul] using integral_real_multiplier_tendsto (l := 0) (a := fun n x ↦ cutoffDerivative n x^2) (u.integrable_val_mul v)
      (fun n ↦ ((cutoffDerivative_continuous n).pow 2).aestronglyMeasurable)
      (D := D^2) (fun n x ↦ by
        rw [abs_pow]; nlinarith [hDb n x,abs_nonneg (cutoffDerivative n x)])
      (fun x ↦ by simpa using (cutoffDerivative_tendsto x).pow 2)
  have hc : Tendsto (fun n ↦ ∫ x, (cutoff n x*cutoffDerivative n x)*(u.val x*v.grad x-u.grad x*v.val x)) atTop (𝓝 0) := by
    simpa only [zero_mul,Pi.sub_apply,Pi.mul_apply] using integral_real_multiplier_tendsto (l := 0) (a := fun n x ↦ cutoff n x*cutoffDerivative n x)
      ((u.val_memLp.integrable_mul v.grad_memLp).sub (u.grad_memLp.integrable_mul v.val_memLp))
      (fun n ↦ (((cutoff_contDiff n).continuous).mul (cutoffDerivative_continuous n)).aestronglyMeasurable)
      (D := D) (fun n x ↦ by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_right (cutoff_bound n x) (abs_nonneg _)).trans (by simpa using hDb n x))
      (fun x ↦ by simpa using (cutoff_tendsto x).mul (cutoffDerivative_tendsto x))
  simp_rw [cut_energy_identity hu hW v]
  simpa only [add_zero] using (((u.cutoff_inner_tendsto v).const_mul (-k^2)).add hd).add hc

lemma eigen_orthogonal {W : ℝ → ℝ} {k l : ℝ} {u v : C1L2}
    (hu : u.IsEigen W k) (hv : v.IsEigen W l) (hW : LocallyIntegrable W volume)
    (hkl : k^2 ≠ l^2) : inner ℝ u v = 0 := by
  have h1 := cut_energy_tendsto hu hW v
  have h2 := cut_energy_tendsto hv hW u
  have h2' : Tendsto (fun n ↦ energy W (u.cut n) (v.cut n)) atTop (𝓝 (-l^2*inner ℝ u v)) := by
    convert h2 using 1
    · ext n; exact energy_symm W _ _
    · rw [real_inner_comm v u]
  have hh := tendsto_nhds_unique h1 h2'
  exact (mul_eq_zero.mp (show (k^2-l^2)*inner ℝ u v = 0 by linarith)).resolve_left (sub_ne_zero.mpr hkl)

end SharpLiebThirring.SobolevProof.C1L2

end

end OAI
