import OAI.Analysis.HotSpots.Hodge
import OAI.Analysis.HotSpots.Pullback

namespace OAI

section ActualVectorSupport
noncomputable section
section H1SmoothMultiplierActualCompatibleLayer
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal
namespace StrictHotSpots



lemma HasH1Gradient.mul_smooth {Ω : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : HasH1Gradient Ω u g) {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
    (hb0 : MemLp b ∞ (volume.restrict Ω))
    (hb1 : MemLp (gradient b) ∞ (volume.restrict Ω)) :
    HasH1Gradient Ω (fun x => b x*u x) (fun x => b x • g x+u x • gradient b x) := by
  have hval : MemLp (fun x => b x*u x) 2 (volume.restrict Ω) := hb0.fun_mul hu.1
  have hbg : MemLp (fun x => b x • g x) 2 (volume.restrict Ω) := hb0.smul hu.2.1
  have hug : MemLp (fun x => u x • gradient b x) 2 (volume.restrict Ω) := hu.1.smul hb1
  refine ⟨hval,hbg.add hug,?_⟩
  intro φ hφ hk hs e
  have hp : HasCompactSupport (fun x => b x*φ x) := hk.mul_left
  have hps : tsupport (fun x => b x*φ x) ⊆ Ω := tsupport_mul_subset_right.trans hs
  have h := hu.2.2 (fun x => b x*φ x) (hb.mul hφ) hp hps e
  have hdb (x : Plane) : fderiv ℝ (fun x => b x*φ x) x e =
      (fderiv ℝ b x e)*φ x+b x*(fderiv ℝ φ x e) := by
    rw [fderiv_fun_mul (hb.differentiable (by simp) x) (hφ.differentiable (by simp) x)]
    simp only [add_apply,smul_apply,smul_eq_mul]
    ring
  have hφ2 := test_memLp (Ω := Ω) hφ hk
  have hdφ2 := test_derivative_memLp (Ω := Ω) hφ hk e
  have hd : MemLp (fun x => fderiv ℝ b x e) ∞ (volume.restrict Ω) := by
    simpa only [inner_gradient_left] using hb1.inner_const (𝕜 := ℝ) e
  have hud : MemLp (fun x => (fderiv ℝ b x e)*u x) 2 (volume.restrict Ω) := hd.fun_mul hu.1
  have hui : Integrable (fun x => u x*(fderiv ℝ b x e)*φ x) (volume.restrict Ω) :=
    (hud.integrable_mul hφ2).congr (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  have hvi : Integrable (fun x => b x*u x*(fderiv ℝ φ x e)) (volume.restrict Ω) :=
    hval.integrable_mul hdφ2
  have hgi : Integrable (fun x => inner ℝ (b x • g x) e*φ x) (volume.restrict Ω) :=
    (hbg.inner_const (𝕜 := ℝ) e).integrable_mul hφ2
  simp_rw [hdb,mul_add] at h
  have hl : (∫ x in Ω, u x*((fderiv ℝ b x e)*φ x)+u x*(b x*(fderiv ℝ φ x e))) =
      (∫ x in Ω, u x*(fderiv ℝ b x e)*φ x)+
      (∫ x in Ω, b x*u x*(fderiv ℝ φ x e)) := by
    convert integral_add hui hvi using 1
    congr 1
    funext x
    ring
  rw [hl] at h
  have hr : (∫ x in Ω, inner ℝ (g x) e*(b x*φ x)) =
      ∫ x in Ω, inner ℝ (b x • g x) e*φ x := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [real_inner_smul_left]
    ring
  rw [hr] at h
  have hg : (∫ x in Ω, inner ℝ (b x • g x+u x • gradient b x) e*φ x) =
      (∫ x in Ω,inner ℝ (b x • g x) e*φ x)+
      (∫ x in Ω,u x*(fderiv ℝ b x e)*φ x) := by
    simp_rw [inner_add_left,real_inner_smul_left,inner_gradient_left,add_mul]
    simpa only [real_inner_smul_left] using integral_add hgi hui
  rw [hg]
  linarith

namespace H1
variable {Ω : Set Plane} {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
    (hb0 : MemLp b ∞ (volume.restrict Ω))
    (hb1 : MemLp (gradient b) ∞ (volume.restrict Ω))

def smoothMul (u : H1 Ω) : H1 Ω :=
  ((H1.hasH1Gradient u).mul_smooth hb hb0 hb1).toH1

lemma smoothMul_value_ae (u : H1 Ω) : H1.value (smoothMul hb hb0 hb1 u) =ᵐ[volume.restrict Ω]
    fun x => b x*H1.value u x :=
  ((H1.hasH1Gradient u).mul_smooth hb hb0 hb1).1.coeFn_toLp

lemma smoothMul_grad_ae (u : H1 Ω) : H1.grad (smoothMul hb hb0 hb1 u) =ᵐ[volume.restrict Ω]
    fun x => b x • H1.grad u x+H1.value u x • gradient b x :=
  ((H1.hasH1Gradient u).mul_smooth hb hb0 hb1).2.1.coeFn_toLp
end H1
end StrictHotSpots
end H1SmoothMultiplierActualCompatibleLayer

section NullBoundaryFormActualCompatibleLayer
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal
namespace StrictHotSpots.Hodge
variable {Ω : Set Plane}

lemma rotL_skew (u v : V2 Ω) : inner ℝ (rotL Ω u) v = -inner ℝ u (rotL Ω v) := by
  rw [L2.inner_def,L2.inner_def,← integral_neg]
  apply integral_congr_ae
  filter_upwards [rotL_ae u,rotL_ae v] with x hx hy
  rw [hx,hy,rot_skew]


def skewEnergy (u v : H1 Ω) : ℝ := inner ℝ (H1.grad u) (rotL Ω (H1.grad v))

lemma skewEnergy_skew (u v : H1 Ω) : skewEnergy u v = -skewEnergy v u := by
  exact (real_inner_comm _ _).trans (rotL_skew _ _)

lemma skewEnergy_zero_right (ho : IsOpen Ω) (u : H1 Ω) (v : H10 ho) :
    skewEnergy u v.val = 0 := grad_rotGrad_orthogonal ho u v

lemma skewEnergy_zero_left (ho : IsOpen Ω) (u : H10 ho) (v : H1 Ω) :
    skewEnergy u.val v = 0 := (skewEnergy_skew _ _).trans (by rw [skewEnergy_zero_right ho,neg_zero])

lemma skewEnergy_add_left (u v w : H1 Ω) : skewEnergy (u+v) w = skewEnergy u w+skewEnergy v w := by
  unfold skewEnergy
  rw [map_add,inner_add_left]
lemma skewEnergy_add_right (u v w : H1 Ω) : skewEnergy u (v+w) = skewEnergy u v+skewEnergy u w := by
  unfold skewEnergy
  rw [map_add,map_add,inner_add_right]




def boundaryDefect (X Y : Fin 2 → H1 Ω) : ℝ :=
  -skewEnergy (X 0) (Y 1)+skewEnergy (X 1) (Y 0)

lemma boundaryDefect_symm (X Y : Fin 2 → H1 Ω) : boundaryDefect X Y = boundaryDefect Y X := by
  unfold boundaryDefect
  rw [skewEnergy_skew (X 0),skewEnergy_skew (X 1)]
  ring

lemma boundaryDefect_zero_right (ho : IsOpen Ω) (X : Fin 2 → H1 Ω) (Y : Fin 2 → H10 ho) :
    boundaryDefect X (fun i => (Y i).val) = 0 := by
  unfold boundaryDefect
  rw [skewEnergy_zero_right ho,skewEnergy_zero_right ho]
  ring

lemma boundaryDefect_add_right (X Y Z : Fin 2 → H1 Ω) :
    boundaryDefect X (Y+Z) = boundaryDefect X Y+boundaryDefect X Z := by
  unfold boundaryDefect
  simp only [Pi.add_apply,skewEnergy_add_right]
  ring

lemma boundaryDefect_add_left (X Y Z : Fin 2 → H1 Ω) :
    boundaryDefect (X+Y) Z = boundaryDefect X Z+boundaryDefect Y Z := by
  rw [boundaryDefect_symm,boundaryDefect_add_right,boundaryDefect_symm Z X,boundaryDefect_symm Z Y]

lemma boundaryDefect_class_right (ho : IsOpen Ω) (X Y Z : Fin 2 → H1 Ω)
    (hYZ : ∀ i, ∃ w : H10 ho, Y i-Z i=w.val) : boundaryDefect X Y = boundaryDefect X Z := by
  choose w hw using hYZ
  have he : Y=Z+fun i => (w i).val := by
    funext i
    exact (sub_eq_iff_eq_add.mp (hw i)).trans (add_comm _ _)
  rw [he,boundaryDefect_add_right,boundaryDefect_zero_right ho,add_zero]

lemma boundaryDefect_class (ho : IsOpen Ω) (X Y X' Y' : Fin 2 → H1 Ω)
    (hX : ∀ i, ∃ w : H10 ho, X i-X' i=w.val)
    (hY : ∀ i, ∃ w : H10 ho, Y i-Y' i=w.val) :
    boundaryDefect X Y=boundaryDefect X' Y' := by
  rw [boundaryDefect_class_right ho X Y Y' hY,boundaryDefect_symm X Y',
    boundaryDefect_class_right ho Y' X X' hX,boundaryDefect_symm Y' X']

lemma skewEnergy_integral (u v : H1 Ω) : skewEnergy u v =
    ∫ x in Ω, inner ℝ (H1.grad u x) (rot (H1.grad v x)) := by
  unfold skewEnergy
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [rotL_ae (H1.grad v)] with x hx
  rw [hx]

lemma boundaryDefect_integral (X Y : Fin 2 → H1 Ω) : boundaryDefect X Y =
    ∫ x in Ω, -inner ℝ (H1.grad (X 0) x) (rot (H1.grad (Y 1) x))+
      inner ℝ (H1.grad (X 1) x) (rot (H1.grad (Y 0) x)) := by
  have hi (i j : Fin 2) : Integrable (fun x => inner ℝ (H1.grad (X i) x)
      (rot (H1.grad (Y j) x))) (volume.restrict Ω) :=
    integrable_inner_of_memLp (Lp.memLp _) (rot.comp_memLp' (Lp.memLp _))
  have hh := integral_add (hi 0 1).neg (hi 1 0)
  simp only [Pi.neg_apply,integral_neg] at hh
  exact (congrArg₂ (fun a b : ℝ => -a+b)
    (skewEnergy_integral _ _) (skewEnergy_integral _ _)).trans hh.symm

lemma defect_multiplier_algebra (b u v : ℝ) (A B C : Plane) :
    -inner ℝ (b • A+u • C) (rot (b • B+v • C))+
      inner ℝ (b • B+v • C) (rot (b • A+u • C)) =
    -inner ℝ A (rot (b • (b • B+v • C)+(b*v) • C))+
      inner ℝ B (rot (b • (b • A+u • C)+(b*u) • C)) := by
  have hCA : inner ℝ C (rot A) = -inner ℝ A (rot C) :=
    (real_inner_comm _ _).trans (rot_skew _ _)
  have hCB : inner ℝ C (rot B) = -inner ℝ B (rot C) :=
    (real_inner_comm _ _).trans (rot_skew _ _)
  simp only [map_add,map_smul,inner_add_left,inner_add_right,real_inner_smul_left,
    real_inner_smul_right,hCA,hCB]
  ring

lemma defect_multiplier_substitute (b u v u' v' : ℝ)
    (A B C A' B' A'' B'' : Plane)
    (hA : A' = b • A+u • C) (hB : B' = b • B+v • C)
    (hu : u'=b*u) (hv : v'=b*v)
    (hAA : A''=b • A'+u' • C) (hBB : B''=b • B'+v' • C) :
    -inner ℝ A' (rot B')+inner ℝ B' (rot A') =
      -inner ℝ A (rot B'')+inner ℝ B (rot A'') := by
  rw [hAA,hBB,hA,hB,hu,hv]
  exact defect_multiplier_algebra _ _ _ _ _ _

variable {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
    (hb0 : MemLp b ∞ (volume.restrict Ω))
    (hb1 : MemLp (gradient b) ∞ (volume.restrict Ω))



theorem boundaryDefect_multiplier (X : Fin 2 → H1 Ω) :
    boundaryDefect (fun i => H1.smoothMul hb hb0 hb1 (X i))
      (fun i => H1.smoothMul hb hb0 hb1 (X i)) =
    boundaryDefect X (fun i => H1.smoothMul hb hb0 hb1 (H1.smoothMul hb hb0 hb1 (X i))) := by
  rw [boundaryDefect_integral,boundaryDefect_integral]
  apply integral_congr_ae
  let M := H1.smoothMul hb hb0 hb1
  filter_upwards [H1.smoothMul_grad_ae hb hb0 hb1 (X 0),
    H1.smoothMul_grad_ae hb hb0 hb1 (X 1),
    H1.smoothMul_value_ae hb hb0 hb1 (X 0),
    H1.smoothMul_value_ae hb hb0 hb1 (X 1),
    H1.smoothMul_grad_ae hb hb0 hb1 (M (X 0)),
    H1.smoothMul_grad_ae hb hb0 hb1 (M (X 1))] with x h0 h1 hv0 hv1 hh0 hh1
  change H1.grad (M (X 0)) x = _ at h0
  change H1.grad (M (X 1)) x = _ at h1
  change H1.value (M (X 0)) x = _ at hv0
  change H1.value (M (X 1)) x = _ at hv1
  change -inner ℝ (H1.grad (M (X 0)) x) (rot (H1.grad (M (X 1)) x))+
      inner ℝ (H1.grad (M (X 1)) x) (rot (H1.grad (M (X 0)) x)) = _
  exact defect_multiplier_substitute (b x) (H1.value (X 0) x) (H1.value (X 1) x)
    (H1.value (M (X 0)) x) (H1.value (M (X 1)) x)
    (H1.grad (X 0) x) (H1.grad (X 1) x) (gradient b x)
    (H1.grad (M (X 0)) x) (H1.grad (M (X 1)) x)
    (H1.grad (M (M (X 0))) x) (H1.grad (M (M (X 1))) x)
    h0 h1 hv0 hv1 hh0 hh1
end StrictHotSpots.Hodge
end NullBoundaryFormActualCompatibleLayer

section VectorSobolevActualCompatibleLayer
open Set MeasureTheory Filter
open scoped InnerProductSpace ContDiff
namespace StrictHotSpots.Hodge
variable {Ω : Set Plane}


def coordinateL (Ω : Set Plane) (i : Fin 2) : V2 Ω →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  (innerSL ℝ (e i)).compLpL 2 (volume.restrict Ω)
lemma coordinateL_ae (i : Fin 2) (v : V2 Ω) :
    coordinateL Ω i v =ᵐ[volume.restrict Ω] fun x => c i (v x) := by
  filter_upwards [(innerSL ℝ (e i)).coeFn_compLpL v] with x hx
  apply hx.trans
  change inner ℝ (e i) (v x) = inner ℝ (v x) (e i)
  exact real_inner_comm _ _


def axisL (Ω : Set Plane) (i : Fin 2) : Lp ℝ 2 (volume.restrict Ω) →L[ℝ] V2 Ω :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (e i)).compLpL 2 (volume.restrict Ω)
lemma axisL_ae (i : Fin 2) (u : Lp ℝ 2 (volume.restrict Ω)) :
    axisL Ω i u =ᵐ[volume.restrict Ω] fun x => u x • e i :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (e i)).coeFn_compLpL u

def partialL (i : Fin 2) (u : H1 Ω) : Lp ℝ 2 (volume.restrict Ω) :=
  coordinateL Ω i (H1.grad u)

lemma scalar_pair_L2 (u v : Lp ℝ 2 (volume.restrict Ω)) :
    inner ℝ u v = ∫ x in Ω, u x*v x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [RCLike.inner_apply,RCLike.conj_to_real]
    exact mul_comm _ _

lemma partialL_compact_integration_by_parts (ho : IsOpen Ω) (i : Fin 2)
    (u : H1 Ω) (φ : smoothTestSpace Ω) :
    inner ℝ (H1.value u) (partialL i (smoothTestToH10 ho φ).val) =
      -inner ℝ (partialL i u) (H10.value ho (smoothTestToH10 ho φ)) := by
  have hv : H10.value ho (smoothTestToH10 ho φ) =ᵐ[volume.restrict Ω] φ.val :=
    (test_memLp φ.property.1 φ.property.2.1).coeFn_toLp
  have hg : H10.grad ho (smoothTestToH10 ho φ) =ᵐ[volume.restrict Ω] gradient φ.val :=
    (test_gradient_memLp φ.property.1 φ.property.2.1).coeFn_toLp
  rw [scalar_pair_L2,scalar_pair_L2]
  have hl : (∫ x in Ω, H1.value u x*partialL i (smoothTestToH10 ho φ).val x) =
      ∫ x in Ω, H1.value u x*(fderiv ℝ φ.val x) (e i) := by
    apply integral_congr_ae
    filter_upwards [coordinateL_ae i (H10.grad ho (smoothTestToH10 ho φ)),hg] with x hx hy
    exact congrArg (fun a : ℝ => H1.value u x*a)
      (hx.trans ((congrArg (c i) hy).trans (gradient_c _ _ _)))
  have hr : (∫ x in Ω, partialL i u x*H10.value ho (smoothTestToH10 ho φ) x) =
      ∫ x in Ω, inner ℝ (H1.grad u x) (e i)*φ.val x := by
    apply integral_congr_ae
    filter_upwards [coordinateL_ae i (H1.grad u),hv] with x hx hy
    exact congrArg₂ (fun a b : ℝ => a*b) hx hy
  exact hl.trans (((H1.hasH1Gradient u).2.2 φ.val φ.property.1 φ.property.2.1
    φ.property.2.2 (e i)).trans (congrArg Neg.neg hr).symm)



lemma partialL_integration_by_parts (ho : IsOpen Ω) (i : Fin 2) (u : H1 Ω) (v : H10 ho) :
    inner ℝ (H1.value u) (partialL i v.val) =
      -inner ℝ (partialL i u) (H10.value ho v) := by
  apply isClosed_property (dense_smoothTestToH10 ho) _ _ v
  · exact isClosed_eq
      (continuous_const.inner ((coordinateL Ω i).continuous.comp (H10.grad ho).continuous))
      ((continuous_const.inner (H10.value ho).continuous).neg)
  · exact partialL_compact_integration_by_parts ho i u

def vectorValue (X : Fin 2 → H1 Ω) : V2 Ω :=
  axisL Ω 0 (H1.value (X 0))+axisL Ω 1 (H1.value (X 1))
def divergenceL (X : Fin 2 → H1 Ω) : Lp ℝ 2 (volume.restrict Ω) :=
  partialL 0 (X 0)+partialL 1 (X 1)
def curlL (X : Fin 2 → H1 Ω) : Lp ℝ 2 (volume.restrict Ω) :=
  partialL 0 (X 1)-partialL 1 (X 0)

lemma axis_coordinate_pair (i : Fin 2) (u : Lp ℝ 2 (volume.restrict Ω)) (v : V2 Ω) :
    inner ℝ (axisL Ω i u) v = inner ℝ u (coordinateL Ω i v) := by
  rw [L2.inner_def,scalar_pair_L2]
  apply integral_congr_ae
  filter_upwards [axisL_ae i u,coordinateL_ae i v] with x hx hy
  rw [hx,hy,real_inner_smul_left]
  exact congrArg (fun t : ℝ => u x*t) (real_inner_comm _ _)

lemma coordinateL_rot_zero (v : V2 Ω) :
    coordinateL Ω 0 (rotL Ω v) = -coordinateL Ω 1 v := by
  apply Lp.ext
  filter_upwards [coordinateL_ae 0 (rotL Ω v),rotL_ae v,
    coordinateL_ae 1 v,Lp.coeFn_neg (coordinateL Ω 1 v)] with x h0 hr h1 hn
  rw [h0,hr,hn,Pi.neg_apply,h1,(c_rot _).1]

lemma coordinateL_rot_one (v : V2 Ω) :
    coordinateL Ω 1 (rotL Ω v) = coordinateL Ω 0 v := by
  apply Lp.ext
  filter_upwards [coordinateL_ae 1 (rotL Ω v),rotL_ae v,
    coordinateL_ae 0 v] with x h0 hr h1
  rw [h0,hr,h1,(c_rot _).2]

lemma axis_sum_pair (a b : Lp ℝ 2 (volume.restrict Ω)) (v : V2 Ω) :
    inner ℝ (axisL Ω 0 a+axisL Ω 1 b) v =
      inner ℝ a (coordinateL Ω 0 v)+inner ℝ b (coordinateL Ω 1 v) := by
  rw [inner_add_left,axis_coordinate_pair,axis_coordinate_pair]

lemma axis_sum_rot_pair (a b : Lp ℝ 2 (volume.restrict Ω)) (v : V2 Ω) :
    inner ℝ (axisL Ω 0 a+axisL Ω 1 b) (rotL Ω v) =
      -inner ℝ a (coordinateL Ω 1 v)+inner ℝ b (coordinateL Ω 0 v) := by
  rw [axis_sum_pair,coordinateL_rot_zero,coordinateL_rot_one,inner_neg_right]

lemma partialL_test_curl (ho : IsOpen Ω) (X : Fin 2 → H1 Ω) (v : H10 ho) :
    inner ℝ (vectorValue X) (rotL Ω (H10.grad ho v)) =
      -inner ℝ (curlL X) (H10.value ho v) := by
  calc
    _ = -inner ℝ (H1.value (X 0)) (partialL 1 v.val)+
        inner ℝ (H1.value (X 1)) (partialL 0 v.val) := axis_sum_rot_pair _ _ _
    _ = -(-inner ℝ (partialL 1 (X 0)) (H10.value ho v))+
        (-inner ℝ (partialL 0 (X 1)) (H10.value ho v)) :=
      congrArg₂ (fun a b : ℝ => -a+b) (partialL_integration_by_parts ho 1 (X 0) v)
        (partialL_integration_by_parts ho 0 (X 1) v)
    _ = _ := by simp only [curlL,inner_sub_left]; ring

lemma vectorValue_zero_trace_normal (ho : IsOpen Ω) (X : Fin 2 → H10 ho) (u : H1 Ω) :
    inner ℝ (vectorValue (fun i => (X i).val)) (H1.grad u) =
      -inner ℝ (divergenceL (fun i => (X i).val)) (H1.value u) := by
  have h0 : inner ℝ (H1.value (X 0).val) (partialL 0 u) =
      -inner ℝ (partialL 0 (X 0).val) (H1.value u) := by
    have hh := partialL_integration_by_parts ho 0 u (X 0)
    change inner ℝ (H1.value u) (partialL 0 (X 0).val) =
      -inner ℝ (partialL 0 u) (H1.value (X 0).val) at hh
    linarith only [hh,real_inner_comm (H1.value u) (partialL 0 (X 0).val),
      real_inner_comm (H1.value (X 0).val) (partialL 0 u)]
  have h1 : inner ℝ (H1.value (X 1).val) (partialL 1 u) =
      -inner ℝ (partialL 1 (X 1).val) (H1.value u) := by
    have hh := partialL_integration_by_parts ho 1 u (X 1)
    change inner ℝ (H1.value u) (partialL 1 (X 1).val) =
      -inner ℝ (partialL 1 u) (H1.value (X 1).val) at hh
    linarith only [hh,real_inner_comm (H1.value u) (partialL 1 (X 1).val),
      real_inner_comm (H1.value (X 1).val) (partialL 1 u)]
  calc
    _ = inner ℝ (H1.value (X 0).val) (partialL 0 u)+
        inner ℝ (H1.value (X 1).val) (partialL 1 u) := axis_sum_pair _ _ _
    _ = -inner ℝ (partialL 0 (X 0).val) (H1.value u)+
        -inner ℝ (partialL 1 (X 1).val) (H1.value u) := congrArg₂ (·+·) h0 h1
    _ = _ := by simp only [divergenceL,inner_add_left,neg_add_rev]; ring
end StrictHotSpots.Hodge
end VectorSobolevActualCompatibleLayer

section VectorDefectEnergyActualCompatibleLayer
open Set MeasureTheory Filter
open scoped InnerProductSpace ContDiff
namespace StrictHotSpots.Hodge
variable {Ω : Set Plane}

lemma axis_coordinates (v : V2 Ω) :
    axisL Ω 0 (coordinateL Ω 0 v)+axisL Ω 1 (coordinateL Ω 1 v)=v := by
  apply Lp.ext
  filter_upwards [axisL_ae 0 (coordinateL Ω 0 v),axisL_ae 1 (coordinateL Ω 1 v),
    coordinateL_ae 0 v,coordinateL_ae 1 v,
    Lp.coeFn_add (axisL Ω 0 (coordinateL Ω 0 v)) (axisL Ω 1 (coordinateL Ω 1 v))]
    with x ha hb h0 h1 hadd
  rw [hadd,Pi.add_apply,ha,hb,h0,h1,expand]

lemma coordinate_pair (u v : V2 Ω) : inner ℝ u v =
    inner ℝ (coordinateL Ω 0 u) (coordinateL Ω 0 v)+
    inner ℝ (coordinateL Ω 1 u) (coordinateL Ω 1 v) :=
  (congrArg (fun x : V2 Ω => inner ℝ x v) (axis_coordinates u)).symm.trans (axis_sum_pair _ _ _)

lemma coordinate_rot_pair (u v : V2 Ω) : inner ℝ u (rotL Ω v) =
    -inner ℝ (coordinateL Ω 0 u) (coordinateL Ω 1 v)+
    inner ℝ (coordinateL Ω 1 u) (coordinateL Ω 0 v) := by
  rw [coordinate_pair,coordinateL_rot_zero,coordinateL_rot_one,inner_neg_right]

lemma axis_inner_point (a b c d : ℝ) :
    inner ℝ (a • e 0+b • e 1) (c • e 0+d • e 1)=a*c+b*d := by
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,
    real_inner_smul_right,basis_inner]
  norm_num
  ring

lemma axis_sum_ae (a b : Lp ℝ 2 (volume.restrict Ω)) :
    axisL Ω 0 a+axisL Ω 1 b =ᵐ[volume.restrict Ω] fun x => a x • e 0+b x • e 1 := by
  filter_upwards [axisL_ae 0 a,axisL_ae 1 b,Lp.coeFn_add (axisL Ω 0 a) (axisL Ω 1 b)]
    with x ha hb hs
  exact hs.trans (congrArg₂ (fun u v : Plane => u+v) ha hb)

lemma axis_sum_inner (a b c d : Lp ℝ 2 (volume.restrict Ω)) :
    inner ℝ (axisL Ω 0 a+axisL Ω 1 b) (axisL Ω 0 c+axisL Ω 1 d) =
      inner ℝ a c+inner ℝ b d := by
  rw [L2.inner_def,scalar_pair_L2,scalar_pair_L2]
  have hi := (Lp.memLp a).integrable_mul (Lp.memLp c)
  have hj := (Lp.memLp b).integrable_mul (Lp.memLp d)
  calc
    _ = ∫ x in Ω, a x*c x+b x*d x := by
      apply integral_congr_ae
      filter_upwards [axis_sum_ae a b,axis_sum_ae c d] with x hx hy
      exact (congrArg₂ (inner ℝ) hx hy).trans (axis_inner_point _ _ _ _)
    _ = _ := integral_add hi hj

lemma divcurl_pair_algebra (A B C D : V2 Ω) :
    inner ℝ (coordinateL Ω 0 A+coordinateL Ω 1 B) (coordinateL Ω 0 C+coordinateL Ω 1 D)+
    inner ℝ (coordinateL Ω 0 B-coordinateL Ω 1 A) (coordinateL Ω 0 D-coordinateL Ω 1 C) =
    inner ℝ A C+inner ℝ B D-inner ℝ A (rotL Ω D)+inner ℝ B (rotL Ω C) := by
  rw [coordinate_rot_pair,coordinate_rot_pair,coordinate_pair A C,coordinate_pair B D]
  simp only [inner_add_left,inner_add_right,inner_sub_left,inner_sub_right]
  ring

def cartesianEnergy (X Y : Fin 2 → H1 Ω) : ℝ :=
  inner ℝ (H1.grad (X 0)) (H1.grad (Y 0))+inner ℝ (H1.grad (X 1)) (H1.grad (Y 1))

def vectorForm (μ : ℝ) (X Y : Fin 2 → H1 Ω) : ℝ :=
  inner ℝ (divergenceL X) (divergenceL Y)+inner ℝ (curlL X) (curlL Y)-
    μ*inner ℝ (vectorValue X) (vectorValue Y)

def cartesianForm (μ : ℝ) (X Y : Fin 2 → H1 Ω) : ℝ :=
  cartesianEnergy X Y-μ*(inner ℝ (H1.value (X 0)) (H1.value (Y 0))+
    inner ℝ (H1.value (X 1)) (H1.value (Y 1)))

lemma vectorValue_pair (X Y : Fin 2 → H1 Ω) :
    inner ℝ (vectorValue X) (vectorValue Y) =
      inner ℝ (H1.value (X 0)) (H1.value (Y 0))+
      inner ℝ (H1.value (X 1)) (H1.value (Y 1)) := axis_sum_inner _ _ _ _



theorem vectorForm_eq_cartesian_add_defect (μ : ℝ) (X Y : Fin 2 → H1 Ω) :
    vectorForm μ X Y=cartesianForm μ X Y+boundaryDefect X Y := by
  have h := divcurl_pair_algebra (H1.grad (X 0)) (H1.grad (X 1))
    (H1.grad (Y 0)) (H1.grad (Y 1))
  change inner ℝ (divergenceL X) (divergenceL Y)+inner ℝ (curlL X) (curlL Y) =
    cartesianEnergy X Y-skewEnergy (X 0) (Y 1)+skewEnergy (X 1) (Y 0) at h
  unfold vectorForm cartesianForm boundaryDefect
  rw [h,vectorValue_pair]
  ring
end StrictHotSpots.Hodge
end VectorDefectEnergyActualCompatibleLayer

section TangentVectorClassActualCompatibleLayer
open Set MeasureTheory Filter
open scoped InnerProductSpace ContDiff
namespace StrictHotSpots.Hodge
variable {Ω : Set Plane}


def TangentWeak (X : Fin 2 → H1 Ω) : Prop :=
  WeakNormalDiv (vectorValue X) (divergenceL X)

lemma vectorValue_add (X Y : Fin 2 → H1 Ω) :
    vectorValue (X+Y)=vectorValue X+vectorValue Y := by
  simp only [vectorValue,Pi.add_apply,map_add]
  abel
lemma vectorValue_smul (r : ℝ) (X : Fin 2 → H1 Ω) :
    vectorValue (r • X)=r • vectorValue X := by
  simp only [vectorValue,Pi.smul_apply,map_smul,smul_add]
lemma partialL_add (i : Fin 2) (u v : H1 Ω) : partialL i (u+v)=partialL i u+partialL i v := by
  simp only [partialL,map_add]
lemma partialL_smul (i : Fin 2) (r : ℝ) (u : H1 Ω) : partialL i (r • u)=r • partialL i u := by
  simp only [partialL,map_smul]
lemma divergenceL_add (X Y : Fin 2 → H1 Ω) :
    divergenceL (X+Y)=divergenceL X+divergenceL Y := by
  simp only [divergenceL,Pi.add_apply,partialL_add]
  abel
lemma divergenceL_smul (r : ℝ) (X : Fin 2 → H1 Ω) :
    divergenceL (r • X)=r • divergenceL X := by
  simp only [divergenceL,Pi.smul_apply,partialL_smul,smul_add]
lemma curlL_add (X Y : Fin 2 → H1 Ω) : curlL (X+Y)=curlL X+curlL Y := by
  simp only [curlL,Pi.add_apply,partialL_add]
  abel
lemma curlL_smul (r : ℝ) (X : Fin 2 → H1 Ω) : curlL (r • X)=r • curlL X := by
  simp only [curlL,Pi.smul_apply,partialL_smul,smul_sub]

lemma TangentWeak.add {X Y : Fin 2 → H1 Ω} (hX : TangentWeak X) (hY : TangentWeak Y) :
    TangentWeak (X+Y) := by
  intro u
  rw [vectorValue_add,divergenceL_add,inner_add_left,inner_add_left,hX u,hY u]
  ring
lemma TangentWeak.smul {X : Fin 2 → H1 Ω} (hX : TangentWeak X) (r : ℝ) :
    TangentWeak (r • X) := by
  intro u
  rw [vectorValue_smul,divergenceL_smul,real_inner_smul_left,real_inner_smul_left,hX u]
  ring
lemma tangentWeak_zero_trace (ho : IsOpen Ω) (X : Fin 2 → H10 ho) :
    TangentWeak (fun i => (X i).val) := vectorValue_zero_trace_normal ho X


lemma TangentWeak.of_class (ho : IsOpen Ω) {X Y : Fin 2 → H1 Ω}
    (hY : TangentWeak Y) (hXY : ∀ i, ∃ w : H10 ho, X i-Y i=w.val) : TangentWeak X := by
  choose w hw using hXY
  have he : X=Y+fun i => (w i).val := by
    funext i
    exact (sub_eq_iff_eq_add.mp (hw i)).trans (add_comm _ _)
  rw [he]
  exact hY.add (tangentWeak_zero_trace ho w)

lemma vectorForm_symm (μ : ℝ) (X Y : Fin 2 → H1 Ω) : vectorForm μ X Y=vectorForm μ Y X := by
  unfold vectorForm
  rw [real_inner_comm (divergenceL X),real_inner_comm (curlL X),real_inner_comm (vectorValue X)]
lemma vectorForm_add_left (μ : ℝ) (X Y Z : Fin 2 → H1 Ω) :
    vectorForm μ (X+Y) Z=vectorForm μ X Z+vectorForm μ Y Z := by
  simp only [vectorForm,divergenceL_add,curlL_add,vectorValue_add,inner_add_left]
  ring
lemma vectorForm_smul_left (μ r : ℝ) (X Y : Fin 2 → H1 Ω) :
    vectorForm μ (r • X) Y=r*vectorForm μ X Y := by
  simp only [vectorForm,divergenceL_smul,curlL_smul,vectorValue_smul,real_inner_smul_left]
  ring
lemma vectorForm_add_right (μ : ℝ) (X Y Z : Fin 2 → H1 Ω) :
    vectorForm μ X (Y+Z)=vectorForm μ X Y+vectorForm μ X Z := by
  rw [vectorForm_symm,vectorForm_add_left,vectorForm_symm μ Y X,vectorForm_symm μ Z X]
lemma vectorForm_smul_right (μ r : ℝ) (X Y : Fin 2 → H1 Ω) :
    vectorForm μ X (r • Y)=r*vectorForm μ X Y := by
  rw [vectorForm_symm,vectorForm_smul_left,vectorForm_symm μ Y X]


theorem vectorForm_nonneg (ho : IsOpen Ω) (hne : Ω.Nonempty) (hs : IsSimplyConnected Ω)
    (hb : Bornology.IsBounded Ω) (hμ : 0 < firstPositiveNeumannValue Ω)
    {L : ℝ} (hl : firstPositiveNeumannValue Ω < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2)
    (X : Fin 2 → H1 Ω) (hX : TangentWeak X) :
    0 ≤ vectorForm (firstPositiveNeumannValue Ω) X X := by
  have hh := vector_inequality ho hne hs hb hμ hl hD (vectorValue X)
    (divergenceL X) (curlL X) hX (partialL_test_curl ho X)
  simpa only [vectorForm,real_inner_self_eq_norm_sq,sub_nonneg] using hh

lemma quadratic_null_pair {b c : ℝ} (h : ∀ r : ℝ, 0 ≤ 2*r*b+r^2*c) : b=0 := by
  have h1 := h 1
  have hm := h (-1)
  have hc : 0 ≤ c := by nlinarith
  by_cases hz : c=0
  · rw [hz] at h1 hm
    nlinarith
  · have hp : 0 < c := lt_of_le_of_ne hc (Ne.symm hz)
    have hh := h (-b/c)
    have hd := mul_nonneg hh (sq_nonneg c)
    have he : (2*(-b/c)*b+(-b/c)^2*c)*c^2 = -b^2*c := by field_simp; ring
    rw [he] at hd
    have hs : 0 ≤ -b^2 := nonneg_of_mul_nonneg_left hd hp
    nlinarith [sq_nonneg b]



theorem vectorForm_null_pair (μ : ℝ) (X Y : Fin 2 → H1 Ω)
    (hX : TangentWeak X) (hY : TangentWeak Y)
    (hpos : ∀ Z : Fin 2 → H1 Ω, TangentWeak Z → 0 ≤ vectorForm μ Z Z)
    (hz : vectorForm μ X X=0) : vectorForm μ X Y=0 := by
  apply quadratic_null_pair (c := vectorForm μ Y Y)
  intro r
  have hh := hpos (X+r • Y) (hX.add (hY.smul r))
  rw [vectorForm_add_left,vectorForm_add_right,vectorForm_add_right,
    vectorForm_smul_left,vectorForm_smul_right,vectorForm_smul_right,hz,
    vectorForm_symm μ Y X,vectorForm_smul_left] at hh
  convert hh using 1
  ring
end StrictHotSpots.Hodge
end TangentVectorClassActualCompatibleLayer

section NormalMultiplierActualCompatibleLayer
open Set MeasureTheory Filter
open scoped InnerProductSpace ContDiff ENNReal
namespace StrictHotSpots.Hodge
variable {Ω : Set Plane}

lemma divergenceL_ae (X : Fin 2 → H1 Ω) : divergenceL X =ᵐ[volume.restrict Ω]
    fun x => c 0 (H1.grad (X 0) x)+c 1 (H1.grad (X 1) x) := by
  filter_upwards [coordinateL_ae 0 (H1.grad (X 0)),coordinateL_ae 1 (H1.grad (X 1)),
    Lp.coeFn_add (partialL 0 (X 0)) (partialL 1 (X 1))] with x h0 h1 ha
  exact ha.trans (congrArg₂ (fun a b : ℝ => a+b) h0 h1)
lemma vectorValue_ae (X : Fin 2 → H1 Ω) : vectorValue X =ᵐ[volume.restrict Ω]
    fun x => H1.value (X 0) x • e 0+H1.value (X 1) x • e 1 := axis_sum_ae _ _

lemma divergence_multiplier_algebra (b u v : ℝ) (A B C : Plane) :
    c 0 (b • A+u • C)+c 1 (b • B+v • C) =
      b*(c 0 A+c 1 B)+inner ℝ (u • e 0+v • e 1) C := by
  have h0 : inner ℝ (e 0) C = inner ℝ C (e 0) := real_inner_comm _ _
  have h1 : inner ℝ (e 1) C = inner ℝ C (e 1) := real_inner_comm _ _
  simp only [c,inner_add_left,real_inner_smul_left,h0,h1]
  ring

variable {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
    (hb0 : MemLp b ∞ (volume.restrict Ω))
    (hb1 : MemLp (gradient b) ∞ (volume.restrict Ω))

lemma vectorValue_smoothMul_ae (X : Fin 2 → H1 Ω) :
    vectorValue (fun i => H1.smoothMul hb hb0 hb1 (X i)) =ᵐ[volume.restrict Ω]
      fun x => b x • vectorValue X x := by
  let M := H1.smoothMul hb hb0 hb1
  filter_upwards [vectorValue_ae (fun i => M (X i)),vectorValue_ae X,
    H1.smoothMul_value_ae hb hb0 hb1 (X 0),H1.smoothMul_value_ae hb hb0 hb1 (X 1)]
      with x hV hX h0 h1
  apply hV.trans
  exact (congrArg₂ (fun a d : ℝ => a • e 0+d • e 1) h0 h1).trans
    (by rw [hX]; module)

lemma divergenceL_smoothMul_ae (X : Fin 2 → H1 Ω) :
    divergenceL (fun i => H1.smoothMul hb hb0 hb1 (X i)) =ᵐ[volume.restrict Ω]
      fun x => b x*divergenceL X x+inner ℝ (vectorValue X x) (gradient b x) := by
  let M := H1.smoothMul hb hb0 hb1
  filter_upwards [divergenceL_ae (fun i => M (X i)),divergenceL_ae X,vectorValue_ae X,
    H1.smoothMul_grad_ae hb hb0 hb1 (X 0),H1.smoothMul_grad_ae hb hb0 hb1 (X 1)]
      with x hD hX hV h0 h1
  apply hD.trans
  exact (congrArg₂ (fun A B : Plane => c 0 A+c 1 B) h0 h1).trans
    ((divergence_multiplier_algebra _ _ _ _ _ _).trans
      (congrArg₂ (fun d : ℝ => fun V : Plane => b x*d+inner ℝ V (gradient b x)) hX hV).symm)

lemma normal_pair_integral (X : Fin 2 → H1 Ω) (u : H1 Ω) :
    inner ℝ (vectorValue X) (H1.grad u)+inner ℝ (divergenceL X) (H1.value u) =
      ∫ x in Ω, inner ℝ (vectorValue X x) (H1.grad u x)+divergenceL X x*H1.value u x := by
  have hi := integrable_inner_of_memLp (Lp.memLp (vectorValue X)) (Lp.memLp (H1.grad u))
  have hj := (Lp.memLp (divergenceL X)).integrable_mul (Lp.memLp (H1.value u))
  exact (congrArg₂ (fun a b : ℝ => a+b) (L2.inner_def _ _) (scalar_pair_L2 _ _)).trans
    (integral_add hi hj).symm

lemma normal_multiplier_algebra (b u F : ℝ) (V G C : Plane) :
    inner ℝ (b • V) G+(b*F+inner ℝ V C)*u =
      inner ℝ V (b • G+u • C)+F*(b*u) := by
  simp only [real_inner_smul_left,inner_add_right,real_inner_smul_right]
  ring

lemma normal_pair_smoothMul (X : Fin 2 → H1 Ω) (u : H1 Ω) :
    inner ℝ (vectorValue (fun i => H1.smoothMul hb hb0 hb1 (X i))) (H1.grad u)+
      inner ℝ (divergenceL (fun i => H1.smoothMul hb hb0 hb1 (X i))) (H1.value u) =
    inner ℝ (vectorValue X) (H1.grad (H1.smoothMul hb hb0 hb1 u))+
      inner ℝ (divergenceL X) (H1.value (H1.smoothMul hb hb0 hb1 u)) := by
  refine Eq.trans (normal_pair_integral _ _) (Eq.trans ?_ (normal_pair_integral _ _).symm)
  apply integral_congr_ae
  filter_upwards [vectorValue_smoothMul_ae hb hb0 hb1 X,divergenceL_smoothMul_ae hb hb0 hb1 X,
    H1.smoothMul_grad_ae hb hb0 hb1 u,H1.smoothMul_value_ae hb hb0 hb1 u] with x hV hD hG hu
  exact (congrArg₂ (fun V : Plane => fun F : ℝ =>
    inner ℝ V (H1.grad u x)+F*H1.value u x) hV hD).trans
      ((normal_multiplier_algebra _ _ _ _ _ _).trans
        (congrArg₂ (fun G : Plane => fun v : ℝ => inner ℝ (vectorValue X x) G+divergenceL X x*v) hG hu).symm)


theorem TangentWeak.smoothMul {X : Fin 2 → H1 Ω} (hX : TangentWeak X) :
    TangentWeak (fun i => H1.smoothMul hb hb0 hb1 (X i)) := by
  intro u
  have he := normal_pair_smoothMul hb hb0 hb1 X u
  have hz := hX (H1.smoothMul hb hb0 hb1 u)
  linarith only [he,hz]
end StrictHotSpots.Hodge
end NormalMultiplierActualCompatibleLayer

section BoundaryClassMultiplierActualCompatibleLayer
open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal
namespace StrictHotSpots.Hodge
variable {Ω : Set Plane} (ho : IsOpen Ω)
variable {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
    (hb0 : MemLp b ∞ (volume.restrict Ω))
    (hb1 : MemLp (gradient b) ∞ (volume.restrict Ω))




theorem boundaryClass_multiplier_identity (μ : ℝ) (X Y Z : Fin 2 → H1 Ω)
    (hX : TangentWeak X)
    (hY : ∀ i, ∃ w : H10 ho, Y i-H1.smoothMul hb hb0 hb1 (X i)=w.val)
    (hZ : ∀ i, ∃ w : H10 ho,
      Z i-H1.smoothMul hb hb0 hb1 (H1.smoothMul hb hb0 hb1 (X i))=w.val)
    (hpos : ∀ V : Fin 2 → H1 Ω, TangentWeak V → 0 ≤ vectorForm μ V V)
    (hnull : vectorForm μ X X=0) :
    vectorForm μ Y Y=cartesianForm μ Y Y-cartesianForm μ X Z := by
  let M := H1.smoothMul hb hb0 hb1
  have htZ : TangentWeak Z := TangentWeak.of_class ho
    ((hX.smoothMul hb hb0 hb1).smoothMul hb hb0 hb1) hZ
  have hz : vectorForm μ X Z=0 := vectorForm_null_pair μ X Z hX htZ hpos hnull
  have hYY : boundaryDefect Y Y = boundaryDefect (fun i => M (X i)) (fun i => M (X i)) :=
    boundaryDefect_class ho Y Y _ _ hY hY
  have hZZ : boundaryDefect X Z = boundaryDefect X (fun i => M (M (X i))) :=
    boundaryDefect_class_right ho X Z _ hZ
  have he : boundaryDefect Y Y = boundaryDefect X Z :=
    hYY.trans ((boundaryDefect_multiplier hb hb0 hb1 X).trans hZZ.symm)
  have hqY := vectorForm_eq_cartesian_add_defect μ Y Y
  have hqZ := vectorForm_eq_cartesian_add_defect μ X Z
  linarith only [hqY,hqZ,he,hz]



theorem boundaryClass_multiplier_nonneg (hne : Ω.Nonempty) (hs : IsSimplyConnected Ω)
    (hbounded : Bornology.IsBounded Ω) (hμ : 0 < firstPositiveNeumannValue Ω)
    {L : ℝ} (hl : firstPositiveNeumannValue Ω < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2)
    (X Y Z : Fin 2 → H1 Ω) (hX : TangentWeak X)
    (hY : ∀ i, ∃ w : H10 ho, Y i-H1.smoothMul hb hb0 hb1 (X i)=w.val)
    (hZ : ∀ i, ∃ w : H10 ho,
      Z i-H1.smoothMul hb hb0 hb1 (H1.smoothMul hb hb0 hb1 (X i))=w.val)
    (hnull : vectorForm (firstPositiveNeumannValue Ω) X X=0) :
    0 ≤ cartesianForm (firstPositiveNeumannValue Ω) Y Y-
      cartesianForm (firstPositiveNeumannValue Ω) X Z := by
  have hp := vectorForm_nonneg ho hne hs hbounded hμ hl hD
  have he := boundaryClass_multiplier_identity ho hb hb0 hb1
    (firstPositiveNeumannValue Ω) X Y Z hX hY hZ hp hnull
  have htY := TangentWeak.of_class ho (hX.smoothMul hb hb0 hb1) hY
  exact he ▸ hp Y htY
end StrictHotSpots.Hodge
end BoundaryClassMultiplierActualCompatibleLayer

section GradientVectorEnergyActualCompatibleLayer
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal Topology
namespace StrictHotSpots
namespace Hodge
variable {Ω : Set Plane}

lemma scalar_eq_zero_of_H10_pair (ho : IsOpen Ω) (f : Lp ℝ 2 (volume.restrict Ω))
    (h : ∀ v : H10 ho, inner ℝ f (H10.value ho v)=0) : f=0 := by
  apply eq_zero_of_inner_smoothTest_eq_zero ho f
  intro φ
  exact (real_inner_comm _ _).trans (h (smoothTestToH10 ho φ))

lemma vectorValue_test_normal (ho : IsOpen Ω) (X : Fin 2 → H1 Ω) (v : H10 ho) :
    inner ℝ (vectorValue X) (H10.grad ho v) =
      -inner ℝ (divergenceL X) (H10.value ho v) := by
  calc
    _ = inner ℝ (H1.value (X 0)) (partialL 0 v.val)+
        inner ℝ (H1.value (X 1)) (partialL 1 v.val) := axis_sum_pair _ _ _
    _ = -inner ℝ (partialL 0 (X 0)) (H10.value ho v)+
        -inner ℝ (partialL 1 (X 1)) (H10.value ho v) :=
      congrArg₂ (·+·) (partialL_integration_by_parts ho 0 (X 0) v)
        (partialL_integration_by_parts ho 1 (X 1) v)
    _ = _ := by simp only [divergenceL,inner_add_left,neg_add_rev]; ring

lemma gradient_curl_zero (ho : IsOpen Ω) (X : Fin 2 → H1 Ω) (u : H1 Ω)
    (hX : vectorValue X=H1.grad u) : curlL X=0 := by
  apply scalar_eq_zero_of_H10_pair ho
  intro v
  have hh := partialL_test_curl ho X v
  have hz := grad_rotGrad_orthogonal ho u v
  rw [hX] at hh
  linarith only [hh,hz]


def NeumannEuler (μ : ℝ) (u : H1 Ω) : Prop := ∀ w : H1 Ω,
  inner ℝ (H1.grad u) (H1.grad w)=μ*inner ℝ (H1.value u) (H1.value w)

lemma inner_add_smul_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c : E) (μ t : ℝ) (ha : t = -inner ℝ a c) (hb : t = μ*inner ℝ b c) :
    inner ℝ (a+μ • b) c=0 := by
  rw [inner_add_left, real_inner_smul_left]
  linarith only [ha,hb]

lemma gradient_divergence (ho : IsOpen Ω) (μ : ℝ) (X : Fin 2 → H1 Ω) (u : H1 Ω)
    (hX : vectorValue X=H1.grad u) (hu : NeumannEuler μ u) :
    divergenceL X=(-μ) • H1.value u := by
  have hz : divergenceL X+μ • H1.value u=0 := by
    apply scalar_eq_zero_of_H10_pair ho
    intro v
    have hh := vectorValue_test_normal ho X v
    have he := hu v.val
    rw [hX] at hh
    change inner ℝ (H1.grad u) (H10.grad ho v)=
      μ*inner ℝ (H1.value u) (H10.value ho v) at he
    exact inner_add_smul_zero (divergenceL X) (H1.value u) (H10.value ho v) μ
      (inner ℝ (H1.grad u) (H10.grad ho v)) hh he
  exact (eq_neg_of_add_eq_zero_left hz).trans (neg_smul μ (H1.value u)).symm

lemma gradient_tangent (ho : IsOpen Ω) (μ : ℝ) (X : Fin 2 → H1 Ω) (u : H1 Ω)
    (hX : vectorValue X=H1.grad u) (hu : NeumannEuler μ u) : TangentWeak X := by
  have hd := gradient_divergence ho μ X u hX hu
  intro w
  rw [hX,hd,real_inner_smul_left,hu w]
  ring

lemma gradient_form_algebra {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (μ : ℝ) (g : E) (v : F) (he : inner ℝ g g=μ*inner ℝ v v) :
    inner ℝ ((-μ) • v) ((-μ) • v)+inner ℝ (0:F) (0:F)-μ*inner ℝ g g=0 := by
  simp only [real_inner_smul_left,real_inner_smul_right,inner_zero_left,he]
  ring



theorem gradient_vector_null (ho : IsOpen Ω) (μ : ℝ) (X : Fin 2 → H1 Ω) (u : H1 Ω)
    (hX : vectorValue X=H1.grad u) (hu : NeumannEuler μ u) :
    TangentWeak X ∧ vectorForm μ X X=0 := by
  refine ⟨gradient_tangent ho μ X u hX hu,?_⟩
  have hd := gradient_divergence ho μ X u hX hu
  have hc := gradient_curl_zero ho X u hX
  unfold vectorForm
  rw [hd,hc,hX]
  exact gradient_form_algebra μ (H1.grad u) (H1.value u) (hu u)
end Hodge
end StrictHotSpots
end GradientVectorEnergyActualCompatibleLayer

open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace StrictHotSpots
namespace Hodge
variable {Ω : Set Plane} {u : Plane → ℝ}




def eigenGradientField (hΩ : AdmissibleDomain Ω) (hu : InFirstNeumannEigenspace Ω u) :
    Fin 2 → H1 Ω := fun i =>
  (smooth_closure_H1 hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.2
    (closure_directional_smooth hΩ.2.1 hΩ.2.2.2.2 hu.1 (e i))).toH1

lemma eigenGradientField_value_ae (hΩ : AdmissibleDomain Ω)
    (hu : InFirstNeumannEigenspace Ω u) (i : Fin 2) :
    H1.value (eigenGradientField hΩ hu i) =ᵐ[volume.restrict Ω]
      fun x => fderivWithin ℝ u (closure Ω) x (e i) :=
  (smooth_closure_H1 hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.2
    (closure_directional_smooth hΩ.2.1 hΩ.2.2.2.2 hu.1 (e i))).1.coeFn_toLp

lemma eigenGradientField_vector (hΩ : AdmissibleDomain Ω)
    (hu : InFirstNeumannEigenspace Ω u) :
    vectorValue (eigenGradientField hΩ hu)=H1.grad hu.2.1.toH1 := by
  apply Lp.ext
  filter_upwards [axis_sum_ae (H1.value (eigenGradientField hΩ hu 0))
    (H1.value (eigenGradientField hΩ hu 1)),eigenGradientField_value_ae hΩ hu 0,
    eigenGradientField_value_ae hΩ hu 1,hu.2.1.2.1.coeFn_toLp,
    ae_restrict_mem hΩ.2.1.measurableSet] with x hv h0 h1 hg hx
  change (vectorValue (eigenGradientField hΩ hu)) x = _ at hv
  change (H1.grad hu.2.1.toH1) x = gradient u x at hg
  have he (i : Fin 2) : fderivWithin ℝ u (closure Ω) x (e i)=c i (gradient u x) := by
    rw [fderivWithin_of_mem_nhds (mem_of_superset (hΩ.2.1.mem_nhds hx) subset_closure)]
    exact (gradient_c u i x).symm
  exact hv.trans ((congrArg₂ (fun a b : ℝ => a • e 0+b • e 1)
    (h0.trans (he 0)) (h1.trans (he 1))).trans ((expand _).trans hg.symm))

lemma eigen_NeumannEuler (hu : InFirstNeumannEigenspace Ω u) :
    NeumannEuler (firstPositiveNeumannValue Ω) hu.2.1.toH1 := by
  intro w
  have hl : inner ℝ (H1.grad hu.2.1.toH1) (H1.grad w) =
      ∫ x in Ω, inner ℝ (gradient u x) (H1.grad w x) := by
    refine (L2.inner_def _ _).trans (integral_congr_ae ?_)
    filter_upwards [hu.2.1.2.1.coeFn_toLp] with x hx
    exact congrArg (fun v : Plane => inner ℝ v (H1.grad w x)) hx
  have hr : inner ℝ (H1.value hu.2.1.toH1) (H1.value w) =
      ∫ x in Ω, u x*H1.value w x := by
    refine (scalar_pair_L2 _ _).trans (integral_congr_ae ?_)
    filter_upwards [hu.2.1.1.coeFn_toLp] with x hx
    exact congrArg (fun v : ℝ => v*H1.value w x) hx
  exact hl.trans ((hu.2.2.2 _ _ (H1.hasH1Gradient w)).trans
    (congrArg (fun t : ℝ => firstPositiveNeumannValue Ω*t) hr).symm)




theorem eigenGradientField_null (hΩ : AdmissibleDomain Ω)
    (hu : InFirstNeumannEigenspace Ω u) :
    TangentWeak (eigenGradientField hΩ hu) ∧
      vectorForm (firstPositiveNeumannValue Ω) (eigenGradientField hΩ hu)
        (eigenGradientField hΩ hu)=0 :=
  gradient_vector_null hΩ.2.1 (firstPositiveNeumannValue Ω) (eigenGradientField hΩ hu)
    hu.2.1.toH1 (eigenGradientField_vector hΩ hu) (eigen_NeumannEuler hu)
end Hodge
end StrictHotSpots
end
end ActualVectorSupport

section ActualScalarEnergy

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
variable (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
variable (hμ : 0 ≤ firstPositiveNeumannValue Ω)

lemma boundarySolution_datum_class {w : Plane → ℝ}
    (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn)) :
    ∃ v : H10 diskOpen,
      boundarySolution c.densityBound_ne_top (c.density_bound hμ)
        (c.datumTrace w hw.continuousOn) hl = (c.pullDatum_H1 hb hs hw).toH1+v.val := by
  obtain ⟨a,ha⟩ := boundarySolution_class c.densityBound_ne_top (c.density_bound hμ)
    (c.datumTrace w hw.continuousOn) hl
  obtain ⟨b,hb'⟩ := c.pullDatum_Poisson_class hb hs hw hl
  refine ⟨a-b,?_⟩
  change _ = _+(a.val-b.val)
  rw [← ha,← hb']
  abel



def datumCorrection {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn)) : H10 diskOpen :=
  (c.boundarySolution_datum_class hb hs hμ hw hl).choose

lemma datumCorrection_spec {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn)) :
    boundarySolution c.densityBound_ne_top (c.density_bound hμ)
      (c.datumTrace w hw.continuousOn) hl =
    (c.pullDatum_H1 hb hs hw).toH1+(c.datumCorrection hb hs hμ hw hl).val :=
  (c.boundarySolution_datum_class hb hs hμ hw hl).choose_spec

def physicalSolution {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn)) : H1 Ω :=
  (smooth_closure_H1 (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hw).toH1+
    (show H1 Ω from (transportH10 c.diskMap c.diskMap_inverse_smooth
      (c.datumCorrection hb hs hμ hw hl)).val)

lemma physicalSolution_class {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn)) :
    ∃ v : H10 (show IsOpen Ω from c.diskMap.open_target), c.physicalSolution hb hs hμ hw hl-
      (smooth_closure_H1 (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hw).toH1=v.val := by
  refine ⟨transportH10 c.diskMap c.diskMap_inverse_smooth (c.datumCorrection hb hs hμ hw hl),?_⟩
  exact add_sub_cancel_left _ _

lemma physicalSolution_grad_pair {w z : Plane → ℝ}
    (hw : ContDiffOn ℝ ∞ w (closure Ω)) (hz : ContDiffOn ℝ ∞ z (closure Ω)) {B D : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn))
    (hk : LipschitzWith D (c.datumTrace z hz.continuousOn)) :
    inner ℝ (H1.grad (c.physicalSolution hb hs hμ hw hl))
      (H1.grad (c.physicalSolution hb hs hμ hz hk)) =
    inner ℝ (H1.grad (boundarySolution c.densityBound_ne_top (c.density_bound hμ)
      (c.datumTrace w hw.continuousOn) hl))
      (H1.grad (boundarySolution c.densityBound_ne_top (c.density_bound hμ)
      (c.datumTrace z hz.continuousOn) hk)) := by
  have hh := affine_grad_pair c.diskMap c.diskMap_inverse_smooth c.d c.diskMap_deriv hb
    ((hw.mono subset_closure).differentiableOn (by simp))
    ((hz.mono subset_closure).differentiableOn (by simp))
    (smooth_closure_H1 (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hw)
    (smooth_closure_H1 (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hz)
    (c.pullDatum_comp_H1 hb hs hw) (c.pullDatum_comp_H1 hb hs hz)
    (c.datumCorrection hb hs hμ hw hl) (c.datumCorrection hb hs hμ hz hk)
  apply hh.trans
  apply congrArg₂ (fun U V : H1 disk => inner ℝ (H1.grad U) (H1.grad V))
  · exact (congrArg (fun U : H1 disk => U+(c.datumCorrection hb hs hμ hw hl).val)
      (c.pullDatum_comp_toH1 hb hs hw)).trans (c.datumCorrection_spec hb hs hμ hw hl).symm
  · exact (congrArg (fun U : H1 disk => U+(c.datumCorrection hb hs hμ hz hk).val)
      (c.pullDatum_comp_toH1 hb hs hz)).trans (c.datumCorrection_spec hb hs hμ hz hk).symm

lemma physicalSolution_mass_pair {w z : Plane → ℝ}
    (hw : ContDiffOn ℝ ∞ w (closure Ω)) (hz : ContDiffOn ℝ ∞ z (closure Ω)) {B D : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn))
    (hk : LipschitzWith D (c.datumTrace z hz.continuousOn)) :
    firstPositiveNeumannValue Ω * inner ℝ (H1.value (c.physicalSolution hb hs hμ hw hl))
      (H1.value (c.physicalSolution hb hs hμ hz hk)) =
    inner ℝ (SubcriticalExtension.observe c.densityBound_ne_top (c.density_bound hμ)
      (boundarySolution c.densityBound_ne_top (c.density_bound hμ)
      (c.datumTrace w hw.continuousOn) hl))
      (SubcriticalExtension.observe c.densityBound_ne_top (c.density_bound hμ)
      (boundarySolution c.densityBound_ne_top (c.density_bound hμ)
      (c.datumTrace z hz.continuousOn) hk)) := by
  let S := boundarySolution c.densityBound_ne_top (c.density_bound hμ)
    (c.datumTrace w hw.continuousOn) hl
  let T := boundarySolution c.densityBound_ne_top (c.density_bound hμ)
    (c.datumTrace z hz.continuousOn) hk
  have hh := affine_value_pair c.diskMap c.diskMap_inverse_smooth c.d c.diskMap_deriv hb
    (smooth_closure_H1 (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hw)
    (smooth_closure_H1 (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hz)
    (c.pullDatum_comp_H1 hb hs hw) (c.pullDatum_comp_H1 hb hs hz)
    (c.datumCorrection hb hs hμ hw hl) (c.datumCorrection hb hs hμ hz hk)
  have hw' : (c.pullDatum_comp_H1 hb hs hw).toH1+(c.datumCorrection hb hs hμ hw hl).val=S :=
    (congrArg (fun U : H1 disk => U+(c.datumCorrection hb hs hμ hw hl).val)
      (c.pullDatum_comp_toH1 hb hs hw)).trans (c.datumCorrection_spec hb hs hμ hw hl).symm
  have hz' : (c.pullDatum_comp_H1 hb hs hz).toH1+(c.datumCorrection hb hs hμ hz hk).val=T :=
    (congrArg (fun U : H1 disk => U+(c.datumCorrection hb hs hμ hz hk).val)
      (c.pullDatum_comp_toH1 hb hs hz)).trans (c.datumCorrection_spec hb hs hμ hz hk).symm
  have hr := congrArg₂ (fun U V : H1 disk =>
    ∫ x, H1.value U x*H1.value V x ∂chartMeasure c.diskMap c.d) hw' hz'
  have hp := potentialMeasure_integral c.diskMap c.d hμ (fun x => H1.value S x*H1.value T x)
  have hq := congrArg (fun ν : Measure Plane => ∫ x, H1.value S x*H1.value T x ∂ν)
    c.potential_diskMap
  exact (congrArg (fun t : ℝ => firstPositiveNeumannValue Ω*t) (hh.trans hr)).trans
    (hp.symm.trans (hq.trans (observe_inner c.densityBound_ne_top (c.density_bound hμ) S T).symm))



theorem physicalSolution_energy (hne : Ω.Nonempty) (hμp : 0 < firstPositiveNeumannValue Ω)
    {w z : Plane → ℝ}
    (hw : ContDiffOn ℝ ∞ w (closure Ω)) (hz : ContDiffOn ℝ ∞ z (closure Ω)) {B D : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn))
    (hk : LipschitzWith D (c.datumTrace z hz.continuousOn)) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hb
    inner ℝ (H1.grad (c.physicalSolution hb hs hμ hw hl))
      (H1.grad (c.physicalSolution hb hs hμ hz hk)) -
    firstPositiveNeumannValue Ω * inner ℝ (H1.value (c.physicalSolution hb hs hμ hw hl))
      (H1.value (c.physicalSolution hb hs hμ hz hk)) =
    (1/2:ℝ)*(∫ q : Boundary × Boundary, boundaryInteraction q.1 q.2 *
      inner ℝ (w (c.F q.1)-w (c.F q.2)) (z (c.F q.1)-z (c.F q.2))
      ∂boundaryMeasure.prod boundaryMeasure) -
    (∫ q : Boundary × Boundary, fullBoundaryR c.densityBound_ne_top (c.density_bound hμ) q.1 q.2 *
      w (c.F q.1) * z (c.F q.2) ∂boundaryMeasure.prod boundaryMeasure) := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hb
  have he := boundarySolution_energy c.densityBound_ne_top (c.density_bound hμ)
    (c.operator_norm_lt_one hb hne hμp) (c.datumTrace w hw.continuousOn)
      (c.datumTrace z hz.continuousOn) hl hk
  exact (congrArg₂ (fun a b : ℝ => a-b)
    (c.physicalSolution_grad_pair hb hs hμ hw hz hl hk)
    (c.physicalSolution_mass_pair hb hs hμ hw hz hl hk)).trans he

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ActualScalarEnergy

section ActualVectorEnergy

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Laplacian
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
variable (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
variable (hμ : 0 < firstPositiveNeumannValue Ω)


def scalarSolution {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) : H1 Ω :=
  c.physicalSolution hb hs hμ.le hw (c.datumTrace_lipschitz hb hs hw).choose_spec

lemma scalarSolution_class {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) :
    ∃ v : H10 (show IsOpen Ω from c.diskMap.open_target), c.scalarSolution hb hs hμ hw-
      (smooth_closure_H1 (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hw).toH1=v.val :=
  c.physicalSolution_class hb hs hμ.le hw (c.datumTrace_lipschitz hb hs hw).choose_spec

lemma datumCorrection_eq_zero_of_helmholtz (hne : Ω.Nonempty)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω))
    (hp : ∀ x ∈ Ω, Δ w x = -firstPositiveNeumannValue Ω*w x) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn)) :
    c.datumCorrection hb hs hμ.le hw hl = 0 := by
  obtain ⟨δ,hδ,hδ1,hsub⟩ := c.subcritical hb hne hμ
  have he := boundarySolution_eq_of_trace c.densityBound_ne_top (c.density_bound hμ.le)
    hδ.le hδ1 hsub (c.datumTrace w hw.continuousOn) hl
    (c.pullDatum_smooth (hw.mono subset_closure)) (c.pullDatum_continuous hw.continuousOn)
    (c.pullDatum_H1 hb hs hw) (fun _ => rfl) (c.smooth_pull_weak hb hs hw hμ.le hp)
  apply Subtype.ext
  have ha := (c.datumCorrection_spec hb hs hμ.le hw hl).symm.trans he
  exact add_left_cancel (ha.trans (add_zero _).symm)

lemma physicalSolution_eq_of_helmholtz (hne : Ω.Nonempty)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω))
    (hp : ∀ x ∈ Ω, Δ w x = -firstPositiveNeumannValue Ω*w x) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn)) :
    c.physicalSolution hb hs hμ.le hw hl =
      (smooth_closure_H1 (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hw).toH1 := by
  have hz := c.datumCorrection_eq_zero_of_helmholtz hb hs hμ hne hw hp hl
  have ht : (transportH10 c.diskMap c.diskMap_inverse_smooth
      (c.datumCorrection hb hs hμ.le hw hl)).val = (0 : H1 Ω) := by
    exact (congrArg (fun v : H10 diskOpen =>
      (transportH10 c.diskMap c.diskMap_inverse_smooth v).val) hz).trans
      (congrArg (fun v : H10 (show IsOpen Ω from c.diskMap.open_target) => v.val)
        (map_zero (transportH10 c.diskMap c.diskMap_inverse_smooth)))
  exact (congrArg (fun U : H1 Ω =>
    (smooth_closure_H1 (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hw).toH1+U) ht).trans
      (add_zero _)

lemma scalarSolution_eq_of_helmholtz (hne : Ω.Nonempty)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω))
    (hp : ∀ x ∈ Ω, Δ w x = -firstPositiveNeumannValue Ω*w x) :
    c.scalarSolution hb hs hμ hw = (smooth_closure_H1 (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hw).toH1 :=
  c.physicalSolution_eq_of_helmholtz hb hs hμ hne hw hp _

lemma scalarSolution_energy (hne : Ω.Nonempty)
    {w z : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω))
    (hz : ContDiffOn ℝ ∞ z (closure Ω)) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hb
    inner ℝ (H1.grad (c.scalarSolution hb hs hμ hw)) (H1.grad (c.scalarSolution hb hs hμ hz)) -
    firstPositiveNeumannValue Ω*inner ℝ (H1.value (c.scalarSolution hb hs hμ hw))
      (H1.value (c.scalarSolution hb hs hμ hz)) =
    (1/2:ℝ)*(∫ q : Boundary × Boundary, boundaryInteraction q.1 q.2 *
      inner ℝ (w (c.F q.1)-w (c.F q.2)) (z (c.F q.1)-z (c.F q.2))
      ∂boundaryMeasure.prod boundaryMeasure) -
    (∫ q : Boundary × Boundary, fullBoundaryR c.densityBound_ne_top (c.density_bound hμ.le) q.1 q.2 *
      w (c.F q.1) * z (c.F q.2) ∂boundaryMeasure.prod boundaryMeasure) :=
  c.physicalSolution_energy hb hs hμ.le hne hμ hw hz _ _

end StrictHotSpots.Conformal.ClosedDiskChart
namespace StrictHotSpots

lemma smoothMul_smooth_closure {Ω : Set Plane} (ho : IsOpen Ω) (hbound : Bornology.IsBounded Ω)
    (hs : SmoothBoundary Ω) {b w : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
    (hb0 : MemLp b ∞ (volume.restrict Ω)) (hb1 : MemLp (gradient b) ∞ (volume.restrict Ω))
    (hw : ContDiffOn ℝ ∞ w (closure Ω)) :
    H1.smoothMul hb hb0 hb1 (smooth_closure_H1 ho hbound hs hw).toH1 =
      (smooth_closure_H1 ho hbound hs (hb.contDiffOn.mul hw)).toH1 := by
  apply H1.value_injective ho
  apply Lp.ext
  filter_upwards [H1.smoothMul_value_ae hb hb0 hb1 (smooth_closure_H1 ho hbound hs hw).toH1,
    (smooth_closure_H1 ho hbound hs hw).1.coeFn_toLp,
    (smooth_closure_H1 ho hbound hs (hb.contDiffOn.mul hw)).1.coeFn_toLp] with x h1 h2 h3
  exact h1.trans ((congrArg (fun t : ℝ => b x*t) h2).trans h3.symm)

lemma closed_directional_helmholtz {Ω : Set Plane} (ho : IsOpen Ω)
    {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u) (e : Plane) {x : Plane} (hx : x ∈ Ω) :
    Δ (fun z => fderivWithin ℝ u (closure Ω) z e) x =
      -firstPositiveNeumannValue Ω * fderivWithin ℝ u (closure Ω) x e := by
  have heq : (fun z => fderivWithin ℝ u (closure Ω) z e) =ᶠ[nhds x]
      directionalDerivative u e :=
    Filter.eventually_of_mem (ho.mem_nhds hx) (fun _ hz => closed_directional_eq ho hz e)
  rw [(InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds,closed_directional_eq ho hx e]
  linear_combination eigenfunction_derivative_helmholtz ho hu hx e

end StrictHotSpots
end
end ActualVectorEnergy

section ActualBoundaryMultiplier

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma harmonic_multiplier_integral {g : Boundary → E} {b : Boundary → ℝ} {A B : ℝ≥0}
    (hg : LipschitzWith A g) (hb : LipschitzWith B b) :
    (∫ z : Boundary × Boundary, boundaryInteraction z.1 z.2 *
      inner ℝ (b z.1 • g z.1-b z.2 • g z.2) (b z.1 • g z.1-b z.2 • g z.2)
        ∂boundaryMeasure.prod boundaryMeasure) -
    (∫ z : Boundary × Boundary, boundaryInteraction z.1 z.2 *
      inner ℝ (g z.1-g z.2) (b z.1^2 • g z.1-b z.2^2 • g z.2)
        ∂boundaryMeasure.prod boundaryMeasure) =
    ∫ z : Boundary × Boundary, boundaryInteraction z.1 z.2 * (b z.1-b z.2)^2 *
      inner ℝ (g z.1) (g z.2) ∂boundaryMeasure.prod boundaryMeasure := by
  obtain ⟨L,hL⟩ := boundary_smul_lipschitz hb hg
  obtain ⟨D,hD⟩ := boundary_smul_lipschitz hb hb
  have hD' : LipschitzWith D (fun s => b s^2) := by simpa only [smul_eq_mul,pow_two] using hD
  obtain ⟨F,hF⟩ := boundary_smul_lipschitz hD' hg
  rw [← integral_sub (harmonic_boundary_integrable hL hL) (harmonic_boundary_integrable hg hF)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← mul_sub,harmonic_multiplier_algebra,mul_assoc]

lemma interaction_multiplier_integral {R : Boundary → Boundary → ℝ}
    (hR : Integrable (fun z : Boundary × Boundary => R z.1 z.2) (boundaryMeasure.prod boundaryMeasure))
    (hRs : ∀ s t, R s t = R t s) {g : Boundary → E} {b : Boundary → ℝ}
    (hg : Continuous g) (hb : Continuous b) :
    (∫ z : Boundary × Boundary, R z.1 z.2 * inner ℝ (g z.1) (b z.2^2 • g z.2)
        ∂boundaryMeasure.prod boundaryMeasure) -
    (∫ z : Boundary × Boundary, R z.1 z.2 * inner ℝ (b z.1 • g z.1) (b z.2 • g z.2)
        ∂boundaryMeasure.prod boundaryMeasure) =
    (1/2:ℝ) * ∫ z : Boundary × Boundary, R z.1 z.2 * (b z.1-b z.2)^2 *
      inner ℝ (g z.1) (g z.2) ∂boundaryMeasure.prod boundaryMeasure := by
  let q : Measure (Boundary × Boundary) := boundaryMeasure.prod boundaryMeasure
  let f₁ := fun z : Boundary × Boundary => R z.1 z.2 * inner ℝ (b z.1^2 • g z.1) (g z.2)
  let f₂ := fun z : Boundary × Boundary => R z.1 z.2 * inner ℝ (g z.1) (b z.2^2 • g z.2)
  let f₃ := fun z : Boundary × Boundary => R z.1 z.2 * inner ℝ (b z.1 • g z.1) (b z.2 • g z.2)
  have h1 : Integrable f₁ q := interaction_boundary_integrable hR ((hb.pow 2).smul hg) hg
  have h2 : Integrable f₂ q := interaction_boundary_integrable hR hg ((hb.pow 2).smul hg)
  have h3 : Integrable f₃ q := interaction_boundary_integrable hR (hb.smul hg) (hb.smul hg)
  have hswap : (∫ z, f₁ z ∂q) = ∫ z, f₂ z ∂q := by
    change (∫ z, f₁ z ∂boundaryMeasure.prod boundaryMeasure) = _
    rw [← integral_prod_swap f₁]
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [f₁,f₂]
    rw [hRs z.2 z.1,real_inner_comm (g z.1) (b z.2^2 • g z.2)]
  have he : (fun z : Boundary × Boundary => R z.1 z.2 * (b z.1-b z.2)^2 * inner ℝ (g z.1) (g z.2)) =
      fun z => f₁ z+f₂ z-2*f₃ z := by
    funext z
    dsimp [f₁,f₂,f₃]
    simp only [real_inner_smul_left,real_inner_smul_right]
    ring
  rw [he]
  change (∫ z, f₂ z ∂q)-(∫ z, f₃ z ∂q) = (1/2:ℝ)*(∫ z, f₁ z+f₂ z-2*f₃ z ∂q)
  have h12 : Integrable (fun z => f₁ z+f₂ z) q := h1.add h2
  rw [integral_sub h12 (h3.const_mul 2),integral_add h1 h2,integral_const_mul,hswap]
  ring

lemma multiplier_integrand_integrable {R : Boundary → Boundary → ℝ}
    (hR : Integrable (fun z : Boundary × Boundary => R z.1 z.2) (boundaryMeasure.prod boundaryMeasure))
    {g : Boundary → E} {b : Boundary → ℝ} {A B : ℝ≥0}
    (hg : LipschitzWith A g) (hb : LipschitzWith B b) :
    Integrable (fun z : Boundary × Boundary => (boundaryInteraction z.1 z.2+R z.1 z.2) *
      (b z.1-b z.2)^2 * inner ℝ (g z.1) (g z.2)) (boundaryMeasure.prod boundaryMeasure) := by
  obtain ⟨L,hL⟩ := boundary_smul_lipschitz hb hg
  obtain ⟨D,hD⟩ := boundary_smul_lipschitz hb hb
  have hD' : LipschitzWith D (fun s => b s^2) := by simpa only [smul_eq_mul,pow_two] using hD
  obtain ⟨F,hF⟩ := boundary_smul_lipschitz hD' hg
  have h0 := (harmonic_boundary_integrable hL hL).sub (harmonic_boundary_integrable hg hF)
  have h1 := interaction_boundary_integrable hR hF.continuous hg.continuous
  have h2 := interaction_boundary_integrable hR hg.continuous hF.continuous
  have h3 := interaction_boundary_integrable hR hL.continuous hL.continuous
  apply (h0.add ((h1.add h2).sub (h3.const_mul 2))).congr
  filter_upwards [] with z
  simp only [Pi.add_apply,Pi.sub_apply]
  rw [← mul_sub,harmonic_multiplier_algebra]
  simp only [real_inner_smul_left,real_inner_smul_right]
  ring


theorem boundaryForm_multiplier_difference {R : Boundary → Boundary → ℝ} {c : Boundary → ℝ}
    (hR : Integrable (fun z : Boundary × Boundary => R z.1 z.2) (boundaryMeasure.prod boundaryMeasure))
    (hRs : ∀ s t, R s t = R t s)
    {g : Boundary → E} {b : Boundary → ℝ} {A B : ℝ≥0}
    (hg : LipschitzWith A g) (hb : LipschitzWith B b) :
    boundaryForm R c (fun s => b s • g s) (fun s => b s • g s) -
      boundaryForm R c g (fun s => b s^2 • g s) =
    (1/2:ℝ) * ∫ z : Boundary × Boundary, (boundaryInteraction z.1 z.2+R z.1 z.2) *
      (b z.1-b z.2)^2 * inner ℝ (g z.1) (g z.2) ∂boundaryMeasure.prod boundaryMeasure := by
  have hcurv : (∫ s, c s * inner ℝ (b s • g s) (b s • g s) ∂boundaryMeasure) =
      ∫ s, c s * inner ℝ (g s) (b s^2 • g s) ∂boundaryMeasure := by
    apply integral_congr_ae
    filter_upwards [] with s
    simp only [real_inner_smul_left,real_inner_smul_right]
    ring
  obtain ⟨L,hL⟩ := boundary_smul_lipschitz hb hg
  obtain ⟨D,hD⟩ := boundary_smul_lipschitz hb hb
  have hD' : LipschitzWith D (fun s => b s^2) := by simpa only [smul_eq_mul,pow_two] using hD
  obtain ⟨F,hF⟩ := boundary_smul_lipschitz hD' hg
  have h0 : Integrable (fun z : Boundary × Boundary => boundaryInteraction z.1 z.2 *
      (b z.1-b z.2)^2 * inner ℝ (g z.1) (g z.2)) (boundaryMeasure.prod boundaryMeasure) := by
    apply ((harmonic_boundary_integrable hL hL).sub (harmonic_boundary_integrable hg hF)).congr
    filter_upwards [] with z
    simp only [Pi.sub_apply]
    rw [← mul_sub,harmonic_multiplier_algebra,mul_assoc]
  have h1 : Integrable (fun z : Boundary × Boundary => R z.1 z.2 *
      (b z.1-b z.2)^2 * inner ℝ (g z.1) (g z.2)) (boundaryMeasure.prod boundaryMeasure) := by
    have := (multiplier_integrand_integrable hR hg hb).sub h0
    apply this.congr
    filter_upwards [] with z
    simp only [Pi.sub_apply]
    ring
  have he : (fun z : Boundary × Boundary => (boundaryInteraction z.1 z.2+R z.1 z.2) *
      (b z.1-b z.2)^2 * inner ℝ (g z.1) (g z.2)) =
      fun z => boundaryInteraction z.1 z.2*(b z.1-b z.2)^2*inner ℝ (g z.1) (g z.2) +
        R z.1 z.2*(b z.1-b z.2)^2*inner ℝ (g z.1) (g z.2) := by
    funext z; ring
  rw [he,integral_add h0 h1]
  have hh := harmonic_multiplier_integral hg hb
  have hi := interaction_multiplier_integral hR hRs hg.continuous hb.continuous
  unfold boundaryForm
  rw [hcurv]
  linarith

end StrictHotSpots.PlaneGreen
end
end ActualBoundaryMultiplier

section SmoothPhysicalMultiplier

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
variable (hμ : 0 < firstPositiveNeumannValue Ω)



def multipliedGradient {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b) : Fin 2 → H1 Ω := fun i =>
  c.scalarSolution hΩ.2.2.1 hΩ.2.2.2.2 hμ
    (hb.contDiffOn.mul (closure_directional_smooth hΩ.2.1 hΩ.2.2.2.2 hu.1 (Hodge.e i)))

lemma multipliedGradient_class {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
    (hb0 : MemLp b ∞ (volume.restrict Ω)) (hb1 : MemLp (gradient b) ∞ (volume.restrict Ω))
    (i : Fin 2) : ∃ w : H10 hΩ.2.1,
      c.multipliedGradient hΩ hu hμ hb i-H1.smoothMul hb hb0 hb1 (eigenGradientField hΩ hu i)=w.val := by
  have he := smoothMul_smooth_closure hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.2 hb hb0 hb1
    (closure_directional_smooth hΩ.2.1 hΩ.2.2.2.2 hu.1 (Hodge.e i))
  exact he.symm ▸ c.scalarSolution_class hΩ.2.2.1 hΩ.2.2.2.2 hμ
    (hb.contDiffOn.mul (closure_directional_smooth hΩ.2.1 hΩ.2.2.2.2 hu.1 (Hodge.e i)))

lemma multipliedGradient_square_class {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
    (hb0 : MemLp b ∞ (volume.restrict Ω)) (hb1 : MemLp (gradient b) ∞ (volume.restrict Ω))
    (i : Fin 2) : ∃ w : H10 hΩ.2.1,
      c.multipliedGradient hΩ hu hμ (hb.mul hb) i-
        H1.smoothMul hb hb0 hb1 (H1.smoothMul hb hb0 hb1 (eigenGradientField hΩ hu i))=w.val := by
  let hw := closure_directional_smooth hΩ.2.1 hΩ.2.2.2.2 hu.1 (Hodge.e i)
  have h1 := smoothMul_smooth_closure hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.2 hb hb0 hb1 hw
  have h2 := smoothMul_smooth_closure hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.2 hb hb0 hb1 (hb.contDiffOn.mul hw)
  have h3 : (fun x => b x*(b x*fderivWithin ℝ u (closure Ω) x (Hodge.e i))) =
      (fun x => (b x*b x)*fderivWithin ℝ u (closure Ω) x (Hodge.e i)) := by funext x; ring
  have he : H1.smoothMul hb hb0 hb1 (H1.smoothMul hb hb0 hb1 (eigenGradientField hΩ hu i)) =
    (smooth_closure_H1 hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.2 ((hb.contDiffOn.mul hb.contDiffOn).mul hw)).toH1 := by
    apply H1.value_injective hΩ.2.1
    change H1.value (H1.smoothMul hb hb0 hb1 (H1.smoothMul hb hb0 hb1
      (smooth_closure_H1 hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.2 hw).toH1)) = _
    rw [h1,h2]
    apply Lp.ext
    filter_upwards [(smooth_closure_H1 hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.2 (hb.contDiffOn.mul (hb.contDiffOn.mul hw))).1.coeFn_toLp,
      (smooth_closure_H1 hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.2 ((hb.contDiffOn.mul hb.contDiffOn).mul hw)).1.coeFn_toLp]
      with x hx hy
    exact hx.trans ((congrFun h3 x).trans hy.symm)
  exact he.symm ▸ c.scalarSolution_class hΩ.2.2.1 hΩ.2.2.2.2 hμ
    ((hb.contDiffOn.mul hb.contDiffOn).mul hw)



theorem multipliedGradient_identity {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
    (hb0 : MemLp b ∞ (volume.restrict Ω)) (hb1 : MemLp (gradient b) ∞ (volume.restrict Ω)) :
    vectorForm (firstPositiveNeumannValue Ω) (c.multipliedGradient hΩ hu hμ hb)
      (c.multipliedGradient hΩ hu hμ hb) =
    cartesianForm (firstPositiveNeumannValue Ω) (c.multipliedGradient hΩ hu hμ hb)
      (c.multipliedGradient hΩ hu hμ hb)-
    cartesianForm (firstPositiveNeumannValue Ω) (eigenGradientField hΩ hu)
      (c.multipliedGradient hΩ hu hμ (hb.mul hb)) := by
  obtain ⟨L,_hL,hLμ,hD⟩ := H10.subcritical hΩ.2.1 hΩ.1 hΩ.2.2.1
  have hp := vectorForm_nonneg hΩ.2.1 hΩ.1 hΩ.2.2.2.1 hΩ.2.2.1 hμ hLμ hD
  exact boundaryClass_multiplier_identity hΩ.2.1 hb hb0 hb1 _ _ _ _
    (eigenGradientField_null hΩ hu).1
    (c.multipliedGradient_class hΩ hu hμ hb hb0 hb1)
    (c.multipliedGradient_square_class hΩ hu hμ hb hb0 hb1) hp
    (eigenGradientField_null hΩ hu).2

lemma multipliedGradient_tangent {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
    (hb0 : MemLp b ∞ (volume.restrict Ω)) (hb1 : MemLp (gradient b) ∞ (volume.restrict Ω)) :
    TangentWeak (c.multipliedGradient hΩ hu hμ hb) :=
  TangentWeak.of_class hΩ.2.1 ((eigenGradientField_null hΩ hu).1.smoothMul hb hb0 hb1)
    (c.multipliedGradient_class hΩ hu hμ hb hb0 hb1)

lemma multipliedGradient_nonneg {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
    (hb0 : MemLp b ∞ (volume.restrict Ω)) (hb1 : MemLp (gradient b) ∞ (volume.restrict Ω)) :
    0 ≤ vectorForm (firstPositiveNeumannValue Ω) (c.multipliedGradient hΩ hu hμ hb)
      (c.multipliedGradient hΩ hu hμ hb) := by
  obtain ⟨L,_hL,hLμ,hD⟩ := H10.subcritical hΩ.2.1 hΩ.1 hΩ.2.2.1
  exact vectorForm_nonneg hΩ.2.1 hΩ.1 hΩ.2.2.2.1 hΩ.2.2.1 hμ hLμ hD _
    (c.multipliedGradient_tangent hΩ hu hμ hb hb0 hb1)

end StrictHotSpots.Conformal.ClosedDiskChart
end
end SmoothPhysicalMultiplier


end OAI
