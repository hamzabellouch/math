import Mathlib
import OAI.Geometry.CubicTorus.Regularity.SurfaceH1Translation

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeQuadraticWeight (a n : Plane) (κ ε : ℝ) (x : Plane) : ℝ :=
  ⟪n,x-a⟫+(κ/2)*⟪n,x-a⟫^2-(ε/2)*‖x-a‖^2

lemma planeQuadraticWeight_smooth (a n : Plane) (κ ε : ℝ) :
    PlaneSmooth (planeQuadraticWeight a n κ ε) :=
  ((contDiff_const.inner ℝ (contDiff_id.sub contDiff_const)).add
    (contDiff_const.mul ((contDiff_const.inner ℝ (contDiff_id.sub contDiff_const)).pow 2))).sub
    (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ))

lemma planeQuadraticWeight_fderiv (a n : Plane) (κ ε : ℝ) (x : Plane) :
    fderiv ℝ (planeQuadraticWeight a n κ ε) x=
      innerSL ℝ n+(κ*⟪n,x-a⟫) • innerSL ℝ n-ε • innerSL ℝ (x-a) := by
  have hl := (innerSL ℝ n).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)
  have hd := (hl.add ((hl.pow 2).const_mul (κ/2))).sub
    (((hasFDerivAt_id x).sub_const a).norm_sq.const_mul (ε/2))
  change HasFDerivAt (planeQuadraticWeight a n κ ε) _ x at hd
  rw [hd.fderiv]
  ext v
  simp only [add_apply,sub_apply,smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,innerSL_apply_apply,smul_eq_mul,
    nsmul_eq_mul,Nat.cast_ofNat,Function.comp_apply,id_eq]
  ring

lemma planeQuadraticWeight_gradient (a n : Plane) (κ ε : ℝ) (x : Plane) :
    gradient (planeQuadraticWeight a n κ ε) x=
      n+(κ*⟪n,x-a⟫) • n-ε • (x-a) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,planeQuadraticWeight_fderiv]
  simp only [add_apply,sub_apply,smul_apply,innerSL_apply_apply,
    inner_sub_left,inner_add_left,real_inner_smul_left,smul_eq_mul]

lemma planeQuadraticWeight_hessian (a n : Plane) (κ ε : ℝ) (x v : Plane) :
    fderiv ℝ (gradient (planeQuadraticWeight a n κ ε)) x v=
      (κ*⟪n,v⟫) • n-ε • v := by
  have he : gradient (planeQuadraticWeight a n κ ε)=
      fun y => n+(κ*⟪n,y-a⟫) • n-ε • (y-a) :=
    funext (planeQuadraticWeight_gradient a n κ ε)
  rw [he]
  have hl := (innerSL ℝ n).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)
  have hd := (((hl.const_mul κ).smul_const n).const_add n).sub
    (((hasFDerivAt_id x).sub_const a).const_smul ε)
  change HasFDerivAt (fun y => n+(κ*⟪n,y-a⟫) • n-ε • (y-a)) _ x at hd
  rw [hd.fderiv]
  simp only [sub_apply,smul_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,innerSL_apply_apply,
    smul_eq_mul]

lemma planeQuadraticWeight_gradient_center (a n : Plane) (κ ε : ℝ) :
    gradient (planeQuadraticWeight a n κ ε) a=n := by
  simp [planeQuadraticWeight_gradient]

lemma quadratic_weight_R {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (a n : Plane) (κ ε : ℝ) (x w : Plane) :
    planeCarlemanR A (fun y => A y (gradient (planeQuadraticWeight a n κ ε) y)) x w=
      4*κ*⟪n,A x w⟫^2-4*ε*‖A x w‖^2+
      4*⟪w,(fderiv ℝ A x (A x w)) (gradient (planeQuadraticWeight a n κ ε) x)⟫-
      2*⟪w,(fderiv ℝ A x (A x (gradient (planeQuadraticWeight a n κ ε) x))) w⟫ := by
  have hg := plane_gradient_contDiff (planeQuadraticWeight_smooth a n κ ε)
  rw [planeCarlemanR,fderiv_clm_apply (hA.differentiable (by simp) x)
    (hg.differentiable (by simp) x)]
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    planeQuadraticWeight_hessian,map_sub,map_smul,inner_add_right,inner_sub_right,real_inner_smul_right]
  rw [hAs x w n,hAs x w (A x w),real_inner_self_eq_norm_sq]
  ring

lemma quadratic_weight_transport_center {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (a n : Plane) (κ ε : ℝ) :
    planeDrift (fun y => A y (gradient (planeQuadraticWeight a n κ ε) y))
      (planeEnergy A (planeQuadraticWeight a n κ ε)) a=
      2*κ*⟪n,A a n⟫^2-2*ε*‖A a n‖^2+⟪n,(fderiv ℝ A a (A a n)) n⟫ := by
  rw [planeDrift,planeEnergy_fderiv hA (planeQuadraticWeight_smooth a n κ ε) hAs,
    planeQuadraticWeight_gradient_center,planeQuadraticWeight_hessian]
  simp only [inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_inner_clm_bound (A : Plane →L[ℝ] Plane) (v w : Plane) :
    |⟪v,A w⟫|≤‖v‖*‖A‖*‖w‖ := by
  calc
    |⟪v,A w⟫|≤‖v‖*‖A w‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v‖*(‖A‖*‖w‖) := mul_le_mul_of_nonneg_left (A.le_opNorm w) (norm_nonneg _)
    _ = _ := by ring

lemma plane_inner_double_clm_bound (B : Plane →L[ℝ] (Plane →L[ℝ] Plane)) (v w z : Plane) :
    |⟪v,B w z⟫|≤‖v‖*‖B‖*‖w‖*‖z‖ := by
  calc
    |⟪v,B w z⟫|≤‖v‖*‖B w‖*‖z‖ := plane_inner_clm_bound _ _ _
    _ ≤ ‖v‖*(‖B‖*‖w‖)*‖z‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (B.le_opNorm w) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

lemma quadratic_weight_R_lower {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (a n : Plane) {κ ε M K P : ℝ} (hκ : 0≤κ) (hε : 0≤ε)
    {x : Plane} (hM : ‖A x‖≤M) (hK : ‖fderiv ℝ A x‖≤K)
    (hP : ‖gradient (planeQuadraticWeight a n κ ε) x‖≤P) (w : Plane) :
    -(4*ε*M^2+6*K*M*P)*‖w‖^2≤
    planeCarlemanR A (fun y => A y (gradient (planeQuadraticWeight a n κ ε) y)) x w := by
  let p := gradient (planeQuadraticWeight a n κ ε) x
  have hM0 : 0≤M := (norm_nonneg _).trans hM
  have hK0 : 0≤K := (norm_nonneg (fderiv ℝ A x)).trans hK
  have hP0 : 0≤P := (norm_nonneg _).trans hP
  have haw : ‖A x w‖≤M*‖w‖ := (A x).le_opNorm w |>.trans
    (mul_le_mul_of_nonneg_right hM (norm_nonneg _))
  have hap : ‖A x p‖≤M*P := ((A x).le_opNorm p).trans
    (mul_le_mul hM hP (norm_nonneg _) hM0)
  have h₁ : |⟪w,(fderiv ℝ A x (A x w)) p⟫|≤K*M*P*‖w‖^2 := by
    calc
      _ ≤ ‖w‖*‖fderiv ℝ A x‖*‖A x w‖*‖p‖ := plane_inner_double_clm_bound _ _ _ _
      _ ≤ ‖w‖*K*(M*‖w‖)*P := by gcongr
      _ = _ := by ring
  have h₂ : |⟪w,(fderiv ℝ A x (A x p)) w⟫|≤K*M*P*‖w‖^2 := by
    calc
      _ ≤ ‖w‖*‖fderiv ℝ A x‖*‖A x p‖*‖w‖ := plane_inner_double_clm_bound _ _ _ _
      _ ≤ ‖w‖*K*(M*P)*‖w‖ := by gcongr
      _ = _ := by ring
  have hs : ‖A x w‖^2≤M^2*‖w‖^2 := by
    calc
      _ ≤ (M*‖w‖)^2 := sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM0 (norm_nonneg _)) |>.mpr haw
      _ = _ := by ring
  have hsq : 0≤4*κ*⟪n,A x w⟫^2 := by positivity
  have hneg := mul_le_mul_of_nonneg_left hs (show 0≤4*ε by positivity)
  rw [quadratic_weight_R hA hAs]
  have hleft := (abs_le.mp h₁).1
  have hright := (abs_le.mp h₂).2
  dsimp only [p] at hleft hright
  nlinarith only [hleft,hright,hneg,hsq]

lemma quadratic_weight_transport_lower {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (a : Plane) {n : Plane} (hn : ‖n‖=1) {κ ε M K ℓ : ℝ}
    (hκ : 0≤κ) (hε : 0≤ε) (hℓ : 0≤ℓ)
    (hell : ℓ≤⟪n,A a n⟫) (hM : ‖A a‖≤M) (hK : ‖fderiv ℝ A a‖≤K) :
    2*κ*ℓ^2-2*ε*M^2-K*M≤
    planeDrift (fun y => A y (gradient (planeQuadraticWeight a n κ ε) y))
      (planeEnergy A (planeQuadraticWeight a n κ ε)) a := by
  have hM0 : 0≤M := (norm_nonneg _).trans hM
  have hK0 : 0≤K := (norm_nonneg (fderiv ℝ A a)).trans hK
  have han : ‖A a n‖≤M := by
    simpa only [hn,mul_one] using ((A a).le_opNorm n).trans
      (mul_le_mul_of_nonneg_right hM (norm_nonneg n))
  have he : |⟪n,(fderiv ℝ A a (A a n)) n⟫|≤K*M := by
    calc
      _ ≤ ‖n‖*‖fderiv ℝ A a‖*‖A a n‖*‖n‖ := plane_inner_double_clm_bound _ _ _ _
      _ = ‖fderiv ℝ A a‖*‖A a n‖ := by rw [hn]; ring
      _ ≤ K*M := mul_le_mul hK han (norm_nonneg _) hK0
  have hs₁ := mul_le_mul_of_nonneg_left
    (sq_le_sq₀ hℓ (hℓ.trans hell) |>.mpr hell) (show 0≤2*κ by positivity)
  have hs₂ := mul_le_mul_of_nonneg_left
    (sq_le_sq₀ (norm_nonneg _) hM0 |>.mpr han) (show 0≤2*ε by positivity)
  rw [quadratic_weight_transport_center hA hAs]
  linarith [(abs_le.mp he).1]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_ellipticity_perturb {A B : Plane →L[ℝ] Plane} {ℓ δ : ℝ}
    (hA : ∀ v,ℓ*‖v‖^2≤⟪v,A v⟫) (hAB : ‖B-A‖≤δ) (v : Plane) :
    (ℓ-δ)*‖v‖^2≤⟪v,B v⟫ := by
  have hh := plane_inner_clm_bound (B-A) v v
  have hd : |⟪v,(B-A) v⟫|≤δ*‖v‖^2 := by
    calc
      _ ≤ ‖v‖*‖B-A‖*‖v‖ := hh
      _ ≤ ‖v‖*δ*‖v‖ := by gcongr
      _ = _ := by ring
  simp only [sub_apply,inner_sub_right] at hd
  linarith [(abs_le.mp hd).1,hA v]

theorem planeCarleman_weight_exists {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (a : Plane) {n : Plane} (hn : ‖n‖=1) {ℓ ε : ℝ} (hℓ : 0<ℓ) (hε : 0<ε)
    (hell : ∀ v,ℓ*‖v‖^2≤⟪v,A a v⟫) :
    ∃ κ>0,∃ r>0,∃ C D Q c : ℝ,
      PlaneCarlemanData A (fun y => A y (gradient (planeQuadraticWeight a n κ ε) y))
        (planeEnergy A (planeQuadraticWeight a n κ ε)) (Metric.ball a r) C D Q c ∧
      ∀ x∈Metric.ball a r,∀ v,(ℓ/2)*‖v‖^2≤⟪v,A x v⟫ := by
  let M := ‖A a‖+1
  let K := ‖fderiv ℝ A a‖+1
  let B := 4*ε*M^2+12*K*M
  let C := B/(ℓ/2)
  let Q := 4*M
  let c := ((C+1)*Q+2)/2
  have hM : 0<M := by dsimp [M]; positivity
  have hK : 0<K := by dsimp [K]; positivity
  have hB : 0≤B := by dsimp [B]; positivity
  have hC : 0≤C := div_nonneg hB (by positivity)
  have hQ : 0<Q := by dsimp [Q]; positivity
  have hc : 0<c := by dsimp [c]; positivity
  let κ := max 1 ((c+2*ε*M^2+K*M+1)/(2*ℓ^2))
  have hκ : 0<κ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hlarge : c+2*ε*M^2+K*M+1≤2*κ*ℓ^2 := by
    have hh := (div_le_iff₀ (show 0<2*ℓ^2 by positivity)).mp
      (le_max_right 1 ((c+2*ε*M^2+K*M+1)/(2*ℓ^2)))
    dsimp only [κ]
    nlinarith only [hh]
  let φ := planeQuadraticWeight a n κ ε
  let b : Plane → Plane := fun y => A y (gradient φ y)
  let q := planeEnergy A φ
  have hφ : PlaneSmooth φ := planeQuadraticWeight_smooth _ _ _ _
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := hA.clm_apply (plane_gradient_contDiff hφ)
  have hq : PlaneSmooth q := planeEnergy_contDiff hA hφ
  have htrans : c<planeDrift b q a := by
    have hh := quadratic_weight_transport_lower hA hAs a hn hκ.le hε.le hℓ.le
      (by simpa only [hn,one_pow,mul_one] using hell n)
      (show ‖A a‖≤M by dsimp [M]; linarith)
      (show ‖fderiv ℝ A a‖≤K by dsimp [K]; linarith)
    change 2*κ*ℓ^2-2*ε*M^2-K*M≤planeDrift b q a at hh
    linarith
  let D := |planeElliptic A (planeDivergence b) a|+1
  have hD : 0≤D := by dsimp [D]; positivity
  have hDA := hA.continuous_fderiv (by simp)
  have hevM : ∀ᶠ x in 𝓝 a,‖A x‖<M :=
    (hA.continuous.norm.tendsto a).eventually (eventually_lt_nhds (lt_add_one _))
  have hevK : ∀ᶠ x in 𝓝 a,‖fderiv ℝ A x‖<K :=
    (hDA.norm.tendsto a).eventually (eventually_lt_nhds (lt_add_one _))
  have hevp : ∀ᶠ x in 𝓝 a,‖gradient φ x‖<2 :=
    ((plane_gradient_contDiff hφ).continuous.norm.tendsto a).eventually
      (eventually_lt_nhds (by simp only [φ,planeQuadraticWeight_gradient_center,hn]; norm_num))
  have hevell : ∀ᶠ x in 𝓝 a,‖A x-A a‖<ℓ/2 :=
    ((hA.continuous.sub continuous_const).norm.tendsto a).eventually
      (eventually_lt_nhds (by change ‖A a-A a‖<ℓ/2; simp only [sub_self,norm_zero]; positivity))
  have hevt : ∀ᶠ x in 𝓝 a,c<planeDrift b q x :=
    ((planeDrift_contDiff hb hq).continuous.tendsto a).eventually (eventually_gt_nhds htrans)
  have hevd : ∀ᶠ x in 𝓝 a,planeElliptic A (planeDivergence b) x<D :=
    ((planeElliptic_contDiff hA (planeDivergence_contDiff hb)).continuous.tendsto a).eventually
      (eventually_lt_nhds (by dsimp [D]; linarith [le_abs_self (planeElliptic A (planeDivergence b) a)]))
  have hev := hevM.and (hevK.and (hevp.and (hevell.and (hevt.and hevd))))
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hell' (x : Plane) (hx : x∈Metric.ball a r) (v : Plane) :
      (ℓ/2)*‖v‖^2≤⟪v,A x v⟫ := by
    have hh := plane_ellipticity_perturb hell (hball hx).2.2.2.1.le v
    convert hh using 1
    ring
  refine ⟨κ,hκ,r,hr,C,D,Q,c,?_,hell'⟩
  refine ⟨hC,hD,?_,?_,?_,?_,?_⟩
  · dsimp [c]
    linarith
  · intro x hx v
    obtain ⟨hMx,hKx,hpx,_,_,_⟩ := hball hx
    have hh := quadratic_weight_R_lower hA hAs a n hκ.le hε.le hMx.le hKx.le hpx.le v
    have hmul := mul_le_mul_of_nonneg_left (hell' x hx v) hC
    have hCB : C*(ℓ/2)=B := by dsimp [C]; exact div_mul_cancel₀ _ (by positivity)
    change -C*⟪v,A x v⟫≤planeCarlemanR A b x v
    have he : (4*ε*M^2+6*K*M*2)=B := by dsimp [B]; ring
    rw [he] at hh
    dsimp only [φ,b]
    nlinarith only [hh,hmul,hCB]
  · intro x hx
    obtain ⟨hMx,_,hpx,_,_,_⟩ := hball hx
    have hh := plane_inner_clm_bound (A x) (gradient φ x) (gradient φ x)
    change ⟪gradient φ x,A x (gradient φ x)⟫≤Q
    calc
      _ ≤ |⟪gradient φ x,A x (gradient φ x)⟫| := le_abs_self _
      _ ≤ ‖gradient φ x‖*‖A x‖*‖gradient φ x‖ := hh
      _ ≤ 2*M*2 := by gcongr
      _ = Q := by dsimp [Q]; ring
  · intro x hx
    exact (hball hx).2.2.2.2.1.le
  · intro x hx
    exact (hball hx).2.2.2.2.2.le

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma quadratic_weight_scalar_outside {s t κ ε R : ℝ} (hR : 0<R) (ht : 0≤t)
    (hκ : 0≤κ) (hsmall : κ*t≤1) (hst : |s|≤t)
    (hout : 2*R*s≤t^2) (hε : 4/R≤ε) :
    s+(κ/2)*s^2-(ε/2)*t^2≤ -(1/R)*t^2 := by
  have hlin : s+(κ/2)*s^2≤t^2/R := by
    by_cases hs : s≤0
    · have hst' : -s≤t := by simpa only [abs_of_nonpos hs] using hst
      have hsκ : κ*(-s)≤1 :=
        (mul_le_mul_of_nonneg_left hst' hκ).trans hsmall
      have hh := mul_le_mul_of_nonneg_right hsκ (neg_nonneg.mpr hs)
      have hn : 0≤t^2/R := div_nonneg (pow_nonneg ht 2) hR.le
      nlinarith only [hh,hn,hs]
    · have hs0 : 0≤ s := le_of_not_ge hs
      have hst' : s≤t := (le_abs_self _).trans hst
      have hsκ : κ*s≤1 := (mul_le_mul_of_nonneg_left hst' hκ).trans hsmall
      have hh := mul_le_mul_of_nonneg_right hsκ hs0
      have hhout : 2*s≤t^2/R := (le_div_iff₀ hR).mpr (by nlinarith only [hout])
      nlinarith only [hh,hhout,hs0]
  have he := mul_le_mul_of_nonneg_right hε (sq_nonneg t)
  have heq₁ : (4/R)*t^2=4*(t^2/R) := by ring
  have heq₂ : -(1/R)*t^2= -(t^2/R) := by ring
  rw [heq₁] at he
  rw [heq₂]
  nlinarith only [he,hlin]

lemma planeQuadraticWeight_outside {a n x : Plane} {κ ε R : ℝ}
    (hn : ‖n‖=1) (hR : 0<R) (hκ : 0≤κ) (hsmall : κ*‖x-a‖≤1)
    (hout : R≤‖x-(a+R • n)‖) (hε : 4/R≤ε) :
    planeQuadraticWeight a n κ ε x≤ -(1/R)*‖x-a‖^2 := by
  have hst : |⟪n,x-a⟫|≤‖x-a‖ := by
    simpa only [hn,one_mul] using abs_real_inner_le_norm n (x-a)
  have he : ‖x-(a+R • n)‖^2=‖x-a‖^2+R^2-2*R*⟪n,x-a⟫ := by
    rw [show x-(a+R • n)=(x-a)-R • n by abel,norm_sub_sq_real]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR,hn,mul_one,real_inner_smul_right,
      real_inner_comm (x-a) n]
    ring
  have hout' : 2*R*⟪n,x-a⟫≤‖x-a‖^2 := by
    have hh := sq_le_sq₀ hR.le (norm_nonneg _) |>.mpr hout
    rw [he] at hh
    linarith
  exact quadratic_weight_scalar_outside hR (norm_nonneg _) hκ hsmall hst hout' hε

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_gradient_exp {f : Plane → ℝ} (hf : PlaneSmooth f) (τ : ℝ) (x : Plane) :
    gradient (fun y => Real.exp (τ*f y)) x=(τ*Real.exp (τ*f x)) • gradient f x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,real_inner_smul_left,inner_gradient_left]
  rw [(((hf.differentiable (by simp) x).hasFDerivAt.const_mul τ).exp).fderiv]
  simp only [smul_apply,smul_eq_mul]
  ring

lemma planeElliptic_mul {A : Plane → Plane →L[ℝ] Plane} {f g : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : PlaneSmooth f) (hg : PlaneSmooth g)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) (x : Plane) :
    planeElliptic A (fun y => f y*g y) x=
      f x*planeElliptic A g x+g x*planeElliptic A f x+2*⟪gradient f x,A x (gradient g x)⟫ := by
  have hF := hA.clm_apply (plane_gradient_contDiff hf)
  have hG := hA.clm_apply (plane_gradient_contDiff hg)
  have he : (fun y => A y (gradient (fun z => f z*g z) y))=
      fun y => f y • A y (gradient g y)+g y • A y (gradient f y) := by
    funext y
    rw [plane_gradient_mul (hf.differentiable (by simp) y) (hg.differentiable (by simp) y)]
    simp only [map_add,map_smul]
  unfold planeElliptic
  rw [he]
  erw [planeDivergence_add ((hf.smul hG).differentiable (by simp) x)
      ((hg.smul hF).differentiable (by simp) x),
    planeDivergence_smul (hf.differentiable (by simp) x) (hG.differentiable (by simp) x),
    planeDivergence_smul (hg.differentiable (by simp) x) (hF.differentiable (by simp) x)]
  rw [hAs x (gradient g x) (gradient f x)]
  ring

lemma planeElliptic_exp {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : PlaneSmooth f) (τ : ℝ) (x : Plane) :
    planeElliptic A (fun y => Real.exp (τ*f y)) x=
      Real.exp (τ*f x)*(τ*planeElliptic A f x+τ^2*planeEnergy A f x) := by
  have he : (fun y => A y (gradient (fun z => Real.exp (τ*f z)) y))=
      fun y => (τ*Real.exp (τ*f y)) • A y (gradient f y) := by
    funext y
    rw [plane_gradient_exp hf,map_smul]
  have hF := hA.clm_apply (plane_gradient_contDiff hf)
  have hk : PlaneSmooth (fun y => τ*Real.exp (τ*f y)) :=
    contDiff_const.mul ((contDiff_const.mul hf).exp)
  unfold planeElliptic
  rw [he]
  erw [planeDivergence_smul (hk.differentiable (by simp) x) (hF.differentiable (by simp) x)]
  rw [inner_gradient_left,fderiv_const_mul (((contDiff_const.mul hf).exp).differentiable (by simp) x)]
  rw [(((hf.differentiable (by simp) x).hasFDerivAt.const_mul τ).exp).fderiv]
  simp only [smul_apply,smul_eq_mul,← inner_gradient_left,planeEnergy]
  ring

theorem planeCarleman_conjugation {A : Plane → Plane →L[ℝ] Plane} {φ v : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hφ : PlaneSmooth φ) (hv : PlaneSmooth v)
    (hAs : ∀ x w z,⟪w,A x z⟫=⟪z,A x w⟫) (τ : ℝ) (x : Plane) :
    planeCarlemanP A (fun y => A y (gradient φ y)) (planeEnergy A φ) τ
      (fun y => Real.exp (τ*φ y)*v y) x=Real.exp (τ*φ x)*planeElliptic A v x := by
  have he : PlaneSmooth (fun y => Real.exp (τ*φ y)) := (contDiff_const.mul hφ).exp
  unfold planeCarlemanP planeCarlemanS planeCarlemanT planeDrift
  rw [planeElliptic_mul hA he hv hAs,planeElliptic_exp hA hφ,plane_gradient_exp hφ,
    fderiv_fun_mul (he.differentiable (by simp) x) (hv.differentiable (by simp) x)]
  rw [(((hφ.differentiable (by simp) x).hasFDerivAt.const_mul τ).exp).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,← inner_gradient_left,real_inner_smul_left,
    planeEnergy,planeElliptic]
  rw [hAs x (gradient v x) (gradient φ x)]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_square_compact {u : Plane → ℝ} (hc : HasCompactSupport u) :
    HasCompactSupport (fun x => u x^2) := hc.mono (by
  intro x hx hz
  exact hx (by simp [hz]))

theorem planeCarleman_weighted {A : Plane → Plane →L[ℝ] Plane} {φ v : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hφ : PlaneSmooth φ) (hv : PlaneSmooth v)
    (hc : HasCompactSupport v) (hAs : ∀ x w z,⟪w,A x z⟫=⟪z,A x w⟫)
    {U : Set Plane} {C D Q c τ : ℝ} (hs : tsupport v⊆U)
    (hell : ∀ x∈U,∀ w,0≤⟪w,A x w⟫)
    (hdata : PlaneCarlemanData A (fun y => A y (gradient φ y)) (planeEnergy A φ) U C D Q c)
    (hτ : 1≤τ) (hbudget : D+(C+1)^2≤τ) :
    τ^3*(∫ x,(Real.exp (τ*φ x))^2*v x^2)≤
      ∫ x,(Real.exp (τ*φ x))^2*(planeElliptic A v x)^2 := by
  let u : Plane → ℝ := fun x => Real.exp (τ*φ x)*v x
  have hu : PlaneSmooth u := ((contDiff_const.mul hφ).exp).mul hv
  have huc : HasCompactSupport u := hc.mul_left
  have hus : tsupport u⊆tsupport v := tsupport_mul_subset_right
  have hb := hA.clm_apply (plane_gradient_contDiff hφ)
  have hq := planeEnergy_contDiff hA hφ
  have he := planeCarleman_coercive hA hb hq hu huc hAs (hus.trans hs) hdata hτ hbudget
  have hn (x : Plane) : 0≤planeEnergy A u x := by
    by_cases hx : x∈tsupport u
    · exact hell x (hs (hus hx)) (gradient u x)
    · have hg : gradient u x=0 := by simp [gradient,fderiv_of_notMem_tsupport ℝ hx]
      simp [planeEnergy,hg]
  have hi : Integrable (fun x => τ^3*u x^2) :=
    (((hu.continuous.pow 2).integrable_of_hasCompactSupport (plane_square_compact huc)).const_mul _)
  have hj : Integrable (fun x => τ*planeEnergy A u x+τ^3*u x^2) :=
    (((planeEnergy_contDiff hA hu).continuous.integrable_of_hasCompactSupport
      (planeEnergy_compact huc)).const_mul τ).add hi
  have hm := integral_mono hi hj (fun x => le_add_of_nonneg_left (mul_nonneg (by linarith) (hn x)))
  have ht := hm.trans he
  simp only [u,planeCarleman_conjugation hA hφ hv hAs,mul_pow] at ht
  rwa [integral_const_mul] at ht

theorem planeCarleman_vanish_above {A : Plane → Plane →L[ℝ] Plane} {φ v : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hφ : PlaneSmooth φ) (hv : PlaneSmooth v)
    (hc : HasCompactSupport v) (hAs : ∀ x w z,⟪w,A x z⟫=⟪z,A x w⟫)
    {U : Set Plane} {C D Q c d : ℝ} (hs : tsupport v⊆U)
    (hell : ∀ x∈U,∀ w,0≤⟪w,A x w⟫)
    (hdata : PlaneCarlemanData A (fun y => A y (gradient φ y)) (planeEnergy A φ) U C D Q c)
    (hres : ∀ x,planeElliptic A v x≠0 → φ x≤d) :
    ∀ x,d<φ x → v x=0 := by
  let S : Set Plane := {x | d<φ x}
  have hSo : IsOpen S := isOpen_lt continuous_const hφ.continuous
  have hSm : MeasurableSet S := hSo.measurableSet
  have hvI : Integrable (fun x => v x^2) :=
    (hv.continuous.pow 2).integrable_of_hasCompactSupport (plane_square_compact hc)
  have hL := planeElliptic_contDiff hA hv
  have hLc := planeElliptic_compact (A := A) hc
  have hLI : Integrable (fun x => planeElliptic A v x^2) :=
    (hL.continuous.pow 2).integrable_of_hasCompactSupport (plane_square_compact hLc)
  let I : ℝ := ∫ x in S,v x^2
  let N : ℝ := ∫ x,planeElliptic A v x^2
  have hI : 0≤I := integral_nonneg (fun _ => sq_nonneg _)
  have hN : 0≤N := integral_nonneg (fun _ => sq_nonneg _)
  have hbound (τ : ℝ) (ht : 1≤τ) (hb : D+(C+1)^2≤τ) : τ^3*I≤N := by
    have ht0 : 0≤τ := by linarith
    let w : Plane → ℝ := fun x => (Real.exp (τ*φ x))^2
    let W : ℝ := (Real.exp (τ*d))^2
    have hW : 0<W := sq_pos_of_pos (Real.exp_pos _)
    have hw : Continuous w := (Real.continuous_exp.comp (continuous_const.mul hφ.continuous)).pow 2
    have hi : Integrable (fun x => w x*v x^2) :=
      (hw.mul (hv.continuous.pow 2)).integrable_of_hasCompactSupport
        (plane_square_compact hc).mul_left
    have hj : Integrable (fun x => w x*planeElliptic A v x^2) :=
      (hw.mul (hL.continuous.pow 2)).integrable_of_hasCompactSupport
        (plane_square_compact hLc).mul_left
    have hlo : W*I≤∫ x,w x*v x^2 := by
      rw [← integral_const_mul,← integral_indicator hSm]
      apply integral_mono ((hvI.const_mul W).indicator hSm) hi
      intro x
      by_cases hx : x∈S
      · rw [indicator_of_mem hx]
        apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact pow_le_pow_left₀ (Real.exp_nonneg _) (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (le_of_lt hx) ht0)) 2
      · rw [indicator_of_notMem hx]
        exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hhi : (∫ x,w x*planeElliptic A v x^2)≤W*N := by
      rw [← integral_const_mul]
      apply integral_mono hj (hLI.const_mul W)
      intro x
      by_cases hx : planeElliptic A v x=0
      · simp [hx]
      · apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact pow_le_pow_left₀ (Real.exp_nonneg _) (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (hres x hx) ht0)) 2
    have hh := planeCarleman_weighted hA hφ hv hc hAs hs hell hdata ht hb
    have hmul := mul_le_mul_of_nonneg_left hlo (pow_nonneg ht0 3)
    have hf : W*(τ^3*I)≤W*N := by nlinarith only [hmul,hh,hhi]
    nlinarith only [hf,hW]
  have hIz : I=0 := by
    by_contra hz
    have hip : 0<I := lt_of_le_of_ne hI (Ne.symm hz)
    let τ := max 1 (max (D+(C+1)^2) (N/I+1))
    have ht : 1≤τ := le_max_left _ _
    have hb : D+(C+1)^2≤τ := (le_max_left _ _).trans (le_max_right _ _)
    have hlarge : N/I+1≤τ := (le_max_right _ _).trans (le_max_right _ _)
    have hτI : N<τ*I := by
      have hx := (div_lt_iff₀ hip).mp (show N/I<τ by linarith)
      linarith
    have hpow : τ≤τ^3 := by nlinarith [sq_nonneg (τ-1)]
    have hp := mul_le_mul_of_nonneg_right hpow hI
    linarith [hbound τ ht hb]
  have hae : (fun x => v x^2)=ᵐ[volume.restrict S] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall (fun x => sq_nonneg (v x)))
      hvI.integrableOn).mp hIz
  have heq := Measure.eqOn_open_of_ae_eq hae hSo (hv.continuous.pow 2).continuousOn continuousOn_const
  intro x hx
  have hz := heq hx
  exact sq_eq_zero_iff.mp hz

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_gradient_eventuallyEq {f g : Plane → ℝ} {x : Plane}
    (h : f=ᶠ[𝓝 x] g) : gradient f=ᶠ[𝓝 x] gradient g := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  simp only [gradient,hy]

lemma planeElliptic_congr_nhds {A : Plane → Plane →L[ℝ] Plane} {f g : Plane → ℝ}
    {x : Plane} (h : f=ᶠ[𝓝 x] g) : planeElliptic A f x=planeElliptic A g x := by
  have hg : (fun y => A y (gradient f y))=ᶠ[𝓝 x] (fun y => A y (gradient g y)) := by
    filter_upwards [plane_gradient_eventuallyEq h] with y hy
    rw [hy]
  simp only [planeElliptic,planeDivergence,hg.fderiv_eq]

@[simp] lemma planeElliptic_zero (A : Plane → Plane →L[ℝ] Plane) (x : Plane) :
    planeElliptic A (fun _ => 0) x=0 := by
  simp [planeElliptic,planeDivergence,gradient]

lemma planeElliptic_zero_of_notMem_tsupport {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ}
    {x : Plane} (hx : x∉tsupport f) : planeElliptic A f x=0 := by
  have he : f=ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [planeElliptic_congr_nhds he,planeElliptic_zero]

lemma planeElliptic_zero_on_open {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ}
    {U : Set Plane} (hU : IsOpen U) (hz : ∀ x∈U,f x=0) {x : Plane} (hx : x∈U) :
    planeElliptic A f x=0 := by
  have he : f=ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hz y hy
  rw [planeElliptic_congr_nhds he,planeElliptic_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem planeElliptic_continue_tangent_ball {A : Plane → Plane →L[ℝ] Plane}
    {f : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : PlaneSmooth f)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    {U : Set Plane} (hU : IsOpen U) {a n : Plane} (ha : a∈U) (hn : ‖n‖=1)
    {ℓ R : ℝ} (hℓ : 0<ℓ) (hR : 0<R)
    (hell : ∀ v,ℓ*‖v‖^2≤⟪v,A a v⟫)
    (heq : ∀ x∈U,planeElliptic A f x=0)
    (hz : ∀ x∈Metric.ball (a+R • n) R,f x=0) :
    a∈interior {x | f x=0} := by
  obtain ⟨κ,hκ,r₀,hr₀,C,D,Q,c,hdata,hell'⟩ :=
    planeCarleman_weight_exists hA hAs a hn hℓ (show 0<4/R by positivity) hell
  obtain ⟨rU,hrU,hballU⟩ := Metric.isOpen_iff.mp hU a ha
  let r := min r₀ (min rU (1/(κ+1)))
  have hr : 0<r := lt_min hr₀ (lt_min hrU (by positivity))
  have hrr₀ : r≤r₀ := min_le_left _ _
  have hrrU : r≤rU := (min_le_left _ _).trans' (min_le_right _ _)
  have hrrκ : r≤1/(κ+1) := (min_le_right _ _).trans (min_le_right _ _)
  let χ : ContDiffBump a := ⟨r/4,r/2,by positivity,by linarith⟩
  let v : Plane → ℝ := fun x => χ x*f x
  let φ := planeQuadraticWeight a n κ (4/R)
  let d := -(1/R)*(r/4)^2
  have hv : PlaneSmooth v := χ.contDiff.mul hf
  have hvc : HasCompactSupport v := χ.hasCompactSupport.mul_right
  have hvs : tsupport v⊆Metric.closedBall a (r/2) := by
    calc tsupport v ⊆ tsupport (χ : Plane → ℝ) := tsupport_mul_subset_left
         _ = _ := χ.tsupport_eq
  have hs₀ : tsupport v⊆Metric.ball a r₀ := by
    intro x hx
    have hh : dist x a≤r/2 := hvs hx
    change dist x a<r₀
    linarith
  have hsU : tsupport v⊆U := by
    intro x hx
    apply hballU
    have hh : dist x a≤r/2 := hvs hx
    change dist x a<rU
    linarith
  have hveq {x : Plane} (hx : x∈Metric.ball a (r/4)) : v=ᶠ[𝓝 x] f := by
    filter_upwards [χ.eventuallyEq_one_of_mem_ball hx] with y hy
    change χ y*f y=f y
    simp only [hy,Pi.one_apply,one_mul]
  have hres (x : Plane) (hx : planeElliptic A v x≠0) : φ x≤d := by
    have hxs : x∈tsupport v := by
      by_contra h
      exact hx (planeElliptic_zero_of_notMem_tsupport h)
    have hsmall : κ*‖x-a‖≤1 := by
      have hdist : ‖x-a‖≤r/2 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hvs hxs
      have hk : κ*r≤1 := by
        have hb := (le_div_iff₀ (show 0<κ+1 by positivity)).mp hrrκ
        nlinarith
      nlinarith
    have hout : R≤‖x-(a+R • n)‖ := by
      by_contra h
      have hxin : x∈Metric.ball (a+R • n) R := by
        simpa only [Metric.mem_ball,dist_eq_norm] using (lt_of_not_ge h)
      apply hx
      apply planeElliptic_zero_on_open Metric.isOpen_ball (x := x) (hx := hxin)
      intro y hy
      dsimp [v]
      rw [hz y hy,mul_zero]
    have hfar : r/4≤‖x-a‖ := by
      by_contra h
      have hxin : x∈Metric.ball a (r/4) := by
        simpa only [Metric.mem_ball,dist_eq_norm] using (lt_of_not_ge h)
      exact hx ((planeElliptic_congr_nhds (hveq hxin)).trans (heq x (hsU hxs)))
    have hh := planeQuadraticWeight_outside hn hR hκ.le hsmall hout (le_refl (4/R))
    change φ x≤d
    apply hh.trans
    dsimp [d]
    have hsq : (r/4)^2≤‖x-a‖^2 := (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hfar
    nlinarith [mul_le_mul_of_nonneg_left hsq (show 0≤1/R by positivity)]
  have hvan := planeCarleman_vanish_above hA (planeQuadraticWeight_smooth _ _ _ _)
    hv hvc hAs hs₀ (fun x hx w => (by positivity : 0≤(ℓ/2)*‖w‖^2).trans (hell' x hx w))
    hdata hres
  have hd : d<φ a := by
    dsimp [φ,planeQuadraticWeight,d]
    simp only [sub_self,inner_zero_right,zero_pow (by decide : 2≠0),mul_zero,norm_zero,
      zero_add]
    have hp : 0<(1/R)*(r/4)^2 := by positivity
    linarith
  have ho : IsOpen {x : Plane | d<φ x} :=
    isOpen_lt continuous_const (planeQuadraticWeight_smooth _ _ _ _).continuous
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (inter_mem (ho.mem_nhds hd)
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (show 0<r/4 by positivity))))
  intro x hx
  have hvz := hvan x hx.1
  have he := Filter.EventuallyEq.eq_of_nhds (hveq hx.2)
  exact he.symm.trans hvz

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeHopfBarrier (c : Plane) (α R : ℝ) (x : Plane) : ℝ :=
  Real.exp (-α*‖x-c‖^2)-Real.exp (-α*R^2)

lemma planeHopfBarrier_smooth (c : Plane) (α R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (planeHopfBarrier c α R) :=
  ((contDiff_const.mul (((contDiff_id : ContDiff ℝ (⊤ : ℕ∞) (fun x : Plane => x)).sub contDiff_const).norm_sq ℝ)).exp).sub contDiff_const

lemma planeHopfBarrier_fderiv (c : Plane) (α R : ℝ) (x : Plane) :
    fderiv ℝ (planeHopfBarrier c α R) x=
      (-2*α*Real.exp (-α*‖x-c‖^2)) • innerSL ℝ (x-c) := by
  have h := (((hasFDerivAt_id x).sub_const c).norm_sq.const_mul (-α)).exp.sub_const
    (Real.exp (-α*R^2))
  change fderiv ℝ (fun x => Real.exp (-α*‖x-c‖^2)-Real.exp (-α*R^2)) x=_
  simp only [id_eq] at h
  rw [h.fderiv]
  ext v
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,innerSL_apply_apply,smul_eq_mul]
  ring

lemma planeHopfBarrier_gradient (c : Plane) (α R : ℝ) (x : Plane) :
    gradient (planeHopfBarrier c α R) x=
      (-2*α*Real.exp (-α*‖x-c‖^2)) • (x-c) := by
  ext i
  rw [plane_gradient_component,planeHopfBarrier_fderiv]
  simp only [smul_apply,innerSL_apply_apply,
    EuclideanSpace.inner_single_right,conj_trivial,one_mul,smul_eq_mul,PiLp.smul_apply]

lemma planeHopfBarrier_hessian (c : Plane) (α R : ℝ) (x v : Plane) :
    ⟪fderiv ℝ (gradient (planeHopfBarrier c α R)) x v,v⟫=
      Real.exp (-α*‖x-c‖^2)*(4*α^2*⟪x-c,v⟫^2-2*α*‖v‖^2) := by
  have he : gradient (planeHopfBarrier c α R)=
      fun y => (-2*α*Real.exp (-α*‖y-c‖^2)) • (y-c) :=
    funext (planeHopfBarrier_gradient c α R)
  rw [he]
  have hd := (((((hasFDerivAt_id x).sub_const c).norm_sq.const_mul (-α)).exp).const_mul (-2*α)).smul
    ((hasFDerivAt_id x).sub_const c)
  simp only [id_eq] at hd
  change HasFDerivAt (fun y : Plane => (-2*α*Real.exp (-α*‖y-c‖^2)) • (y-c)) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,innerSL_apply_apply,
    smul_eq_mul,inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq]
  ring

lemma planeFrameOperator_barrier (B : Plane → Fin 2 → Plane) (b : Plane → Plane)
    (c : Plane) (α R : ℝ) (x : Plane) :
    planeFrameOperator B b (planeHopfBarrier c α R) x=
      Real.exp (-α*‖x-c‖^2)*
        (4*α^2*(∑ i,⟪x-c,B x i⟫^2)-2*α*(∑ i,‖B x i‖^2)-2*α*⟪x-c,b x⟫) := by
  simp only [planeFrameOperator,planeHopfBarrier_hessian,planeHopfBarrier_gradient,
    real_inner_smul_left,Finset.sum_sub_distrib,← Finset.mul_sum]
  ring

lemma planeFrameOperator_barrier_pos (B : Plane → Fin 2 → Plane) (b : Plane → Plane)
    (c : Plane) {α R r κ K : ℝ} (hr : 0<r) (hκ : 0<κ) (hK : 0≤K)
    (hα : 0<α) (hlarge : K*(1+R)<2*α*κ*r^2)
    {x : Plane} (hrx : r≤‖x-c‖) (hxR : ‖x-c‖≤R)
    (hell : κ*‖x-c‖^2≤∑ i,⟪x-c,B x i⟫^2)
    (hB : (∑ i,‖B x i‖^2)≤K) (hb : ‖b x‖≤K) :
    0<planeFrameOperator B b (planeHopfBarrier c α R) x := by
  rw [planeFrameOperator_barrier]
  apply mul_pos (Real.exp_pos _) ?_
  have hb' : ⟪x-c,b x⟫≤R*K := (real_inner_le_norm _ _).trans
    ((mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hxR hK))
  have hsq : r^2≤‖x-c‖^2 := sq_le_sq₀ hr.le (norm_nonneg _) |>.mpr hrx
  have he : κ*r^2≤∑ i,⟪x-c,B x i⟫^2 :=
    (mul_le_mul_of_nonneg_left hsq hκ.le).trans hell
  have ha2 : 0<2*α := by positivity
  have ha4 : 0≤4*α^2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left he ha4
  have h2 := mul_le_mul_of_nonneg_left hB ha2.le
  have h3 := mul_le_mul_of_nonneg_left hb' ha2.le
  have h4 := mul_lt_mul_of_pos_left hlarge ha2
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma deriv_nonneg_of_right_min {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (hm : ∀ᶠ t in 𝓝[>] (0 : ℝ),f 0≤f t) : 0≤d := by
  have ht := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono (0 : ℝ) (show Ioi 0⊆{0}ᶜ from fun t ht => ne_of_gt ht))
  apply ge_of_tendsto ht
  filter_upwards [hm,self_mem_nhdsWithin] with t hmt ht
  rw [slope_def_field]
  exact div_nonneg (sub_nonneg.mpr hmt) (by simpa using (show 0≤t from le_of_lt ht))

lemma planeHopfBarrier_inward (c : Plane) {α R : ℝ} (hα : 0<α) (hR : 0<R)
    {y : Plane} (hy : ‖y-c‖=R) :
    0<fderiv ℝ (planeHopfBarrier c α R) y (c-y) := by
  rw [planeHopfBarrier_fderiv]
  simp only [smul_apply,innerSL_apply_apply,smul_eq_mul]
  have hi : ⟪y-c,c-y⟫= -R^2 := by
    rw [show c-y= -(y-c) by abel,inner_neg_right,real_inner_self_eq_norm_sq,hy]
  rw [hi]
  have hp : 0<2*α*Real.exp (-α*‖y-c‖^2)*R^2 := by positivity
  nlinarith

theorem planeFrameOperator_hopf (B : Plane → Fin 2 → Plane) (b : Plane → Plane)
    {u : Plane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (c : Plane) {R κ K : ℝ} (hR : 0<R) (hκ : 0<κ) (hK : 0≤K)
    (hcoeff : ∀ x,R/2≤‖x-c‖ → ‖x-c‖≤R →
      κ*‖x-c‖^2≤∑ i,⟪x-c,B x i⟫^2 ∧
        (∑ i,‖B x i‖^2)≤K ∧ ‖b x‖≤K)
    (hL : ∀ x,‖x-c‖<R → planeFrameOperator B b u x≤0)
    (hpos : ∀ x,‖x-c‖<R → 0<u x)
    {y : Plane} (hy : ‖y-c‖=R) (huy : u y=0) :
    0<fderiv ℝ u y (c-y) := by
  let r := R/2
  have hr : 0<r := half_pos hR
  have hrR : r<R := half_lt_self hR
  have hbound : ∀ x,‖x-c‖≤R → 0≤u x := by
    have hs : Metric.ball c R⊆{x | 0≤u x} := by
      intro x hx
      exact (hpos x (by simpa only [Metric.mem_ball,dist_eq_norm] using hx)).le
    have hc := closure_minimal hs (isClosed_le continuous_const hu.continuous)
    rw [closure_ball c hR.ne'] at hc
    intro x hx
    exact hc (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx)
  obtain ⟨z,hz,hzmin⟩ := (isCompact_closedBall c r).exists_isMinOn
    (Metric.nonempty_closedBall.mpr hr.le) hu.continuous.continuousOn
  have hzr : ‖z-c‖≤r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  let δ := u z
  have hδ : 0<δ := hpos z (hzr.trans_lt hrR)
  let α := (K*(1+R)+1)/(2*κ*r^2)
  have hα : 0<α := by dsimp [α]; positivity
  have hlarge : K*(1+R)<2*α*κ*r^2 := by
    have he : 2*α*κ*r^2=K*(1+R)+1 := by
      dsimp [α]; field_simp
    rw [he]; linarith
  let φ := planeHopfBarrier c α R
  have hφ := planeHopfBarrier_smooth c α R
  have hφle (x : Plane) : φ x≤1 := by
    have he : Real.exp (-α*‖x-c‖^2)≤1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα.le) (sq_nonneg _))
    dsimp [φ,planeHopfBarrier]
    linarith [Real.exp_pos (-α*R^2)]
  have hφzero (x : Plane) (hx : ‖x-c‖=R) : φ x=0 := by simp only [φ,planeHopfBarrier,hx,sub_self]
  have hcomp : ∀ x,r≤‖x-c‖ → ‖x-c‖≤R → 0≤u x-δ*φ x := by
    apply planeFrameOperator_annulus_comparison B b (hu.sub (contDiff_const.mul hφ)) c hr hrR
    · intro x hx
      change 0≤u x-δ*φ x
      rcases hx with hx|hx
      · have hzle : δ≤u x := hzmin (by simpa only [Metric.mem_closedBall,dist_eq_norm,hx] using (le_refl r))
        have hh := mul_le_mul_of_nonneg_left (hφle x) hδ.le
        nlinarith
      · rw [hφzero x hx,mul_zero,sub_zero]
        exact hbound x hx.le
    · intro x hrx hxR
      rw [planeFrameOperator_sub B b hu (contDiff_const.mul hφ),
        planeFrameOperator_smul B b hφ]
      have hc := hcoeff x hrx.le hxR.le
      have hbar := planeFrameOperator_barrier_pos B b c hr hκ hK hα hlarge
        hrx.le hxR.le hc.1 hc.2.1 hc.2.2
      exact sub_neg.mpr ((hL x hxR).trans_lt (mul_pos hδ hbar))
  let g : ℝ → ℝ := fun t => u (y+t • (c-y))-δ*φ (y+t • (c-y))
  have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
    (hu.sub (contDiff_const.mul hφ)).comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hg0 : g 0=0 := by simp only [g,zero_smul,add_zero,huy,hφzero y hy,mul_zero,sub_self]
  have hm : ∀ᶠ t in 𝓝[>] (0 : ℝ),g 0≤g t := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/2)).filter_mono nhdsWithin_le_nhds] with t ht hth
    have ht0 : 0<t := ht
    have hnorm : ‖y+t • (c-y)-c‖=(1-t)*R := by
      rw [show y+t • (c-y)-c=(1-t) • (y-c) by module,
        norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith),hy]
    rw [hg0]
    apply hcomp
    · rw [hnorm]; dsimp [r]; nlinarith
    · rw [hnorm]; nlinarith
  have hd := deriv_nonneg_of_right_min (hg.differentiable (by simp) 0).hasDerivAt hm
  have he : deriv g 0=fderiv ℝ u y (c-y)-δ*fderiv ℝ φ y (c-y) := by
    have hl := smooth_line_deriv (hu.sub ((contDiff_const (c := δ)).mul hφ)) y (c-y) 0
    change deriv g 0=_ at hl
    rw [hl]
    simp only [zero_smul,add_zero]
    rw [fderiv_fun_sub (hu.differentiable (by simp) y)
      ((contDiff_const.mul hφ).differentiable (by simp) y),
      fderiv_const_mul (hφ.differentiable (by simp) y)]
    simp [φ]

  rw [he] at hd
  exact (mul_pos hδ (planeHopfBarrier_inward c hα hR hy)).trans_le (sub_nonneg.mp hd)

end CubicTorus

end
end

end OAI
