import Mathlib
import OAI.Analysis.Conductivity.Variational.UnitSquarePoincare

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

lemma unitCubeAverage_add {f g : Box3 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    unitCubeAverage (fun z => f z+g z)=unitCubeAverage f+unitCubeAverage g := by
  dsimp [unitCubeAverage]
  have hh (y : ℝ×ℝ) := unitAverage_add (f := fun x => f (y,x)) (g := fun x => g (y,x))
    (hf.comp (continuous_const.prodMk continuous_id)) (hg.comp (continuous_const.prodMk continuous_id))
  simp_rw [hh]
  exact unitSquareAverage_add (continuous_unitAverage hf) (continuous_unitAverage hg)

lemma unitCubeAverage_mul (c : ℝ) (f : Box3 → ℝ) :
    unitCubeAverage (fun z => c*f z)=c*unitCubeAverage f := by
  simp only [unitCubeAverage,unitAverage_mul,unitSquareAverage_mul]

lemma unitCubeAverage_const (c : ℝ) : unitCubeAverage (fun _ => c)=c := by
  simp only [unitCubeAverage,unitAverage_const,unitSquareAverage_const]

lemma unitCubeAverage_mono {f g : Box3 → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ z : Box3, f z ≤ g z) : unitCubeAverage f ≤ unitCubeAverage g := by
  apply unitSquareAverage_mono (continuous_unitAverage hf) (continuous_unitAverage hg)
  intro y hy x hx
  apply unitAverage_mono (hf.comp (continuous_const.prodMk continuous_id))
    (hg.comp (continuous_const.prodMk continuous_id))
  intro t ht; exact h _

def boxRescale (a r : Box3) (z : Box3) : Box3 :=
  ((a.1.1+r.1.1*z.1.1,a.1.2+r.1.2*z.1.2),a.2+r.2*z.2)

def boxAverage (a r : Box3) (f : Box3 → ℝ) : ℝ :=
  unitCubeAverage (fun z => f (boxRescale a r z))

lemma boxRescale_smooth (a r : Box3) : ContDiff ℝ (↑(⊤ : ℕ∞)) (boxRescale a r) := by
  change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z : Box3 =>
    ((a.1.1+r.1.1*z.1.1,a.1.2+r.1.2*z.1.2),a.2+r.2*z.2))
  fun_prop

lemma boxRescale_fderiv (a r z v : Box3) :
    fderiv ℝ (boxRescale a r) z v=((r.1.1*v.1.1,r.1.2*v.1.2),r.2*v.2) := by
  let D : Box3 →L[ℝ] Box3 :=
    ((r.1.1 • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ×ℝ) ℝ)).prod
      (r.1.2 • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ×ℝ) ℝ))).prod
      (r.2 • ContinuousLinearMap.snd ℝ (ℝ×ℝ) ℝ)
  have he : boxRescale a r=fun z => a+D z := by rfl
  rw [he,fderiv_const_add,D.fderiv]
  rfl

lemma box_partial_one {f : Box3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a r z : Box3) :
    cubePartial (f ∘ boxRescale a r) ((1,0),0) z=
      r.1.1*cubePartial f ((1,0),0) (boxRescale a r z) := by
  rw [cubePartial,fderiv_comp z (hf.differentiable (by simp) _) ((boxRescale_smooth a r).differentiable (by simp) _)]
  change fderiv ℝ f (boxRescale a r z) (fderiv ℝ (boxRescale a r) z ((1,0),0)) = _
  rw [boxRescale_fderiv]
  have he : ((r.1.1*(1:ℝ),r.1.2*0),r.2*0)=r.1.1 • (((1,0),0) : Box3) := by simp
  rw [he,map_smul]
  rfl

lemma box_partial_two {f : Box3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a r z : Box3) :
    cubePartial (f ∘ boxRescale a r) ((0,1),0) z=
      r.1.2*cubePartial f ((0,1),0) (boxRescale a r z) := by
  rw [cubePartial,fderiv_comp z (hf.differentiable (by simp) _) ((boxRescale_smooth a r).differentiable (by simp) _)]
  change fderiv ℝ f (boxRescale a r z) (fderiv ℝ (boxRescale a r) z ((0,1),0)) = _
  rw [boxRescale_fderiv]
  have he : ((r.1.1*(0:ℝ),r.1.2*1),r.2*0)=r.1.2 • (((0,1),0) : Box3) := by simp
  rw [he,map_smul]
  rfl

lemma box_partial_three {f : Box3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a r z : Box3) :
    cubePartial (f ∘ boxRescale a r) ((0,0),1) z=
      r.2*cubePartial f ((0,0),1) (boxRescale a r z) := by
  rw [cubePartial,fderiv_comp z (hf.differentiable (by simp) _) ((boxRescale_smooth a r).differentiable (by simp) _)]
  change fderiv ℝ f (boxRescale a r z) (fderiv ℝ (boxRescale a r) z ((0,0),1)) = _
  rw [boxRescale_fderiv]
  have he : ((r.1.1*(0:ℝ),r.1.2*0),r.2*1)=r.2 • (((0,0),1) : Box3) := by simp
  rw [he,map_smul]
  rfl

theorem smooth_box_poincare {f : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a r : Box3) :
    boxAverage a r (fun z => (f z-boxAverage a r f)^2) ≤
      4*boxAverage a r (fun z =>
        r.1.1^2*(cubePartial f ((1,0),0) z)^2+
        r.1.2^2*(cubePartial f ((0,1),0) z)^2+
        r.2^2*(cubePartial f ((0,0),1) z)^2) := by
  have h := smooth_unit_cube_poincare (hf.comp (boxRescale_smooth a r))
  change unitCubeAverage (fun z => (f (boxRescale a r z)-boxAverage a r f)^2) ≤
    4*unitCubeAverage (fun z => _) at h
  simpa only [box_partial_one hf,box_partial_two hf,box_partial_three hf,mul_pow,boxAverage] using h

def closedBox (a r : Box3) : Set Box3 :=
  (Icc a.1.1 (a.1.1+r.1.1) ×ˢ Icc a.1.2 (a.1.2+r.1.2)) ×ˢ Icc a.2 (a.2+r.2)

lemma isCompact_closedBox (a r : Box3) : IsCompact (closedBox a r) :=
  (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc

lemma unitSquareAverage_eq_integral {f : ℝ×ℝ → ℝ} (hf : Continuous f) :
    unitSquareAverage f=∫ z in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, f z := by
  exact (setIntegral_prod f (hf.continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc))).symm

lemma unitCubeAverage_eq_integral {f : Box3 → ℝ} (hf : Continuous f) :
    unitCubeAverage f=∫ z in (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) ×ˢ Icc (0:ℝ) 1, f z := by
  rw [unitCubeAverage,unitSquareAverage_eq_integral (continuous_unitAverage hf)]
  exact (setIntegral_prod f (hf.continuousOn.integrableOn_compact
    ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc))).symm

lemma unitAverage_comp_affine (f : ℝ → ℝ) (a : ℝ) {r : ℝ} (hr : 0<r) :
    unitAverage (fun t => f (a+r*t))=r⁻¹*(∫ x in Icc a (a+r), f x) := by
  rw [unitAverage_eq_interval]
  have h := intervalIntegral.integral_comp_mul_add (a := 0) (b := 1) f hr.ne' a
  simp only [mul_zero,mul_one,zero_add,smul_eq_mul] at h
  rw [add_comm r a,intervalIntegral.integral_of_le (by linarith : a≤a+r),
    ← integral_Icc_eq_integral_Ioc] at h
  simpa only [add_comm a] using h

lemma box_volume_integral_iterated {f : Box3 → ℝ} (hf : Continuous f) (a r : Box3) :
    (∫ z in closedBox a r, f z)=
      ∫ x in Icc a.1.1 (a.1.1+r.1.1), ∫ y in Icc a.1.2 (a.1.2+r.1.2),
        ∫ t in Icc a.2 (a.2+r.2), f ((x,y),t) := by
  have hc : Continuous (fun p : ℝ×ℝ => ∫ t in Icc a.2 (a.2+r.2), f (p,t)) :=
    continuous_parametric_integral_of_continuous (f := fun p t => f (p,t)) hf isCompact_Icc
  calc
    _ = ∫ p in Icc a.1.1 (a.1.1+r.1.1) ×ˢ Icc a.1.2 (a.1.2+r.1.2),
        ∫ t in Icc a.2 (a.2+r.2), f (p,t) :=
      setIntegral_prod f (hf.continuousOn.integrableOn_compact (isCompact_closedBox a r))
    _ = _ := setIntegral_prod _ (hc.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc))

lemma boxAverage_eq_integral {f : Box3 → ℝ} (hf : Continuous f) (a r : Box3)
    (h₁ : 0<r.1.1) (h₂ : 0<r.1.2) (h₃ : 0<r.2) :
    boxAverage a r f=(r.1.1*r.1.2*r.2)⁻¹*(∫ z in closedBox a r, f z) := by
  have hx (v w : ℝ) := unitAverage_comp_affine
    (fun t => f ((a.1.1+r.1.1*v,a.1.2+r.1.2*w),t)) a.2 h₃
  have hy (v : ℝ) := unitAverage_comp_affine
    (fun w => ∫ t in Icc a.2 (a.2+r.2), f ((a.1.1+r.1.1*v,w),t)) a.1.2 h₂
  have hz := unitAverage_comp_affine
    (fun v => ∫ w in Icc a.1.2 (a.1.2+r.1.2),
      ∫ t in Icc a.2 (a.2+r.2), f ((v,w),t)) a.1.1 h₁
  simp only [boxAverage,unitCubeAverage,unitSquareAverage,boxRescale]
  simp_rw [hx,unitAverage_mul,hy,unitAverage_mul,hz]
  rw [box_volume_integral_iterated hf,mul_inv,mul_inv]
  ring

end ScalarConductivity

end

end OAI
