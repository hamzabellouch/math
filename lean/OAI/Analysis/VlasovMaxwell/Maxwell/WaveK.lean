import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.BallCutoff

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma continuous_sphereSum {g : Vec → ℝ} (hg : Continuous g) : Continuous (sphereSum g) := by
  apply continuous_integral_sphere (F:=fun p : (ℝ × Vec) × Vec => g (p.1.2+p.1.1 • p.2))
  exact hg.comp ((continuous_snd.comp continuous_fst).add
    ((continuous_fst.comp continuous_fst).smul continuous_snd))

lemma sphereSum_radial_darboux_zero {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g)
    {R : ℝ} (hR : 0<R) :
    2*deriv (fun r => sphereSum g (r,0)) R +
      R*deriv (deriv (fun r => sphereSum g (r,0))) R =
      R*sphereSum (laplace g) (R,0) := by
  let F : ℝ → ℝ := fun r => sphereSum g (r,0)
  have hF : ContDiff ℝ ∞ F := (contDiff_sphereSum hg).comp (contDiff_id.prodMk contDiff_const)
  have hFd : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.mp hF).2
  let H : ℝ → ℝ := fun r => r^2*sphereSum (laplace g) (r,0)
  have hh : Continuous H := (continuous_id.pow 2).mul
    ((continuous_sphereSum (continuous_laplace hg)).comp (continuous_id.prodMk continuous_const))
  have he : (fun r => r^2*deriv F r) =ᶠ[𝓝 R] (fun r => ∫ s in 0..r, H s) := by
    filter_upwards [Ioi_mem_nhds hR] with r hr
    exact sphereSum_flux hg hr
  have hl := ((hasDerivAt_id R).pow 2).mul
    (hFd.differentiable (by simp) R).hasDerivAt
  have hr := intervalIntegral.integral_hasDerivAt_right (hh.intervalIntegrable 0 R)
    hh.stronglyMeasurable.stronglyMeasurableAtFilter hh.continuousAt
  have h := hl.unique (hr.congr_of_eventuallyEq he)
  dsimp only [H] at h
  norm_num at h
  change 2*deriv F R+R*deriv (deriv F) R=R*sphereSum (laplace g) (R,0)
  nlinarith

lemma sphereSum_radial_wave_zero {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g)
    {R : ℝ} (hR : 0<R) :
    deriv (deriv (fun r => r*sphereSum g (r,0))) R =
      R*sphereSum (laplace g) (R,0) := by
  let F : ℝ → ℝ := fun r => sphereSum g (r,0)
  have hF : ContDiff ℝ ∞ F := (contDiff_sphereSum hg).comp (contDiff_id.prodMk contDiff_const)
  have hFd : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.mp hF).2
  have hd : deriv (fun r => r*F r) = fun r => F r+r*deriv F r := by
    funext r
    change deriv (id * F) r = _
    convert ((hasDerivAt_id r).mul (hF.differentiable (by simp) r).hasDerivAt).deriv using 1; simp
  change deriv (deriv (fun r => r*F r)) R = _
  rw [hd]
  change deriv (F + id * deriv F) R = _
  rw [((hF.differentiable (by simp) R).hasDerivAt.add
    ((hasDerivAt_id R).mul (hFd.differentiable (by simp) R).hasDerivAt)).deriv]
  have h := sphereSum_radial_darboux_zero hg hR
  change 2*deriv F R+R*deriv (deriv F) R = _ at h
  dsimp only [id]
  nlinarith

lemma sphereSum_spatialPartial {g : Vec → ℝ} (hg : ContDiff ℝ 1 g)
    (r : ℝ) (x : Vec) (i : Fin 3) :
    spatialPartial (fun y => sphereSum g (r,y)) x i =
      sphereSum (fun y => spatialPartial g y i) (r,x) := by
  let F : Vec × Vec → ℝ := fun p => g (p.1+r • p.2)
  have hF : ContDiff ℝ 1 F := hg.comp (contDiff_fst.add (contDiff_snd.const_smul r))
  have hd := (hasFDerivAt_integral_sphere hF x).fderiv
  have hDa (n : Sphere) : ((fderiv ℝ F (x,n.1)).comp
      (ContinuousLinearMap.inl ℝ Vec Vec)) (basis i) =
      fderiv ℝ g (x+r • n.1) (basis i) := by
    have hi : HasFDerivAt (fun p : Vec × Vec => p.1+r • p.2)
        ((ContinuousLinearMap.fst ℝ Vec Vec)+r • ContinuousLinearMap.snd ℝ Vec Vec) (x,n.1) :=
      (hasFDerivAt_fst).add ((hasFDerivAt_snd).const_smul r)
    have he := ((hg.differentiable (by simp)) (x+r • n.1)).hasFDerivAt.comp (x,n.1) hi
    change HasFDerivAt F _ (x,n.1) at he
    rw [he.fderiv]
    simp
  have hc : Continuous (fun n : Sphere => (fderiv ℝ F (x,n.1)).comp
      (ContinuousLinearMap.inl ℝ Vec Vec)) :=
    ((hF.continuous_fderiv (by simp)).comp (continuous_const.prodMk continuous_subtype_val)).clm_comp continuous_const
  unfold spatialPartial sphereSum
  change (fderiv ℝ (fun y => ∫ n : Sphere, F (y,n.1) ∂sphereMeasure) x) (basis i) = _
  rw [hd,ContinuousLinearMap.integral_apply (hc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) (basis i)]
  apply integral_congr_ae
  exact ae_of_all _ hDa

lemma contDiff_spatialPartial {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x => spatialPartial g x i) :=
  ((contDiff_infty_iff_fderiv.mp hg).2).clm_apply contDiff_const

lemma gradient_apply (g : Vec → ℝ) (x : Vec) (i : Fin 3) :
    gradient g x i = spatialPartial g x i := by
  have h := inner_gradient_left (𝕜:=ℝ) (f:=g) (x:=x) (y:=basis i)
  rw [← dot_eq_inner] at h
  simpa [dot,basis,spatialPartial] using h

lemma laplace_eq_sum (g : Vec → ℝ) (x : Vec) :
    laplace g x = ∑ i : Fin 3, spatialPartial (fun y => spatialPartial g y i) x i := by
  simp only [laplace,divergence,gradient_apply]

lemma sphereSum_sum {ι : Type*} (s : Finset ι) {G : ι → Vec → ℝ}
    (hG : ∀ i ∈ s, Continuous (G i)) (p : ℝ × Vec) :
    sphereSum (fun x => ∑ i ∈ s, G i x) p = ∑ i ∈ s, sphereSum (G i) p := by
  unfold sphereSum
  apply integral_finsetSum
  intro i hi
  have h : Continuous (fun n : Sphere => G i (p.2+p.1 • n.1)) :=
    (hG i hi).comp (continuous_const.add (continuous_subtype_val.const_smul p.1))
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma sphereSum_spatial_laplace {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (r : ℝ) (x : Vec) :
    laplace (fun y => sphereSum g (r,y)) x = sphereSum (laplace g) (r,x) := by
  rw [laplace_eq_sum]
  have he : ∀ i, (fun y => spatialPartial (fun z => sphereSum g (r,z)) y i) =
      (fun y => sphereSum (fun z => spatialPartial g z i) (r,y)) := by
    intro i
    funext y
    exact sphereSum_spatialPartial (hg.of_le (by simp)) r y i
  calc
    _ = ∑ i : Fin 3, spatialPartial (fun y => sphereSum (fun z => spatialPartial g z i) (r,y)) x i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [he i]
    _ = ∑ i : Fin 3, sphereSum (fun y => spatialPartial (fun z => spatialPartial g z i) y i) (r,x) := by
      apply Finset.sum_congr rfl
      intro i _
      exact sphereSum_spatialPartial ((contDiff_spatialPartial hg i).of_le (by simp)) r x i
    _ = sphereSum (laplace g) (r,x) := by
      rw [← sphereSum_sum Finset.univ (fun i _ =>
        (contDiff_spatialPartial (contDiff_spatialPartial hg i) i).continuous)]
      congr 1
      funext y
      exact (laplace_eq_sum g y).symm

lemma spatialPartial_translate {g : Vec → ℝ} (hg : Differentiable ℝ g)
    (c x : Vec) (i : Fin 3) :
    spatialPartial (fun y => g (c+y)) x i = spatialPartial g (c+x) i := by
  have h := (hg (c+x)).hasFDerivAt.comp x
    ((hasFDerivAt_const c x).add (hasFDerivAt_id x))
  change HasFDerivAt (fun y => g (c+y)) _ x at h
  unfold spatialPartial
  rw [h.fderiv]
  simp

lemma laplace_translate {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (c x : Vec) :
    laplace (fun y => g (c+y)) x = laplace g (c+x) := by
  rw [laplace_eq_sum,laplace_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun y => spatialPartial (fun z => g (c+z)) y i) =
      fun y => spatialPartial g (c+y) i := by
    funext y
    exact spatialPartial_translate (hg.differentiable (by simp)) c y i
  rw [he]
  exact spatialPartial_translate ((contDiff_spatialPartial hg i).differentiable (by simp)) c x i

lemma sphereSum_radial_wave {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g)
    (x : Vec) {R : ℝ} (hR : 0<R) :
    deriv (deriv (fun r => r*sphereSum g (r,x))) R =
      R*sphereSum (laplace g) (R,x) := by
  have hs (r : ℝ) : sphereSum (fun y => g (x+y)) (r,0) = sphereSum g (r,x) := by
    simp only [sphereSum,zero_add]
  have hl (r : ℝ) : sphereSum (laplace (fun y => g (x+y))) (r,0) =
      sphereSum (laplace g) (r,x) := by
    simp only [sphereSum,laplace_translate hg,zero_add]
  have hx : ContDiff ℝ ∞ (fun y => g (x+y)) := hg.comp (contDiff_const.add contDiff_id)
  convert sphereSum_radial_wave_zero hx hR using 1
  · congr 2
    funext r
    rw [hs]
  · rw [hl]

lemma spatialPartial_const_mul {g : Vec → ℝ} (hg : Differentiable ℝ g)
    (c : ℝ) (x : Vec) (i : Fin 3) :
    spatialPartial (fun y => c*g y) x i = c*spatialPartial g x i := by
  unfold spatialPartial
  rw [((hg x).hasFDerivAt.const_mul c).fderiv]
  simp

lemma laplace_const_mul {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (c : ℝ) (x : Vec) :
    laplace (fun y => c*g y) x = c*laplace g x := by
  simp only [laplace_eq_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun y => spatialPartial (fun z => c*g z) y i) =
      fun y => c*spatialPartial g y i := by
    funext y
    exact spatialPartial_const_mul (hg.differentiable (by simp)) c y i
  rw [he,spatialPartial_const_mul ((contDiff_spatialPartial hg i).differentiable (by simp))]

lemma contDiff_laplace {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (laplace g) := by
  have he : laplace g = fun x => ∑ i : Fin 3, spatialPartial (fun y => spatialPartial g y i) x i :=
    funext (laplace_eq_sum g)
  rw [he]
  exact ContDiff.sum (fun i _ => contDiff_spatialPartial (contDiff_spatialPartial hg i) i)

lemma sphere_area : sphereMeasure.real univ = 4*Real.pi := by
  rw [sphereMeasure,Measure.toSphere_real_apply_univ]
  simp only [Vec,finrank_euclideanSpace,Measure.real,EuclideanSpace.volume_ball_fin_three,
    ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal (by positivity : 0≤Real.pi*4/3)]
  norm_num
  ring

def waveK (g : Vec → ℝ) (p : ℝ × Vec) : ℝ :=
  (4*Real.pi)⁻¹ * (p.1*sphereSum g p)

lemma contDiff_waveK {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (waveK g) :=
  contDiff_const.mul (contDiff_fst.mul (contDiff_sphereSum hg))

lemma waveK_zero (g : Vec → ℝ) (x : Vec) : waveK g (0,x)=0 := by simp [waveK]

lemma waveK_initial_velocity {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (x : Vec) :
    deriv (fun t => waveK g (t,x)) 0 = g x := by
  have hd := ((hasDerivAt_id (0:ℝ)).mul
    (sphereSum_radial_deriv (hg.of_le (by simp)) x 0)).const_mul ((4*Real.pi)⁻¹)
  change HasDerivAt (fun t => waveK g (t,x)) _ 0 at hd
  rw [hd.deriv]
  simp only [id_eq,one_mul,zero_mul,add_zero,sphereSum,zero_smul,add_zero,integral_const,
    smul_eq_mul,sphere_area]
  field_simp

lemma waveK_equation_pos {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (x : Vec)
    {t : ℝ} (ht : 0<t) :
    deriv (deriv (fun r => waveK g (r,x))) t = laplace (fun y => waveK g (t,y)) x := by
  have hF : ContDiff ℝ ∞ (fun r => r*sphereSum g (r,x)) :=
    contDiff_id.mul ((contDiff_sphereSum hg).comp (contDiff_id.prodMk contDiff_const))
  have he : deriv (fun r => waveK g (r,x)) =
      fun r => (4*Real.pi)⁻¹ * deriv (fun r => r*sphereSum g (r,x)) r := by
    funext r
    exact ((hF.differentiable (by simp) r).hasDerivAt.const_mul _).deriv
  rw [he]
  rw [(((contDiff_infty_iff_deriv.mp hF).2.differentiable (by simp) t).hasDerivAt.const_mul _).deriv]
  rw [sphereSum_radial_wave hg x ht]
  have hS : ContDiff ℝ ∞ (fun y => sphereSum g (t,y)) :=
    (contDiff_sphereSum hg).comp (contDiff_const.prodMk contDiff_id)
  change _ = laplace (fun y => (4*Real.pi)⁻¹ * (t*sphereSum g (t,y))) x
  rw [laplace_const_mul (contDiff_const.mul hS),laplace_const_mul hS,sphereSum_spatial_laplace hg]

lemma waveK_equation {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (x : Vec)
    {t : ℝ} (ht : 0≤t) :
    deriv (deriv (fun r => waveK g (r,x))) t = laplace (fun y => waveK g (t,y)) x := by
  have hF : ContDiff ℝ ∞ (fun r => waveK g (r,x)) :=
    (contDiff_waveK hg).comp (contDiff_id.prodMk contDiff_const)
  have hc : Continuous (deriv (deriv (fun r => waveK g (r,x)))) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hF).2).2.continuous
  have hr : Continuous (fun t => laplace (fun y => waveK g (t,y)) x) := by
    have he : (fun t => laplace (fun y => waveK g (t,y)) x) =
        fun t => (4*Real.pi)⁻¹ * (t*sphereSum (laplace g) (t,x)) := by
      funext t
      have hS : ContDiff ℝ ∞ (fun y => sphereSum g (t,y)) :=
        (contDiff_sphereSum hg).comp (contDiff_const.prodMk contDiff_id)
      change laplace (fun y => (4*Real.pi)⁻¹ * (t*sphereSum g (t,y))) x = _
      rw [laplace_const_mul (contDiff_const.mul hS),laplace_const_mul hS,sphereSum_spatial_laplace hg]
    rw [he]
    exact (continuous_id.mul ((continuous_sphereSum (continuous_laplace hg)).comp
      (continuous_id.prodMk continuous_const))).const_mul _
  have he : EqOn (deriv (deriv (fun r => waveK g (r,x))))
      (fun t => laplace (fun y => waveK g (t,y)) x) (Ioi 0) :=
    fun _ ht => waveK_equation_pos hg x ht
  exact he.closure hc hr (by simpa only [closure_Ioi,mem_Ici] using ht)
end RVM
end

end OAI
