import Mathlib
import OAI.Geometry.CubicTorus.Rigidity.LocalGraphSphere

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem Periodic.isMinimizerAt_power_affine_standard_ball {V : ℝ} (hV : V∈Ioo 0 (1/2))
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) {a b : ℝ}
    (he : ∀ᶠ W in 𝓝 V,isoperimetricProfile W^(3/2 : ℝ)=a*W+b) :
    V≤4*Real.pi/81 ∧ CongruentAE E (canonicalBall V) := by
  obtain ⟨c,r,hr,hr',hbd⟩ := isMinimizerAt_power_affine_spherical hV hE hmin hc he
  exact isMinimizerAt_spherical_standard_ball ⟨hV.1,hV.2.le⟩ hE hmin hr hr' hbd

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

abbrev SurfaceJet (μ : FiniteMeasure NormalBundle) :=
  Lp ℝ 2 (μ : Measure NormalBundle) × Lp Cover 2 (μ : Measure NormalBundle)

def surfaceMultiplier (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) :
    Lp ℝ 2 (μ : Measure NormalBundle) →L[ℝ] Lp ℝ 2 (μ : Measure NormalBundle) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ q • f
      map_add' := fun f g ↦ Lp.add_smul q f g
      map_smul' := fun c f ↦ (Lp.smul_comm c q f).symm }
    ‖q‖ (fun f ↦ Lp.norm_smul_le q f)

def surfaceJacobiB (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u v : SurfaceJet μ) : ℝ :=
  ⟪u.2,v.2⟫-⟪surfaceMultiplier μ q u.1,v.1⟫

lemma surfaceJacobiB_continuous (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) :
    Continuous (fun p : SurfaceJet μ × SurfaceJet μ ↦ surfaceJacobiB μ q p.1 p.2) := by
  unfold surfaceJacobiB
  fun_prop

lemma surfaceJacobiB_symm (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u v : SurfaceJet μ) :
    surfaceJacobiB μ q u v=surfaceJacobiB μ q v u := by
  have he : ⟪surfaceMultiplier μ q u.1,v.1⟫=⟪surfaceMultiplier μ q v.1,u.1⟫ := by
    rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_lpSMul (r := 2) q u.1,Lp.coeFn_lpSMul (r := 2) q v.1] with z hu hv
    change (q • u.1 : Lp ℝ 2 (μ : Measure NormalBundle)) z = _ at hu
    change (q • v.1 : Lp ℝ 2 (μ : Measure NormalBundle)) z = _ at hv
    change ⟪(q • u.1 : Lp ℝ 2 (μ : Measure NormalBundle)) z,v.1 z⟫ =
      ⟪(q • v.1 : Lp ℝ 2 (μ : Measure NormalBundle)) z,u.1 z⟫
    rw [hu,hv]
    simp only [smul_eq_mul,Pi.mul_apply,RCLike.inner_apply,RCLike.conj_to_real]
    ring
  unfold surfaceJacobiB
  rw [he,real_inner_comm u.2 v.2]

lemma surfaceJacobiB_add_left (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u v w : SurfaceJet μ) :
    surfaceJacobiB μ q (u+v) w=surfaceJacobiB μ q u w+surfaceJacobiB μ q v w := by
  simp only [surfaceJacobiB,Prod.fst_add,Prod.snd_add,map_add,inner_add_left]
  ring

lemma surfaceJacobiB_smul_left (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (c : ℝ) (u v : SurfaceJet μ) :
    surfaceJacobiB μ q (c • u) v=c*surfaceJacobiB μ q u v := by
  change ⟪c • u.2,v.2⟫-⟪surfaceMultiplier μ q (c • u.1),v.1⟫ =
    c*(⟪u.2,v.2⟫-⟪surfaceMultiplier μ q u.1,v.1⟫)
  simp only [map_smul,real_inner_smul_left]
  ring

theorem surfaceJacobi_zero_polarizes (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (S : Submodule ℝ (SurfaceJet μ))
    (hs : ∀ u∈S,0 ≤ surfaceJacobiB μ q u u)
    {u : SurfaceJet μ} (hu : u∈S) (hz : surfaceJacobiB μ q u u=0)
    {v : SurfaceJet μ} (hv : v∈S) : surfaceJacobiB μ q u v=0 := by
  have hquad (t : ℝ) : 0≤2*t*surfaceJacobiB μ q u v+t^2*surfaceJacobiB μ q v v := by
    have h := hs (u+t • v) (S.add_mem hu (S.smul_mem t hv))
    rw [surfaceJacobiB_add_left,surfaceJacobiB_smul_left,
      surfaceJacobiB_symm μ q u (u+t • v),surfaceJacobiB_add_left,
      surfaceJacobiB_smul_left,surfaceJacobiB_symm μ q v (u+t • v),
      surfaceJacobiB_add_left,surfaceJacobiB_smul_left,hz,
      surfaceJacobiB_symm μ q v u] at h
    nlinarith only [h]
  by_contra h
  let a := surfaceJacobiB μ q u v
  let b := surfaceJacobiB μ q v v
  have hb : 0≤b := hs v hv
  have hd : 0<b+1 := by linarith
  have hh := hquad (-a/(b+1))
  change 0≤2*(-a/(b+1))*a+(-a/(b+1))^2*b at hh
  have hh' := mul_nonneg hh (sq_nonneg (b+1))
  have he : (2*(-a/(b+1))*a+(-a/(b+1))^2*b)*(b+1)^2= -a^2*(b+2) := by
    field_simp [hd.ne']
    ring
  rw [he] at hh'
  have ha : 0<a^2 := sq_pos_of_ne_zero h
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def smoothPeriodicScalars : Submodule ℝ (Cover → ℝ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f ∧ ∀ m x,f (x+latticeVector m)=f x}
  zero_mem' := ⟨contDiff_const,by simp⟩
  add_mem' := by
    rintro f g ⟨hf,hfp⟩ ⟨hg,hgp⟩
    exact ⟨hf.add hg,fun m x ↦ by simp only [Pi.add_apply,hfp,hgp]⟩
  smul_mem' := by
    rintro c f ⟨hf,hfp⟩
    exact ⟨contDiff_const.smul hf,fun m x ↦ by simp only [Pi.smul_apply,hfp]⟩

def smoothScalarValue (f : smoothPeriodicScalars) : C(NormalBundle,ℝ) :=
  ⟨fun z ↦ f.val z.1,f.property.1.continuous.comp (continuous_subtype_val.comp continuous_fst)⟩

def smoothScalarGradient (f : smoothPeriodicScalars) : C(NormalBundle,Cover) :=
  ⟨fun z ↦ gradient f.val z.1-⟪(z.2 : Cover),gradient f.val z.1⟫ • (z.2 : Cover),by
    have hg : Continuous (fun z : NormalBundle ↦ gradient f.val z.1) :=
      (gradient_contDiff f.property.1).continuous.comp normalEmbedding_continuous.fst
    exact hg.sub (((continuous_subtype_val.comp continuous_snd).inner (𝕜 := ℝ) hg).smul
      (continuous_subtype_val.comp continuous_snd))⟩

lemma smoothScalarGradient_add (f g : smoothPeriodicScalars) :
    smoothScalarGradient (f+g)=smoothScalarGradient f+smoothScalarGradient g := by
  apply ContinuousMap.ext
  intro z
  have hg : gradient (f.val+g.val) z.1=gradient f.val z.1+gradient g.val z.1 := by
    simp only [gradient,fderiv_add (f.property.1.differentiable (by simp) _)
      (g.property.1.differentiable (by simp) _),map_add]
  change gradient (f.val+g.val) z.1-⟪(z.2 : Cover),gradient (f.val+g.val) z.1⟫ • (z.2 : Cover)=_
  rw [hg,inner_add_right,add_smul]
  change _=(gradient f.val z.1-⟪(z.2 : Cover),gradient f.val z.1⟫ • (z.2 : Cover))+
    (gradient g.val z.1-⟪(z.2 : Cover),gradient g.val z.1⟫ • (z.2 : Cover))
  abel

lemma smoothScalarGradient_smul (c : ℝ) (f : smoothPeriodicScalars) :
    smoothScalarGradient (c • f)=c • smoothScalarGradient f := by
  apply ContinuousMap.ext
  intro z
  have hg : gradient (c • f.val) z.1=c • gradient f.val z.1 := by
    simp only [gradient,fderiv_const_smul (f.property.1.differentiable (by simp) _) c,map_smul]
  change gradient (c • f.val) z.1-⟪(z.2 : Cover),gradient (c • f.val) z.1⟫ • (z.2 : Cover)=_
  rw [hg,real_inner_smul_right,mul_smul]
  change _=c • (gradient f.val z.1-⟪(z.2 : Cover),gradient f.val z.1⟫ • (z.2 : Cover))
  rw [smul_sub]

def surfaceSmoothJet (μ : FiniteMeasure NormalBundle) :
    smoothPeriodicScalars →ₗ[ℝ] SurfaceJet μ where
  toFun f := (ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ (smoothScalarValue f),
    ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ (smoothScalarGradient f))
  map_add' f g := by
    apply Prod.ext
    · change (ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ) (smoothScalarValue f+smoothScalarValue g)=_
      exact map_add (ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ) (smoothScalarValue f) (smoothScalarValue g)
    · change (ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ) (smoothScalarGradient (f+g))=_
      rw [smoothScalarGradient_add,map_add]
      rfl
  map_smul' c f := by
    apply Prod.ext
    · change (ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ) (c • smoothScalarValue f)=_
      exact map_smul (ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ) c (smoothScalarValue f)
    · change (ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ) (smoothScalarGradient (c • f))=_
      rw [smoothScalarGradient_smul,map_smul]
      rfl

def surfaceH1 (μ : FiniteMeasure NormalBundle) : Submodule ℝ (SurfaceJet μ) :=
  (surfaceSmoothJet μ).range.topologicalClosure

def surfaceCurvatureLp (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) : Lp ℝ ∞ (μ : Measure NormalBundle) :=
  ContinuousMap.toLp ∞ (μ : Measure NormalBundle) ℝ
    ⟨fun z ↦ coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1)),
      (normal_curvature_continuous hN).comp (continuous_subtype_val.comp continuous_fst)⟩

lemma surfaceSmoothJet_jacobi (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (f : smoothPeriodicScalars) :
    surfaceJacobiB μ (surfaceCurvatureLp μ N hN) (surfaceSmoothJet μ f) (surfaceSmoothJet μ f)=
      normalExtensionJacobi μ f.val N := by
  have hf := (smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hg := (smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hq := (show C(NormalBundle,ℝ) from ⟨_,
    (normal_curvature_continuous hN).comp (continuous_subtype_val.comp continuous_fst)⟩).coeFn_toLp
    (p := ∞) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hp := Lp.coeFn_lpSMul (r := 2) (surfaceCurvatureLp μ N hN) (surfaceSmoothJet μ f).1
  unfold surfaceJacobiB normalExtensionJacobi
  rw [L2.inner_def,L2.inner_def,← integral_sub
    (L2.integrable_inner (surfaceSmoothJet μ f).2 (surfaceSmoothJet μ f).2)
    (L2.integrable_inner (surfaceMultiplier μ (surfaceCurvatureLp μ N hN) (surfaceSmoothJet μ f).1)
      (surfaceSmoothJet μ f).1)]
  apply integral_congr_ae
  filter_upwards [hf,hg,hq,hp] with z hfz hgz hqz hpz
  change ((surfaceSmoothJet μ f).1) z=f.val z.1 at hfz
  change ((surfaceSmoothJet μ f).2) z=_ at hgz
  change (surfaceCurvatureLp μ N hN) z=_ at hqz
  change (surfaceMultiplier μ (surfaceCurvatureLp μ N hN) (surfaceSmoothJet μ f).1) z=_ at hpz
  rw [hpz]
  simp only [smul_eq_mul,Pi.mul_apply,hfz,hqz,hgz,
    real_inner_self_eq_norm_sq,RCLike.inner_apply,RCLike.conj_to_real]
  dsimp [smoothScalarGradient]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def smoothScalarOne : smoothPeriodicScalars := ⟨fun _ ↦ 1,contDiff_const,by simp⟩

def surfaceOne (μ : FiniteMeasure NormalBundle) : SurfaceJet μ :=
  surfaceSmoothJet μ smoothScalarOne

def surfaceMean (μ : FiniteMeasure NormalBundle) : SurfaceJet μ →L[ℝ] ℝ :=
  (innerSL ℝ (surfaceOne μ).1).comp (ContinuousLinearMap.fst ℝ _ _)

lemma surfaceMean_of_smooth (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars) :
    surfaceMean μ (surfaceSmoothJet μ f)=(∫ z,f.val z.1 ∂(μ : Measure NormalBundle)) := by
  change ⟪(ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ) (smoothScalarValue smoothScalarOne),
    (ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ) (smoothScalarValue f)⟫=_
  rw [ContinuousMap.inner_toLp]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change f.val z.1 * (starRingEnd ℝ) 1=f.val z.1
  simp

lemma surfaceMean_one (μ : FiniteMeasure NormalBundle) :
    surfaceMean μ (surfaceOne μ)=(μ : Measure NormalBundle).real univ := by
  rw [surfaceOne,surfaceMean_of_smooth]
  simp [smoothScalarOne,integral_const,smul_eq_mul]

lemma surfaceOne_mem (μ : FiniteMeasure NormalBundle) : surfaceOne μ∈surfaceH1 μ :=
  subset_closure (LinearMap.mem_range_self _ smoothScalarOne)

def surfaceCenter (μ : FiniteMeasure NormalBundle) (u : SurfaceJet μ) : SurfaceJet μ :=
  u-(surfaceMean μ u/(μ : Measure NormalBundle).real univ) • surfaceOne μ

lemma continuous_surfaceCenter (μ : FiniteMeasure NormalBundle) : Continuous (surfaceCenter μ) := by
  unfold surfaceCenter
  fun_prop

lemma surfaceMean_center (μ : FiniteMeasure NormalBundle)
    (hm : (μ : Measure NormalBundle).real univ≠0) (u : SurfaceJet μ) :
    surfaceMean μ (surfaceCenter μ u)=0 := by
  simp only [surfaceCenter,map_sub,map_smul,smul_eq_mul,surfaceMean_one]
  field_simp [hm]
  ring

lemma surfaceCenter_mem (μ : FiniteMeasure NormalBundle) {u : SurfaceJet μ}
    (hu : u∈surfaceH1 μ) : surfaceCenter μ u∈surfaceH1 μ :=
  (surfaceH1 μ).sub_mem hu ((surfaceH1 μ).smul_mem _ (surfaceOne_mem μ))

lemma surfaceCenter_of_smooth (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars) :
    surfaceCenter μ (surfaceSmoothJet μ f)=surfaceSmoothJet μ
      (f-(surfaceMean μ (surfaceSmoothJet μ f)/(μ : Measure NormalBundle).real univ) • smoothScalarOne) := by
  rw [map_sub,map_smul]
  rfl

lemma surfaceCenter_eq_self (μ : FiniteMeasure NormalBundle) {u : SurfaceJet μ}
    (hu : surfaceMean μ u=0) : surfaceCenter μ u=u := by simp [surfaceCenter,hu]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem surfaceH1_stability_of_smooth (μ : FiniteMeasure NormalBundle)
    (hm : (μ : Measure NormalBundle).real univ≠0)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hs : ∀ f : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) f →
      (∀ m x,f (x+latticeVector m)=f x) →
      (∫ z,f z.1 ∂(μ : Measure NormalBundle))=0 →
      0≤normalExtensionJacobi μ f N)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) (hz : surfaceMean μ u=0) :
    0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u := by
  let A : Set (SurfaceJet μ) := {v | 0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
    (surfaceCenter μ v) (surfaceCenter μ v)}
  have hc : Continuous (fun v : SurfaceJet μ ↦ surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceCenter μ v) (surfaceCenter μ v)) := by
    unfold surfaceJacobiB
    have hcenter := continuous_surfaceCenter μ
    exact (hcenter.snd.inner (𝕜 := ℝ) hcenter.snd).sub
      (((surfaceMultiplier μ (surfaceCurvatureLp μ N hN)).continuous.comp hcenter.fst).inner
        (𝕜 := ℝ) hcenter.fst)
  have hclosed : IsClosed A := isClosed_Ici.preimage hc
  have hrange : Set.range (surfaceSmoothJet μ)⊆A := by
    rintro _ ⟨f,rfl⟩
    change 0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceCenter μ (surfaceSmoothJet μ f)) (surfaceCenter μ (surfaceSmoothJet μ f))
    let g := f-(surfaceMean μ (surfaceSmoothJet μ f)/(μ : Measure NormalBundle).real univ) • smoothScalarOne
    have he : surfaceCenter μ (surfaceSmoothJet μ f)=surfaceSmoothJet μ g := surfaceCenter_of_smooth μ f
    rw [he,surfaceSmoothJet_jacobi]
    apply hs g.val g.property.1 g.property.2
    rw [← surfaceMean_of_smooth,← he,surfaceMean_center μ hm]
  have hmem : u∈closure (Set.range (surfaceSmoothJet μ)) := hu
  have hh := closure_minimal hrange hclosed hmem
  change 0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
    (surfaceCenter μ u) (surfaceCenter μ u) at hh
  rwa [surfaceCenter_eq_self μ hz] at hh

namespace Periodic

theorem isMinimizerAt_H1_trace_stability {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N),
      IsNormalMeasure E μ ∧ (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H ∧
          0≤coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))) ∧
      ∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
        0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u := by
  obtain ⟨μ,H,N,hμ,hN,hp,hae,hb,hs⟩ := isMinimizerAt_curvature_stability hV hE hmin
  have hm : (μ : Measure NormalBundle).real univ≠0 := by
    rw [Measure.real,← FiniteMeasure.ennreal_mass]
    change (μ.mass : ℝ)≠0
    rw [hμ.1]
    exact (ENNReal.toReal_pos (perimeter_pos_of_volume hV hmin.1.1 hmin.2.1).ne' hmin.1.2.ne).ne'
  exact ⟨μ,H,N,hN,hμ,hp,hae,hb,fun u hu hz ↦ surfaceH1_stability_of_smooth μ hm N hN hs hu hz⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def surfaceH1ZeroMean (μ : FiniteMeasure NormalBundle) : Submodule ℝ (SurfaceJet μ) :=
  surfaceH1 μ ⊓ (surfaceMean μ).ker

theorem surfaceH1_zero_mode_constant (μ : FiniteMeasure NormalBundle)
    (hm : (μ : Measure NormalBundle).real univ≠0)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle))
    (hs : ∀ w∈surfaceH1 μ,surfaceMean μ w=0 → 0 ≤ surfaceJacobiB μ q w w)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) (hmean : surfaceMean μ u=0)
    (hz : surfaceJacobiB μ q u u=0) :
    ∀ v∈surfaceH1 μ,surfaceJacobiB μ q u v=
      (surfaceJacobiB μ q u (surfaceOne μ)/(μ : Measure NormalBundle).real univ)*surfaceMean μ v := by
  intro v hv
  have hpoly : ∀ w∈surfaceH1ZeroMean μ,0 ≤ surfaceJacobiB μ q w w := by
    intro w hw
    exact hs w hw.1 hw.2
  have hu' : u∈surfaceH1ZeroMean μ := ⟨hu,hmean⟩
  have hw' : surfaceCenter μ v∈surfaceH1ZeroMean μ :=
    ⟨surfaceCenter_mem μ hv,surfaceMean_center μ hm v⟩
  have hp := surfaceJacobi_zero_polarizes μ q (surfaceH1ZeroMean μ) hpoly hu' hz hw'
  have he : v=surfaceCenter μ v+(surfaceMean μ v/(μ : Measure NormalBundle).real univ) • surfaceOne μ := by
    simp [surfaceCenter]
  rw [surfaceJacobiB_symm μ q u v,he,surfaceJacobiB_add_left,surfaceJacobiB_smul_left,
    surfaceJacobiB_symm μ q (surfaceCenter μ v) u,hp,
    surfaceJacobiB_symm μ q (surfaceOne μ) u,zero_add]
  rw [map_add,map_smul,surfaceMean_center μ hm,surfaceMean_one]
  simp only [zero_add,smul_eq_mul]
  field_simp [hm]

theorem surfaceH1_zero_mode_homogeneous (μ : FiniteMeasure NormalBundle)
    (hm : (μ : Measure NormalBundle).real univ≠0)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle))
    (hs : ∀ w∈surfaceH1 μ,surfaceMean μ w=0 → 0 ≤ surfaceJacobiB μ q w w)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) (hmean : surfaceMean μ u=0)
    (hz : surfaceJacobiB μ q u u=0)
    {v : SurfaceJet μ} (hv : v∈surfaceH1 μ) (hvmean : surfaceMean μ v≠0)
    (huv : surfaceJacobiB μ q u v=0) :
    ∀ w∈surfaceH1 μ,surfaceJacobiB μ q u w=0 := by
  have hc := surfaceH1_zero_mode_constant μ hm q hs hu hmean hz
  have hh := hc v hv
  rw [huv] at hh
  have hz' : surfaceJacobiB μ q u (surfaceOne μ)/(μ : Measure NormalBundle).real univ=0 :=
    (mul_eq_zero.mp hh.symm).resolve_right hvmean
  intro w hw
  rw [hc w hw,hz',zero_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_positive_patch_test {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {U : Set Torus} (hU : IsOpen U) (ha : (U∩frontier (openRepresentative E)).Nonempty) :
    ∃ f : smoothPeriodicScalars,0<surfaceMean μ (surfaceSmoothJet μ f) ∧
      ∀ x,quotientMap x∉U → ∀ᶠ y in 𝓝 x,f.val y=0 := by
  obtain ⟨a,haU,hab⟩ := ha
  obtain ⟨φ,hφ,hp,hb,⟨W,hW,haW,hone⟩,hzero⟩ := exists_periodic_local_cutoff a hU haU
  let f : smoothPeriodicScalars := ⟨φ,hφ,hp⟩
  refine ⟨f,?_,hzero⟩
  rw [surfaceMean_of_smooth]
  change 0<(∫ z,φ z.1 ∂(μ : Measure NormalBundle))
  by_contra! h
  have hz : (∫ z,φ z.1 ∂(μ : Measure NormalBundle))=0 :=
    le_antisymm h (integral_nonneg fun z ↦ (hb z.1).1)
  have hae := (integral_eq_zero_iff_of_nonneg (fun z : NormalBundle ↦ (hb z.1).1)
    (integrable_normal_base hφ.continuous μ)).mp hz
  have he := isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ hφ.continuous (continuous_const (y := (0 : ℝ))) hp
    (fun _ _ ↦ rfl) hae (representative a) (by simpa only [quotientMap_representative] using hab)
  have hh := (hone (representative a) (by simpa only [quotientMap_representative] using haW)).self_of_nhds
  change φ (representative a)=(0 : ℝ) at he
  linarith

lemma surfaceJacobiB_unused_patch (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) {u : SurfaceJet μ} {U : Set Torus}
    (hu : ∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U → u.1 z=0 ∧ u.2 z=0)
    (f : smoothPeriodicScalars)
    (hf : ∀ x,quotientMap x∉U → ∀ᶠ y in 𝓝 x,f.val y=0) :
    surfaceJacobiB μ q u (surfaceSmoothJet μ f)=0 := by
  have hfv := (smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hfg := (smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hqu := Lp.coeFn_lpSMul (r := 2) q u.1
  have hgrad : ⟪u.2,(surfaceSmoothJet μ f).2⟫=0 := by
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [hu,hfg] with z hz hgz
    by_cases hx : normalProjection z∈U
    · rw [(hz hx).2,inner_zero_left]
      rfl
    · change ((surfaceSmoothJet μ f).2) z=_ at hgz
      rw [hgz]
      have he : f.val=ᶠ[𝓝 (z.1 : Cover)]fun _ ↦ (0 : ℝ) := hf z.1 hx
      have hd := he.fderiv_eq (𝕜 := ℝ)
      have hg : gradient f.val z.1=0 := by simp [gradient,hd]
      change ⟪u.2 z,gradient f.val z.1-⟪(z.2 : Cover),gradient f.val z.1⟫ • (z.2 : Cover)⟫=0
      rw [hg]
      simp
  have hval : ⟪surfaceMultiplier μ q u.1,(surfaceSmoothJet μ f).1⟫=0 := by
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [hu,hfv,hqu] with z hz hvz hqz
    change (surfaceMultiplier μ q u.1) z=_ at hqz
    by_cases hx : normalProjection z∈U
    · rw [hqz]
      simp [(hz hx).1]
    · change ((surfaceSmoothJet μ f).1) z=f.val z.1 at hvz
      rw [hvz,(hf z.1 hx).self_of_nhds,inner_zero_right]
      rfl
  simp only [surfaceJacobiB,hgrad,hval,sub_self]

theorem isMinimizerAt_H1_unused_patch_homogeneous {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle))
    (hs : ∀ w∈surfaceH1 μ,surfaceMean μ w=0 → 0 ≤ surfaceJacobiB μ q w w)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) (hmean : surfaceMean μ u=0)
    (hz : surfaceJacobiB μ q u u=0) {U : Set Torus}
    (hU : IsOpen U) (ha : (U∩frontier (openRepresentative E)).Nonempty)
    (hzero : ∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U → u.1 z=0 ∧ u.2 z=0) :
    ∀ w∈surfaceH1 μ,surfaceJacobiB μ q u w=0 := by
  obtain ⟨f,hf,hfg⟩ := isMinimizerAt_positive_patch_test hV hE hmin hμ hU ha
  have hm : (μ : Measure NormalBundle).real univ≠0 := by
    rw [Measure.real,← FiniteMeasure.ennreal_mass]
    change (μ.mass : ℝ)≠0
    rw [hμ.1]
    exact (ENNReal.toReal_pos (perimeter_pos_of_volume hV hmin.1.1 hmin.2.1).ne' hmin.1.2.ne).ne'
  exact surfaceH1_zero_mode_homogeneous μ hm q hs hu hmean hz
    (subset_closure (LinearMap.mem_range_self _ f)) hf.ne'
    (surfaceJacobiB_unused_patch μ q hzero f hfg)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cover_gradient_mul {f g : Cover → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (x : Cover) :
    gradient (f*g) x=g x • gradient f x+f x • gradient g x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,inner_add_left,real_inner_smul_left,real_inner_smul_left,
    inner_gradient_left,inner_gradient_left]
  rw [fderiv_mul (hf x) (hg x)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

def smoothScalarMul (f g : smoothPeriodicScalars) : smoothPeriodicScalars :=
  ⟨f.val*g.val,f.property.1.mul g.property.1,fun m x ↦ by
    simp only [Pi.mul_apply,f.property.2,g.property.2]⟩

lemma smoothScalarGradient_mul (f g : smoothPeriodicScalars) (z : NormalBundle) :
    smoothScalarGradient (smoothScalarMul f g) z=
      g.val z.1 • smoothScalarGradient f z+f.val z.1 • smoothScalarGradient g z := by
  change gradient (f.val*g.val) z.1-⟪(z.2 : Cover),gradient (f.val*g.val) z.1⟫ • (z.2 : Cover)=_
  rw [cover_gradient_mul (f.property.1.differentiable (by simp)) (g.property.1.differentiable (by simp)),
    inner_add_right,real_inner_smul_right,real_inner_smul_right,add_smul]
  change _=g.val z.1 • (gradient f.val z.1-⟪(z.2 : Cover),gradient f.val z.1⟫ • (z.2 : Cover))+
    f.val z.1 • (gradient g.val z.1-⟪(z.2 : Cover),gradient g.val z.1⟫ • (z.2 : Cover))
  simp only [smul_sub,smul_smul]
  abel

lemma surfaceSmoothJet_bilinear (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (f g : smoothPeriodicScalars) :
    surfaceJacobiB μ (surfaceCurvatureLp μ N hN) (surfaceSmoothJet μ f) (surfaceSmoothJet μ g)=
      ∫ z,⟪smoothScalarGradient f z,smoothScalarGradient g z⟫-
        coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))*f.val z.1*g.val z.1
        ∂(μ : Measure NormalBundle) := by
  have hf := (smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hg := (smoothScalarValue g).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hdf := (smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hdg := (smoothScalarGradient g).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hq := (show C(NormalBundle,ℝ) from ⟨_,
    (normal_curvature_continuous hN).comp normalEmbedding_continuous.fst⟩).coeFn_toLp
    (p := ∞) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hp := Lp.coeFn_lpSMul (r := 2) (surfaceCurvatureLp μ N hN) (surfaceSmoothJet μ f).1
  unfold surfaceJacobiB
  rw [L2.inner_def,L2.inner_def,← integral_sub
    (L2.integrable_inner (surfaceSmoothJet μ f).2 (surfaceSmoothJet μ g).2)
    (L2.integrable_inner (surfaceMultiplier μ (surfaceCurvatureLp μ N hN) (surfaceSmoothJet μ f).1)
      (surfaceSmoothJet μ g).1)]
  apply integral_congr_ae
  filter_upwards [hf,hg,hdf,hdg,hq,hp] with z hfz hgz hdfz hdgz hqz hpz
  change (surfaceSmoothJet μ f).1 z=f.val z.1 at hfz
  change (surfaceSmoothJet μ g).1 z=g.val z.1 at hgz
  change (surfaceSmoothJet μ f).2 z=smoothScalarGradient f z at hdfz
  change (surfaceSmoothJet μ g).2 z=smoothScalarGradient g z at hdgz
  change (surfaceCurvatureLp μ N hN) z=coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1)) at hqz
  change (surfaceMultiplier μ (surfaceCurvatureLp μ N hN) (surfaceSmoothJet μ f).1) z=_ at hpz
  rw [hpz]
  simp only [smul_eq_mul,Pi.mul_apply] at *
  rw [hfz,hgz,hdfz,hdgz,hqz]
  simp only [RCLike.inner_apply,RCLike.conj_to_real]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graph_shape_metric_symmetric {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y v w : Plane) :
    ⟪fderiv ℝ (normalGraph n g) y (graphShapeOperator g y v),fderiv ℝ (normalGraph n g) y w⟫=
      ⟪fderiv ℝ (normalGraph n g) y v,fderiv ℝ (normalGraph n g) y (graphShapeOperator g y w)⟫ := by
  have he (v w : Plane) :
      ⟪fderiv ℝ (normalGraph n g) y (graphShapeOperator g y v),fderiv ℝ (normalGraph n g) y w⟫=
        (cmcWeight (gradient g y))⁻¹*⟪fderiv ℝ (gradient g) y v,w⟫ := by
    rw [normalGraph_metric hn hg]
    have h := graphInverseMetric_identity (gradient g y) (fderiv ℝ (gradient g) y v) w
    simp only [graphInverseMetric,smul_apply,real_inner_smul_left,
      real_inner_smul_right] at h
    change ⟪cmcJacobian (gradient g y) (fderiv ℝ (gradient g) y v),w⟫+
      ⟪gradient g y,cmcJacobian (gradient g y) (fderiv ℝ (gradient g) y v)⟫*⟪gradient g y,w⟫=_
    field_simp [(cmcWeight_pos (gradient g y)).ne']
    nlinarith only [h]
  rw [he]
  conv_rhs => rw [real_inner_comm,he]
  rw [plane_hessian_symmetric hg,real_inner_comm v]

theorem graph_normal_tangent_symmetric (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Plane)
    {σ : ℝ} (hσ : σ=1 ∨ σ= -1) {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hm : ∀ᶠ z in 𝓝 y,N (a+normalGraph n g z)=σ • graphSlopeNormal n (gradient g z))
    (v w : Cover) (hv : ⟪N (a+normalGraph n g y),v⟫=0)
    (hw : ⟪N (a+normalGraph n g y),w⟫=0) :
    ⟪fderiv ℝ N (a+normalGraph n g y) v,w⟫=
      ⟪v,fderiv ℝ N (a+normalGraph n g y) w⟫ := by
  have hnσ : σ≠0 := by rcases hσ with rfl|rfl <;> norm_num
  have hv' : ⟪graphSlopeNormal n (gradient g y),v⟫=0 := by
    rw [hm.self_of_nhds,real_inner_smul_left] at hv
    exact (mul_eq_zero.mp hv).resolve_left hnσ
  have hw' : ⟪graphSlopeNormal n (gradient g y),w⟫=0 := by
    rw [hm.self_of_nhds,real_inner_smul_left] at hw
    exact (mul_eq_zero.mp hw).resolve_left hnσ
  let q (v : Cover) := graphInverseMetric (gradient g y) (normalPlaneCoordinates n v+⟪n,v⟫ • gradient g y)
  have hj (v : Cover) (hv : ⟪graphSlopeNormal n (gradient g y),v⟫=0) :
      fderiv ℝ (normalGraph n g) y (q v)=v := by
    rw [normalGraph_fderiv_apply hg]
    dsimp [q]
    rw [graph_metric_projection hn,hv,zero_smul,sub_zero]
  have hΦ := (normalGraph_hasFDerivAt (n := n) (hg.differentiable (by simp) y)).differentiableAt.hasFDerivAt.const_add a
  have hGN : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ graphSlopeNormal n (gradient g z)) :=
    (graphSlopeNormal_contDiff hn).comp (plane_gradient_contDiff hg)
  have hm' : (fun z ↦ N (a+normalGraph n g z))=ᶠ[𝓝 y]
      (fun z ↦ σ • graphSlopeNormal n (gradient g z)) := hm
  have hd := hm'.fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (N ∘ fun z ↦ a+normalGraph n g z) y=
    fderiv ℝ (fun z ↦ σ • graphSlopeNormal n (gradient g z)) y at hd
  rw [((hN.differentiable (by simp) _).hasFDerivAt.comp y hΦ).fderiv,
    ] at hd
  change (fderiv ℝ N (a+normalGraph n g y)).comp (fderiv ℝ (normalGraph n g) y)=
    fderiv ℝ (σ • (fun z ↦ graphSlopeNormal n (gradient g z))) y at hd
  rw [fderiv_const_smul (hGN.differentiable (by simp) y)] at hd
  have hdv (r : Plane) : fderiv ℝ N (a+normalGraph n g y) (fderiv ℝ (normalGraph n g) y r)=
      σ • (-fderiv ℝ (normalGraph n g) y (graphShapeOperator g y r)) := by
    have h := congrArg (fun L : Plane →L[ℝ] Cover ↦ L r) hd
    simp only [ContinuousLinearMap.comp_apply,smul_apply] at h
    exact h.trans (congrArg (fun z : Cover ↦ σ • z) (graph_weingarten hn hg y r))
  calc
    _ = ⟪fderiv ℝ N (a+normalGraph n g y) (fderiv ℝ (normalGraph n g) y (q v)),
        fderiv ℝ (normalGraph n g) y (q w)⟫ := by rw [hj v hv',hj w hw']
    _ = ⟪fderiv ℝ (normalGraph n g) y (q v),
        fderiv ℝ N (a+normalGraph n g y) (fderiv ℝ (normalGraph n g) y (q w))⟫ := by
      rw [hdv,hdv]
      simp only [real_inner_smul_left,real_inner_smul_right,inner_neg_left,inner_neg_right]
      rw [graph_shape_metric_symmetric hn hg]
    _ = _ := by rw [hj v hv',hj w hw']

 theorem isMinimizerAt_shape_tangent_symmetric {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E))
    (v w : Cover) (hv : ⟪N x,v⟫=0) (hw : ⟪N x,w⟫=0) :
    ⟪fderiv ℝ N x v,w⟫=⟪v,fderiv ℝ N x w⟫ := by
  obtain ⟨n,f,σ,hn,hf,hf0,hσ,hm⟩ := isMinimizerAt_normal_geometry hV hE hmin hμ hN hp hae x hx
  have hx0 : x+normalGraph n f 0=x := by
    have hz : normalPlaneEmbedding n 0=0 := norm_eq_zero.mp (by rw [normalPlaneEmbedding_norm,norm_zero])
    simp [normalGraph,hf0,hz]
  simpa only [hx0] using graph_normal_tangent_symmetric x hn hf 0 hσ hN hm v w
    (by simpa only [hx0] using hv) (by simpa only [hx0] using hw)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normal_tangent_trace_norm {n : Cover} (hn : ‖n‖=1)
    (D : Cover →L[ℝ] Cover) (hD : ∀ v,⟪n,D v⟫=0)
    (hs : ∀ v w,⟪n,v⟫=0 → ⟪n,w⟫=0 → ⟪D v,w⟫=⟪v,D w⟫) :
    (∑ i : Fin 3,‖D.adjoint (EuclideanSpace.single i 1)-
      ⟪n,D.adjoint (EuclideanSpace.single i 1)⟫ • n‖^2)=coverTrace (D.comp D) := by
  let P : Cover →L[ℝ] Cover := ContinuousLinearMap.id ℝ Cover-(innerSL ℝ n).smulRight n
  have hP (v : Cover) : P v=v-⟪n,v⟫ • n := rfl
  have ht (v : Cover) : ⟪n,P v⟫=0 := by
    rw [hP,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one,sub_self]
  have hPs : P.adjoint=P := by
    apply ContinuousLinearMap.ext
    intro v
    apply ext_inner_right ℝ
    intro w
    rw [ContinuousLinearMap.adjoint_inner_left,hP,hP,
      inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,real_inner_comm n v]
    ring
  let K := D.comp P
  have hKs (v w : Cover) : ⟪K v,w⟫=⟪v,K w⟫ := by
    have h := hs (P v) (P w) (ht v) (ht w)
    dsimp [K]
    have he (v w : Cover) : ⟪D (P v),P w⟫=⟪D (P v),w⟫ := by
      rw [hP w,inner_sub_right,real_inner_smul_right,real_inner_comm n (D (P v)),hD,mul_zero,sub_zero]
    have he' (v w : Cover) : ⟪P v,D (P w)⟫=⟪v,D (P w)⟫ := by
      rw [hP,inner_sub_left,real_inner_smul_left,hD,mul_zero,sub_zero]
    exact (he _ _).symm.trans (h.trans (he' _ _))
  have hKa : K.adjoint=K := by
    apply ContinuousLinearMap.ext
    intro v
    apply ext_inner_right ℝ
    intro w
    rw [ContinuousLinearMap.adjoint_inner_left,hKs]
  have hK (v : Cover) : K v=P (D.adjoint v) := by
    conv_lhs => rw [← hKa]
    change (D.comp P).adjoint v=_
    rw [ContinuousLinearMap.adjoint_comp,hPs]
    rfl
  have htr : coverTrace (D.comp D)=coverTrace (K.comp K) := by
    apply normal_trace_square_invariance hn hD
    · intro v
      exact hD (P v)
    · intro v hv
      change D v=D (P v)
      rw [hP,hv,zero_smul,sub_zero]
  rw [htr]
  unfold coverTrace
  apply Finset.sum_congr rfl
  intro i _
  rw [← hP,← hK,← real_inner_self_eq_norm_sq]
  change ⟪K (EuclideanSpace.single i 1),K (EuclideanSpace.single i 1)⟫=
    K (K (EuclideanSpace.single i 1)) i
  rw [hKs]
  simp only [EuclideanSpace.inner_single_left,conj_trivial,one_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma gradient_normal_component {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (v x : Cover) :
    gradient (fun y ↦ ⟪v,N y⟫) x=(fderiv ℝ N x).adjoint v := by
  apply ext_inner_right ℝ
  intro w
  rw [inner_gradient_left,ContinuousLinearMap.adjoint_inner_left]
  have hd := ((innerSL ℝ v).hasFDerivAt.comp x
    (hN.differentiable (by simp) x).hasFDerivAt).fderiv
  change fderiv ℝ (fun y ↦ ⟪v,N y⟫) x=(innerSL ℝ v).comp (fderiv ℝ N x) at hd
  rw [hd]
  rfl

def normalComponentScalar (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) (i : Fin 3) : smoothPeriodicScalars :=
  ⟨fun x ↦ ⟪EuclideanSpace.single i 1,N x⟫,(contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Cover ↦ EuclideanSpace.single i (1 : ℝ))).inner ℝ hN,fun m x ↦ by dsimp; rw [hp]⟩

lemma normalComponentScalar_apply (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) (i : Fin 3) (x : Cover) :
    (normalComponentScalar N hN hp i).val x=N x i := by
  simp only [normalComponentScalar,EuclideanSpace.inner_single_left,conj_trivial,one_mul]

lemma normalComponentScalar_mean_zero {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (i : Fin 3) :
    surfaceMean μ (surfaceSmoothJet μ (normalComponentScalar N hN hp i))=0 := by
  let e : Cover := EuclideanSpace.single i 1
  have he : ‖e‖=1 := by simp [e]
  have hF : AdmissibleField (fun _ : Cover ↦ e) := ⟨contDiff_const,fun _ _ ↦ rfl,fun _ ↦ he.le⟩
  have hflux := hμ.2 _ hF
  have hd : divergence (fun _ : Cover ↦ e)=fun _ ↦ 0 := by funext x; simp [divergence]
  rw [hd,integral_zero] at hflux
  rw [surfaceMean_of_smooth,← hflux]
  apply integral_congr_ae
  filter_upwards [hae] with z hz
  change ⟪e,N z.1⟫=⟪(z.2 : Cover),e⟫
  rw [hz,real_inner_comm]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normalComponentScalar_energy_sum {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ∀ᶠ y in 𝓝 x,‖N y‖=1) :
    (∑ i : Fin 3,normalExtensionJacobi μ (normalComponentScalar N hN hp i).val N)=0 := by
  let f (i : Fin 3) := normalComponentScalar N hN hp i
  let J (i : Fin 3) (z : NormalBundle) :=
    ‖gradient (f i).val z.1-⟪(z.2 : Cover),gradient (f i).val z.1⟫ • (z.2 : Cover)‖^2-
      ((f i).val z.1)^2*coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))
  have hi (i : Fin 3) : Integrable (J i) (μ : Measure NormalBundle) := by
    have hg : Continuous (fun z : NormalBundle ↦ gradient (f i).val z.1) :=
      (gradient_contDiff (f i).property.1).continuous.comp normalEmbedding_continuous.fst
    have hfc : Continuous (fun z : NormalBundle ↦ (f i).val z.1) :=
      (f i).property.1.continuous.comp normalEmbedding_continuous.fst
    have hq := (normal_curvature_continuous hN).comp normalEmbedding_continuous.fst
    have hc : Continuous (J i) :=
      ((hg.sub ((continuous_normalUnit.inner (𝕜 := ℝ) hg).smul continuous_normalUnit)).norm.pow 2).sub
        ((hfc.pow 2).mul hq)
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hμU := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμU
  have he : ∀ᵐ z ∂(μ : Measure NormalBundle),(∑ i : Fin 3,J i z)=0 := by
    filter_upwards [hbd,hae] with z hz hzn
    have hunit := hu z.1 hz
    have hn : ‖N z.1‖=1 := hunit.self_of_nhds
    have hd := smooth_unit_normal_derivative (hN.differentiable (by simp) z.1) hunit
    have ht (v : Cover) : ⟪N z.1,fderiv ℝ N z.1 v⟫=0 := by
      rw [← ContinuousLinearMap.adjoint_inner_left,hd,inner_zero_left]
    have hs := isMinimizerAt_shape_tangent_symmetric hV hE hmin hμ hN hp hae z.1 hz
    have hsum := normal_tangent_trace_norm hn (fderiv ℝ N z.1) ht hs
    have hg (i : Fin 3) : gradient (f i).val z.1=(fderiv ℝ N z.1).adjoint (EuclideanSpace.single i 1) :=
      gradient_normal_component hN _ _
    have hv : (∑ i : Fin 3,((f i).val z.1)^2)=1 := by
      simp only [f,normalComponentScalar_apply,← EuclideanSpace.real_norm_sq_eq,hn,one_pow]
    dsimp [J]
    simp_rw [hg,← hzn]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,hsum,hv,one_mul,sub_self]
  change (∑ i : Fin 3,∫ z,J i z ∂(μ : Measure NormalBundle))=0
  rw [← integral_finsetSum _ (fun i _ ↦ hi i)]
  exact integral_eq_zero_of_ae he

end CubicTorus
end
end
end

end OAI
