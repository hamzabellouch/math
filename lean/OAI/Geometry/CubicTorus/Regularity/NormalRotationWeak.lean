import Mathlib
import OAI.Geometry.CubicTorus.Curvature.SurfaceJacobiLocalization

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalTangentRotation_test_divergence {N : Cover → Cover} {φ : Cover → ℝ}
    {x : Cover} (hp : DifferentiableAt ℝ φ x) (hN : DifferentiableAt ℝ N x)
    (hn : ‖N x‖=1) (hD : ∀ v,⟪N x,fderiv ℝ N x v⟫=0)
    (hs : ∀ v w,⟪N x,v⟫=0 → ⟪N x,w⟫=0 →
      ⟪fderiv ℝ N x v,w⟫=⟪v,fderiv ℝ N x w⟫) :
    tangentialDivergence (fun y => φ y • normalTangentRotation N y) x (N x)=
      fderiv ℝ φ x (normalTangentRotation N x) := by
  have h₁ := (EuclideanSpace.proj 1 : Cover →L[ℝ] ℝ).hasFDerivAt.comp x hN.hasFDerivAt
  have h₂ := (EuclideanSpace.proj 2 : Cover →L[ℝ] ℝ).hasFDerivAt.comp x hN.hasFDerivAt
  change HasFDerivAt (fun y => N y 1) _ x at h₁
  change HasFDerivAt (fun y => N y 2) _ x at h₂
  have hd₁ := (hp.hasFDerivAt.mul h₁).fderiv
  have hd₂ := (hp.hasFDerivAt.mul h₂).fderiv
  change fderiv ℝ (fun y => φ y*N y 1) x=_ at hd₁
  change fderiv ℝ (fun y => φ y*N y 2) x=_ at hd₂
  have hm₁ : DifferentiableAt ℝ (fun y => φ y*N y 1) x := hp.mul h₁.differentiableAt
  have hm₂ : DifferentiableAt ℝ (fun y => φ y*N y 2) x := hp.mul h₂.differentiableAt
  have hc := tangent_shape_cross hn (fderiv ℝ N x) hD hs
  have he : (fun y => φ y • normalTangentRotation N y)=
      (fun y => (φ y*N y 2) • EuclideanSpace.single 1 1-
        (φ y*N y 1) • EuclideanSpace.single 2 1) := by
    funext y
    simp only [normalTangentRotation,smul_sub,smul_smul]
  rw [he,tangentialDivergence_sub_fields
    (hm₂.smul_const _) (hm₁.smul_const _),
    tangentialDivergence_smul_const hm₂,
    tangentialDivergence_smul_const hm₁,hd₂,hd₁]
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.comp_apply,smul_eq_mul]
  change φ x*((fderiv ℝ N x (tangentPart (N x) (EuclideanSpace.single 1 1))) 2)+
    N x 2*fderiv ℝ φ x (tangentPart (N x) (EuclideanSpace.single 1 1))-
    (φ x*((fderiv ℝ N x (tangentPart (N x) (EuclideanSpace.single 2 1))) 1)+
    N x 1*fderiv ℝ φ x (tangentPart (N x) (EuclideanSpace.single 2 1)))=
    fderiv ℝ φ x (normalTangentRotation N x)
  rw [hc]
  simp only [tangentPart,map_sub,map_smul,smul_eq_mul,normalTangentRotation,
    EuclideanSpace.inner_single_right,conj_trivial]
  ring

theorem isMinimizerAt_normalTangentRotation_weak_identity {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖N y‖=1) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (φ : smoothPeriodicScalars) :
    (∫ z,fderiv ℝ φ.val z.1 (normalTangentRotation N z.1)
      ∂(μ : Measure NormalBundle))=0 := by
  let F := fun y => φ.val y • normalTangentRotation N y
  have hW : ContDiff ℝ (⊤ : ℕ∞) (normalTangentRotation N) :=
    (((EuclideanSpace.proj 2 : Cover →L[ℝ] ℝ).contDiff.comp hN).smul contDiff_const).sub
      (((EuclideanSpace.proj 1 : Cover →L[ℝ] ℝ).contDiff.comp hN).smul contDiff_const)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := φ.property.1.smul hW
  have hFp : ∀ m x,F (x+latticeVector m)=F x := by
    intro m x
    simp only [F,normalTangentRotation,φ.property.2,hp]
  have hh := hCMC F hF hFp
  have hμU := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hm).symm
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμU
  have hzero : (∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ha] with z hz
    change ⟪(z.2 : Cover),φ.val z.1 • normalTangentRotation N z.1⟫=0
    rw [← hz,real_inner_smul_right,normalTangentRotation_orthogonal,mul_zero]
  rw [hzero,mul_zero] at hh
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [ha,hbd] with z hz hb
  rw [← hz]
  symm
  apply normalTangentRotation_test_divergence
    (φ.property.1.differentiable (by simp) _) (hN.differentiable (by simp) _)
    (hu z.1 hb).self_of_nhds
  · intro v
    rw [← ContinuousLinearMap.adjoint_inner_left,
      smooth_unit_normal_derivative (hN.differentiable (by simp) _) (hu z.1 hb),inner_zero_left]
  · exact isMinimizerAt_shape_tangent_symmetric hV hE hm hμ hN hp ha z.1 hb

theorem isMinimizerAt_exists_rotation_conservation {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (_ : ContDiff ℝ (⊤ : ℕ∞) N) (_ : ∀ m x,N (x+latticeVector m)=N x),
      IsNormalMeasure E μ ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        ∀ᶠ y in 𝓝 x,‖N y‖=1) ∧
      (∀ φ : smoothPeriodicScalars,
        (∫ z,fderiv ℝ φ.val z.1 (normalTangentRotation N z.1)
          ∂(μ : Measure NormalBundle))=0) := by
  obtain ⟨μ,H,N,hN,hp,hμ,ha,hu,hCMC,_,_⟩ :=
    Periodic.isMinimizerAt_full_jacobi_system hV hE hm
  refine ⟨μ,N,hN,hp,hμ,ha,(fun x hx => (hu x hx).1),?_⟩
  intro φ
  exact isMinimizerAt_normalTangentRotation_weak_identity hV hE hm hμ hN hp ha
    (fun x hx => (hu x hx).1) hCMC φ

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem surfaceSmoothJacobi_commutator (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (f u v : smoothPeriodicScalars)
    (hu : ∀ w∈surfaceH1 μ,surfaceJacobiB μ q (surfaceSmoothJet μ u) w=0) :
    surfaceJacobiB μ q (surfaceSmoothJet μ (smoothScalarMul f u)) (surfaceSmoothJet μ v)=
      ∫ z,u.val z.1*⟪smoothScalarGradient f z,smoothScalarGradient v z⟫-
        v.val z.1*⟪smoothScalarGradient u z,smoothScalarGradient f z⟫
        ∂(μ : Measure NormalBundle) := by
  have hh := surfaceH1_jacobi_cutoff_commutator μ q f hu
    (show surfaceSmoothJet μ v∈surfaceH1 μ from subset_closure ⟨v,rfl⟩)
  rw [surfaceCutoffJet_smooth] at hh
  rw [hh,L2.inner_def,L2.inner_def,← integral_sub
    (L2.integrable_inner (surfaceCutoffError μ f (surfaceSmoothJet μ u)) (surfaceSmoothJet μ v).2)
    (L2.integrable_inner (surfaceSmoothJet μ u).2 (surfaceCutoffError μ f (surfaceSmoothJet μ v)))]
  apply integral_congr_ae
  filter_upwards [surfaceCutoffError_ae μ f (surfaceSmoothJet μ u),
    surfaceCutoffError_ae μ f (surfaceSmoothJet μ v),
    (smoothScalarValue u).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle),
    (smoothScalarValue v).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle),
    (smoothScalarGradient u).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle),
    (smoothScalarGradient v).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)]
      with z heu hev hu hv hdu hdv
  change (surfaceSmoothJet μ u).1 z=u.val z.1 at hu
  change (surfaceSmoothJet μ v).1 z=v.val z.1 at hv
  change (surfaceSmoothJet μ u).2 z=smoothScalarGradient u z at hdu
  change (surfaceSmoothJet μ v).2 z=smoothScalarGradient v z at hdv
  rw [heu,hev,hu,hv,hdu,hdv,real_inner_smul_left,real_inner_smul_right]

lemma smoothScalarGradient_of_coordinate_germ (f : smoothPeriodicScalars)
    (z : NormalBundle) (j : Fin 3) (b : ℝ)
    (he : f.val =ᶠ[𝓝 (z.1 : Cover)] (fun y => y j-b)) :
    smoothScalarGradient f z=tangentPart (z.2 : Cover) (EuclideanSpace.single j 1) := by
  have hd : HasFDerivAt (fun y : Cover => y j-b) (EuclideanSpace.proj j : Cover →L[ℝ] ℝ) z.1 := by
    simpa using (EuclideanSpace.proj j : Cover →L[ℝ] ℝ).hasFDerivAt.sub_const b
  have hg : gradient f.val z.1=EuclideanSpace.single j 1 := by
    apply ext_inner_right ℝ
    intro w
    rw [inner_gradient_left,he.fderiv_eq,hd.fderiv]
    simp only [EuclideanSpace.inner_single_left,conj_trivial,one_mul]
    rfl
  change tangentPart (z.2 : Cover) (gradient f.val z.1)=_
  rw [hg]

lemma smoothScalarGradient_inner_tangent (f : smoothPeriodicScalars)
    (z : NormalBundle) (w : Cover) :
    ⟪smoothScalarGradient f z,tangentPart (z.2 : Cover) w⟫=
      fderiv ℝ f.val z.1 (tangentPart (z.2 : Cover) w) := by
  change ⟪gradient f.val z.1-⟪(z.2 : Cover),gradient f.val z.1⟫ • (z.2 : Cover),
    tangentPart (z.2 : Cover) w⟫=_
  rw [inner_sub_left,real_inner_smul_left]
  have hz : ⟪(z.2 : Cover),tangentPart (z.2 : Cover) w⟫=0 := by
    simp only [tangentPart,inner_sub_right,real_inner_smul_right,
      real_inner_self_eq_norm_sq,z.2.property,one_pow,mul_one,sub_self]
  rw [hz,mul_zero,sub_zero,inner_gradient_left]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma rotation_commutator_density {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (f₁ f₂ φ : smoothPeriodicScalars) (z : NormalBundle)
    (ha : N z.1=(z.2 : Cover))
    (hD : ∀ v,⟪N z.1,fderiv ℝ N z.1 v⟫=0)
    (hs : ∀ v w,⟪N z.1,v⟫=0 → ⟪N z.1,w⟫=0 →
      ⟪fderiv ℝ N z.1 v,w⟫=⟪v,fderiv ℝ N z.1 w⟫)
    (b₁ b₂ : ℝ)
    (he₁ : f₁.val =ᶠ[𝓝 (z.1 : Cover)] (fun y => y 1-b₁))
    (he₂ : f₂.val =ᶠ[𝓝 (z.1 : Cover)] (fun y => y 2-b₂)) :
    N z.1 2*⟪smoothScalarGradient f₁ z,smoothScalarGradient φ z⟫-
      φ.val z.1*⟪smoothScalarGradient (normalComponentScalar N hN hp 2) z,smoothScalarGradient f₁ z⟫-
      (N z.1 1*⟪smoothScalarGradient f₂ z,smoothScalarGradient φ z⟫-
      φ.val z.1*⟪smoothScalarGradient (normalComponentScalar N hN hp 1) z,smoothScalarGradient f₂ z⟫)=
      fderiv ℝ φ.val z.1 (normalTangentRotation N z.1) := by
  rw [smoothScalarGradient_of_coordinate_germ f₁ z 1 b₁ he₁,
    smoothScalarGradient_of_coordinate_germ f₂ z 2 b₂ he₂]
  rw [real_inner_comm (smoothScalarGradient φ z) (tangentPart (z.2 : Cover) (EuclideanSpace.single 1 1)),
    real_inner_comm (smoothScalarGradient φ z) (tangentPart (z.2 : Cover) (EuclideanSpace.single 2 1))]
  simp only [smoothScalarGradient_inner_tangent]
  have hd₁ := (EuclideanSpace.proj 1 : Cover →L[ℝ] ℝ).hasFDerivAt.comp (z.1 : Cover)
    (hN.differentiable (by simp) z.1).hasFDerivAt
  have hd₂ := (EuclideanSpace.proj 2 : Cover →L[ℝ] ℝ).hasFDerivAt.comp (z.1 : Cover)
    (hN.differentiable (by simp) z.1).hasFDerivAt
  change HasFDerivAt (fun y => N y 1)
    ((EuclideanSpace.proj 1 : Cover →L[ℝ] ℝ).comp (fderiv ℝ N z.1)) (z.1 : Cover) at hd₁
  change HasFDerivAt (fun y => N y 2)
    ((EuclideanSpace.proj 2 : Cover →L[ℝ] ℝ).comp (fderiv ℝ N z.1)) (z.1 : Cover) at hd₂
  have hv₁ : (normalComponentScalar N hN hp 1).val=(fun y => N y 1) :=
    funext fun y => normalComponentScalar_apply N hN hp 1 y
  have hv₂ : (normalComponentScalar N hN hp 2).val=(fun y => N y 2) :=
    funext fun y => normalComponentScalar_apply N hN hp 2 y
  rw [hv₁,hv₂,hd₁.fderiv,hd₂.fderiv,← ha]
  change N z.1 2*fderiv ℝ φ.val z.1 (tangentPart (N z.1) (EuclideanSpace.single 1 1))-
    φ.val z.1*((fderiv ℝ N z.1 (tangentPart (N z.1) (EuclideanSpace.single 1 1))) 2)-
    (N z.1 1*fderiv ℝ φ.val z.1 (tangentPart (N z.1) (EuclideanSpace.single 2 1))-
    φ.val z.1*((fderiv ℝ N z.1 (tangentPart (N z.1) (EuclideanSpace.single 2 1))) 1))=_
  rw [tangent_shape_cross (by rw [ha]; exact z.2.property) (fderiv ℝ N z.1) hD hs]
  simp only [tangentPart,normalTangentRotation,map_sub,map_smul,smul_eq_mul,
    EuclideanSpace.inner_single_right,conj_trivial]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceJacobiB_sub_left (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u v w : SurfaceJet μ) :
    surfaceJacobiB μ q (u-v) w=surfaceJacobiB μ q u w-surfaceJacobiB μ q v w := by
  simp only [surfaceJacobiB,Prod.fst_sub,Prod.snd_sub,map_sub,inner_sub_left]
  ring

lemma smoothJacobi_commutator_integrable (μ : FiniteMeasure NormalBundle)
    (f u v : smoothPeriodicScalars) :
    Integrable (fun z : NormalBundle =>
      u.val z.1*⟪smoothScalarGradient f z,smoothScalarGradient v z⟫-
      v.val z.1*⟪smoothScalarGradient u z,smoothScalarGradient f z⟫)
      (μ : Measure NormalBundle) := by
  exact (((smoothScalarValue u).continuous.mul
    ((smoothScalarGradient f).continuous.inner (𝕜 := ℝ) (smoothScalarGradient v).continuous)).sub
    ((smoothScalarValue v).continuous.mul
      ((smoothScalarGradient u).continuous.inner (𝕜 := ℝ) (smoothScalarGradient f).continuous))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

attribute [local irreducible] surfaceSmoothJet surfaceCurvatureLp surfaceJacobiB

theorem isMinimizerAt_rotation_jacobi_from_germs {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖N y‖=1) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (hj : ∀ i : Fin 3,∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (normalComponentScalar N hN hp i)) w=0)
    (f₁ f₂ : smoothPeriodicScalars)
    (he : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ∃ b₁ b₂ : ℝ,
      (f₁.val =ᶠ[𝓝 x] (fun y => y 1-b₁)) ∧
      (f₂.val =ᶠ[𝓝 x] (fun y => y 2-b₂))) :
    ∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ
        (smoothScalarMul f₁ (normalComponentScalar N hN hp 2)-
          smoothScalarMul f₂ (normalComponentScalar N hN hp 1))) w=0 := by
  let U := surfaceSmoothJet μ
    (smoothScalarMul f₁ (normalComponentScalar N hN hp 2)-
      smoothScalarMul f₂ (normalComponentScalar N hN hp 1))
  have hμU := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hm).symm
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμU
  have htest (φ : smoothPeriodicScalars) :
      surfaceJacobiB μ (surfaceCurvatureLp μ N hN) U (surfaceSmoothJet μ φ)=0 := by
    dsimp only [U]
    rw [map_sub (surfaceSmoothJet μ)
      (smoothScalarMul f₁ (normalComponentScalar N hN hp 2))
      (smoothScalarMul f₂ (normalComponentScalar N hN hp 1)),
      surfaceJacobiB_sub_left,
      surfaceSmoothJacobi_commutator μ (surfaceCurvatureLp μ N hN) f₁
        (normalComponentScalar N hN hp 2) φ (hj 2),
      surfaceSmoothJacobi_commutator μ (surfaceCurvatureLp μ N hN) f₂
        (normalComponentScalar N hN hp 1) φ (hj 1),
      ← integral_sub (smoothJacobi_commutator_integrable μ f₁ (normalComponentScalar N hN hp 2) φ)
        (smoothJacobi_commutator_integrable μ f₂ (normalComponentScalar N hN hp 1) φ)]
    rw [← isMinimizerAt_normalTangentRotation_weak_identity hV hE hm hμ hN hp ha hu hCMC φ]
    apply integral_congr_ae
    filter_upwards [ha,hbd] with z haz hb
    obtain ⟨b₁,b₂,he₁,he₂⟩ := he z.1 hb
    have hdz : ∀ v,⟪N z.1,fderiv ℝ N z.1 v⟫=0 := by
      intro v
      rw [← ContinuousLinearMap.adjoint_inner_left,
        smooth_unit_normal_derivative (hN.differentiable (by simp) _) (hu z.1 hb),inner_zero_left]
    have hsz := isMinimizerAt_shape_tangent_symmetric hV hE hm hμ hN hp ha z.1 hb
    simpa only [normalComponentScalar_apply] using
      rotation_commutator_density hN hp f₁ f₂ φ z haz hdz hsz b₁ b₂ he₁ he₂
  have hc : IsClosed {w : SurfaceJet μ | surfaceJacobiB μ (surfaceCurvatureLp μ N hN) U w=0} :=
    isClosed_eq ((surfaceJacobiB_continuous μ _).comp
      (continuous_const.prodMk continuous_id)) continuous_const
  intro w hw
  apply closure_minimal (s := Set.range (surfaceSmoothJet μ)) _ hc hw
  rintro _ ⟨φ,rfl⟩
  exact htest φ

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma periodicRotationNormalScalar_eq (g : ℝ → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hp : Function.Periodic g 1)
    (c : Cover) (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hNp : ∀ m x,N (x+latticeVector m)=N x) :
    periodicRotationNormalScalar g hg hp c N hN hNp =
      smoothScalarMul (periodicCoordinate g hg hp c 1) (normalComponentScalar N hN hNp 2)-
        smoothScalarMul (periodicCoordinate g hg hp c 2) (normalComponentScalar N hN hNp 1) := by
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_sub,Pi.sub_apply,smoothScalarMul,Pi.mul_apply,
    normalComponentScalar_apply,periodicRotationNormalScalar,periodicRotation]
  change ⟪N x, (periodicCoordinate g hg hp c 1).val x • EuclideanSpace.single 2 1-
    (periodicCoordinate g hg hp c 2).val x • EuclideanSpace.single 1 1⟫ =
    (periodicCoordinate g hg hp c 1).val x * (N x 2)-
    (periodicCoordinate g hg hp c 2).val x * (N x 1)
  simp only [inner_sub_right,real_inner_smul_right,EuclideanSpace.inner_single_right,
    conj_trivial,one_mul]

theorem TrueRadialTube.exists_rotation_jacobi {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {c : Cover} {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r) :
    ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hNp : ∀ m x,N (x+latticeVector m)=N x)
      (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hp : Function.Periodic g 1),
      IsNormalMeasure E μ ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        ∀ᶠ y in 𝓝 x,‖N y‖=1) ∧
      (∀ p,(g =ᶠ[𝓝 (r p • unitAngle p.2).re] id) ∧
        (g =ᶠ[𝓝 (r p • unitAngle p.2).im] id)) ∧
      surfaceMean μ (surfaceSmoothJet μ (periodicRotationNormalScalar g hg hp c N hN hNp))=0 ∧
      (∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
        (surfaceSmoothJet μ (periodicRotationNormalScalar g hg hp c N hN hNp)) w=0) ∧
      (∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
        0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u) := by
  obtain ⟨μ,H,N,hN,hNp,hμ,ha,hu,hCMC,hs,hj⟩ := Periodic.isMinimizerAt_full_jacobi_system hV hE hm
  obtain ⟨g,hg,hp,he⟩ := hr.periodic_transverse_germs
  refine ⟨μ,N,hN,hNp,g,hg,hp,hμ,ha,(fun x hx => (hu x hx).1),he,
    periodicRotationNormalScalar_mean_zero hμ g hg hp c N hN hNp ha,?_,hs⟩
  rw [periodicRotationNormalScalar_eq]
  apply isMinimizerAt_rotation_jacobi_from_germs hV hE hm hμ hN hNp ha
    (fun x hx => (hu x hx).1) hCMC hj
  intro x hx
  rw [← hr.boundary_range] at hx
  obtain ⟨p,hpx⟩ := hx
  obtain ⟨m,hm⟩ := same_quotient_lattice hpx.symm
  have h₁ : x 1-c 1-(m 1 : ℝ)=(r p • unitAngle p.2).re := by
    rw [hm]
    simp [latticeVector]
    ring
  have h₂ : x 2-c 2-(m 2 : ℝ)=(r p • unitAngle p.2).im := by
    rw [hm]
    simp [latticeVector]
    ring
  refine ⟨c 1+(m 1 : ℝ),c 2+(m 2 : ℝ),?_,?_⟩
  · simpa only [sub_add_eq_sub_sub] using
      periodicCoordinate_germ g hg hp c 1 x (m 1) (by rw [h₁]; exact (he p).1)
  · simpa only [sub_add_eq_sub_sub] using
      periodicCoordinate_germ g hg hp c 2 x (m 2) (by rw [h₂]; exact (he p).2)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem PlaneWeakGradientOn.jacobi_equationNear
    {p : Plane → Plane} (hp : Continuous p) (hpb : ∀ y, ‖p y‖ ≤ 1)
    {R α D : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α ≤ 1) (hD : 0 ≤ D)
    (hHolder : ∀ x ∈ Metric.ball (0 : Plane) R, ∀ y ∈ Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x) - cmcJacobian (p y)‖ ≤ D * (dist x y)^α)
    (hpc : ContDiffAt ℝ (⊤ : ℕ∞) p 0)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hpe : ∀ y ∈ Metric.ball (0 : Plane) R, p y = gradient g y)
    (hlin : ∀ i : Fin 2, LinearCMCEquation
      (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g)
      (fun _ => 0) (Metric.ball 0 R))
    {u : Lp ℝ 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    {G : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    (hw : PlaneWeakGradientOn (Metric.ball 0 R) u G)
    (hJ : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 R →
      (∫ y in Metric.ball (0 : Plane) R, (cmcWeight (gradient g y))^2 *
        ⟪G y, cmcJacobian (gradient g y) (gradient ψ y)⟫ -
        cmcWeight (gradient g y) * graphSquaredSecondFundamentalForm g y * u y * ψ y) = 0)
    {f : Plane → ℝ} (hf : ContinuousOn f (Metric.ball 0 R))
    (hfu : f =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)] (u : Plane → ℝ)) :
    LinearCMCEquationNear (fun y => cmcWeight (gradient g y)*f y)
      (gradient g) (fun _ => 0) := by
  let q : Plane → ℝ := fun y => cmcWeight (gradient g y)
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := cmcWeight_contDiff.comp (plane_gradient_contDiff hg)
  obtain ⟨v,J,hv,hJv,hwJ⟩ := hw.weighted_L2 hq
  have hde := weak_cmc_graph_jacobi_linearization Metric.isOpen_ball hw hg hlin hJ
  have hd : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 R →
        (∫ y, fderiv ℝ ψ y (cmcJacobian (p y) (J y))) = 0 := by
    intro ψ hψ hc hs
    rw [← hde ψ hψ hc hs]
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hJv] with y hy
    by_cases hys : y ∈ Metric.ball (0 : Plane) R
    · rw [hy hys, hpe y hys]
    · rw [fderiv_of_notMem_tsupport ℝ (fun hh => hys (hs hh))]
      rfl
  have hvf : (fun y => q y * f y) =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)]
      (v : Plane → ℝ) := by
    filter_upwards [hv,hfu] with y hyv hyf
    rw [hyv,hyf]
  have hpContinuous : Continuous p := continuous_iff_continuousAt.mpr fun point => by
    rcases eq_or_ne point 0 with rfl | _
    · exact hpc.continuousAt
    · exact hp.continuousAt
  have heq := (hwJ.cmc_classical_near hpContinuous hpb hR hα hα1 hD hHolder hd
    (hq.continuous.continuousOn.mul hf) hvf).2
  apply heq.congr (Filter.EventuallyEq.rfl) ?_ (Filter.EventuallyEq.rfl)
  filter_upwards [Metric.ball_mem_nhds (0 : Plane) hR] with y hy
  exact (hpe y hy).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem surfaceH1_jacobi_graph_equationNear
    (μ : FiniteMeasure NormalBundle) (q : Lp ℝ ∞ (μ : Measure NormalBundle))
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ, surfaceJacobiB μ q u z=0)
    (a : Cover) {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ} {K : ℝ≥0}
    (hgL : LipschitzWith K g) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {φ : Cover → ℝ} (hφ : Measurable φ) (hφb : ∀ x, φ x∈Icc 0 1)
    (hφO : tsupport φ ⊆ {x | ∀ i, 0<x i ∧ x i<1})
    (hm : (μ : Measure NormalBundle).withDensity (fun z => ENNReal.ofReal (φ z.1)) =
      Measure.map (actualNormalGraphChart a hn g)
        (volume.withDensity (fun y => ENNReal.ofReal
          (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))))
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ {x | ∀ i, 0<x i ∧ x i<1})
    (hφχ : ∀ x∈tsupport χ, φ x=1)
    {R α D : ℝ} (hR : 0<R) (hα : 0<α) (hα1 : α≤1) (hD : 0≤D)
    (hunit : ∀ y∈Metric.ball (0 : Plane) R, χ (a+normalGraph n g y)=1)
    {p : Plane → Plane} (hp : Continuous p) (hpb : ∀ y, ‖p y‖≤1)
    (hpc : ContDiffAt ℝ (⊤ : ℕ∞) p 0)
    (hpe : ∀ y∈Metric.ball (0 : Plane) R, p y=gradient g y)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R, ∀ y∈Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*(dist x y)^α)
    (hlin : ∀ i : Fin 2, LinearCMCEquation
      (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g)
      (fun _ => 0) (Metric.ball 0 R))
    (hqp : (fun y => q (actualNormalGraphChart a hn g y))
      =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)] graphSquaredSecondFundamentalForm g)
    {f : Plane → ℝ} (hf : ContinuousOn f (Metric.ball 0 R))
    (hfu : f =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)]
      fun y => u.1 (actualNormalGraphChart a hn g y)) :
    LinearCMCEquationNear (fun y => cmcWeight (gradient g y)*f y)
      (gradient g) (fun _ => 0) := by
  have hφunit (y : Plane) (hy : y∈Metric.ball (0 : Plane) R) : φ (a+normalGraph n g y)=1 := by
    apply hφχ
    apply subset_tsupport
    rw [Function.mem_support,hunit y hy]
    exact one_ne_zero
  have hd := graph_chart_measure_le a hn hg.continuous hφb hm measurableSet_ball hφunit
  have hcell (y : Plane) (hy : y∈Metric.ball (0 : Plane) R) (i : Fin 3) :
      (a+normalGraph n g y) i∈Icc 0 1 := by
    have hz : a+normalGraph n g y∈tsupport φ := subset_tsupport _ (by
      rw [Function.mem_support,hφunit y hy]; exact one_ne_zero)
    exact ⟨(hφO hz i).1.le,(hφO hz i).2.le⟩
  let hchart := actualNormalGraphChart_measurable a hn hg.continuous
  let v := lpPullbackLE hchart hd u.1
  let w := lpPullbackLE hchart hd u.2
  let G := graphCovectorLp hn hgL w
  have hv := lpPullbackLE_ae hchart hd u.1
  have hG : G =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)]
      fun y => graphCovector n g y (u.2 (actualNormalGraphChart a hn g y)) := by
    filter_upwards [graphCovectorLp_ae hn hgL w,lpPullbackLE_ae hchart hd u.2] with y hy hz
    change G y=graphCovector n g y (w y) at hy
    change w y=u.2 (actualNormalGraphChart a hn g y) at hz
    rw [hy,hz]
  have hw := surfaceH1_chart_weak_gradient μ a hn hgL Metric.isOpen_ball
    (hg.of_le (by simp)).contDiffOn hcell hd hu
  apply hw.jacobi_equationNear hp hpb hR hα hα1 hD hHolder hpc hg hpe hlin
  · intro ψ hψ hψc hs
    have he := surfaceJacobiB_chart_form μ q u a hn hg.continuous hφ
      (fun x => (hφb x).1) hφO hm (fun y _ => hg.differentiable (by simp) y)
      hχ hc hχO hφχ Metric.isOpen_ball hunit hψ hs
    rw [hhom _ (subset_closure (LinearMap.mem_range_self _ _))] at he
    refine Eq.trans ?_ he.symm
    apply integral_congr_ae
    filter_upwards [hv,hG,hqp] with y hy hz hqz
    change v y=u.1 (actualNormalGraphChart a hn g y) at hy
    rw [hy,hz,hqz]
  · exact hf
  · exact hfu.trans hv.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normalMeasure_H1_jacobi_graph_equationNear {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    {σ : ℝ} (hσ : σ=1 ∨ σ= -1)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=σ • (z.2 : Cover))
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0)
    {U : Set Cover} (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hgL : LipschitzWith K g) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgraph : ∀ᵐ x : Cover ∂volume,x∈U →
      (quotientMap x∈E ↔ ⟪n,x-a⟫<graphHeightExtension a n g x))
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ⊆U) (hφO : tsupport φ⊆{x | ∀ i,0<x i ∧ x i<1})
    {R : ℝ} (hφR : tsupport φ⊆Metric.closedBall a R) (hφb : ∀ x,φ x∈Icc 0 1)
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hsχ : HasCompactSupport χ)
    (hχO : tsupport χ⊆{x | ∀ i,0<x i ∧ x i<1})
    (hφχ : ∀ x∈tsupport χ,φ x=1)
    {s D : ℝ} (hs : 0<s) (hD : 0≤D)
    (hunit : ∀ y∈Metric.ball (0 : Plane) s,χ (a+normalGraph n g y)=1)
    {p : Plane → Plane} (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hpb : ∀ y,‖p y‖≤1)
    (hpe : EqOn p (gradient g) (Metric.ball 0 s))
    (hpD : ∀ x y,‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*dist x y)
    (hlin : ∀ i : Fin 2,LinearCMCEquation
      (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g)
      (fun _ => 0) (Metric.ball 0 s))
    (hNu : ∀ y∈Metric.ball (0 : Plane) s,∀ᶠ x in 𝓝 (a+normalGraph n g y),‖N x‖=1)
    {S : Set Torus} {F : Torus → ℝ} (hF : ContinuousOn F S)
    (hS : ∀ y∈Metric.ball (0 : Plane) s,quotientMap (a+normalGraph n g y)∈S)
    (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection) :
    LinearCMCEquationNear (fun y => cmcWeight (gradient g y)*
      F (quotientMap (a+normalGraph n g y))) (gradient g) (fun _ => 0) := by
  have hm := normalMeasure_graph_area_measure hE hμ a hn hgL
    (fun y _ => ((hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.continuousAt (x := y)))
    hgraph hφ hsφ hφU hφO hφR hφb
  have hφunit (y : Plane) (hy : y∈Metric.ball (0 : Plane) s) : φ (a+normalGraph n g y)=1 := by
    apply hφχ
    apply subset_tsupport
    rw [Function.mem_support,hunit y hy]
    exact one_ne_zero
  have hd := graph_chart_measure_le a hn hg.continuous hφb hm measurableSet_ball hφunit
  have hcell (y : Plane) (hy : y∈Metric.ball (0 : Plane) s) (i : Fin 3) :
      (a+normalGraph n g y) i∈Icc 0 1 := by
    have hz : a+normalGraph n g y∈tsupport φ := subset_tsupport _ (by
      rw [Function.mem_support,hφunit y hy]; exact one_ne_zero)
    exact ⟨(hφO hz i).1.le,(hφO hz i).2.le⟩
  have hq := surfaceCurvatureLp_graph_ae μ N hN hσ hae a hn hg Metric.isOpen_ball hcell hd hNu
  apply surfaceH1_jacobi_graph_equationNear μ (surfaceCurvatureLp μ N hN) hu hhom a hn hgL hg
    hφ.continuous.measurable hφb hφO hm hχ hsχ hχO hφχ hs
    (α := 1) (by norm_num) (by norm_num) hD hunit hp.continuous hpb hp.contDiffAt
    (fun y hy => hpe hy) (fun x _ y _ => by simpa only [Real.rpow_one] using hpD x y) hlin hq
  · apply hF.comp
    · exact (continuous_quotientMap.comp
        (continuous_const.add ((normalPlaneLinearIsometry n).continuous.add
          (hg.continuous.smul continuous_const)))).continuousOn
    · exact hS
  · have hmp : Measure.QuasiMeasurePreserving (actualNormalGraphChart a hn g)
        (volume.restrict (Metric.ball (0 : Plane) s)) (μ : Measure NormalBundle) :=
      ⟨actualNormalGraphChart_measurable a hn hg.continuous,Measure.absolutelyContinuous_of_le hd⟩
    filter_upwards [hmp.ae_eq_comp hFu,ae_restrict_mem measurableSet_ball] with y hy hys
    change u.1 (actualNormalGraphChart a hn g y)=
      F (quotientMap (actualNormalGraphChart a hn g y).1) at hy
    rw [actualNormalGraphChart_position a hn g (hcell y hys)] at hy
    exact hy.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normalMeasure_H1_jacobi_signed_graph_equationNear {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0)
    {U : Set Cover} (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hgL : LipschitzWith K g) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgraph : (∀ᵐ x : Cover ∂volume,x∈U →
      (quotientMap x∈E ↔ graphSignedHeight a n g x<0)) ∨
      (∀ᵐ x : Cover ∂volume,x∈U →
      (quotientMap x∈E ↔ 0<graphSignedHeight a n g x)))
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ⊆U) (hφO : tsupport φ⊆{x | ∀ i,0<x i ∧ x i<1})
    {R : ℝ} (hφR : tsupport φ⊆Metric.closedBall a R) (hφb : ∀ x,φ x∈Icc 0 1)
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hsχ : HasCompactSupport χ)
    (hχO : tsupport χ⊆{x | ∀ i,0<x i ∧ x i<1})
    (hφχ : ∀ x∈tsupport χ,φ x=1)
    {s D : ℝ} (hs : 0<s) (hD : 0≤D)
    (hunit : ∀ y∈Metric.ball (0 : Plane) s,χ (a+normalGraph n g y)=1)
    {p : Plane → Plane} (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hpb : ∀ y,‖p y‖≤1)
    (hpe : EqOn p (gradient g) (Metric.ball 0 s))
    (hpD : ∀ x y,‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*dist x y)
    (hlin : ∀ i : Fin 2,LinearCMCEquation
      (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g)
      (fun _ => 0) (Metric.ball 0 s))
    (hNu : ∀ y∈Metric.ball (0 : Plane) s,∀ᶠ x in 𝓝 (a+normalGraph n g y),‖N x‖=1)
    {S : Set Torus} {F : Torus → ℝ} (hF : ContinuousOn F S)
    (hS : ∀ y∈Metric.ball (0 : Plane) s,quotientMap (a+normalGraph n g y)∈S)
    (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection) :
    LinearCMCEquationNear (fun y => cmcWeight (gradient g y)*
      F (quotientMap (a+normalGraph n g y))) (gradient g) (fun _ => 0) := by
  rcases hgraph with hphase | hphase
  · have hgph : ∀ᵐ x : Cover ∂volume,x∈U →
        (quotientMap x∈E ↔ ⟪n,x-a⟫<graphHeightExtension a n g x) := by
      simpa only [graphSignedHeight,sub_neg] using hphase
    have hn' : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(1 : ℝ) • (z.2 : Cover) := by
      simpa only [one_smul] using hae
    exact normalMeasure_H1_jacobi_graph_equationNear hE hμ N hN (Or.inl rfl) hn' hu hhom
      a hn hgL hg hgph hφ hsφ hφU hφO hφR hφb hχ hsχ hχO hφχ hs hD hunit
      hp hpb hpe hpD hlin hNu hF hS hFu
  · have hgph : ∀ᵐ x : Cover ∂volume,x∈U →
        (x∈quotientMap ⁻¹' E ↔ graphHeightExtension a n g x<⟪n,x-a⟫) := by
      simpa only [graphSignedHeight,sub_pos,mem_preimage] using hphase
    have hcph := graph_superlevel_compl_ae a hn hg.continuous hgph
    have hn' : ∀ᵐ z ∂(μ.map reverseNormal : Measure NormalBundle),
        N z.1=(-1 : ℝ) • (z.2 : Cover) := by
      have hh := (reverseNormal_measurePreserving_back μ).quasiMeasurePreserving.ae_eq_comp hae
      filter_upwards [hh] with z hz
      simpa only [Function.comp_apply,reverseNormal,neg_one_smul] using hz
    have hf' : ((surfaceJetReverse μ u).1 : NormalBundle → ℝ)
        =ᵐ[(μ.map reverseNormal : Measure NormalBundle)] F ∘ normalProjection := by
      have hh := (reverseNormal_measurePreserving_back μ).quasiMeasurePreserving.ae_eq_comp hFu
      filter_upwards [normalReverseLp_ae μ 2 u.1,hh] with z hz hh
      exact hz.trans hh
    have hh := surfaceJacobi_homogeneous_reverse μ (surfaceCurvatureLp μ N hN) hhom
    rw [surfaceCurvatureLp_reverse] at hh
    exact normalMeasure_H1_jacobi_graph_equationNear hE.compl (isNormalMeasure_compl hE hμ)
      N hN (Or.inr rfl) hn' (surfaceH1_reverse μ hu) hh
      a hn hgL hg hcph hφ hsφ hφU hφO hφR hφb hχ hsχ hχO hφχ hs hD hunit
      hp hpb hpe hpD hlin hNu hF hS hf'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_centered_H1_jacobi_equation {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hNu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖N y‖=1)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0)
    {F : Torus → ℝ} (hF : ContinuousOn F (frontier (openRepresentative E)))
    (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection) :
    ∃ (n : Cover) (f : Plane → ℝ) (s : ℝ),‖n‖=1 ∧ 0<s ∧ f 0=0 ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧
      (∀ y∈Metric.ball (0 : Plane) s,
        quotientMap (cubeCenter+normalGraph n f y)∈frontier (openRepresentative E)) ∧
      (∀ x∈Metric.ball (0 : Cover) s,
        quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
          normalGraph n f (normalPlaneCoordinates n x)=x) ∧
      LinearCMCEquationNear (fun y => cmcWeight (gradient f y)*
        F (quotientMap (cubeCenter+normalGraph n f y))) (gradient f) (fun _ => 0) := by
  obtain ⟨n,g,r,H,hn,hr,hg,hg0,hgc,hi,hcover,hw,_⟩ :=
    isMinimizerAt_smooth_CMC hV hE hmin (quotientMap cubeCenter) hcenter
  obtain ⟨f,Kf,p,rj,D,hrj,hrjr,hf,hfc,hfL,hfg,hp,hpb,hD,hpf,hpD,hlin⟩ :=
    hw.smooth_jacobi_data hg (by norm_num) hr hgc
  have hf0 : f 0=0 := (hfg (Metric.mem_ball_self (half_pos hr))).trans hg0
  have hcover' (x : Cover) (hx : x∈Metric.ball (0 : Cover) (r/2)) :
      quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n x)=x := by
    rw [quotientMap_add]
    exact hcover x (Metric.ball_subset_ball (by linarith) hx)
  obtain ⟨R,ρ,U,hRr,_,_,_,hR,hρ,hgC,hU,hρU,hUR,hUO,_,hphase⟩ :=
    actual_centered_graph_phase_patch hV hE hmin hcenter hn (half_pos hr)
      hg hg0 ((hgc.of_le (by simp)).mono (Metric.ball_subset_ball (by linarith))) hcover'
  have hext (x : Cover) (hx : x∈U) :
      graphSignedHeight cubeCenter n f x=graphSignedHeight cubeCenter n g x := by
    have hy : normalPlaneCoordinates n (x-cubeCenter)∈Metric.ball (0 : Plane) (r/2) := by
      have hz : ‖x-cubeCenter‖<R := by
        simpa only [Metric.mem_ball,dist_eq_norm] using hUR hx
      simpa only [Metric.mem_ball,dist_zero_right] using
        (normalPlaneCoordinates_norm_le n (x-cubeCenter)).trans_lt (hz.trans hRr)
    simp only [graphSignedHeight,graphHeightExtension,hfg hy]
  have hphasef : (∀ᵐ x : Cover ∂volume,x∈U →
        (quotientMap x∈E ↔ graphSignedHeight cubeCenter n f x<0)) ∨
      (∀ᵐ x : Cover ∂volume,x∈U →
        (quotientMap x∈E ↔ 0<graphSignedHeight cubeCenter n f x)) := by
    rcases hphase with hphase|hphase
    · left; filter_upwards [hphase] with x hx hxu
      rw [hext x hxu]; exact hx hxu
    · right; filter_upwards [hphase] with x hx hxu
      rw [hext x hxu]; exact hx hxu
  let φ := radialHeightCutoff cubeCenter ρ
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := radialDensityWeight_contDiff _ _ _
  have hsφ : HasCompactSupport φ := radialDensityWeight_hasCompactSupport (by positivity) (by positivity)
  have hφs : tsupport φ⊆Metric.closedBall cubeCenter (2*ρ) :=
    radialDensityWeight_tsupport (by positivity) (by positivity)
  have hφU := hφs.trans hρU
  have hφO := hφU.trans hUO
  have hφR := hφU.trans (hUR.trans Metric.ball_subset_closedBall)
  have hφb (x : Cover) : φ x∈Icc 0 1 :=
    ⟨radialDensityWeight_nonneg _ _ _ _,radialDensityWeight_le_one _ _ _ _⟩
  let χ := radialHeightCutoff cubeCenter (ρ/4)
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := radialDensityWeight_contDiff _ _ _
  have hsχ : HasCompactSupport χ := radialDensityWeight_hasCompactSupport (by positivity) (by positivity)
  have hχs : tsupport χ⊆Metric.closedBall cubeCenter (ρ/2) := by
    have hh := radialDensityWeight_tsupport (a := cubeCenter)
      (by positivity : 0≤2*(ρ/4)) (by positivity : 0<3*(ρ/4)^2)
    convert hh using 1 <;> congr 1
    ring
  have hφχ (x : Cover) (hx : x∈tsupport χ) : φ x=1 :=
    radialHeightCutoff_one hρ (Metric.closedBall_subset_closedBall (by linarith) (hχs hx))
  have hχO : tsupport χ⊆{x | ∀ i,0<x i ∧ x i<1} :=
    hχs.trans ((Metric.closedBall_subset_closedBall (by linarith)).trans (hρU.trans hUO))
  have hΦ : Continuous (fun y => cubeCenter+normalGraph n f y) :=
    continuous_const.add ((normalPlaneLinearIsometry n).continuous.add
      (hf.continuous.smul continuous_const))
  have hΦ0 : cubeCenter+normalGraph n f 0=cubeCenter := by
    simp only [normalGraph,hf0,zero_smul,add_zero]
    change cubeCenter+(normalPlaneLinearIsometry n) 0=cubeCenter
    rw [map_zero,add_zero]
  have hnb : ∀ᶠ y in 𝓝 (0 : Plane),
      cubeCenter+normalGraph n f y∈Metric.ball cubeCenter (ρ/4) := by
    apply hΦ.continuousAt
    change Metric.ball cubeCenter (ρ/4)∈𝓝 (cubeCenter+normalGraph n f 0)
    rw [hΦ0]
    exact Metric.ball_mem_nhds _ (by positivity)
  obtain ⟨t,ht,htb⟩ := Metric.mem_nhds_iff.mp hnb
  let s := min rj t
  have hs : 0<s := lt_min hrj ht
  have hsj : s≤rj := min_le_left _ _
  have hsr : s≤r/2 := hsj.trans hrjr
  have hunit (y : Plane) (hy : y∈Metric.ball (0 : Plane) s) :
      χ (cubeCenter+normalGraph n f y)=1 :=
    radialHeightCutoff_one (by positivity)
      (Metric.ball_subset_closedBall (htb (Metric.ball_subset_ball (min_le_right _ _) hy)))
  have hin (y : Plane) (hy : y∈Metric.ball (0 : Plane) s) :
      quotientMap (cubeCenter+normalGraph n f y)∈frontier (openRepresentative E) := by
    have hy' := Metric.ball_subset_ball hsr hy
    simp only [normalGraph,hfg hy',quotientMap_add]
    exact hi y (Metric.ball_subset_ball (by linarith) hy')
  refine ⟨n,f,s,hn,hs,hf0,hf,hin,?_,?_⟩
  · intro x hx
    have hx' := Metric.ball_subset_ball hsr hx
    have hp' : normalPlaneCoordinates n x∈Metric.ball (0 : Plane) (r/2) := by
      simpa only [Metric.mem_ball,dist_zero_right] using
        (normalPlaneCoordinates_norm_le n x).trans_lt
          (show ‖x‖<r/2 from by simpa only [Metric.mem_ball,dist_zero_right] using hx')
    simpa only [normalGraph,hfg hp'] using hcover' x hx'
  · exact normalMeasure_H1_jacobi_signed_graph_equationNear hE hμ N hN hae hu hhom
      cubeCenter hn hfL hf hphasef hφ hsφ hφU hφO hφR hφb hχ hsχ hχO hφχ
      hs hD hunit hp hpb (hpf.mono (Metric.ball_subset_ball hsj)) hpD
      (fun i => (hlin i).mono (Metric.ball_subset_ball hsj))
      (fun y hy => hNu _ (hin y hy)) hF hin hFu

end CubicTorus

end
end

end OAI
