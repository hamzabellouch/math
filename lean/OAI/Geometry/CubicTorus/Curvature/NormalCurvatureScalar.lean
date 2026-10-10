import Mathlib
import OAI.Geometry.CubicTorus.Estimates.SurfaceJet

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normalComponentScalar_null {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ∀ᶠ y in 𝓝 x,‖N y‖=1)
    (hs : ∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
      0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u) (i : Fin 3) :
    surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (normalComponentScalar N hN hp i))
      (surfaceSmoothJet μ (normalComponentScalar N hN hp i))=0 := by
  have hn (j : Fin 3) : 0 ≤ normalExtensionJacobi μ (normalComponentScalar N hN hp j).val N := by
    rw [← surfaceSmoothJet_jacobi]
    exact hs _ (subset_closure (LinearMap.mem_range_self _ _))
      (normalComponentScalar_mean_zero hμ hN hp hae j)
  rw [surfaceSmoothJet_jacobi]
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ hn j)).mp
    (normalComponentScalar_energy_sum hV hE hmin hμ hN hp hae hu) i (Finset.mem_univ i)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalComponentScalar_geometry {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ∀ᶠ y in 𝓝 x,‖N y‖=1) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),
      (∑ i : Fin 3,((normalComponentScalar N hN hp i).val z.1)^2)=1 ∧
      (∑ i : Fin 3,‖smoothScalarGradient (normalComponentScalar N hN hp i) z‖^2)=
        coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1)) ∧
      (∑ i : Fin 3,(normalComponentScalar N hN hp i).val z.1 •
        smoothScalarGradient (normalComponentScalar N hN hp i) z)=0 := by
  have hμU := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμU
  filter_upwards [hbd,hae] with z hz hzn
  have hunit := hu z.1 hz
  have hn : ‖N z.1‖=1 := hunit.self_of_nhds
  have hd := smooth_unit_normal_derivative (hN.differentiable (by simp) z.1) hunit
  have ht (v : Cover) : ⟪N z.1,fderiv ℝ N z.1 v⟫=0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left,hd,inner_zero_left]
  have hs := isMinimizerAt_shape_tangent_symmetric hV hE hmin hμ hN hp hae z.1 hz
  have hsum := normal_tangent_trace_norm hn (fderiv ℝ N z.1) ht hs
  let P : Cover →L[ℝ] Cover := ContinuousLinearMap.id ℝ Cover-(innerSL ℝ (N z.1)).smulRight (N z.1)
  have hg (i : Fin 3) : smoothScalarGradient (normalComponentScalar N hN hp i) z=
      P ((fderiv ℝ N z.1).adjoint (EuclideanSpace.single i 1)) := by
    change gradient (fun y ↦ ⟪EuclideanSpace.single i 1,N y⟫) z.1-
      ⟪(z.2 : Cover),gradient (fun y ↦ ⟪EuclideanSpace.single i 1,N y⟫) z.1⟫ • (z.2 : Cover)=_
    rw [gradient_normal_component hN,← hzn]
    rfl
  refine ⟨?_,?_,?_⟩
  · simp only [normalComponentScalar_apply,← EuclideanSpace.real_norm_sq_eq,hn,one_pow]
  · simp_rw [hg]
    exact hsum
  · simp_rw [normalComponentScalar_apply,hg,← map_smul]
    rw [← map_sum,← map_sum,← cover_decompose,hd,map_zero]

theorem normalComponentScalar_product_sum {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ∀ᶠ y in 𝓝 x,‖N y‖=1)
    (ψ : smoothPeriodicScalars) :
    (∑ i : Fin 3,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (normalComponentScalar N hN hp i))
      (surfaceSmoothJet μ (smoothScalarMul (normalComponentScalar N hN hp i) ψ)))=0 := by
  let f (i : Fin 3) := normalComponentScalar N hN hp i
  let J (i : Fin 3) (z : NormalBundle) :=
    ⟪smoothScalarGradient (f i) z,smoothScalarGradient (smoothScalarMul (f i) ψ) z⟫-
      coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))*(f i).val z.1*(smoothScalarMul (f i) ψ).val z.1
  have hi (i : Fin 3) : Integrable (J i) (μ : Measure NormalBundle) := by
    have hc : Continuous (J i) :=
      (((smoothScalarGradient (f i)).continuous).inner (𝕜 := ℝ)
        (smoothScalarGradient (smoothScalarMul (f i) ψ)).continuous).sub
      ((((normal_curvature_continuous hN).comp normalEmbedding_continuous.fst).mul
        (smoothScalarValue (f i)).continuous).mul (smoothScalarValue (smoothScalarMul (f i) ψ)).continuous)
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [surfaceSmoothJet_bilinear]
  change (∑ i : Fin 3,∫ z,J i z ∂(μ : Measure NormalBundle))=0
  rw [← integral_finsetSum _ (fun i _ ↦ hi i)]
  apply integral_eq_zero_of_ae
  filter_upwards [normalComponentScalar_geometry hV hE hmin hμ hN hp hae hu] with z hz
  rcases hz with ⟨hv,hg,hd⟩
  have he (i : Fin 3) : J i z=
      ψ.val z.1*‖smoothScalarGradient (f i) z‖^2+
      ⟪(f i).val z.1 • smoothScalarGradient (f i) z,smoothScalarGradient ψ z⟫-
      (ψ.val z.1*coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1)))*((f i).val z.1)^2 := by
    dsimp [J]
    rw [smoothScalarGradient_mul,inner_add_right,real_inner_smul_right,real_inner_smul_right,
      real_inner_self_eq_norm_sq,real_inner_smul_left]
    simp only [smoothScalarMul,Pi.mul_apply]
    ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,← sum_inner]
  change ψ.val z.1*(∑ i : Fin 3,‖smoothScalarGradient (normalComponentScalar N hN hp i) z‖^2)+
    ⟪∑ i : Fin 3,(normalComponentScalar N hN hp i).val z.1 • smoothScalarGradient (normalComponentScalar N hN hp i) z,
      smoothScalarGradient ψ z⟫-_=0
  rw [hg,hd,inner_zero_left,hv,mul_one]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normal_curvature_contDiff {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ N) := hN.fderiv_right (by simp)
  exact coverTraceCLM.contDiff.comp (hd.clm_comp hd)

def normalCurvatureScalar (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) : smoothPeriodicScalars :=
  ⟨fun x ↦ coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x)),normal_curvature_contDiff hN,
    fun m x ↦ by dsimp; rw [fderiv_periodic hp]⟩

lemma normalComponent_one_pairing (μ : FiniteMeasure NormalBundle)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) (f : smoothPeriodicScalars) :
    surfaceJacobiB μ (surfaceCurvatureLp μ N hN) (surfaceSmoothJet μ f) (surfaceOne μ)=
      -surfaceMean μ (surfaceSmoothJet μ (smoothScalarMul f (normalCurvatureScalar N hN hp))) := by
  rw [surfaceOne,surfaceSmoothJet_bilinear,surfaceMean_of_smooth,← integral_neg]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  have hg : smoothScalarGradient smoothScalarOne z=0 := by
    change gradient (fun _ : Cover ↦ (1 : ℝ)) z.1-
      ⟪(z.2 : Cover),gradient (fun _ : Cover ↦ (1 : ℝ)) z.1⟫ • (z.2 : Cover)=0
    simp [gradient]
  dsimp only
  rw [hg,inner_zero_right]
  change 0-coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))*f.val z.1*1=
    -(f.val z.1*coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1)))
  ring

theorem normalComponentScalar_global_jacobi {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ∀ᶠ y in 𝓝 x,‖N y‖=1)
    (hs : ∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
      0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u) (i : Fin 3) :
    ∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (normalComponentScalar N hN hp i)) w=0 := by
  have hm : (μ : Measure NormalBundle).real univ≠0 := by
    rw [Measure.real,← FiniteMeasure.ennreal_mass]
    change (μ.mass : ℝ)≠0
    rw [hμ.1]
    exact (ENNReal.toReal_pos (perimeter_pos_of_volume hV hmin.1.1 hmin.2.1).ne' hmin.1.2.ne).ne'
  let f (j : Fin 3) := normalComponentScalar N hN hp j
  let q := surfaceCurvatureLp μ N hN
  let b (j : Fin 3) := surfaceJacobiB μ q (surfaceSmoothJet μ (f j)) (surfaceOne μ)
  have hc (j : Fin 3) : ∀ w∈surfaceH1 μ,surfaceJacobiB μ q (surfaceSmoothJet μ (f j)) w=
      (b j/(μ : Measure NormalBundle).real univ)*surfaceMean μ w :=
    surfaceH1_zero_mode_constant μ hm q hs (subset_closure (LinearMap.mem_range_self _ _))
      (normalComponentScalar_mean_zero hμ hN hp hae j)
      (normalComponentScalar_null hV hE hmin hμ hN hp hae hu hs j)
  have he (j : Fin 3) : surfaceJacobiB μ q (surfaceSmoothJet μ (f j))
      (surfaceSmoothJet μ (smoothScalarMul (f j) (normalCurvatureScalar N hN hp)))=
        -(b j)^2/(μ : Measure NormalBundle).real univ := by
    rw [hc j _ (subset_closure (LinearMap.mem_range_self _ _))]
    have hb := normalComponent_one_pairing μ N hN hp (f j)
    change b j= -surfaceMean μ (surfaceSmoothJet μ (smoothScalarMul (f j) (normalCurvatureScalar N hN hp))) at hb
    rw [show surfaceMean μ (surfaceSmoothJet μ (smoothScalarMul (f j) (normalCurvatureScalar N hN hp)))= -b j by linarith]
    ring
  have hsum := normalComponentScalar_product_sum hV hE hmin hμ hN hp hae hu (normalCurvatureScalar N hN hp)
  change (∑ j : Fin 3,surfaceJacobiB μ q (surfaceSmoothJet μ (f j))
      (surfaceSmoothJet μ (smoothScalarMul (f j) (normalCurvatureScalar N hN hp))))=0 at hsum
  simp_rw [he] at hsum
  rw [← Finset.sum_div,Finset.sum_neg_distrib,neg_div] at hsum
  have hsq : (∑ j : Fin 3,(b j)^2)=0 := (div_eq_zero_iff.mp (neg_eq_zero.mp hsum)).resolve_right hm
  have hb : b i=0 := sq_eq_zero_iff.mp
    ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg (b j))).mp hsq i (Finset.mem_univ i))
  intro w hw
  rw [hc i w hw,hb,zero_div,zero_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem isMinimizerAt_H1_jacobi_system {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N),
      IsNormalMeasure E μ ∧ (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H ∧
          0≤coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))) ∧
      (∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
        0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u) ∧
      (∀ (u : SurfaceJet μ),u∈surfaceH1 μ → surfaceMean μ u=0 →
        surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u=0 →
        ∀ U : Set Torus,IsOpen U → (U∩frontier (openRepresentative E)).Nonempty →
        (∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U → u.1 z=0 ∧ u.2 z=0) →
        ∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u w=0) := by
  obtain ⟨μ,H,N,hN,hμ,hp,hae,hb,hs⟩ := isMinimizerAt_H1_trace_stability hV hE hmin
  refine ⟨μ,H,N,hN,hμ,hp,hae,hb,hs,?_⟩
  intro u hu hm hz U hU ha hzero
  exact isMinimizerAt_H1_unused_patch_homogeneous hV hE hmin hμ
    (surfaceCurvatureLp μ N hN) hs hu hm hz hU ha hzero

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem isMinimizerAt_H1_translation_jacobi {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N)
      (hp : ∀ m x,N (x+latticeVector m)=N x),
      IsNormalMeasure E μ ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H ∧
          0 ≤ coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))) ∧
      (∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
        0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u) ∧
      (∀ i : Fin 3,surfaceMean μ (surfaceSmoothJet μ (normalComponentScalar N hN hp i))=0 ∧
        ∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
          (surfaceSmoothJet μ (normalComponentScalar N hN hp i)) w=0) ∧
      (∀ (u : SurfaceJet μ),u∈surfaceH1 μ → surfaceMean μ u=0 →
        surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u=0 →
        ∀ U : Set Torus,IsOpen U → (U∩frontier (openRepresentative E)).Nonempty →
        (∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U → u.1 z=0 ∧ u.2 z=0) →
        ∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u w=0) := by
  obtain ⟨μ,H,N,hN,hμ,hp,hae,hb,hs,hunused⟩ := isMinimizerAt_H1_jacobi_system hV hE hmin
  refine ⟨μ,H,N,hN,hp,hμ,hae,hb,hs,?_,hunused⟩
  intro i
  exact ⟨normalComponentScalar_mean_zero hμ hN hp hae i,
    normalComponentScalar_global_jacobi hV hE hmin hμ hN hp hae (fun x hx ↦ (hb x hx).1) hs i⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def positiveTrunc (n : ℕ) (t : ℝ) : ℝ := t*Real.smoothTransition (((n:ℝ)+1)*t)
def positiveTruncCoeff (t : ℝ) : ℝ := Real.smoothTransition t+t*deriv Real.smoothTransition t

lemma smoothTransition_deriv_zero_neg {t : ℝ} (ht : t<0) : deriv Real.smoothTransition t=0 := by
  have he : Real.smoothTransition=ᶠ[𝓝 t] (fun _ ↦ (0:ℝ)) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact Real.smoothTransition.zero_of_nonpos hs.le
  rw [he.deriv_eq]
  simp

lemma smoothTransition_deriv_zero_gt {t : ℝ} (ht : 1<t) : deriv Real.smoothTransition t=0 := by
  have he : Real.smoothTransition=ᶠ[𝓝 t] (fun _ ↦ (1:ℝ)) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact Real.smoothTransition.one_of_one_le hs.le
  rw [he.deriv_eq]
  simp

lemma positiveTruncCoeff_zero {t : ℝ} (ht : t≤0) : positiveTruncCoeff t=0 := by
  rcases ht.eq_or_lt with rfl|ht
  · simp [positiveTruncCoeff]
  · simp [positiveTruncCoeff,Real.smoothTransition.zero_of_nonpos ht.le,smoothTransition_deriv_zero_neg ht]

lemma positiveTruncCoeff_one {t : ℝ} (ht : 1<t) : positiveTruncCoeff t=1 := by
  simp [positiveTruncCoeff,Real.smoothTransition.one_of_one_le ht.le,smoothTransition_deriv_zero_gt ht]

lemma positiveTruncCoeff_bounded : ∃ K : ℝ,0≤K ∧ ∀ t,‖positiveTruncCoeff t‖≤K := by
  have hd : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition).continuous_deriv (by simp)
  have hc : Continuous positiveTruncCoeff := Real.smoothTransition.continuous.add (continuous_id.mul hd)
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc (-1:ℝ) 2)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max (max M 1) 0,le_max_right _ _,?_⟩
  intro t
  by_cases ht : t∈Icc (-1:ℝ) 2
  · exact (hM t ht).trans ((le_max_left M 1).trans (le_max_left _ _))
  · rcases lt_or_gt_of_ne (show t≠(-1:ℝ) by intro he; subst t; exact ht (by norm_num)) with hlt|hgt
    · rw [positiveTruncCoeff_zero (by linarith),norm_zero]
      exact le_max_right _ _
    · have htwo : 2<t := lt_of_not_ge (fun h ↦ ht ⟨hgt.le,h⟩)
      rw [positiveTruncCoeff_one (by linarith),norm_one]
      exact (le_max_right M 1).trans (le_max_left _ _)

lemma positiveTrunc_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (positiveTrunc n) :=
  contDiff_id.mul (Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id))

lemma positiveTrunc_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (positiveTrunc n) (positiveTruncCoeff (((n:ℝ)+1)*t)) t := by
  have hS := (Real.smoothTransition.contDiff : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition).differentiable (by simp)
  have h := (hasDerivAt_id t).mul ((hS _).hasDerivAt.comp t ((hasDerivAt_id t).const_mul ((n:ℝ)+1)))
  have he : 1*(Real.smoothTransition ∘ fun y : ℝ ↦ ((n:ℝ)+1)*id y) t+
      id t*(deriv Real.smoothTransition (((n:ℝ)+1)*id t)*(((n:ℝ)+1)*1))=
      positiveTruncCoeff (((n:ℝ)+1)*t) := by
    dsimp [positiveTruncCoeff]
    ring
  rw [he] at h
  exact h

lemma positiveTrunc_bound (n : ℕ) (t : ℝ) : ‖positiveTrunc n t‖≤‖t‖ := by
  rw [positiveTrunc,norm_mul]
  apply mul_le_of_le_one_right (norm_nonneg _)
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

lemma positiveTrunc_eventually (t : ℝ) :
    ∀ᶠ n : ℕ in atTop,positiveTrunc n t=max t 0 ∧
      positiveTruncCoeff (((n:ℝ)+1)*t)=(if 0<t then 1 else 0) := by
  by_cases ht : 0<t
  · have hn : Tendsto (fun n : ℕ ↦ ((n:ℝ)+1)*t) atTop atTop :=
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_mul_const ht
    filter_upwards [hn.eventually (eventually_gt_atTop 1)] with n hn
    rw [positiveTrunc,Real.smoothTransition.one_of_one_le hn.le,positiveTruncCoeff_one hn,
      mul_one,max_eq_left ht.le,ite_eq_left ht]
    exact ⟨rfl,rfl⟩
  · have hn (n : ℕ) : ((n:ℝ)+1)*t≤0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.mp ht)
    filter_upwards [] with n
    rw [positiveTrunc,Real.smoothTransition.zero_of_nonpos (hn n),positiveTruncCoeff_zero (hn n),
      mul_zero,max_eq_right (not_lt.mp ht),ite_eq_right ht]
    exact ⟨rfl,rfl⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceL2_bounded_convergence {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F]
    (μ : FiniteMeasure NormalBundle) (f : ℕ → NormalBundle → F)
    (g : NormalBundle → F) (hf : ∀ n,MemLp (f n) 2 (μ : Measure NormalBundle))
    (hg : MemLp g 2 (μ : Measure NormalBundle)) {M : ℝ} (hM : 0≤M)
    (hfb : ∀ n,∀ᵐ z ∂(μ : Measure NormalBundle),‖f n z‖≤M)
    (hgb : ∀ᵐ z ∂(μ : Measure NormalBundle),‖g z‖≤M)
    (ht : ∀ᵐ z ∂(μ : Measure NormalBundle),Tendsto (fun n ↦ f n z) atTop (𝓝 (g z))) :
    Tendsto (fun n ↦ (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  have he (n : ℕ) : ‖(hf n).toLp (f n)-hg.toLp g‖^2=
      ∫ z,‖f n z-g z‖^2 ∂(μ : Measure NormalBundle) := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hf n).toLp (f n)) (hg.toLp g),
      (hf n).coeFn_toLp,hg.coeFn_toLp] with z hsub hfz hgz
    rw [hsub,Pi.sub_apply,hfz,hgz,real_inner_self_eq_norm_sq]
  have hi : Tendsto (fun n ↦ ∫ z,‖f n z-g z‖^2 ∂(μ : Measure NormalBundle)) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (f := fun _ : NormalBundle ↦ (0:ℝ)) (fun _ : NormalBundle ↦ (2*M)^2)
      (fun n ↦ (((hf n).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm.pow 2))
      (integrable_const _) ?_ ?_
    · simpa using h
    · intro n
      filter_upwards [hfb n,hgb] with z hfz hgz
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hb : ‖f n z-g z‖≤2*M := (norm_sub_le _ _).trans (by linarith)
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hM)).2 hb
    · filter_upwards [ht] with z hz
      simpa using (((hz.sub (tendsto_const_nhds (x := g z))).norm).pow 2)
  have hn : Tendsto (fun n ↦ ‖(hf n).toLp (f n)-hg.toLp g‖) atTop (𝓝 0) := by
    have hsq : Tendsto (fun n ↦ ‖(hf n).toLp (f n)-hg.toLp g‖^2) atTop (𝓝 0) := by
      simpa only [he] using hi
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using h
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def smoothScalarPositiveTrunc (f : smoothPeriodicScalars) (n : ℕ) : smoothPeriodicScalars :=
  ⟨positiveTrunc n ∘ f.val,(positiveTrunc_contDiff n).comp f.property.1,fun m x ↦ by
    simp only [Function.comp_apply,f.property.2]⟩

lemma gradient_positiveTrunc (f : smoothPeriodicScalars) (n : ℕ) (x : Cover) :
    gradient (smoothScalarPositiveTrunc f n).val x=
      positiveTruncCoeff (((n:ℝ)+1)*f.val x) • gradient f.val x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,real_inner_smul_left,inner_gradient_left]
  have h := (positiveTrunc_hasDerivAt n (f.val x)).hasFDerivAt.comp x
    (f.property.1.differentiable (by simp) x).hasFDerivAt
  change (fderiv ℝ (positiveTrunc n ∘ f.val) x) v=_
  rw [h.fderiv]
  simp [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,mul_comm]

lemma smoothScalarGradient_positiveTrunc (f : smoothPeriodicScalars) (n : ℕ) (z : NormalBundle) :
    smoothScalarGradient (smoothScalarPositiveTrunc f n) z=
      positiveTruncCoeff (((n:ℝ)+1)*f.val z.1) • smoothScalarGradient f z := by
  change gradient (smoothScalarPositiveTrunc f n).val z.1-
    ⟪(z.2 : Cover),gradient (smoothScalarPositiveTrunc f n).val z.1⟫ • (z.2 : Cover)=_
  rw [gradient_positiveTrunc,real_inner_smul_right]
  change _=positiveTruncCoeff (((n:ℝ)+1)*f.val z.1) •
    (gradient f.val z.1-⟪(z.2 : Cover),gradient f.val z.1⟫ • (z.2 : Cover))
  rw [smul_sub,smul_smul]

def positiveSurfaceValue (f : smoothPeriodicScalars) (z : NormalBundle) : ℝ := max (f.val z.1) 0

def positiveSurfaceGradient (f : smoothPeriodicScalars) : NormalBundle → Cover :=
  {z | 0<f.val z.1}.indicator (smoothScalarGradient f)

lemma positiveSurfaceValue_memLp (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars) :
    MemLp (positiveSurfaceValue f) 2 (μ : Measure NormalBundle) := by
  exact ((smoothScalarValue f).continuous.max continuous_const).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma positiveSurfaceGradient_memLp (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars) :
    MemLp (positiveSurfaceGradient f) 2 (μ : Measure NormalBundle) :=
  ((smoothScalarGradient f).continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).indicator
    (isOpen_lt continuous_const (smoothScalarValue f).continuous).measurableSet

def positiveSurfaceJet (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars) : SurfaceJet μ :=
  ((positiveSurfaceValue_memLp μ f).toLp (positiveSurfaceValue f),
    (positiveSurfaceGradient_memLp μ f).toLp (positiveSurfaceGradient f))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceL2_continuous_bounded_convergence {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F]
    (μ : FiniteMeasure NormalBundle) (f : ℕ → C(NormalBundle,F))
    (g : NormalBundle → F) (hg : MemLp g 2 (μ : Measure NormalBundle))
    {M : ℝ} (hM : 0≤M) (hfb : ∀ n z,‖f n z‖≤M) (hgb : ∀ z,‖g z‖≤M)
    (ht : ∀ z,Tendsto (fun n ↦ f n z) atTop (𝓝 (g z))) :
    Tendsto (fun n ↦ ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ (f n))
      atTop (𝓝 (hg.toLp g)) := by
  have hf (n : ℕ) : MemLp (f n) 2 (μ : Measure NormalBundle) :=
    (f n).continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (n : ℕ) : ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ (f n)=
      (hf n).toLp (f n) := by
    apply Lp.ext
    exact (f n).coeFn_toLp (μ : Measure NormalBundle) |>.trans (hf n).coeFn_toLp.symm
  simpa only [he] using surfaceL2_bounded_convergence μ (fun n ↦ f n) g hf hg hM
    (fun n ↦ ae_of_all _ (hfb n)) (ae_of_all _ hgb) (ae_of_all _ ht)

lemma positiveSurfaceJet_mem_surfaceH1 (μ : FiniteMeasure NormalBundle)
    (f : smoothPeriodicScalars) : positiveSurfaceJet μ f∈surfaceH1 μ := by
  have hv : Tendsto (fun n ↦ (surfaceSmoothJet μ (smoothScalarPositiveTrunc f n)).1)
      atTop (𝓝 (positiveSurfaceJet μ f).1) := by
    apply surfaceL2_continuous_bounded_convergence μ
      (fun n ↦ smoothScalarValue (smoothScalarPositiveTrunc f n))
      (positiveSurfaceValue f) (positiveSurfaceValue_memLp μ f)
      (norm_nonneg (smoothScalarValue f))
    · intro n z
      exact (positiveTrunc_bound n (f.val z.1)).trans ((smoothScalarValue f).norm_coe_le_norm z)
    · intro z
      by_cases ht : 0<f.val z.1
      · change ‖max (f.val z.1) 0‖≤_
        rw [max_eq_left ht.le]
        exact (smoothScalarValue f).norm_coe_le_norm z
      · change ‖max (f.val z.1) 0‖≤_
        rw [max_eq_right (not_lt.mp ht),norm_zero]
        exact norm_nonneg _
    · intro z
      apply tendsto_const_nhds.congr'
      filter_upwards [positiveTrunc_eventually (f.val z.1)] with n hn
      exact hn.1.symm
  obtain ⟨K,hK,hKb⟩ := positiveTruncCoeff_bounded
  have hg : Tendsto (fun n ↦ (surfaceSmoothJet μ (smoothScalarPositiveTrunc f n)).2)
      atTop (𝓝 (positiveSurfaceJet μ f).2) := by
    apply surfaceL2_continuous_bounded_convergence μ
      (fun n ↦ smoothScalarGradient (smoothScalarPositiveTrunc f n))
      (positiveSurfaceGradient f) (positiveSurfaceGradient_memLp μ f)
      (mul_nonneg (show 0≤K+1 by linarith) (norm_nonneg (smoothScalarGradient f)))
    · intro n z
      rw [smoothScalarGradient_positiveTrunc,norm_smul]
      exact (mul_le_mul (hKb _) ((smoothScalarGradient f).norm_coe_le_norm z)
        (norm_nonneg _) hK).trans (by nlinarith [norm_nonneg (smoothScalarGradient f)])
    · intro z
      by_cases ht : 0<f.val z.1
      · have he : positiveSurfaceGradient f z=smoothScalarGradient f z := by
          simp [positiveSurfaceGradient,ht]
        rw [he]
        exact ((smoothScalarGradient f).norm_coe_le_norm z).trans
          (by nlinarith [norm_nonneg (smoothScalarGradient f)])
      · have he : positiveSurfaceGradient f z=0 := by simp [positiveSurfaceGradient,ht]
        rw [he,norm_zero]
        positivity
    · intro z
      apply tendsto_const_nhds.congr'
      filter_upwards [positiveTrunc_eventually (f.val z.1)] with n hn
      rw [smoothScalarGradient_positiveTrunc,hn.2]
      by_cases ht : 0<f.val z.1 <;> simp [positiveSurfaceGradient,ht]
  have ht := hv.prodMk_nhds hg
  apply (surfaceSmoothJet μ).range.isClosed_topologicalClosure.mem_of_tendsto ht
  filter_upwards [] with n
  exact subset_closure ⟨smoothScalarPositiveTrunc f n,rfl⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceJacobiB_positive_restriction (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (f : smoothPeriodicScalars) :
    surfaceJacobiB μ q (surfaceSmoothJet μ f) (positiveSurfaceJet μ f)=
      surfaceJacobiB μ q (positiveSurfaceJet μ f) (positiveSurfaceJet μ f) := by
  have hv := (smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hg := (smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hpv := (positiveSurfaceValue_memLp μ f).coeFn_toLp
  have hpg := (positiveSurfaceGradient_memLp μ f).coeFn_toLp
  unfold surfaceJacobiB
  congr 1
  · rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg,hpg] with z hgz hpgz
    change (surfaceSmoothJet μ f).2 z=smoothScalarGradient f z at hgz
    change (positiveSurfaceJet μ f).2 z=positiveSurfaceGradient f z at hpgz
    rw [hgz,hpgz]
    by_cases ht : 0<f.val z.1 <;> simp [positiveSurfaceGradient,ht]
  · rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    have hmf := Lp.coeFn_lpSMul (r := 2) q (surfaceSmoothJet μ f).1
    have hmp := Lp.coeFn_lpSMul (r := 2) q (positiveSurfaceJet μ f).1
    filter_upwards [hv,hpv,hmf,hmp] with z hvz hpvz hmfz hmpz
    change (surfaceSmoothJet μ f).1 z=f.val z.1 at hvz
    change (positiveSurfaceJet μ f).1 z=positiveSurfaceValue f z at hpvz
    change (surfaceMultiplier μ q (surfaceSmoothJet μ f).1) z=_ at hmfz
    change (surfaceMultiplier μ q (positiveSurfaceJet μ f).1) z=_ at hmpz
    rw [hmfz,hmpz]
    simp only [smul_eq_mul,Pi.mul_apply,hvz,hpvz]
    by_cases ht : 0<f.val z.1
    · simp [positiveSurfaceValue,max_eq_left ht.le]
    · simp [positiveSurfaceValue,max_eq_right (not_lt.mp ht)]

lemma surfaceJacobiB_positive_null (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (f : smoothPeriodicScalars)
    (hf : ∀ w∈surfaceH1 μ,surfaceJacobiB μ q (surfaceSmoothJet μ f) w=0) :
    surfaceJacobiB μ q (positiveSurfaceJet μ f) (positiveSurfaceJet μ f)=0 := by
  rw [← surfaceJacobiB_positive_restriction]
  exact hf _ (positiveSurfaceJet_mem_surfaceH1 μ f)

theorem normalComponentScalar_positive_null {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ∀ᶠ y in 𝓝 x,‖N y‖=1)
    (hs : ∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
      0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u) (i : Fin 3) :
    positiveSurfaceJet μ (normalComponentScalar N hN hp i)∈surfaceH1 μ ∧
      surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
        (positiveSurfaceJet μ (normalComponentScalar N hN hp i))
        (positiveSurfaceJet μ (normalComponentScalar N hN hp i))=0 :=
  ⟨positiveSurfaceJet_mem_surfaceH1 _ _,surfaceJacobiB_positive_null _ _ _
    (normalComponentScalar_global_jacobi hV hE hmin hμ hN hp hae hu hs i)⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def directionalNormalScalar (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) (v : Cover) : smoothPeriodicScalars :=
  ∑ i : Fin 3,v i • normalComponentScalar N hN hp i

lemma directionalNormalScalar_apply (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) (v x : Cover) :
    (directionalNormalScalar N hN hp v).val x=⟪v,N x⟫ := by
  simp only [directionalNormalScalar,Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,
    Pi.smul_apply,smul_eq_mul,normalComponentScalar_apply,EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct,star_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma surfaceJacobiB_sum_left {ι : Type*} (s : Finset ι)
    (μ : FiniteMeasure NormalBundle) (q : Lp ℝ ∞ (μ : Measure NormalBundle))
    (u : ι → SurfaceJet μ) (w : SurfaceJet μ) :
    surfaceJacobiB μ q (∑ i∈s,u i) w=∑ i∈s,surfaceJacobiB μ q (u i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [surfaceJacobiB]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,surfaceJacobiB_add_left,ih]

lemma directionalNormalScalar_global_jacobi (μ : FiniteMeasure NormalBundle)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hj : ∀ i : Fin 3,∀ w∈surfaceH1 μ,
      surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
        (surfaceSmoothJet μ (normalComponentScalar N hN hp i)) w=0) (v : Cover) :
    ∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp v)) w=0 := by
  intro w hw
  simp only [directionalNormalScalar,map_sum,map_smul,surfaceJacobiB_sum_left,
    surfaceJacobiB_smul_left,hj _ w hw,mul_zero,Finset.sum_const_zero]

namespace Periodic

theorem isMinimizerAt_translation_positive_nodal {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N)
      (hp : ∀ m x,N (x+latticeVector m)=N x),
      IsNormalMeasure E μ ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H ∧
          0 ≤ coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))) ∧
      (∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
        0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u) ∧
      ∀ v : Cover,
        (∀ x,(directionalNormalScalar N hN hp v).val x=⟪v,N x⟫) ∧
        (∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
          (surfaceSmoothJet μ (directionalNormalScalar N hN hp v)) w=0) ∧
        positiveSurfaceJet μ (directionalNormalScalar N hN hp v)∈surfaceH1 μ ∧
        surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
          (positiveSurfaceJet μ (directionalNormalScalar N hN hp v))
          (positiveSurfaceJet μ (directionalNormalScalar N hN hp v))=0 := by
  obtain ⟨μ,H,N,hN,hp,hμ,hae,hb,hs,hj,_⟩ := isMinimizerAt_H1_translation_jacobi hV hE hmin
  refine ⟨μ,H,N,hN,hp,hμ,hae,hb,hs,?_⟩
  intro v
  have hv := directionalNormalScalar_global_jacobi μ N hN hp (fun i ↦ (hj i).2) v
  exact ⟨directionalNormalScalar_apply N hN hp v,hv,
    positiveSurfaceJet_mem_surfaceH1 μ _,surfaceJacobiB_positive_null μ _ _ hv⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma locallyConnected_of_quotient_graphs (S : Set Torus)
    (hchart : ∀ a∈S,∃ (x : Cover) (G : Plane → Cover) (P : Cover →L[ℝ] Plane),
      quotientMap x=a ∧ Continuous G ∧ G 0=0 ∧
      (∀ᶠ y in 𝓝 (0 : Plane),quotientMap (x+G y)∈S) ∧
      ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈S → G (P v)=v) :
    LocallyConnectedSpace S := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro a U hU
  obtain ⟨T,hT,hTU⟩ := (mem_nhds_subtype S a U).mp hU
  obtain ⟨x,G,P,hx,hG,hG0,hGS,hGP⟩ := hchart a a.property
  let F : Plane → Torus := fun y ↦ quotientMap (x+G y)
  have hF : Continuous F := continuous_quotientMap.comp (continuous_const.add hG)
  have hF0 : F 0=a := by simp [F,hG0,hx]
  have hFT : ∀ᶠ y in 𝓝 (0 : Plane),F y∈T := by
    have ht : Tendsto F (𝓝 (0 : Plane)) (𝓝 (a : Torus)) := by
      simpa only [hF0] using hF.tendsto (0 : Plane)
    exact ht.eventually hT
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp (hGS.and hFT)
  let B : Set Torus := F '' Metric.ball 0 r
  have hBS : B⊆S := by rintro b ⟨y,hy,rfl⟩; exact (hrsub hy).1
  have hBT : B⊆T := by rintro b ⟨y,hy,rfl⟩; exact (hrsub hy).2
  have hBc : IsPreconnected B := (convex_ball (0 : Plane) r).isPreconnected.image F hF.continuousOn
  refine ⟨Subtype.val ⁻¹' B,?_,?_,fun b hb ↦ hTU (hBT hb)⟩
  · have hP : ∀ᶠ v in 𝓝 (0 : Cover),P v∈Metric.ball 0 r := by
      have hp : Tendsto P (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
        simpa only [map_zero] using P.continuous.tendsto (0 : Cover)
      exact hp.eventually (Metric.ball_mem_nhds _ hr)
    obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp (hGP.and hP)
    apply (mem_nhds_subtype S a _).mpr
    refine ⟨Metric.ball (a : Torus) δ,Metric.ball_mem_nhds _ hδ,?_⟩
    intro b hb
    have hb' : b.val∈Metric.ball (quotientMap x) δ := by change b.val∈Metric.ball (a : Torus) δ at hb; simpa only [hx] using hb
    rw [← quotientMap_image_ball x δ] at hb'
    obtain ⟨y,hy,hyb⟩ := hb'
    have hy' : y-x∈Metric.ball (0 : Cover) δ := by
      simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hy
    obtain ⟨hg,hp⟩ := hδsub hy'
    have hxs : quotientMap (x+(y-x))∈S := by simpa only [add_sub_cancel,hyb] using b.property
    have hid := hg hxs
    exact ⟨P (y-x),hp,by simp only [F,hid,add_sub_cancel,hyb]⟩
  · apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    have he : (Subtype.val : S → Torus) '' (Subtype.val ⁻¹' B)=B := by
      ext b
      constructor
      · rintro ⟨c,hc,rfl⟩; exact hc
      · intro hb; exact ⟨⟨b,hBS hb⟩,hb,rfl⟩
    rwa [he]

theorem isMinimizerAt_boundary_locallyConnected {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    LocallyConnectedSpace (frontier (openRepresentative E)) := by
  obtain ⟨μ,H,N,hN,hp,hμ,hae,_⟩ := Periodic.isMinimizerAt_H1_translation_jacobi hV hE hmin
  apply locallyConnected_of_quotient_graphs
  intro a ha
  let x := representative a
  have hx : quotientMap x=a := quotientMap_representative a
  obtain ⟨n,f,σ,hn,hf,hf0,hσ,hgraph,hcover⟩ := isMinimizerAt_normal_graph_chart
    hV hE hmin hμ hN hp hae x (by rwa [hx])
  refine ⟨x,normalGraph n f,normalPlaneCoordinates n,hx,?_,?_,?_,?_⟩
  · unfold normalGraph
    exact (normalPlaneLinearIsometry n).continuous.add (hf.continuous.smul continuous_const)
  · change normalPlaneLinearIsometry n 0+f 0 • n=0
    simp [hf0]
  · exact hgraph.mono (fun y hy ↦ hy.2)
  · exact hcover.mono (fun v hv ↦ hv.mp)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def nodalEpsilon (n : ℕ) : ℝ := ((n:ℝ)+1)⁻¹
def separatedPositiveTrunc (n : ℕ) (t : ℝ) : ℝ := positiveTrunc n (t-nodalEpsilon n)

lemma nodalEpsilon_pos (n : ℕ) : 0<nodalEpsilon n := by unfold nodalEpsilon; positivity

lemma separatedPositiveTrunc_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (separatedPositiveTrunc n) :=
  (positiveTrunc_contDiff n).comp (contDiff_id.sub contDiff_const)

lemma separatedPositiveTrunc_zero (n : ℕ) {t : ℝ} (ht : t≤nodalEpsilon n) :
    separatedPositiveTrunc n t=0 ∧ positiveTruncCoeff (((n:ℝ)+1)*(t-nodalEpsilon n))=0 := by
  have hh : ((n:ℝ)+1)*(t-nodalEpsilon n)≤0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr ht)
  exact ⟨by simp [separatedPositiveTrunc,positiveTrunc,Real.smoothTransition.zero_of_nonpos hh],
    positiveTruncCoeff_zero hh⟩

lemma separatedPositiveTrunc_bound (n : ℕ) (t : ℝ) : ‖separatedPositiveTrunc n t‖≤‖t‖ := by
  by_cases ht : t≤nodalEpsilon n
  · rw [(separatedPositiveTrunc_zero n ht).1,norm_zero]
    exact norm_nonneg _
  · have he := nodalEpsilon_pos n
    exact (positiveTrunc_bound n (t-nodalEpsilon n)).trans (by
      rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (by linarith : 0<t-nodalEpsilon n),
        abs_of_pos (by linarith : 0<t)]
      linarith)

lemma separatedPositiveTrunc_tendsto (t : ℝ) :
    Tendsto (fun n ↦ separatedPositiveTrunc n t) atTop (𝓝 (max t 0)) ∧
    ∀ᶠ n : ℕ in atTop,positiveTruncCoeff (((n:ℝ)+1)*(t-nodalEpsilon n))=(if 0<t then 1 else 0) := by
  by_cases ht : 0<t
  · have hn : Tendsto (fun n : ℕ ↦ ((n:ℝ)+1)*t) atTop atTop :=
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_mul_const ht
    have he (n : ℕ) : ((n:ℝ)+1)*(t-nodalEpsilon n)=((n:ℝ)+1)*t-1 := by
      rw [nodalEpsilon,mul_sub,mul_inv_cancel₀ (by positivity : (n:ℝ)+1≠0)]
    have hc : ∀ᶠ n : ℕ in atTop,1<((n:ℝ)+1)*(t-nodalEpsilon n) := by
      filter_upwards [hn.eventually (eventually_gt_atTop 2)] with n hn
      rw [he]
      linarith
    refine ⟨?_,?_⟩
    · have hε : Tendsto nodalEpsilon atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
      have hl : Tendsto (fun n ↦ t-nodalEpsilon n) atTop (𝓝 (max t 0)) := by
        simpa [max_eq_left ht.le] using tendsto_const_nhds.sub hε
      apply hl.congr'
      filter_upwards [hc] with n hn
      simp [separatedPositiveTrunc,positiveTrunc,Real.smoothTransition.one_of_one_le hn.le]
    · filter_upwards [hc] with n hn
      simp [positiveTruncCoeff_one hn,ht]
  · have hz (n : ℕ) := separatedPositiveTrunc_zero n (le_trans (not_lt.mp ht) (nodalEpsilon_pos n).le)
    refine ⟨?_,?_⟩
    · simpa only [(hz _).1,max_eq_right (not_lt.mp ht)] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:ℝ)) atTop (𝓝 0))
    · filter_upwards [] with n
      simp only [(hz n).2,ite_eq_right ht]

end CubicTorus
end
end
end

end OAI
