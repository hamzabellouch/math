import Mathlib
import OAI.Geometry.CubicTorus.Reflection.AxialFluxDensity

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma regularizedNormal_norm_le (R : Cover → Cover) (x : Cover) : ‖regularizedNormal R x‖≤1 := by
  rw [regularizedNormal,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr (regularizedNormal_denom_pos _))),
    inv_mul_le_iff₀ (Real.sqrt_pos.mpr (regularizedNormal_denom_pos _)),mul_one]
  apply Real.le_sqrt_of_sq_le
  linarith [Real.smoothTransition.le_one (4*‖R x‖^2)]

def axialTangentPart (i : Fin 3) (u : Cover) : Cover := u-u i • EuclideanSpace.single i 1

lemma axialTangentPart_axis (i : Fin 3) (u : Cover) : axialTangentPart i u i=0 := by
  simp [axialTangentPart]

lemma axialTangentPart_norm_sq (i : Fin 3) (u : Cover) :
    ‖axialTangentPart i u‖^2=‖u‖^2-(u i)^2 := by
  rw [axialTangentPart,norm_sub_sq_real,norm_smul,real_inner_smul_right]
  simp only [PiLp.norm_single,Real.norm_eq_abs,abs_one,mul_one,
    EuclideanSpace.inner_single_right,conj_trivial]
  rw [sq_abs]
  ring

lemma inner_axialTangentPart (i : Fin 3) (u : Cover) :
    ⟪u,axialTangentPart i u⟫=‖u‖^2-(u i)^2 := by
  rw [axialTangentPart,inner_sub_right,real_inner_self_eq_norm_sq,real_inner_smul_right]
  simp only [EuclideanSpace.inner_single_right,conj_trivial]
  ring

lemma axialTangentPart_contDiff {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => axialTangentPart i (N x)) :=
  hN.sub (((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hN).smul contDiff_const)

def axialNormalCalibration (N : Cover → Cover) (i : Fin 3) : Cover → Cover :=
  regularizedNormal (fun x => axialTangentPart i (N x))

lemma axialNormalCalibration_admissible {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) (i : Fin 3) :
    AdmissibleField (axialNormalCalibration N i) := by
  refine ⟨regularizedNormal_contDiff (axialTangentPart_contDiff hN i),?_,?_⟩
  · apply regularizedNormal_periodic
    intro m x
    rw [hp]
  · exact regularizedNormal_norm_le _

lemma axialNormalCalibration_axis (N : Cover → Cover) (i : Fin 3) (x : Cover) :
    axialNormalCalibration N i x i=0 := by
  simp only [axialNormalCalibration,regularizedNormal,PiLp.smul_apply,smul_eq_mul,axialTangentPart_axis,mul_zero]

lemma axialNormalCalibration_quadratic_lower (N : Cover → Cover) (i : Fin 3) (x : Cover)
    (hu : ‖N x‖=1) :
    1-(N x i)^2-⟪N x,axialNormalCalibration N i x⟫≤(N x i)^2 := by
  let w := 1-(N x i)^2
  have hw : ‖axialTangentPart i (N x)‖^2=w := by rw [axialTangentPart_norm_sq,hu,one_pow]
  have hw0 : 0≤w := by rw [← hw]; positivity
  have hw1 : w≤1 := by dsimp [w]; linarith [sq_nonneg (N x i)]
  have hin : ⟪N x,axialTangentPart i (N x)⟫=w := by rw [inner_axialTangentPart,hu,one_pow]
  have hf0 : 0≤⟪N x,axialNormalCalibration N i x⟫ := by
    rw [axialNormalCalibration,regularizedNormal,real_inner_smul_right,hin]
    positivity
  by_cases hh : 1/4≤w
  · have hnorm0 : 0<‖axialTangentPart i (N x)‖ := by
      have hpos : 0<‖axialTangentPart i (N x)‖^2 := by rw [hw]; linarith
      exact lt_of_le_of_ne (norm_nonneg _) (fun he => by rw [← he] at hpos; norm_num at hpos)
    have hnorm1 : ‖axialTangentPart i (N x)‖≤1 := by nlinarith [norm_nonneg (axialTangentPart i (N x))]
    have he : ⟪N x,axialNormalCalibration N i x⟫=
        w/‖axialTangentPart i (N x)‖ := by
      rw [axialNormalCalibration,regularizedNormal_eq (by rw [hw]; exact hh),real_inner_smul_right,hin]
      ring
    have hge : w≤⟪N x,axialNormalCalibration N i x⟫ := by
      rw [he,le_div_iff₀ hnorm0]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hnorm1 hw0
    change w-⟪N x,axialNormalCalibration N i x⟫≤_
    linarith [sq_nonneg (N x i)]
  · change w-⟪N x,axialNormalCalibration N i x⟫≤_
    dsimp only [w] at hh ⊢
    linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem axial_slice_endpoint_calibration {V : ℝ} {E : Set Torus}
    (hE : MeasurableSet E) (hvol : torusVolume.real E=V)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (i : Fin 3) (hc : Continuous (axialSectionArea E i))
    (hcf : Continuous (axialSectionIntegral E i (divergence (axialNormalCalibration N i))))
    (a : ℝ) {K : ℝ} (hK : 0≤K)
    (hR : ∀ᵐ z ∂(μ : Measure NormalBundle),|((z.2 : Cover) i)|≤K*|Real.sin (Real.pi*(z.1.1 i-a))|) :
    axialSectionIntegral E i (divergence (axialNormalCalibration N i)) a=
      (μ.mass : ℝ)*axialFluxWeight μ i+H*(axialSectionArea E i a-V) := by
  let F := axialNormalCalibration N i
  have hF : AdmissibleField F := axialNormalCalibration_admissible hN hp i
  have ht : ∀ x,F x i=0 := axialNormalCalibration_axis N i
  apply le_antisymm (axial_slice_endpoint_bound hE hvol hμ hH hF i ht hc hcf a hK hR)
  let p := axialSectionIntegral E i (divergence F)
  let q := fun t => (μ.mass : ℝ)*axialFluxWeight μ i+H*(axialSectionArea E i t-V)
  have hqc : Continuous q := continuous_const.add (continuous_const.mul (hc.sub continuous_const))
  have hpp : Function.Periodic p 1 := axialSectionIntegral_periodic E i (divergence_periodic hF.2.1)
  have hqp : Function.Periodic q 1 := by
    intro t
    dsimp [q]
    rw [axialSectionArea_periodic E i]
  suffices h : q a-p a≤0 by dsimp [p,q,F] at h; linarith
  apply circle_quadratic_contact (hqc.sub hcf) (hqp.sub hpp) a
    (M := K^2*(μ.mass : ℝ)) (by positivity)
  intro f hf hfp hf0 hf1 δ hδ hδsupp
  have hden := axial_density_moment hE hvol hH i hc hf hfp
  have hflux := axial_slice_flux_moment hE hμ hF i ht hf hfp
  have hic : (∫ t in Ico (0 : ℝ) 1,p t*f t)=∫ t in (0 : ℝ)..1,p t*f t := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1),integral_Ico_eq_integral_Ioc]
  change (∫ t in Ico (0 : ℝ) 1,p t*f t)=_ at hflux
  rw [hic] at hflux
  have hsub : (∫ t in (0 : ℝ)..1,(q t-p t)*f t)=
      (∫ t in (0 : ℝ)..1,q t*f t)-(∫ t in (0 : ℝ)..1,p t*f t) := by
    simp_rw [sub_mul]
    exact intervalIntegral.integral_sub ((hqc.mul hf.continuous).intervalIntegrable _ _)
      ((hcf.mul hf.continuous).intervalIntegrable _ _)
  change (∫ t in (0 : ℝ)..1,(q t-p t)*f t)≤_
  rw [hsub]
  change (∫ t in (0 : ℝ)..1,q t*f t)=_ at hden
  rw [hden,hflux]
  have hcT : Continuous (fun z : NormalBundle => f (z.1.1 i)) :=
    hf.continuous.comp ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp
      (continuous_subtype_val.comp continuous_fst))
  have hi1 : Integrable (fun z : NormalBundle => axialNormalWeight i z*f (z.1.1 i)) (μ : Measure NormalBundle) :=
    ((continuous_axialNormalWeight i).mul hcT).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun z : NormalBundle => f (z.1.1 i)*normalTest F hF.1.continuous z) (μ : Measure NormalBundle) :=
    (hcT.mul (normalTest F hF.1.continuous).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_sub hi1 hi2]
  calc
    (∫ z,axialNormalWeight i z*f (z.1.1 i)-f (z.1.1 i)*normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle))≤
        ∫ _ : NormalBundle,K^2*δ^2 ∂(μ : Measure NormalBundle) := by
      apply integral_mono_ae (hi1.sub hi2) (integrable_const _)
      filter_upwards [ha,hR] with z hzn hz
      have hcal := axialNormalCalibration_quadratic_lower N i z.1 (by rw [hzn]; exact z.2.property)
      rw [hzn] at hcal
      have hh := mul_le_mul_of_nonneg_right hcal (hf0 (z.1.1 i))
      change axialNormalWeight i z*f (z.1.1 i)-f (z.1.1 i)*normalTest F hF.1.continuous z≤K^2*δ^2
      by_cases hzero : f (z.1.1 i)=0
      · simp only [hzero,mul_zero,zero_mul,sub_self]
        positivity
      · have hn := hz.trans (mul_le_mul_of_nonneg_left (hδsupp _ hzero) hK)
        have hsq : ((z.2 : Cover) i)^2≤K^2*δ^2 := by
          have he := (sq_le_sq₀ (abs_nonneg ((z.2 : Cover) i)) (mul_nonneg hK hδ)).mpr hn
          simpa only [sq_abs,mul_pow] using he
        have hfa : ((z.2 : Cover) i)^2*f (z.1.1 i)≤((z.2 : Cover) i)^2 := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf1 (z.1.1 i)) (sq_nonneg ((z.2 : Cover) i))
        change (1-((z.2 : Cover) i)^2)*f (z.1.1 i)-f (z.1.1 i)*⟪(z.2 : Cover),F z.1⟫≤_
        dsimp only [F] at ⊢
        nlinarith
    _=K^2*(μ.mass : ℝ)*δ^2 := by
      simp only [integral_const,smul_eq_mul,Measure.real,← FiniteMeasure.ennreal_mass,ENNReal.coe_toReal]
      ring

theorem isMinimizerAt_axial_endpoint_calibration {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3) (b : Bool) :
    axialSectionIntegral (openRepresentative E) i (divergence (axialNormalCalibration N i)) (if b then 1/2 else 0)=
      (μ.mass : ℝ)*axialFluxWeight μ i+
        H*(axialSectionArea (openRepresentative E) i (if b then 1/2 else 0)-V) := by
  have hae := isMinimizerAt_openRepresentative_ae hV hE hm
  have hμo := hμ.congr_ae hae.symm
  have hvol : torusVolume.real (openRepresentative E)=V := by
    rw [Measure.real,measure_congr hae,hm.2.1,ENNReal.toReal_ofReal hV.1.le]
  have hHo : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux (openRepresentative E) D.coordinate D.function := by
    intro D
    rw [directionalFlux_congr_ae hae,hH]
  have hc := isMinimizerAt_continuous_axial_sections hV hE hm hμ hN hp ha hs hsg i
  have hF := axialNormalCalibration_admissible hN hp i
  have hcf := continuous_axialSectionIntegral_of_boundary_null
    (isOpen_openRepresentative E).measurableSet i
    (isMinimizerAt_axial_boundary_null hV hE hm hμ hN hp ha hs hsg i)
    (continuous_divergence hF.1) (divergence_periodic hF.2.1)
  obtain ⟨K,hK⟩ := isMinimizerAt_normal_reflection_rate hV hE hm hμ hN hp ha hs
  apply axial_slice_endpoint_calibration (isOpen_openRepresentative E).measurableSet hvol hμo hHo hN hp ha i hc hcf
    (if b then 1/2 else 0) K.coe_nonneg
  filter_upwards [normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμo,ha] with z hz hzn
  have hh := hK i b z.1 z.1.property hz
  rw [hzn] at hh
  exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialSlicePerimeter (E : Set Torus) (i : Fin 3) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (F : Cover → Cover) (_ : AdmissibleField F) (_ : ∀ x,F x i=0),
    ENNReal.ofReal (axialSectionIntegral E i (divergence F) t)

lemma axialSlicePerimeter_le {E : Set Torus} {i : Fin 3} {t q : ℝ}
    (hb : ∀ (F : Cover → Cover),AdmissibleField F → (∀ x,F x i=0) →
      axialSectionIntegral E i (divergence F) t≤q) :
    axialSlicePerimeter E i t≤ENNReal.ofReal q := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  apply iSup_le
  intro ht
  exact ENNReal.ofReal_le_ofReal (hb F hF ht)

lemma axialSlicePerimeter_ge {E : Set Torus} {i : Fin 3} {t : ℝ}
    {F : Cover → Cover} (hF : AdmissibleField F) (ht : ∀ x,F x i=0) :
    ENNReal.ofReal (axialSectionIntegral E i (divergence F) t)≤axialSlicePerimeter E i t := by
  exact le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le ht le_rfl))

theorem isMinimizerAt_axial_endpoint_perimeter {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3) (b : Bool) :
    axialSlicePerimeter (openRepresentative E) i (if b then 1/2 else 0)=
      ENNReal.ofReal ((μ.mass : ℝ)*axialFluxWeight μ i+
        H*(axialSectionArea (openRepresentative E) i (if b then 1/2 else 0)-V)) := by
  apply le_antisymm
  · apply axialSlicePerimeter_le
    intro F hF ht
    exact isMinimizerAt_axial_slice_endpoint_bound hV hE hm hμ hN hp ha hs hsg hH hF i ht b
  · rw [← isMinimizerAt_axial_endpoint_calibration hV hE hm hμ hN hp ha hs hsg hH i b]
    exact axialSlicePerimeter_ge (axialNormalCalibration_admissible hN hp i) (axialNormalCalibration_axis N i)

lemma axialSlicePerimeter_periodic (E : Set Torus) (i : Fin 3) :
    Function.Periodic (axialSlicePerimeter E i) 1 := by
  intro t
  unfold axialSlicePerimeter
  congr 1
  funext F
  congr 1
  funext hF
  congr 1
  funext ht
  rw [axialSectionIntegral_periodic E i (divergence_periodic hF.2.1)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialTangentialSpeed (i : Fin 3) (z : NormalBundle) : ℝ :=
  ‖axialTangentPart i (z.2 : Cover)‖

lemma continuous_axialTangentialSpeed (i : Fin 3) : Continuous (axialTangentialSpeed i) := by
  exact (continuous_normalUnit.sub
    (((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp continuous_normalUnit).smul continuous_const)).norm

lemma axialTangentialSpeed_sq (i : Fin 3) (z : NormalBundle) :
    (axialTangentialSpeed i z)^2=axialNormalWeight i z := by
  rw [axialTangentialSpeed,axialTangentPart_norm_sq,z.2.property,one_pow]
  rfl

lemma normal_tangent_bound {F : Cover → Cover} (hF : AdmissibleField F)
    (i : Fin 3) (ht : ∀ x,F x i=0) (z : NormalBundle) :
    normalTest F hF.1.continuous z≤axialTangentialSpeed i z := by
  have he : ⟪(z.2 : Cover),F z.1⟫=⟪axialTangentPart i (z.2 : Cover),F z.1⟫ := by
    rw [axialTangentPart,inner_sub_left,real_inner_smul_left]
    simp only [EuclideanSpace.inner_single_left,conj_trivial,ht,mul_zero,sub_zero]
  change ⟪(z.2 : Cover),F z.1⟫≤_
  rw [he]
  exact (real_inner_le_norm _ _).trans
    ((mul_le_mul_of_nonneg_left (hF.2.2 z.1) (norm_nonneg _)).trans_eq (mul_one _))

def axialCircleFlux (E : Set Torus) (i : Fin 3) (F : Cover → Cover) (hF : AdmissibleField F) :
    AddCircle (1 : ℝ) → ℝ :=
  (axialSectionIntegral_periodic E i (divergence_periodic hF.2.1)).lift

lemma axialCircleFlux_coe (E : Set Torus) (i : Fin 3) (F : Cover → Cover) (hF : AdmissibleField F) (t : ℝ) :
    axialCircleFlux E i F hF t=axialSectionIntegral E i (divergence F) t :=
  Function.Periodic.lift_coe _ _

lemma continuous_axialCircleFlux {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    (hz : ∀ t : ℝ,volume {y : Plane | quotientMap ((axialSplit i).symm (t,y))∈frontier E}=0)
    {F : Cover → Cover} (hF : AdmissibleField F) : Continuous (axialCircleFlux E i F hF) :=
  continuous_periodic_lift _ (continuous_axialSectionIntegral_of_boundary_null hE i hz
    (continuous_divergence hF.1) (divergence_periodic hF.2.1))

lemma axialCircleFlux_moment {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {F : Cover → Cover} (hF : AdmissibleField F) (i : Fin 3) (ht : ∀ x,F x i=0)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : Function.Periodic f 1) :
    (∫ t,axialCircleFlux E i F hF t*hp.lift t)=
      ∫ z,normalTest F hF.1.continuous z*hp.lift (axialBundleHeight i z) ∂(μ : Measure NormalBundle) := by
  rw [← AddCircle.intervalIntegral_preimage (1 : ℝ) 0]
  simp only [zero_add,axialCircleFlux_coe,Function.Periodic.lift_coe,axialBundleHeight]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1),← integral_Ico_eq_integral_Ioc,
    axial_slice_flux_moment hE hμ hF i ht hf hp]
  exact integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)

lemma axialCircleFlux_le_density_ae {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    (hz : ∀ t : ℝ,volume {y : Plane | quotientMap ((axialSplit i).symm (t,y))∈frontier E}=0)
    (hac : Measure.map (axialBundleHeight i) (μ : Measure NormalBundle)≪volume)
    {p : AddCircle (1 : ℝ) → ℝ} (hp : Integrable p)
    (hpm : ∀ (f : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) f → ∀ (hper : Function.Periodic f 1),
      (∫ t,p t*hper.lift t)=∫ z,axialTangentialSpeed i z*hper.lift (axialBundleHeight i z) ∂(μ : Measure NormalBundle))
    {F : Cover → Cover} (hF : AdmissibleField F) (ht : ∀ x,F x i=0) :
    axialCircleFlux E i F hF ≤ᵐ[volume] p := by
  apply circle_ae_le_of_ordered_weighted_moments (μ : Measure NormalBundle)
    (continuous_axialBundleHeight i) hac (normalTest F hF.1.continuous).continuous
    (continuous_axialTangentialSpeed i) (normal_tangent_bound hF i ht)
    (circle_continuous_integrable (continuous_axialCircleFlux hE i hz hF)) hp
  · intro f hf hper
    exact axialCircleFlux_moment hE hμ hF i ht hf hper
  · exact hpm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialScaledCalibration (N : Cover → Cover) (i : Fin 3) (n : ℕ) : Cover → Cover :=
  regularizedNormal (fun x => ((n : ℝ)+1) • axialTangentPart i (N x))

lemma axialScaledCalibration_admissible {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) (i : Fin 3) (n : ℕ) :
    AdmissibleField (axialScaledCalibration N i n) := by
  refine ⟨regularizedNormal_contDiff ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Cover => (n : ℝ)+1)).smul (axialTangentPart_contDiff hN i)),?_,?_⟩
  · apply regularizedNormal_periodic
    intro m x
    rw [hp]
  · exact regularizedNormal_norm_le _

lemma axialScaledCalibration_axis (N : Cover → Cover) (i : Fin 3) (n : ℕ) (x : Cover) :
    axialScaledCalibration N i n x i=0 := by
  simp only [axialScaledCalibration,regularizedNormal,PiLp.smul_apply,smul_eq_mul,axialTangentPart_axis,mul_zero]

lemma axialScaledCalibration_error (N : Cover → Cover) (i : Fin 3) (n : ℕ) (x : Cover) :
    ‖axialTangentPart i (N x)‖-⟪N x,axialScaledCalibration N i n x⟫≤1/((n : ℝ)+1) := by
  let c : ℝ := (n : ℝ)+1
  let a : ℝ := ‖axialTangentPart i (N x)‖
  have hc : 0<c := by dsimp [c]; positivity
  have ha : 0≤a := norm_nonneg _
  have hn : ‖c • axialTangentPart i (N x)‖=c*a := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hc]
  have hin : ⟪N x,axialTangentPart i (N x)⟫=a^2 := by
    rw [inner_axialTangentPart,show a^2=‖N x‖^2-(N x i)^2 from axialTangentPart_norm_sq i (N x)]
  have hnonneg : 0≤⟪N x,axialScaledCalibration N i n x⟫ := by
    rw [axialScaledCalibration,regularizedNormal,real_inner_smul_right,real_inner_smul_right,hin]
    have := regularizedNormal_denom_pos (((n : ℝ)+1) • axialTangentPart i (N x))
    positivity
  change a-⟪N x,axialScaledCalibration N i n x⟫≤1/c
  by_cases hh : 1/4≤‖c • axialTangentPart i (N x)‖^2
  · have ha0 : 0<a := by
      rw [hn] at hh
      by_contra h
      have haz : a=0 := le_antisymm (le_of_not_gt h) ha
      rw [haz,mul_zero] at hh
      norm_num at hh
    have he : ⟪N x,axialScaledCalibration N i n x⟫=a := by
      change ⟪N x,regularizedNormal (fun y => c • axialTangentPart i (N y)) x⟫=a
      rw [regularizedNormal_eq (R := fun y => c • axialTangentPart i (N y)) (x := x) hh,real_inner_smul_right,real_inner_smul_right,hin,hn]
      field_simp [hc.ne',ha0.ne']
    rw [he,sub_self]
    positivity
  · have hca : c*a≤1 := by
      rw [hn] at hh
      have hca0 := mul_nonneg hc.le ha
      nlinarith
    have hal : a≤1/c := (le_div_iff₀ hc).mpr (by nlinarith)
    linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

theorem ae_iSup_le_of_lowerSemicontinuous {X : Type*} {ι : Sort*}
    [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X]
    {μ : Measure X} {f : ι → X → ℝ≥0∞} {g : X → ℝ≥0∞}
    (hc : ∀ i,LowerSemicontinuous (f i)) (hb : ∀ i,f i ≤ᵐ[μ] g) :
    (fun x => ⨆ i,f i x) ≤ᵐ[μ] g := by
  have hlub : IsLUB (range f) (fun x => ⨆ i,f i x) := by
    refine ⟨?_,?_⟩
    · rintro v ⟨i,rfl⟩ x
      exact le_iSup (f := fun i => f i x) i
    · intro b hbb x
      exact iSup_le fun i => hbb ⟨i,rfl⟩ x
  obtain ⟨S,hS,hSc,hSlub⟩ := exists_countable_lowerSemicontinuous_isLUB
    (fun v hv => by obtain ⟨i,rfl⟩ := hv; exact hc i) hlub
  have ha : ∀ᵐ x ∂μ,∀ v∈S,v x≤g x := (ae_ball_iff hSc).mpr (by
    intro v hv
    obtain ⟨i,rfl⟩ := hS hv
    exact hb i)
  filter_upwards [ha] with x hx
  apply (isLUB_pi.mp hSlub x).2
  rintro a ⟨v,hv,rfl⟩
  exact hx v hv

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialCirclePerimeter (E : Set Torus) (i : Fin 3) : AddCircle (1 : ℝ) → ℝ≥0∞ :=
  (axialSlicePerimeter_periodic E i).lift

lemma axialCirclePerimeter_coe (E : Set Torus) (i : Fin 3) (t : ℝ) :
    axialCirclePerimeter E i t=axialSlicePerimeter E i t :=
  Function.Periodic.lift_coe _ _

lemma axialCirclePerimeter_eq_iSup (E : Set Torus) (i : Fin 3) :
    axialCirclePerimeter E i=fun t => ⨆ (F : Cover → Cover) (hF : AdmissibleField F)
      (_ : ∀ x,F x i=0),ENNReal.ofReal (axialCircleFlux E i F hF t) := by
  funext t
  induction t using QuotientAddGroup.induction_on with | H u =>
    simp only [axialCirclePerimeter_coe,axialCircleFlux_coe,axialSlicePerimeter]

lemma lowerSemicontinuous_axialCirclePerimeter {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    (hz : ∀ t : ℝ,volume {y : Plane | quotientMap ((axialSplit i).symm (t,y))∈frontier E}=0) :
    LowerSemicontinuous (axialCirclePerimeter E i) := by
  rw [axialCirclePerimeter_eq_iSup]
  apply lowerSemicontinuous_iSup
  intro F
  apply lowerSemicontinuous_iSup
  intro hF
  apply lowerSemicontinuous_iSup
  intro ht
  exact (ENNReal.continuous_ofReal.comp (continuous_axialCircleFlux hE i hz hF)).lowerSemicontinuous

theorem axialCirclePerimeter_le_density_ae {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    (hz : ∀ t : ℝ,volume {y : Plane | quotientMap ((axialSplit i).symm (t,y))∈frontier E}=0)
    (hac : Measure.map (axialBundleHeight i) (μ : Measure NormalBundle)≪volume)
    {p : AddCircle (1 : ℝ) → ℝ} (hp : Integrable p)
    (hpm : ∀ (f : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) f → ∀ (hper : Function.Periodic f 1),
      (∫ t,p t*hper.lift t)=∫ z,axialTangentialSpeed i z*hper.lift (axialBundleHeight i z) ∂(μ : Measure NormalBundle)) :
    axialCirclePerimeter E i ≤ᵐ[volume] fun t => ENNReal.ofReal (p t) := by
  rw [axialCirclePerimeter_eq_iSup]
  apply ae_iSup_le_of_lowerSemicontinuous
  · intro F
    apply lowerSemicontinuous_iSup
    intro hF
    apply lowerSemicontinuous_iSup
    intro ht
    exact (ENNReal.continuous_ofReal.comp (continuous_axialCircleFlux hE i hz hF)).lowerSemicontinuous
  intro F
  apply ae_iSup_le_of_lowerSemicontinuous
  · intro hF
    apply lowerSemicontinuous_iSup
    intro ht
    exact (ENNReal.continuous_ofReal.comp (continuous_axialCircleFlux hE i hz hF)).lowerSemicontinuous
  intro hF
  apply ae_iSup_le_of_lowerSemicontinuous
  · intro ht
    exact (ENNReal.continuous_ofReal.comp (continuous_axialCircleFlux hE i hz hF)).lowerSemicontinuous
  intro ht
  exact (axialCircleFlux_le_density_ae hE hμ i hz hac hp hpm hF ht).mono
    fun t ht => ENNReal.ofReal_le_ofReal ht

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialScaledCalibration_integral_error {μ : FiniteMeasure NormalBundle}
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (i : Fin 3) (n : ℕ) :
    (∫ z,axialTangentialSpeed i z ∂(μ : Measure NormalBundle))≤
      (∫ z,normalTest (axialScaledCalibration N i n)
        (axialScaledCalibration_admissible hN hp i n).1.continuous z ∂(μ : Measure NormalBundle))+
      (μ : Measure NormalBundle).real univ/((n : ℝ)+1) := by
  let F := axialScaledCalibration N i n
  have hF : AdmissibleField F := axialScaledCalibration_admissible hN hp i n
  have hiS : Integrable (axialTangentialSpeed i) (μ : Measure NormalBundle) :=
    (continuous_axialTangentialSpeed i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiF : Integrable (normalTest F hF.1.continuous) (μ : Measure NormalBundle) :=
    (normalTest F hF.1.continuous).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hb : (∫ z,axialTangentialSpeed i z ∂(μ : Measure NormalBundle))≤
      ∫ z,normalTest F hF.1.continuous z+1/((n : ℝ)+1) ∂(μ : Measure NormalBundle) := by
    apply integral_mono_ae hiS (hiF.add (integrable_const _))
    filter_upwards [ha] with z hz
    have he := axialScaledCalibration_error N i n z.1
    rw [hz] at he
    change ‖axialTangentPart i (z.2 : Cover)‖≤⟪(z.2 : Cover),F z.1⟫+1/((n : ℝ)+1)
    dsimp only [F]
    linarith
  rw [integral_add hiF (integrable_const _),integral_const,smul_eq_mul] at hb
  simpa only [mul_one_div] using hb

lemma axialCircleFlux_integral {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {F : Cover → Cover} (hF : AdmissibleField F) (i : Fin 3) (ht : ∀ x,F x i=0) :
    (∫ t,axialCircleFlux E i F hF t)=
      ∫ z,normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle) := by
  have hp : Function.Periodic (fun _ : ℝ => (1 : ℝ)) 1 := fun _ => rfl
  have he := axialCircleFlux_moment hE hμ hF i ht contDiff_const hp
  have hp1 (t : AddCircle (1 : ℝ)) : hp.lift t=1 := by
    induction t using QuotientAddGroup.induction_on with | H u => rfl
  simpa only [hp1,mul_one] using he

lemma axialCircleFlux_le_toReal_ae {E : Set Torus} {i : Fin 3}
    (hfin : ∀ᵐ t,axialCirclePerimeter E i t≠∞)
    {F : Cover → Cover} (hF : AdmissibleField F) (ht : ∀ x,F x i=0) :
    axialCircleFlux E i F hF ≤ᵐ[volume] fun t => (axialCirclePerimeter E i t).toReal := by
  filter_upwards [hfin] with t htt
  apply (ENNReal.ofReal_le_iff_le_toReal htt).mp
  have hsup := congrFun (axialCirclePerimeter_eq_iSup E i) t
  rw [hsup]
  exact le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le ht le_rfl))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem axial_bv_coarea {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hpN : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (i : Fin 3)
    (hz : ∀ t : ℝ,volume {y : Plane | quotientMap ((axialSplit i).symm (t,y))∈frontier E}=0)
    (hac : Measure.map (axialBundleHeight i) (μ : Measure NormalBundle)≪volume) :
    Measurable (axialCirclePerimeter E i) ∧
    (∀ᵐ t,axialCirclePerimeter E i t≠∞) ∧
    Integrable (fun t => (axialCirclePerimeter E i t).toReal) ∧
    ∀ f : AddCircle (1 : ℝ) → ℝ,Measurable f →
      (∫ t,(axialCirclePerimeter E i t).toReal*f t)=
        ∫ z,axialTangentialSpeed i z*f (axialBundleHeight i z) ∂(μ : Measure NormalBundle) := by
  obtain ⟨p,hp,hp0,hpm⟩ := circle_nonneg_weighted_density (μ : Measure NormalBundle)
    (continuous_axialBundleHeight i) hac (continuous_axialTangentialSpeed i)
    (fun z => norm_nonneg _)
  have hb := axialCirclePerimeter_le_density_ae hE hμ i hz hac hp
    (fun f hf hper => hpm hper.lift (continuous_periodic_lift hper hf.continuous).measurable)
  have hfin : ∀ᵐ t,axialCirclePerimeter E i t≠∞ :=
    hb.mono fun t ht => ne_top_of_le_ne_top ENNReal.ofReal_ne_top ht
  have hmeas : Measurable (axialCirclePerimeter E i) :=
    (lowerSemicontinuous_axialCirclePerimeter hE i hz).measurable
  have hreal : (fun t => (axialCirclePerimeter E i t).toReal) ≤ᵐ[volume] p := by
    filter_upwards [hb] with t ht
    have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
    simpa only [ENNReal.toReal_ofReal (hp0 t)] using he
  have hPi : Integrable (fun t => (axialCirclePerimeter E i t).toReal) := by
    apply hp.mono' hmeas.ennreal_toReal.aestronglyMeasurable
    filter_upwards [hreal] with t ht
    simpa only [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg] using ht
  have htot : (∫ t,p t)=∫ z,axialTangentialSpeed i z ∂(μ : Measure NormalBundle) := by
    simpa only [mul_one] using hpm (fun _ => 1) measurable_const
  have hlower : (∫ t,p t)≤∫ t,(axialCirclePerimeter E i t).toReal := by
    have hb_n (n : ℕ) : (∫ t,p t)≤(∫ t,(axialCirclePerimeter E i t).toReal)+
        (μ : Measure NormalBundle).real univ/((n : ℝ)+1) := by
      let F := axialScaledCalibration N i n
      have hF : AdmissibleField F := axialScaledCalibration_admissible hN hpN i n
      have ht : ∀ x,F x i=0 := axialScaledCalibration_axis N i n
      have hl := integral_mono_ae
        (circle_continuous_integrable (continuous_axialCircleFlux hE i hz hF)) hPi
        (axialCircleFlux_le_toReal_ae hfin hF ht)
      rw [axialCircleFlux_integral hE hμ hF i ht] at hl
      rw [htot]
      have he := axialScaledCalibration_integral_error hN hpN ha i n
      change (∫ z,normalTest (axialScaledCalibration N i n) hF.1.continuous z ∂(μ : Measure NormalBundle))≤_ at hl
      linarith
    have hlim : Tendsto (fun n : ℕ => (∫ t,(axialCirclePerimeter E i t).toReal)+
        (μ : Measure NormalBundle).real univ/((n : ℝ)+1)) atTop
        (𝓝 (∫ t,(axialCirclePerimeter E i t).toReal)) := by
      have he := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        ((μ : Measure NormalBundle).real univ)
      simpa only [mul_one_div,mul_zero,add_zero] using tendsto_const_nhds.add he
    exact ge_of_tendsto hlim (Eventually.of_forall hb_n)
  have heq : (fun t => (axialCirclePerimeter E i t).toReal) =ᵐ[volume] p :=
    (integral_eq_iff_of_ae_le hPi hp hreal).mp
      (le_antisymm (integral_mono_ae hPi hp hreal) hlower)
  refine ⟨hmeas,hfin,hPi,?_⟩
  intro f hf
  calc
    _=∫ t,p t*f t := integral_congr_ae (heq.mono fun t ht => congrArg (fun a => a*f t) ht)
    _=_ := hpm f hf

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

def CircleSmoothDensity {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (h : α → AddCircle (1 : ℝ)) (w : α → ℝ) (g : AddCircle (1 : ℝ) → ℝ) : Prop :=
  Integrable g ∧ ∀ (f : ℝ → ℝ),ContDiff ℝ (⊤ : ℕ∞) f → ∀ hp : Function.Periodic f 1,
    (∫ t,g t*hp.lift t)=∫ x,w x*hp.lift (h x) ∂μ

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α] [CompactSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {h : α → AddCircle (1 : ℝ)}

omit [TopologicalSpace α] [BorelSpace α] [CompactSpace α] [IsFiniteMeasure μ] in
lemma CircleSmoothDensity.const_mul {w : α → ℝ} {g : AddCircle (1 : ℝ) → ℝ}
    (hd : CircleSmoothDensity μ h w g) (c : ℝ) :
    CircleSmoothDensity μ h (fun x => c*w x) (fun t => c*g t) := by
  refine ⟨hd.1.const_mul c,?_⟩
  intro f hf hp
  simp_rw [mul_assoc]
  rw [integral_const_mul,integral_const_mul,hd.2 f hf hp]

lemma CircleSmoothDensity.add {w u : α → ℝ} {g p : AddCircle (1 : ℝ) → ℝ}
    (hd : CircleSmoothDensity μ h w g) (he : CircleSmoothDensity μ h u p)
    (hh : Continuous h) (hw : Continuous w) (hu : Continuous u) :
    CircleSmoothDensity μ h (fun x => w x+u x) (fun t => g t+p t) := by
  refine ⟨hd.1.add he.1,?_⟩
  intro f hf hp
  have hc := continuous_periodic_lift hp hf.continuous
  obtain ⟨M,_,hM⟩ := (isCompact_univ.image hc).isBounded.exists_pos_norm_le
  have hb : ∀ᵐ t : AddCircle (1 : ℝ),‖hp.lift t‖≤M :=
    Eventually.of_forall fun t => hM _ ⟨t,mem_univ _,rfl⟩
  have hwi : Integrable (fun x => w x*hp.lift (h x)) μ :=
    (hw.mul (hc.comp hh)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hui : Integrable (fun x => u x*hp.lift (h x)) μ :=
    (hu.mul (hc.comp hh)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [add_mul]
  rw [integral_add (hd.1.mul_bdd hc.aestronglyMeasurable hb)
    (he.1.mul_bdd hc.aestronglyMeasurable hb),integral_add hwi hui,hd.2 f hf hp,he.2 f hf hp]

lemma CircleSmoothDensity.ae_le {w u : α → ℝ} {g p : AddCircle (1 : ℝ) → ℝ}
    (hd : CircleSmoothDensity μ h w g) (he : CircleSmoothDensity μ h u p)
    (hh : Continuous h) (hac : Measure.map h μ≪volume)
    (hw : Continuous w) (hu : Continuous u) (hle : ∀ x,w x≤u x) : g≤ᵐ[volume]p :=
  circle_ae_le_of_ordered_weighted_moments μ hh hac hw hu hle hd.1 he.1 hd.2 he.2

lemma ae_forall_of_closed_parameters {δ β : Type*} [MeasurableSpace δ]
    (ν : Measure δ) [TopologicalSpace β] [TopologicalSpace.SeparableSpace β] [Nonempty β]
    {P : β → δ → Prop} (hc : ∀ x,IsClosed {b | P b x})
    (hp : ∀ b,∀ᵐ x ∂ν,P b x) : ∀ᵐ x ∂ν,∀ b,P b x := by
  have hh : ∀ᵐ x ∂ν,∀ n : ℕ,P (TopologicalSpace.denseSeq β n) x := ae_all_iff.mpr (fun n => hp _)
  exact hh.mono fun x hx => isClosed_property (TopologicalSpace.denseRange_denseSeq β) (hc x) hx

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

def sliceHalfAngle (x : ℝ) : ℝ := x/(1+Real.sqrt (1-x^2))
def sliceHalfAngleSlope (x : ℝ) : ℝ :=
  1/(Real.sqrt (1-x^2)*(1+Real.sqrt (1-x^2)))

lemma sqrt_one_sub_sq_pos {x : ℝ} (hx : x∈Ioo (0 : ℝ) 1) :
    0<Real.sqrt (1-x^2) := by
  apply Real.sqrt_pos.2
  nlinarith [hx.1,hx.2]

lemma hasDerivAt_sliceHalfAngle {x : ℝ} (hx : x∈Ioo (0 : ℝ) 1) :
    HasDerivAt sliceHalfAngle (sliceHalfAngleSlope x) x := by
  have hs := sqrt_one_sub_sq_pos hx
  have hsq : (Real.sqrt (1-x^2))^2=1-x^2 := Real.sq_sqrt (by nlinarith [hx.1,hx.2])
  have hd := ((hasDerivAt_id x).div
    ((hasDerivAt_const x (1 : ℝ)).add
      (((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)).sqrt (by dsimp; nlinarith [hx.1,hx.2])))
    (by positivity : 1+Real.sqrt (1-x^2)≠0))
  convert! hd using 1
  dsimp [sliceHalfAngleSlope]
  field_simp
  nlinarith

lemma continuous_sliceHalfAngle : Continuous sliceHalfAngle := by
  exact continuous_id.div (continuous_const.add
    (Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))))
    (fun x => by positivity)

lemma convexOn_sliceHalfAngle : ConvexOn ℝ (Icc (0 : ℝ) 1) sliceHalfAngle := by
  apply MonotoneOn.convexOn_of_deriv (convex_Icc _ _) continuous_sliceHalfAngle.continuousOn
    (fun x hx => (hasDerivAt_sliceHalfAngle (by simpa using hx)).differentiableAt.differentiableWithinAt)
  intro x hx y hy hxy
  have hx' : x∈Ioo (0 : ℝ) 1 := by simpa using hx
  have hy' : y∈Ioo (0 : ℝ) 1 := by simpa using hy
  rw [(hasDerivAt_sliceHalfAngle hx').deriv,(hasDerivAt_sliceHalfAngle hy').deriv]
  have hsx := sqrt_one_sub_sq_pos hx'
  have hsy := sqrt_one_sub_sq_pos hy'
  have hs : Real.sqrt (1-y^2)≤Real.sqrt (1-x^2) := Real.sqrt_le_sqrt (by nlinarith [hx'.1])
  dsimp [sliceHalfAngleSlope]
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

lemma sliceHalfAngle_support {m x : ℝ} (hm : m∈Ioo (0 : ℝ) 1)
    (hx : x∈Icc (0 : ℝ) 1) :
    sliceHalfAngle m+sliceHalfAngleSlope m*(x-m)≤ sliceHalfAngle x := by
  rcases lt_trichotomy m x with h|h|h
  · have he := convexOn_sliceHalfAngle.deriv_le_slope ⟨hm.1.le,hm.2.le⟩ hx h
      (hasDerivAt_sliceHalfAngle hm).differentiableAt
    rw [(hasDerivAt_sliceHalfAngle hm).deriv,slope_def_field] at he
    have := (le_div_iff₀ (sub_pos.mpr h)).mp he
    linarith
  · subst x
    simp
  · have he := convexOn_sliceHalfAngle.slope_le_deriv hx ⟨hm.1.le,hm.2.le⟩ h
      (hasDerivAt_sliceHalfAngle hm).differentiableAt
    rw [(hasDerivAt_sliceHalfAngle hm).deriv,slope_def_field] at he
    have := (div_le_iff₀ (sub_pos.mpr h)).mp he
    nlinarith

lemma mul_sliceHalfAngle {x : ℝ} (hx : x∈Icc (0 : ℝ) 1) :
    x*sliceHalfAngle x=1-Real.sqrt (1-x^2) := by
  have hs : (Real.sqrt (1-x^2))^2=1-x^2 := Real.sq_sqrt (by nlinarith [hx.1,hx.2])
  dsimp [sliceHalfAngle]
  field_simp
  nlinarith

def sliceSupportC (m J : ℝ) : ℝ :=
  (1-J)*2/m+J*(sliceHalfAngle m-m*sliceHalfAngleSlope m)
def sliceSupportD (m J : ℝ) : ℝ := -(1-J)/m^2+J*sliceHalfAngleSlope m

theorem slice_jensen_support {m J x : ℝ} (hm : m∈Ioo (0 : ℝ) 1)
    (hJ : J∈Icc (0 : ℝ) 1) (hx : x∈Icc (0 : ℝ) 1) :
    sliceSupportC m J*x+sliceSupportD m J*x^2+J*Real.sqrt (1-x^2)≤1 := by
  have ht := mul_le_mul_of_nonneg_left (sliceHalfAngle_support hm hx) (mul_nonneg hJ.1 hx.1)
  have he := mul_sliceHalfAngle hx
  have hb : (1-J)*(2*x/m-x^2/m^2)≤1-J := by
    rw [← div_pow]
    have hz := mul_nonneg (sub_nonneg.mpr hJ.2) (sq_nonneg (x/m-1))
    have heq : 2*x/m=2*(x/m) := by ring
    rw [heq]
    nlinarith
  calc
    _=J*x*(sliceHalfAngle m+sliceHalfAngleSlope m*(x-m))+
        (1-J)*(2*x/m-x^2/m^2)+J*Real.sqrt (1-x^2) := by
      dsimp [sliceSupportC,sliceSupportD]
      ring
    _≤J*x*sliceHalfAngle x+(1-J)+J*Real.sqrt (1-x^2) := by linarith
    _=1 := by rw [mul_assoc,he]; ring

lemma slice_support_contact {m J : ℝ} (hm : m∈Ioo (0 : ℝ) 1) :
    sliceSupportC m J*m+sliceSupportD m J*m^2=1-J*Real.sqrt (1-m^2) := by
  have he := mul_sliceHalfAngle ⟨hm.1.le,hm.2.le⟩
  have hm0 : m≠0 := ne_of_gt hm.1
  dsimp [sliceSupportC,sliceSupportD]
  field_simp
  nlinarith [congrArg (fun t : ℝ => J*t) he]

end CubicTorus

end
end

end OAI
