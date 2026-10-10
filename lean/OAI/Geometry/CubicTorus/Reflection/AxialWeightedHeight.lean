import Mathlib
import OAI.Geometry.CubicTorus.Estimates.CoordinatePlaneRays

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma circle_continuous_integrable {μ : Measure (AddCircle (1 : ℝ))} [IsFiniteMeasure μ]
    {f : AddCircle (1 : ℝ) → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem circle_moment_absolutelyContinuous
    {A B L : Measure (AddCircle (1 : ℝ))}
    [IsFiniteMeasure A] [IsFiniteMeasure B] [IsFiniteMeasure L]
    {H C : ℝ} (hB : B≪L)
    (he : ∀ (f : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) f → ∀ (hp : Function.Periodic f 1),
      (∫ x,hp.lift x ∂A)=H*(∫ x,hp.lift x ∂B)+C*(∫ x,hp.lift x ∂L)) : A≪L := by
  let hp := ENNReal.ofReal (max H 0)
  let hn := ENNReal.ofReal (max (-H) 0)
  let cp := ENNReal.ofReal (max C 0)
  let cn := ENNReal.ofReal (max (-C) 0)
  have hpos (x : ℝ) : 0 ≤ max x 0 := le_max_right _ _
  have hsplit (x : ℝ) : x+max (-x) 0=max x 0 := by
    rcases le_total 0 x with hx|hx
    · rw [max_eq_left hx,max_eq_right (by linarith)]; ring
    · rw [max_eq_right hx,max_eq_left (by linarith)]; ring
  let : IsFiniteMeasure (hp • B) := B.smul_finite ENNReal.ofReal_ne_top
  let : IsFiniteMeasure (hn • B) := B.smul_finite ENNReal.ofReal_ne_top
  let : IsFiniteMeasure (cp • L) := L.smul_finite ENNReal.ofReal_ne_top
  let : IsFiniteMeasure (cn • L) := L.smul_finite ENNReal.ofReal_ne_top
  have hbalance : A+hn • B+cn • L=hp • B+cp • L := by
    apply circle_measure_ext_smooth
    intro f hf hfper
    have hc := continuous_periodic_lift hfper hf.continuous
    have hi (ρ : Measure (AddCircle (1 : ℝ))) [IsFiniteMeasure ρ] : Integrable hfper.lift ρ :=
      circle_continuous_integrable hc
    rw [integral_add_measure (hi _) (hi _),integral_add_measure (hi _) (hi _),
      integral_add_measure (hi _) (hi _)]
    simp only [integral_smul_measure,smul_eq_mul,hp,hn,cp,cn,
      ENNReal.toReal_ofReal (hpos _)]
    rw [he f hf hfper]
    linear_combination (∫ x,hfper.lift x ∂B)*(hsplit H)+
      (∫ x,hfper.lift x ∂L)*(hsplit C)
  intro s hs
  have hb := hB hs
  have hh := congrArg (fun ρ : Measure (AddCircle (1 : ℝ)) => ρ s) hbalance
  simpa only [Measure.add_apply,Measure.smul_apply,hb,hs,smul_eq_mul,mul_zero,add_zero] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

def axialBundleHeight (i : Fin 3) (z : NormalBundle) : AddCircle (1 : ℝ) := z.1.1 i

def axialCoverHeight (i : Fin 3) (x : Cover) : AddCircle (1 : ℝ) := x i

lemma continuous_axialBundleHeight (i : Fin 3) : Continuous (axialBundleHeight i) :=
  (AddCircle.continuous_mk' (1 : ℝ)).comp
    ((PiLp.continuous_apply _ _ i).comp (continuous_subtype_val.comp continuous_fst))

lemma continuous_axialCoverHeight (i : Fin 3) : Continuous (axialCoverHeight i) :=
  (AddCircle.continuous_mk' (1 : ℝ)).comp (PiLp.continuous_apply _ _ i)

def axialWeightedHeight (μ : FiniteMeasure NormalBundle) (i : Fin 3) : Measure (AddCircle (1 : ℝ)) :=
  Measure.map (axialBundleHeight i)
    ((μ : Measure NormalBundle).withDensity (fun z => ENNReal.ofReal (axialNormalWeight i z)))

instance axialWeightedHeight_finite (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    IsFiniteMeasure (axialWeightedHeight μ i) := by
  let := isFiniteMeasure_withDensity_ofReal (integrable_axialNormalWeight μ i).hasFiniteIntegral
  unfold axialWeightedHeight
  infer_instance

def axialVolumeHeight (E : Set Torus) (i : Fin 3) : Measure (AddCircle (1 : ℝ)) :=
  Measure.map (axialCoverHeight i) (volume.restrict (fundamentalCube∩quotientMap ⁻¹' E))

instance axialVolumeHeight_finite (E : Set Torus) (i : Fin 3) :
    IsFiniteMeasure (axialVolumeHeight E i) := by
  unfold axialVolumeHeight
  infer_instance

lemma axialVolumeHeight_le (E : Set Torus) (i : Fin 3) :
    axialVolumeHeight E i≤volume := by
  have hmp := (torus_coordinate_measurePreserving i).comp quotientMap_measurePreserving
  have he : Measure.map (axialCoverHeight i) (volume.restrict fundamentalCube)=volume := hmp.map_eq
  rw [← he]
  exact Measure.map_mono (Measure.restrict_mono_set _ inter_subset_left)
    (continuous_axialCoverHeight i).measurable

lemma integral_axialWeightedHeight (μ : FiniteMeasure NormalBundle) (i : Fin 3)
    {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    (∫ x,hp.lift x ∂axialWeightedHeight μ i)=
      ∫ z,f (z.1.1 i)*axialNormalWeight i z ∂(μ : Measure NormalBundle) := by
  rw [axialWeightedHeight,integral_map (continuous_axialBundleHeight i).measurable.aemeasurable
    (continuous_periodic_lift hp hf).aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      (continuous_axialNormalWeight i).measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [ENNReal.toReal_ofReal (axialNormalWeight_nonneg i z),smul_eq_mul,mul_comm]
    rfl

lemma integral_axialVolumeHeight (E : Set Torus) (i : Fin 3)
    {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    (∫ x,hp.lift x ∂axialVolumeHeight E i)=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x i) := by
  rw [axialVolumeHeight,integral_map (continuous_axialCoverHeight i).measurable.aemeasurable
    (continuous_periodic_lift hp hf).aestronglyMeasurable]
  rfl

theorem axialWeightedHeight_absolutelyContinuous {E : Set Torus}
    {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3) :
    axialWeightedHeight μ i≪volume := by
  apply circle_moment_absolutelyContinuous
    (B := axialVolumeHeight E i) (H := H)
    (C := (∫ z,axialNormalWeight i z ∂(μ : Measure NormalBundle))-
      H*volume.real (fundamentalCube∩quotientMap ⁻¹' E))
    (Measure.absolutelyContinuous_of_le (axialVolumeHeight_le E i))
  intro f hf hp
  rw [integral_axialWeightedHeight μ i hf.continuous hp,
    integral_axialVolumeHeight E i hf.continuous hp]
  have hc := AddCircle.intervalIntegral_preimage (1 : ℝ) 0 hp.lift
  simp only [zero_add,Function.Periodic.lift_coe] at hc
  rw [← hc]
  simpa only [mul_comm] using axial_flux_moment hH i hf hp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_spatialNormalMeasure_noAtoms {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    NullSingletonClass (spatialNormalMeasure μ : Measure Torus) := by
  obtain ⟨R,A,hR,hA,hu⟩ := isMinimizerAt_perimeter_upper_density hV hE hm
  exact ⟨singleton_null_of_quadratic_upper_density (spatialNormalMeasure μ) hR (hu μ hμ)⟩

def axialCriticalLift (E : Set Torus) (N : Cover → Cover) (i : Fin 3) : Set Cover :=
  {x | quotientMap x∈frontier (openRepresentative E) ∧ ∀ j : Fin 3,j≠i → N x j=0}

theorem isMinimizerAt_countable_axialCriticalLift {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    (i : Fin 3) : (axialCriticalLift E N i).Countable := by
  let a (k : Fin 3 → ℤ) : Cover := WithLp.toLp 2 (fun j => (k j : ℝ)/2)
  let L (k : Fin 3 → ℤ) (t : ℝ) : Cover := a k+t • EuclideanSpace.single i 1
  let T (k : Fin 3 → ℤ) : Set ℝ := {t | quotientMap (L k t)∈frontier (openRepresentative E)}
  have ht (k) : (T k).Countable :=
    isMinimizerAt_countable_axial_boundary hV hE hm hμ hN hp ha hs hsg (a k) i
  apply (Set.countable_iUnion (fun k : Fin 3 → ℤ => (ht k).image (L k))).mono
  intro x hx
  have hk : ∀ j : Fin 3,∃ k : ℤ,j=i ∨ x j=(k : ℝ)/2 := by
    intro j
    by_cases hji : j=i
    · exact ⟨0,Or.inl hji⟩
    have hz : coordinateSine j x=0 := by
      by_contra hzero
      exact (isMinimizerAt_normal_nonzero_off_seam hV hE hm hμ hN hp ha hs hsg hx.1 j hzero) (hx.2 j hji)
    obtain ⟨k,hk⟩ := Real.sin_eq_zero_iff.mp hz
    refine ⟨k,Or.inr ?_⟩
    dsimp [coordinateSine] at hk
    nlinarith [Real.pi_pos]
  choose k hk using hk
  have he : L k (x i-a k i)=x := by
    ext j
    change a k j+(x i-a k i)*(EuclideanSpace.single i 1 : Cover) j=x j
    by_cases hji : j=i
    · subst j; simp
    · rw [PiLp.single_apply,ite_eq_right hji,mul_zero,add_zero]
      exact (hk j).resolve_left hji |>.symm
  apply mem_iUnion.mpr
  exact ⟨k,⟨x i-a k i,by change quotientMap (L k (x i-a k i))∈frontier (openRepresentative E); rw [he]; exact hx.1,he⟩⟩

lemma axialNormalWeight_zero_coordinates (i : Fin 3) (z : NormalBundle)
    (hz : axialNormalWeight i z=0) : ∀ j : Fin 3,j≠i → (z.2 : Cover) j=0 := by
  have hn : (∑ j : Fin 3,((z.2 : Cover) j)^2)=1 := by
    rw [← EuclideanSpace.real_norm_sq_eq,z.2.property,one_pow]
  have hi : ((z.2 : Cover) i)^2=1 := by dsimp [axialNormalWeight] at hz; linarith
  intro j hji
  have hh : ((z.2 : Cover) i)^2+((z.2 : Cover) j)^2≤1 := by
    apply le_trans (b := ∑ k : Fin 3,((z.2 : Cover) k)^2) ?_ hn.le
    have he : (∑ k∈({i,j} : Finset (Fin 3)),((z.2 : Cover) k)^2)=
        ((z.2 : Cover) i)^2+((z.2 : Cover) j)^2 := by simp [Ne.symm hji]
    rw [← he]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => sq_nonneg _)
  rw [hi] at hh
  nlinarith [sq_nonneg ((z.2 : Cover) j)]

theorem isMinimizerAt_axialNormalWeight_pos_ae {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    (i : Fin 3) : ∀ᵐ z ∂(μ : Measure NormalBundle),0<axialNormalWeight i z := by
  let K := quotientMap '' axialCriticalLift E N i
  have hK : K.Countable :=
    (isMinimizerAt_countable_axialCriticalLift hV hE hm hμ hN hp ha hs hsg i).image _
  let := isMinimizerAt_spatialNormalMeasure_noAtoms hV hE hm hμ
  have hz : (spatialNormalMeasure μ : Measure Torus) K=0 := hK.measure_zero _
  have hae : ∀ᵐ a ∂(spatialNormalMeasure μ : Measure Torus),a∉K := by
    rw [ae_iff]; simpa only [not_not,Set.ofPred_mem_eq] using hz
  have haf := ae_of_ae_map normalProjection_continuous.measurable.aemeasurable hae
  have hb := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet
    (hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hm).symm)
  filter_upwards [haf,ha,hb] with z hz hn hbz
  apply lt_of_le_of_ne (axialNormalWeight_nonneg i z)
  intro hzero
  apply hz
  refine ⟨z.1,⟨hbz,?_⟩,rfl⟩
  intro j hji
  rw [hn]
  exact axialNormalWeight_zero_coordinates i z hzero.symm j hji

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

theorem axialHeight_absolutelyContinuous {E : Set Torus}
    {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3)
    (hpos : ∀ᵐ z ∂(μ : Measure NormalBundle),0<axialNormalWeight i z) :
    Measure.map (axialBundleHeight i) (μ : Measure NormalBundle)≪volume := by
  have hw : (μ : Measure NormalBundle)≪
      (μ : Measure NormalBundle).withDensity (fun z => ENNReal.ofReal (axialNormalWeight i z)) :=
    withDensity_absolutelyContinuous'
      (continuous_axialNormalWeight i).measurable.ennreal_ofReal.aemeasurable
      (hpos.mono fun z hz => (ENNReal.ofReal_pos.mpr hz).ne')
  exact (hw.map (continuous_axialBundleHeight i).measurable).trans
    (axialWeightedHeight_absolutelyContinuous hH i)

theorem isMinimizerAt_axialHeight_absolutelyContinuous {V : ℝ} (hV : V∈Ioo 0 1)
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
      H*directionalFlux E D.coordinate D.function) (i : Fin 3) :
    Measure.map (axialBundleHeight i) (μ : Measure NormalBundle)≪volume :=
  axialHeight_absolutelyContinuous hH i
    (isMinimizerAt_axialNormalWeight_pos_ae hV hE hm hμ hN hp ha hs hsg i)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma absolutelyContinuous_congrOn {u w : ℝ → ℝ} {a b : ℝ}
    (hw : AbsolutelyContinuousOnInterval w a b) (he : EqOn u w (uIcc a b)) :
    AbsolutelyContinuousOnInterval u a b := by
  rw [absolutelyContinuousOnInterval_iff] at hw ⊢
  intro ε hε
  obtain ⟨δ,hδ,h⟩ := hw ε hε
  refine ⟨δ,hδ,?_⟩
  intro E hE hlen
  convert h E hE hlen using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [he (hE.1 i hi).1,he (hE.1 i hi).2]

lemma integral_compact_eq_interval {f ψ : ℝ → ℝ} {a b : ℝ} (hab : a≤b)
    (hs : tsupport ψ ⊆ Ioo a b) :
    (∫ t in a..b,f t*ψ t)=∫ t,f t*ψ t := by
  rw [intervalIntegral.integral_of_le hab]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  rw [image_eq_zero_of_notMem_tsupport (fun hx => ht (Ioo_subset_Ioc_self (hs hx))),mul_zero]

theorem absolutelyContinuous_of_integrable_weak_derivative {u v : ℝ → ℝ}
    (hu : Continuous u) {a b : ℝ} (hab : a<b)
    (hv : IntegrableOn v (Icc a b))
    (hweak : ∀ ψ : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → tsupport ψ ⊆ Ioo a b →
      (∫ t,u t*deriv ψ t)=-(∫ t,v t*ψ t)) :
    AbsolutelyContinuousOnInterval u a b := by
  let g : ℝ → ℝ := (Icc a b).indicator v
  have hg : Integrable g := hv.integrable_indicator measurableSet_Icc
  let F : ℝ → ℝ := fun t => ∫ s in a..t,g s
  have hF : Continuous F := intervalIntegral.continuous_primitive (fun c d => hg.intervalIntegrable) a
  have hFac : AbsolutelyContinuousOnInterval F a b :=
    hg.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hd : ∀ᵐ t, t∈uIcc a b → deriv F t=g t := by
    filter_upwards [hg.intervalIntegrable.ae_hasDerivAt_integral (a := a) (b := b)] with t ht htab
    exact (ht htab a (by simp)).deriv
  have hz : ∀ ψ : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → tsupport ψ ⊆ Ioo a b →
      (∫ t,(u t-F t)*deriv ψ t)=0 := by
    intro ψ hψ hs
    have hsc : HasCompactSupport ψ := isCompact_Icc.of_isClosed_subset isClosed_closure
      (hs.trans Ioo_subset_Icc_self)
    have hiu : Integrable (fun t => u t*deriv ψ t) :=
      (hu.mul (hψ.continuous_deriv (by simp))).integrable_of_hasCompactSupport hsc.deriv.mul_left
    have hiF : Integrable (fun t => F t*deriv ψ t) :=
      (hF.mul (hψ.continuous_deriv (by simp))).integrable_of_hasCompactSupport hsc.deriv.mul_left
    have hacψ : AbsolutelyContinuousOnInterval ψ a b :=
      (hψ.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
    have hparts := hFac.integral_mul_deriv_eq_deriv_mul hacψ
    have hψa : ψ a=0 := image_eq_zero_of_notMem_tsupport (fun h => (hs h).1.false)
    have hψb : ψ b=0 := image_eq_zero_of_notMem_tsupport (fun h => (hs h).2.false)
    have hsd : tsupport (deriv ψ) ⊆ Ioo a b := (tsupport_deriv_subset (f := ψ)).trans hs
    rw [hψa,hψb,mul_zero,mul_zero,sub_self,zero_sub,
      integral_compact_eq_interval hab.le hsd] at hparts
    have hr : (∫ t in a..b,deriv F t*ψ t)=∫ t,v t*ψ t := by
      calc
        _ = ∫ t in a..b,g t*ψ t := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [hd] with t ht htab
          rw [ht (uIoc_subset_uIcc htab)]
        _ = ∫ t in a..b,v t*ψ t := by
          apply intervalIntegral.integral_congr
          intro t ht
          change g t*ψ t=v t*ψ t
          rw [show g t=v t from indicator_of_mem (by simpa [uIcc_of_le hab.le] using ht) v]
        _ = _ := integral_compact_eq_interval hab.le hs
    rw [hr] at hparts
    simp_rw [sub_mul]
    rw [integral_sub hiu hiF,hweak ψ hψ hs,hparts,sub_self]
  let c := (a+b)/2
  have hc : c∈Ioo a b := by dsimp [c]; constructor <;> linarith
  have he : EqOn u (fun t => F t+(u c-F c)) (Ioo a b) := by
    intro t ht
    have hh := continuous_constant_of_weak_derivative_zero (hu.sub hF) ht hc hz
    change u t-F t=u c-F c at hh
    linarith
  have hec : EqOn u (fun t => F t+(u c-F c)) (Icc a b) := by
    rw [← closure_Ioo hab.ne]
    exact he.closure hu (hF.add continuous_const)
  exact absolutelyContinuous_congrOn
    (hFac.fun_add (contDiff_const.contDiffOn.absolutelyContinuousOnInterval))
    (by simpa [uIcc_of_le hab.le] using hec)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma circlePeriodize_unit_eventuallyEq {f : ℝ → ℝ}
    (hc : HasCompactSupport f) (hs : tsupport f⊆Ioo (0 : ℝ) 1)
    {x : ℝ} (hx : x∈Icc (0 : ℝ) 1) : circlePeriodize f =ᶠ[𝓝 x] f := by
  apply circlePeriodize_eventuallyEq hc (a := 1/2)
  · convert hs using 1; norm_num
  · convert hx using 1; norm_num

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma circle_weighted_density_nonneg {α : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [BorelSpace α] [CompactSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    {h : α → AddCircle (1 : ℝ)} (hh : Continuous h)
    (hac : Measure.map h μ≪volume) {w : α → ℝ} (hw : Continuous w)
    (hw0 : ∀ x,0≤w x) :
    ∃ g : AddCircle (1 : ℝ) → ℝ,Integrable g ∧
      ∀ f : AddCircle (1 : ℝ) → ℝ,Continuous f →
       (∫ t,g t*f t)=∫ x,w x*f (h x) ∂μ := by
  let ν := Measure.map h (μ.withDensity (fun x => ENNReal.ofReal (w x)))
  have hwi : Integrable w μ := hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let := isFiniteMeasure_withDensity_ofReal hwi.hasFiniteIntegral
  have hν : ν≪volume :=
    ((withDensity_absolutelyContinuous μ (fun x => ENNReal.ofReal (w x))).map hh.measurable).trans hac
  refine ⟨fun t => (ν.rnDeriv volume t).toReal,Measure.integrable_toReal_rnDeriv,?_⟩
  intro f hf
  rw [integral_toReal_rnDeriv_mul hν]
  dsimp only [ν]
  rw [integral_map hh.measurable.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hw.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (hw0 x),smul_eq_mul]

theorem circle_weighted_density {α : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [BorelSpace α] [CompactSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    {h : α → AddCircle (1 : ℝ)} (hh : Continuous h)
    (hac : Measure.map h μ≪volume) {w : α → ℝ} (hw : Continuous w) :
    ∃ g : AddCircle (1 : ℝ) → ℝ,Integrable g ∧
      ∀ f : AddCircle (1 : ℝ) → ℝ,Continuous f →
       (∫ t,g t*f t)=∫ x,w x*f (h x) ∂μ := by
  obtain ⟨p,hp,hpm⟩ := circle_weighted_density_nonneg μ hh hac
    (hw.max continuous_const) (fun x => le_max_right (w x) 0)
  obtain ⟨q,hq,hqm⟩ := circle_weighted_density_nonneg μ hh hac
    (hw.neg.max continuous_const) (fun x => le_max_right (-w x) 0)
  refine ⟨fun t => p t-q t,hp.sub hq,?_⟩
  intro f hf
  obtain ⟨M,_,hM⟩ := (isCompact_univ.image hf).isBounded.exists_pos_norm_le
  have hbound : ∀ᵐ t : AddCircle (1 : ℝ),‖f t‖≤M :=
    Eventually.of_forall fun t => hM _ ⟨t,mem_univ _,rfl⟩
  have hip : Integrable (fun t => p t*f t) := hp.mul_bdd hf.aestronglyMeasurable hbound
  have hiq : Integrable (fun t => q t*f t) := hq.mul_bdd hf.aestronglyMeasurable hbound
  have hwpf : Integrable (fun x => max (w x) 0*f (h x)) μ :=
    ((hw.max continuous_const).mul (hf.comp hh)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hwqf : Integrable (fun x => max (-w x) 0*f (h x)) μ :=
    ((hw.neg.max continuous_const).mul (hf.comp hh)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [sub_mul]
  rw [integral_sub hip hiq,hpm f hf,hqm f hf]
  simp only [Pi.neg_apply]
  rw [← integral_sub hwpf hwqf]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [← sub_mul,show max (w x) 0-max (-w x) 0=w x by
      rcases le_total 0 (w x) with h|h
      · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h),sub_zero]
      · rw [max_eq_right h,max_eq_left (neg_nonneg.mpr h)]; ring]

lemma circle_integrable_preimage_Icc {g : AddCircle (1 : ℝ) → ℝ} (hg : Integrable g)
    (a : ℝ) : IntegrableOn (fun t : ℝ => g t) (Icc a (a+1)) := by
  rw [integrableOn_Icc_iff_integrableOn_Ioc]
  exact (AddCircle.measurePreserving_mk (1 : ℝ) a).integrable_comp_of_integrable hg

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma circle_weighted_density_nonneg_measurable {α : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [BorelSpace α] [CompactSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    {h : α → AddCircle (1 : ℝ)} (hh : Continuous h)
    (hac : Measure.map h μ≪volume) {w : α → ℝ} (hw : Continuous w)
    (hw0 : ∀ x,0≤w x) :
    ∃ g : AddCircle (1 : ℝ) → ℝ,Integrable g ∧
      ∀ f : AddCircle (1 : ℝ) → ℝ,Measurable f →
       (∫ t,g t*f t)=∫ x,w x*f (h x) ∂μ := by
  let ν := Measure.map h (μ.withDensity (fun x => ENNReal.ofReal (w x)))
  have hwi : Integrable w μ := hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let := isFiniteMeasure_withDensity_ofReal hwi.hasFiniteIntegral
  have hν : ν≪volume :=
    ((withDensity_absolutelyContinuous μ (fun x => ENNReal.ofReal (w x))).map hh.measurable).trans hac
  refine ⟨fun t => (ν.rnDeriv volume t).toReal,Measure.integrable_toReal_rnDeriv,?_⟩
  intro f hf
  rw [integral_toReal_rnDeriv_mul hν]
  dsimp only [ν]
  rw [integral_map hh.measurable.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hw.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (hw0 x),smul_eq_mul]

theorem circle_weighted_density_bounded {α : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [BorelSpace α] [CompactSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    {h : α → AddCircle (1 : ℝ)} (hh : Continuous h)
    (hac : Measure.map h μ≪volume) {w : α → ℝ} (hw : Continuous w) :
    ∃ g : AddCircle (1 : ℝ) → ℝ,Integrable g ∧
      ∀ f : AddCircle (1 : ℝ) → ℝ,Measurable f → (∃ M : ℝ,∀ t,‖f t‖≤M) →
       (∫ t,g t*f t)=∫ x,w x*f (h x) ∂μ := by
  obtain ⟨p,hp,hpm⟩ := circle_weighted_density_nonneg_measurable μ hh hac
    (hw.max continuous_const) (fun x => le_max_right (w x) 0)
  obtain ⟨q,hq,hqm⟩ := circle_weighted_density_nonneg_measurable μ hh hac
    (hw.neg.max continuous_const) (fun x => le_max_right (-w x) 0)
  refine ⟨fun t => p t-q t,hp.sub hq,?_⟩
  intro f hf ⟨M,hM⟩
  have hbound : ∀ᵐ t : AddCircle (1 : ℝ),‖f t‖≤M :=
    Eventually.of_forall fun t => hM t
  have hip : Integrable (fun t => p t*f t) := hp.mul_bdd hf.aestronglyMeasurable hbound
  have hiq : Integrable (fun t => q t*f t) := hq.mul_bdd hf.aestronglyMeasurable hbound
  have hwpf : Integrable (fun x => max (w x) 0*f (h x)) μ :=
    ((hw.max continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).mul_bdd
        (hf.comp hh.measurable).aestronglyMeasurable (Eventually.of_forall fun x => hM (h x))
  have hwqf : Integrable (fun x => max (-w x) 0*f (h x)) μ :=
    ((hw.neg.max continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).mul_bdd
        (hf.comp hh.measurable).aestronglyMeasurable (Eventually.of_forall fun x => hM (h x))
  simp_rw [sub_mul]
  rw [integral_sub hip hiq,hpm f hf,hqm f hf]
  simp only [Pi.neg_apply]
  rw [← integral_sub hwpf hwqf]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [← sub_mul,show max (w x) 0-max (-w x) 0=w x by
      rcases le_total 0 (w x) with h|h
      · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h),sub_zero]
      · rw [max_eq_right h,max_eq_left (neg_nonneg.mpr h)]; ring]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma circle_integral_withDensity_ofReal {q : AddCircle (1 : ℝ) → ℝ}
    (hq : Integrable q) (hq0 : ∀ t,0≤q t) (f : AddCircle (1 : ℝ) → ℝ) :
    (∫ t,f t ∂volume.withDensity (fun t => ENNReal.ofReal (q t)))=∫ t,q t*f t := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hq.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by dsimp only; rw [ENNReal.toReal_ofReal (hq0 t),smul_eq_mul]

theorem circle_ae_eq_zero_of_smooth_moments {q : AddCircle (1 : ℝ) → ℝ}
    (hq : Integrable q)
    (he : ∀ (f : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) f → ∀ (hp : Function.Periodic f 1),
      (∫ t,q t*hp.lift t)=0) : q =ᵐ[volume] 0 := by
  let p := fun t => max (q t) 0
  let n := fun t => max (-q t) 0
  have hp : Integrable p := hq.pos_part
  have hn : Integrable n := hq.neg_part
  have hp0 (t) : 0≤p t := le_max_right _ _
  have hn0 (t) : 0≤n t := le_max_right _ _
  let P := volume.withDensity (fun t => ENNReal.ofReal (p t))
  let N := volume.withDensity (fun t => ENNReal.ofReal (n t))
  let : IsFiniteMeasure P := isFiniteMeasure_withDensity_ofReal hp.hasFiniteIntegral
  let : IsFiniteMeasure N := isFiniteMeasure_withDensity_ofReal hn.hasFiniteIntegral
  have hsplit (t) : q t+n t=p t := by
    rcases le_total (q t) 0 with h|h
    · simp only [n,p,max_eq_left (neg_nonneg.mpr h),max_eq_right h]; ring
    · simp only [n,p,max_eq_right (neg_nonpos.mpr h),max_eq_left h]; ring
  have hbal : P=N := by
    apply circle_measure_ext_smooth
    intro f hf hper
    change (∫ t,hper.lift t ∂volume.withDensity (fun t => ENNReal.ofReal (p t)))=
      ∫ t,hper.lift t ∂volume.withDensity (fun t => ENNReal.ofReal (n t))
    rw [circle_integral_withDensity_ofReal hp hp0,circle_integral_withDensity_ofReal hn hn0]
    have hfc := continuous_periodic_lift hper hf.continuous
    obtain ⟨M,_,hM⟩ := (isCompact_univ.image hfc).isBounded.exists_pos_norm_le
    have hb : ∀ᵐ t : AddCircle (1 : ℝ),‖hper.lift t‖≤M :=
      Eventually.of_forall fun t => hM _ ⟨t,mem_univ _,rfl⟩
    have hiq := hq.mul_bdd hfc.aestronglyMeasurable hb
    have hin := hn.mul_bdd hfc.aestronglyMeasurable hb
    have hi := integral_add hiq hin
    have hi' : (∫ t,p t*hper.lift t)=(∫ t,q t*hper.lift t)+(∫ t,n t*hper.lift t) := by
      rw [← hi]
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by dsimp only; rw [← add_mul,hsplit]
    rw [hi',he f hf hper,zero_add]
  have hae := (withDensity_eq_iff_of_sigmaFinite hp.aemeasurable.ennreal_ofReal
    hn.aemeasurable.ennreal_ofReal).mp hbal
  filter_upwards [hae] with t ht
  have htt := congrArg ENNReal.toReal ht
  rw [ENNReal.toReal_ofReal (hp0 t),ENNReal.toReal_ofReal (hn0 t)] at htt
  have hh := hsplit t
  change q t=0
  linarith

lemma circle_ae_eq_of_smooth_moments {p q : AddCircle (1 : ℝ) → ℝ}
    (hp : Integrable p) (hq : Integrable q)
    (he : ∀ (f : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) f → ∀ (hper : Function.Periodic f 1),
      (∫ t,p t*hper.lift t)=(∫ t,q t*hper.lift t)) : p =ᵐ[volume] q := by
  have hz : (fun t => p t-q t) =ᵐ[volume] 0 := by
    apply circle_ae_eq_zero_of_smooth_moments (hp.sub hq)
    intro f hf hper
    have hfc := continuous_periodic_lift hper hf.continuous
    obtain ⟨M,_,hM⟩ := (isCompact_univ.image hfc).isBounded.exists_pos_norm_le
    have hb : ∀ᵐ t : AddCircle (1 : ℝ),‖hper.lift t‖≤M :=
      Eventually.of_forall fun t => hM _ ⟨t,mem_univ _,rfl⟩
    change (∫ t,(p t-q t)*hper.lift t)=0
    simp_rw [sub_mul]
    rw [integral_sub (hp.mul_bdd hfc.aestronglyMeasurable hb)
      (hq.mul_bdd hfc.aestronglyMeasurable hb),he f hf hper,sub_self]
  exact hz.mono fun t ht => sub_eq_zero.mp ht

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma circle_nonneg_weighted_density {α : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [BorelSpace α] [CompactSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    {h : α → AddCircle (1 : ℝ)} (hh : Continuous h)
    (hac : Measure.map h μ≪volume) {w : α → ℝ} (hw : Continuous w)
    (hw0 : ∀ x,0≤w x) :
    ∃ g : AddCircle (1 : ℝ) → ℝ,Integrable g ∧ (∀ t,0≤g t) ∧
      ∀ f : AddCircle (1 : ℝ) → ℝ,Measurable f →
       (∫ t,g t*f t)=∫ x,w x*f (h x) ∂μ := by
  let ν := Measure.map h (μ.withDensity (fun x => ENNReal.ofReal (w x)))
  have hwi : Integrable w μ := hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let := isFiniteMeasure_withDensity_ofReal hwi.hasFiniteIntegral
  have hν : ν≪volume :=
    ((withDensity_absolutelyContinuous μ (fun x => ENNReal.ofReal (w x))).map hh.measurable).trans hac
  refine ⟨fun t => (ν.rnDeriv volume t).toReal,Measure.integrable_toReal_rnDeriv,
    fun _ => ENNReal.toReal_nonneg,?_⟩
  intro f hf
  rw [integral_toReal_rnDeriv_mul hν]
  dsimp only [ν]
  rw [integral_map hh.measurable.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hw.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (hw0 x),smul_eq_mul]

theorem circle_ae_le_of_ordered_weighted_moments {α : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [BorelSpace α] [CompactSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    {h : α → AddCircle (1 : ℝ)} (hh : Continuous h)
    (hac : Measure.map h μ≪volume)
    {u w : α → ℝ} (hu : Continuous u) (hw : Continuous w) (huw : ∀ x,u x≤w x)
    {p q : AddCircle (1 : ℝ) → ℝ} (hp : Integrable p) (hq : Integrable q)
    (hpm : ∀ (f : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) f → ∀ (hper : Function.Periodic f 1),
      (∫ t,p t*hper.lift t)=∫ x,u x*hper.lift (h x) ∂μ)
    (hqm : ∀ (f : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) f → ∀ (hper : Function.Periodic f 1),
      (∫ t,q t*hper.lift t)=∫ x,w x*hper.lift (h x) ∂μ) : p ≤ᵐ[volume] q := by
  obtain ⟨r,hr,hr0,hrm⟩ := circle_nonneg_weighted_density μ hh hac (hw.sub hu)
    (fun x => sub_nonneg.mpr (huw x))
  have he : (fun t => q t-p t) =ᵐ[volume] r := by
    apply circle_ae_eq_of_smooth_moments (hq.sub hp) hr
    intro f hf hper
    have hfc := continuous_periodic_lift hper hf.continuous
    obtain ⟨M,_,hM⟩ := (isCompact_univ.image hfc).isBounded.exists_pos_norm_le
    have hb : ∀ᵐ t : AddCircle (1 : ℝ),‖hper.lift t‖≤M :=
      Eventually.of_forall fun t => hM _ ⟨t,mem_univ _,rfl⟩
    change (∫ t,(q t-p t)*hper.lift t)=∫ t,r t*hper.lift t
    simp_rw [sub_mul]
    rw [integral_sub (hq.mul_bdd hfc.aestronglyMeasurable hb)
      (hp.mul_bdd hfc.aestronglyMeasurable hb),hqm f hf hper,hpm f hf hper,
      hrm hper.lift hfc.measurable]
    have hiw : Integrable (fun x => w x*hper.lift (h x)) μ := (hw.mul (hfc.comp hh)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hiu : Integrable (fun x => u x*hper.lift (h x)) μ := (hu.mul (hfc.comp hh)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [← integral_sub hiw hiu]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only [Pi.sub_apply]; ring
  filter_upwards [he] with t ht
  have hh := hr0 t
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

theorem circle_positive_density_of_smooth_moments
    {A : Measure (AddCircle (1 : ℝ))} [IsFiniteMeasure A]
    {q : AddCircle (1 : ℝ) → ℝ} (hq : Continuous q)
    (he : ∀ (f : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) f → ∀ (hp : Function.Periodic f 1),
      (∫ t,hp.lift t ∂A)=∫ t,q t*hp.lift t) :
    (∀ t,0≤q t) ∧ A=volume.withDensity (fun t => ENNReal.ofReal (q t)) := by
  let p : AddCircle (1 : ℝ) → ℝ := fun t => max (q t) 0
  let n : AddCircle (1 : ℝ) → ℝ := fun t => max (-q t) 0
  have hp : Continuous p := hq.max continuous_const
  have hn : Continuous n := hq.neg.max continuous_const
  have hp0 (t) : 0≤p t := le_max_right _ _
  have hn0 (t) : 0≤n t := le_max_right _ _
  let P : Measure (AddCircle (1 : ℝ)) := volume.withDensity (fun t => ENNReal.ofReal (p t))
  let N : Measure (AddCircle (1 : ℝ)) := volume.withDensity (fun t => ENNReal.ofReal (n t))
  let : IsFiniteMeasure P := isFiniteMeasure_withDensity_ofReal
    (circle_continuous_integrable hp).hasFiniteIntegral
  let : IsFiniteMeasure N := isFiniteMeasure_withDensity_ofReal
    (circle_continuous_integrable hn).hasFiniteIntegral
  have hden {w : AddCircle (1 : ℝ) → ℝ} (hw : Continuous w) (hw0 : ∀ t,0≤w t)
      (f : AddCircle (1 : ℝ) → ℝ) :
      (∫ t,f t ∂volume.withDensity (fun t => ENNReal.ofReal (w t)))=∫ t,w t*f t := by
    rw [integral_withDensity_eq_integral_toReal_smul hw.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      dsimp only
      rw [ENNReal.toReal_ofReal (hw0 t),smul_eq_mul]
  have hsplit (t) : q t+n t=p t := by
    rcases le_total (q t) 0 with h|h
    · simp only [n,p,max_eq_left (neg_nonneg.mpr h),max_eq_right h]; ring
    · simp only [n,p,max_eq_right (neg_nonpos.mpr h),max_eq_left h]; ring
  have hbal : A+N=P := by
    apply circle_measure_ext_smooth
    intro f hf hfper
    have hfc := continuous_periodic_lift hfper hf.continuous
    rw [integral_add_measure (circle_continuous_integrable hfc) (circle_continuous_integrable hfc),he f hf hfper]
    change (∫ t,q t*hfper.lift t)+(∫ t,hfper.lift t ∂volume.withDensity (fun t => ENNReal.ofReal (n t)))=
      ∫ t,hfper.lift t ∂volume.withDensity (fun t => ENNReal.ofReal (p t))
    rw [hden hn hn0,hden hp hp0]
    have hiq : Integrable (fun t => q t*hfper.lift t) := circle_continuous_integrable (hq.mul hfc)
    have hin : Integrable (fun t => n t*hfper.lift t) := circle_continuous_integrable (hn.mul hfc)
    have hia := integral_add hiq hin
    change (∫ t,q t*hfper.lift t+n t*hfper.lift t)=
      (∫ t,q t*hfper.lift t)+(∫ t,n t*hfper.lift t) at hia
    rw [← hia]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by dsimp only; rw [← add_mul,hsplit]
  have hzprod (t) : p t*n t=0 := by
    rcases le_total (q t) 0 with h|h
    · simp [p,max_eq_right h]
    · simp [n,max_eq_right (neg_nonpos.mpr h)]
  have htest := congrArg (fun ρ : Measure (AddCircle (1 : ℝ)) => ∫ t,n t ∂ρ) hbal
  rw [integral_add_measure (circle_continuous_integrable hn) (circle_continuous_integrable hn)] at htest
  change (∫ t,n t ∂A)+(∫ t,n t ∂volume.withDensity (fun t => ENNReal.ofReal (n t)))=
    ∫ t,n t ∂volume.withDensity (fun t => ENNReal.ofReal (p t)) at htest
  rw [hden hn hn0,hden hp hp0] at htest
  simp_rw [hzprod] at htest
  rw [integral_zero] at htest
  have hni : 0≤(∫ t,n t ∂A) := integral_nonneg (fun t => hn0 t)
  have hns : 0≤(∫ t,n t*n t) := integral_nonneg (fun t => mul_self_nonneg (n t))
  have hnzero : (∫ t,n t*n t)=0 := by linarith
  have hnae := (integral_eq_zero_iff_of_nonneg (fun t => mul_self_nonneg (n t))
    (circle_continuous_integrable (hn.mul hn))).mp hnzero
  have hzero : n=fun _ => (0 : ℝ) :=
    Measure.eq_of_ae_eq (hnae.mono fun t ht => mul_self_eq_zero.mp ht) hn continuous_const
  have hq0 (t) : 0≤q t := by
    have htt := congrFun hzero t
    have hh : -q t≤n t := le_max_left _ _
    rw [htt] at hh
    linarith
  refine ⟨hq0,?_⟩
  have hNz : N=0 := by
    dsimp only [N]
    simp only [hzero,ENNReal.ofReal_zero]
    exact withDensity_zero
  have hP : P=volume.withDensity (fun t => ENNReal.ofReal (q t)) := by
    dsimp only [P]
    congr 1
    funext t
    rw [show p t=q t from max_eq_left (hq0 t)]
  simpa only [hNz,add_zero,hP] using hbal

end CubicTorus

end
end

end OAI
