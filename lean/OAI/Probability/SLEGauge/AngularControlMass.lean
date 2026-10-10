import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.GlobalAngleBudget
import OAI.Probability.SLEGauge.FutureSupport
import OAI.Probability.SLEGauge.FiniteProductLimit

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEFiniteTilt

 

def angularDensity (a q : ℝ) (j : ℕ) (b : ExactSLEGenerator.Driver) (z : UpperPlane) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-alpha a*Real.log 2)*
    radialTestWeight a (angleLift (sinePower (-q))) b.1 z.1
      (levelRadius a (2*z.1.im) (j+1)))

def angularCompactMass (a q : ℝ) (j : ℕ) (K : Set UpperPlane)
    (b : ExactSLEGenerator.Driver) : ℝ≥0∞ := ∫⁻z in K, angularDensity a q j b z ∂upperArea

lemma angularDensity_measurable (a q : ℝ) (ha : 1/4<a) (j : ℕ) :
    Measurable (Function.uncurry (angularDensity a q j)) := by
  have he (z : UpperPlane) : levelRadius a (2*z.1.im) (j+1)=z.1.im*Real.exp (-2*a*(j+1)) := by
    simp [levelRadius]
  unfold angularDensity Function.uncurry
  simp only [he]
  exact (measurable_const.mul (joint_radialTestWeight_measurable a ha _ (Real.exp_pos _)
      (level_step_le_one a ha j) _ (angleLift_sinePower_measurable (-q)))).ennreal_ofReal

lemma angularCompactMass_measurable (a q : ℝ) (ha : 1/4<a) (j : ℕ) (K : Set UpperPlane) :
    Measurable (angularCompactMass a q j K) := (angularDensity_measurable a q ha j).lintegral_prod_right

lemma angularInitial_continuous (a q C : ℝ) : Continuous (fun z : UpperPlane =>
    physicalGreen a (z.1,0)*(angleLift (sinePower (-q)) (z.1,0)+C)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hsin := Real.sin_pos_of_pos_of_lt_pi (physicalTheta_mem (z.1,0)).1
    (physicalTheta_mem (z.1,0)).2
  have hi : Continuous (fun w : UpperPlane => (w.1,(0:ℝ))) :=
    continuous_subtype_val.prodMk continuous_const
  exact ((contDiffAt_physicalGreen a (z.1,0) z.2).continuousAt.mul
    (((angleLift_smooth (sinePower (-q)) _ z.2 (sinePower_smooth (-q) _ hsin)).continuousAt).add_const C)).comp
      (f := fun w : UpperPlane => (w.1,(0:ℝ))) hi.continuousAt

 
theorem angularCompactMass_uniform_mean (a q : ℝ) (ha : 1/4<a) (hq : 0<q)
    (hqp : q<4*a-1) (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (K : Set UpperPlane) (hK : IsCompact K) :
    ∃ B : ℝ≥0∞, B<∞ ∧ ∀ j, (∫⁻b, angularCompactMass a q j K b ∂W)≤B := by
  obtain ⟨C,hC,hbound⟩ := exists_finite_level_angle_bound a q ha hq hqp
  let A : UpperPlane→ℝ := fun z => physicalGreen a (z.1,0)*
    (angleLift (sinePower (-q)) (z.1,0)+C)
  have hA : Continuous A := angularInitial_continuous a q C
  let R := Real.exp (-alpha a*Real.log 2)
  let B : ℝ≥0∞ := ∫⁻z in K, ENNReal.ofReal (R*A z) ∂upperArea
  have hB : B<∞ := (ContinuousOn.integrableOn_compact (μ := upperArea) hK
    (show ContinuousOn (fun z => R*A z) K from (continuous_const.mul hA).continuousOn)).lintegral_lt_top
  refine ⟨B,hB,?_⟩
  intro j
  have hm := angularDensity_measurable a q ha j
  simp only [angularCompactMass]
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply setLIntegral_mono' hK.measurableSet
  intro z _
  let f : ExactSLEGenerator.Driver→ℝ := fun b =>
    radialTestWeight a (angleLift (sinePower (-q))) b.1 z.1
      (levelRadius a (2*z.1.im) (j+1))
  have hf : Measurable f := by
    have hh := (joint_radialTestWeight_measurable a ha _ (Real.exp_pos _)
      (level_step_le_one a ha j) _ (angleLift_sinePower_measurable (-q))).comp
      (measurable_id.prodMk (measurable_const (a := z)))
    simpa [f,levelRadius,Function.comp_def] using hh
  simp_rw [angularDensity,ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [lintegral_const_mul _ hf.ennreal_ofReal]
  exact (mul_le_mul' le_rfl (hbound W hW z.1 z.2 (j+1) (by positivity))).trans_eq
    (ENNReal.ofReal_mul (Real.exp_pos _).le).symm

 
def convexAngularMass (a q : ℝ) (s : Finset ℕ) (c : ℕ→ℝ)
    (K : Set UpperPlane) (b : ExactSLEGenerator.Driver) : ℝ≥0∞ :=
  ∑j∈s, ENNReal.ofReal (c j)*angularCompactMass a q j K b

lemma convexAngularMass_measurable (a q : ℝ) (ha : 1/4<a) (s : Finset ℕ)
    (c : ℕ→ℝ) (K : Set UpperPlane) : Measurable (convexAngularMass a q s c K) := by
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.mul (angularCompactMass_measurable a q ha j K)

lemma convexAngularMass_mean_bound (a q : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) (K : Set UpperPlane) (B : ℝ≥0∞)
    (hB : ∀ j, (∫⁻b, angularCompactMass a q j K b ∂W)≤B)
    (s : Finset ℕ) (c : ℕ→ℝ) (hc : ∀ j∈s,0≤c j) (hs : ∑ j∈s,c j=1) :
    (∫⁻b, convexAngularMass a q s c K b ∂W)≤B := by
  have hc' : ∑j∈s,ENNReal.ofReal (c j)=1 := by
    rw [←ENNReal.ofReal_sum_of_nonneg hc,hs,ENNReal.ofReal_one]
  simp only [convexAngularMass]
  rw [lintegral_finsetSum s (f := fun j b => ENNReal.ofReal (c j)*angularCompactMass a q j K b) (fun j _ =>
    measurable_const.mul (angularCompactMass_measurable a q ha j K))]
  simp_rw [lintegral_const_mul _ (angularCompactMass_measurable a q ha _ K)]
  exact (Finset.sum_le_sum (fun j _ => mul_le_mul' le_rfl (hB j))).trans_eq (by
    rw [←Finset.sum_mul,hc',one_mul])

 

theorem convexAngularMass_liminf_finite (a q : ℝ) (ha : 1/4<a) (hq : 0<q)
    (hqp : q<4*a-1) (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (K : ℕ→Set UpperPlane) (hK : ∀n,IsCompact (K n)) (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ)
    (hc : ∀ k j,j∈s k→0≤c k j) (hs : ∀k,∑j∈s k,c k j=1) :
    ∀ᵐ b ∂W, ∀ n, liminf (fun k => convexAngularMass a q (s k) (c k) (K n) b) atTop<∞ := by
  apply ae_all_iff.mpr
  intro n
  obtain ⟨B,hB,hBj⟩ := angularCompactMass_uniform_mean a q ha hq hqp W hW (K n) (hK n)
  apply ae_lt_top (Measurable.liminf (fun k =>
    convexAngularMass_measurable a q ha (s k) (c k) (K n)))
  apply ne_top_of_lt
  apply lt_of_le_of_lt (lintegral_liminf_le' (fun k =>
    (convexAngularMass_measurable a q ha (s k) (c k) (K n)).aemeasurable))
  exact (liminf_le_of_frequently_le (Eventually.of_forall (fun k =>
    convexAngularMass_mean_bound a q ha W (K n) B hBj (s k) (c k) (hc k) (hs k))).frequently).trans_lt hB

end ExactSLEGreen
end
end
 

 
section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

 

theorem actual_raw_mass_endpoint (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℕ → ℝ≥0∞) :
    ∃ (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ)
      (hc : ∀ k j, j∈s k → 0≤c k j),
      (∀ k j, j∈s k → k≤j) ∧ (∀ k, ∑ j∈s k, c k j=1) ∧
      let μ := recoveredMass a ha s c hc
      (∀ v b, IsFiniteMeasureOnCompacts (μ v b) ∧ (μ v b).Regular) ∧
      (∀ b, μ 0 b=0) ∧
      (∀ v, Measurable (μ v)) ∧
      IsProgressive rawFiltration (fun v : ℝ≥0 => μ v) ∧
      (∀ i (f : C_c(UpperPlane,ℝ)) (m : ℕ),
        MemLp (fun b => ∫z,f z∂μ (t i) b) (m : ℝ≥0∞) W) ∧
      (∀ i (K : Set UpperPlane), IsCompact K → ∀ m : ℕ,
        MemLp (fun b => (μ (t i) b K).toReal) (m : ℝ≥0∞) W) ∧
      (∀ i (f : C_c(UpperPlane,ℝ)),
        Tendsto (fun k => eLpNorm (fun b =>
          (∑ j∈s k, c k j * ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            - ∫z,f z∂μ (t i) b) 1 W) atTop (𝓝 0)) ∧
      (∀ i, t i=∞ → μ (t i) ∘ₘ W=initialGreenMeasure a) ∧
      (∀ i j (v : ℝ≥0), t i=v → t j=∞ →
        ∀ H : ExactSLEGenerator.Driver × UpperPlane → ℝ≥0∞,
        Measurable[(rawFiltration v).prod (inferInstance : MeasurableSpace UpperPlane)] H →
        (∫⁻b, ∫⁻z, H (b,z) ∂μ (t j) b ∂W) = (∫⁻b, ∫⁻z, H (b,z) ∂μ (t i) b ∂W) +
          ∫⁻b, ∫⁻z, H (b,z) * ENNReal.ofReal (survivingGreen a v b z.1) ∂upperArea ∂W) ∧
      ∀ᵐ b ∂W,
        (∀ i j, t i≤t j → μ (t i) b≤μ (t j) b) ∧
        (∀ i (f : C_c(UpperPlane,ℝ)),
          Tendsto (fun k => ∑ j∈s k, c k j *
            ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            atTop (𝓝 (∫z,f z∂μ (t i) b))) ∧
        (∀ i j, t i≠∞ → t j=∞ →
          (μ (t j) b-μ (t i) b) {z : UpperPlane | ¬alive a b.1 (t i).toNNReal z.1}=0) := by
  obtain ⟨s,c,hc,hs,hsum,hμ,hmeas,hprog,hmom,hL1,hmean,hcond,hH,hconv⟩ :=
    actual_raw_mass_extraction a ha W hW t
  let μ := recoveredMass a ha s c hc
  let (v : ℝ≥0∞) (b : ExactSLEGenerator.Driver) : IsFiniteMeasureOnCompacts (μ v b) :=
    (hμ v b).1
  let K : ℝ≥0∞ → Kernel ExactSLEGenerator.Driver UpperPlane := fun v => ⟨μ v,hmeas v⟩
  have hint (i : ℕ) (f : C_c(UpperPlane,ℝ)) : Integrable (fun b => ∫z,f z∂μ (t i) b) W :=
    memLp_one_iff_integrable.mp (by simpa only [Nat.cast_one] using hmom i f 1)
  have hfut (i j : ℕ) : ∀ᵐ b ∂W, t i≠∞ → t j=∞ →
      (μ (t j) b-μ (t i) b) {z : UpperPlane | ¬alive a b.1 (t i).toNNReal z.1}=0 := by
    by_cases hi : t i=∞
    · exact Eventually.of_forall (fun _ h => False.elim (h hi))
    by_cases hj : t j=∞
    · have hz := conditional_future_support a ha W hW (t i).toNNReal (K (t i)) (K (t j))
        (hint i) (hint j) (by
          filter_upwards [hconv] with b hb
          exact hb.1 i j (by rw [hj]; exact le_top))
        (hcond i j (t i).toNNReal (ENNReal.coe_toNNReal hi).symm hj)
      filter_upwards [hz] with b hb
      exact fun _ _ => hb
    · exact Eventually.of_forall (fun _ _ h => False.elim (hj h))
  refine ⟨s,c,hc,hs,hsum,hμ,recoveredMass_zero a ha s c hc,hmeas,hprog,hmom,?_,hL1,?_,hH,?_⟩
  · intro i A hA m
    exact compact_mass_memLp (K (t i)) W (m : ℝ≥0∞) (fun f => hmom i f m) A hA
  · intro i hi
    exact initialGreenMeasure_eq_average a (K (t i)) W (hint i) (hmean i hi)
  · filter_upwards [hconv,ae_all_iff.mpr (fun i => ae_all_iff.mpr (hfut i))] with b hb hf
    exact ⟨hb.1,hb.2,hf⟩

end ExactSLEGreen
end
 

 
section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain ExactSLEKernel SLEExactGauge.MassVersions

 

def localPairMeasure (α d C : ℝ) (φ : C_c(UpperPlane,ℝ≥0)) : Measure (UpperPlane × UpperPlane) :=
  (upperArea.prod upperArea).withDensity (fun p =>
    (φ p.1:ℝ≥0∞)*(φ p.2:ℝ≥0∞)*(ENNReal.ofReal C*pairKernel α d p))

lemma localPairMeasure_finite (α d C : ℝ) (hα : 0<α) (hα1 : α<1) (hd : 0<d)
    (φ : C_c(UpperPlane,ℝ≥0)) : IsFiniteMeasure (localPairMeasure α d C φ) := by
  let K := tsupport φ
  let B : ℝ≥0∞ := ENNReal.ofReal ‖φ.toReal.toBoundedContinuousFunction‖
  have hB (x : UpperPlane) : (φ x:ℝ≥0∞) ≤ B := by
    have h := φ.toReal.toBoundedContinuousFunction.norm_coe_le_norm x
    have h' : (φ x:ℝ)≤‖φ.toReal.toBoundedContinuousFunction‖ := by
      simpa only [CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply,
        CompactlySupportedContinuousMap.toReal_apply,Real.norm_of_nonneg (φ x).coe_nonneg] using h
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal h'
  have hK : IsCompact K := φ.hasCompactSupport
  apply isFiniteMeasure_withDensity
  apply ne_of_lt
  calc
    _ ≤ ∫⁻p, (K ×ˢ K).indicator (fun p => (B*B*ENNReal.ofReal C)*pairKernel α d p) p
        ∂upperArea.prod upperArea := by
      apply lintegral_mono
      intro p
      by_cases hx : p.1∈K
      · by_cases hy : p.2∈K
        · rw [indicator_of_mem (show p∈K ×ˢ K from ⟨hx,hy⟩)]
          calc
            _ ≤ (B*B)*(ENNReal.ofReal C*pairKernel α d p) :=
              mul_le_mul' (mul_le_mul' (hB p.1) (hB p.2)) le_rfl
            _ = _ := by ac_rfl
        · simp [K, image_eq_zero_of_notMem_tsupport hy, hy]
      · simp [K, image_eq_zero_of_notMem_tsupport hx, hx]
    _ = (B*B*ENNReal.ofReal C)*(∫⁻p in K ×ˢ K, pairKernel α d p ∂upperArea.prod upperArea) := by
      rw [lintegral_indicator (hK.measurableSet.prod hK.measurableSet),
        lintegral_const_mul _ (pairKernel_measurable α d hα.le)]
    _ < ∞ := ENNReal.mul_lt_top (by dsimp [B]; finiteness)
      (pairKernel_integrable_on_compact α d hα hα1 hd K hK)

lemma localPairMeasure_diagonal (α d C : ℝ) (φ : C_c(UpperPlane,ℝ≥0)) :
    localPairMeasure α d C φ (diagonal UpperPlane) = 0 :=
  diagonal_null_of_ac_prod upperArea _ (withDensity_absolutelyContinuous _ _)

 

theorem localized_actualConvexMass_pair_bound (a : ℝ) (ha : 1/4<a) :
    ∃ C : ℝ,0<C ∧ ∀ (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W],
    IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W →
    ∀ (φ : C_c(UpperPlane,ℝ≥0)) (d : ℝ),0<d → (∀ z∈tsupport φ,d≤2*z.1.im) →
    ∀ (s : Finset ℕ) (c : ℕ → ℝ), (∀ j∈s,0≤c j) → (∑j∈s,c j=1) →
    ∀ t : ℝ≥0∞,
      W.bind (fun b => ((actualConvexMass a s c t b).withDensity (fun z => φ z)).prod
        ((actualConvexMass a s c t b).withDensity (fun z => φ z))) ≤
          localPairMeasure (alpha a) d C φ := by
  obtain ⟨C,hC,hb⟩ := actualConvexDensity_pair_bound a ha
  refine ⟨C,hC,?_⟩
  intro W hprob hW φ d hd hdφ s c hc hsum t
  let ρ := actualConvexDensity a s c t
  have hρ : Measurable (Function.uncurry ρ) := actualConvexDensity_measurable a ha s c t
  have hφ : Measurable (fun z => (φ z:ℝ≥0∞)) := φ.continuous.measurable.coe_nnreal_ennreal
  have he (b : ExactSLEGenerator.Driver) :
      (actualConvexMass a s c t b).withDensity (fun z => φ z) =
        upperArea.withDensity (fun z => ρ b z*(φ z:ℝ≥0∞)) := by
    rw [actualConvexMass_density a ha s c t b]
    exact (withDensity_mul upperArea (hρ.comp (measurable_const.prodMk measurable_id)) hφ).symm
  simp_rw [he]
  exact average_localized_density_prod_le W upperArea ρ hρ φ
    (fun p => ENNReal.ofReal C*pairKernel (alpha a) d p)
    (fun x hx y hy => hb W hW s c hc hsum t x y d hd (hdφ x hx) (hdφ y hy))

end ExactSLEGreen
end
end
 

 
section
open MeasureTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace SLEExactGauge.MassVersions

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [BorelSpace X]

 

theorem ae_atomless_of_localizations (W : Measure Ω) (ν : Ω → Measure X)
    (h : ∀ φ : C_c(X,ℝ≥0),∀ᵐ ω ∂W,
      NullSingletonClass ((ν ω).withDensity (fun x => φ x))) :
    ∀ᵐ ω ∂W,NullSingletonClass (ν ω) := by
  let K := CompactExhaustion.choice X
  have hcut (n : ℕ) : ∃ φ : C_c(X,ℝ≥0),∀ x∈K n,φ x=1 := by
    obtain ⟨g,hg1,-,hgc,-⟩ := exists_continuous_one_zero_of_isCompact
      (K.isCompact n) isClosed_empty (disjoint_empty (K n))
    let f : C_c(X,ℝ) := ⟨g,hgc⟩
    refine ⟨f.nnrealPart,?_⟩
    intro x hx
    rw [CompactlySupportedContinuousMap.nnrealPart_apply]
    change (g x).toNNReal=1
    simp only [hg1 hx,Pi.one_apply,Real.toNNReal_one]
  choose φ hφ using hcut
  filter_upwards [ae_all_iff.mpr (fun n => h (φ n))] with ω hω
  constructor
  intro x
  obtain ⟨n,hn⟩ := K.exists_mem x
  let := hω n
  have hz : ((ν ω).withDensity (fun z => φ n z)) {x}=0 := measure_singleton x
  rw [withDensity_apply _ (measurableSet_singleton x),lintegral_singleton,hφ n x hn] at hz
  simpa only [ENNReal.coe_one,one_mul] using hz

end SLEExactGauge.MassVersions
end
 

 
section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain ExactSLEKernel SLEExactGauge.MassVersions

 

theorem actual_limit_pair_bound (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ)
    (hc : ∀ k j,j∈s k → 0≤c k j) (hsum : ∀ k,∑j∈s k,c k j=1)
    (t : ℝ≥0∞) (ν : ExactSLEGenerator.Driver → Measure UpperPlane)
    [∀ b, IsFiniteMeasureOnCompacts (ν b)] (hν : Measurable ν)
    (hconv : ∀ᵐ b ∂W,∀ f : C_c(UpperPlane,ℝ),
      Tendsto (fun k => ∑j∈s k,c k j * ∫z,f z∂actualUpperMass a
        (Real.exp (-2*a*(j+1))) t b) atTop (𝓝 (∫z,f z∂ν b)))
    (φ : C_c(UpperPlane,ℝ≥0)) :
    ∃ (Q : Measure (UpperPlane × UpperPlane)), IsFiniteMeasure Q ∧
      Q (diagonal UpperPlane)=0 ∧
      W.bind (fun b => (ν b |>.withDensity (fun z => φ z)).prod
        (ν b |>.withDensity (fun z => φ z))) ≤ Q := by
  obtain ⟨C,hC,hb⟩ := localized_actualConvexMass_pair_bound a ha
  obtain ⟨d,hd,hdφ⟩ := upper_compact_lower (tsupport φ) φ.hasCompactSupport
  let Q := localPairMeasure (alpha a) d C φ
  have hα1 : alpha a<1 := by
    have ha0 : 0<a := by linarith
    dsimp [alpha]
    have h : (0:ℝ)<1/(4*a) := by positivity
    linarith
  have hQ : IsFiniteMeasure Q := localPairMeasure_finite _ _ _ (alpha_pos ha) hα1 hd φ
  let := hQ
  let (k : ℕ) (b : ExactSLEGenerator.Driver) :
      IsFiniteMeasureOnCompacts (actualConvexMass a (s k) (c k) t b) :=
    actualConvexMass_finiteOnCompacts a ha (s k) (c k) t b
  let μk := fun k b => localizedFinite (actualConvexMass a (s k) (c k) t b) φ
  let μ := fun b => localizedFinite (ν b) φ
  have hμk (k) : Measurable (μk k) := measurable_localizedFinite _
    (actualConvexMass_measurable a ha (s k) (c k) t) φ
  have hμ : Measurable μ := measurable_localizedFinite ν hν φ
  have hl : ∀ᵐ b ∂W,Tendsto (fun k => μk k b) atTop (𝓝 (μ b)) := by
    filter_upwards [hconv] with b hb'
    apply localizedFinite_tendsto
    intro f
    simpa only [actualConvexMass_integral a ha _ _ (hc _) t b f] using hb' f
  refine ⟨Q,hQ,localPairMeasure_diagonal _ _ _ φ,?_⟩
  exact average_prod_le_of_weak_limit W μk μ hμk hμ hl Q
    (fun k => hb W hW φ d hd hdφ (s k) (c k) (hc k) (hsum k) t)

 

theorem actual_limit_localized_atomless (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ)
    (hc : ∀ k j,j∈s k → 0≤c k j) (hsum : ∀ k,∑j∈s k,c k j=1)
    (t : ℝ≥0∞) (ν : ExactSLEGenerator.Driver → Measure UpperPlane)
    [∀ b, IsFiniteMeasureOnCompacts (ν b)] (hν : Measurable ν)
    (hconv : ∀ᵐ b ∂W,∀ f : C_c(UpperPlane,ℝ),
      Tendsto (fun k => ∑j∈s k,c k j * ∫z,f z∂actualUpperMass a
        (Real.exp (-2*a*(j+1))) t b) atTop (𝓝 (∫z,f z∂ν b)))
    (φ : C_c(UpperPlane,ℝ≥0)) :
    ∀ᵐ b ∂W,NullSingletonClass ((ν b).withDensity (fun z => φ z)) := by
  obtain ⟨Q,hQ,hd,hb⟩ := actual_limit_pair_bound a ha W hW s c hc hsum t ν hν hconv φ
  apply ae_nullSingleton_of_average_prod_diagonal W
    (fun b => localizedFinite (ν b) φ) (measurable_localizedFinite ν hν φ)
  apply le_antisymm _ bot_le
  exact (hb (diagonal UpperPlane)).trans_eq hd

 

theorem actual_limit_atomless (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ)
    (hc : ∀ k j,j∈s k → 0≤c k j) (hsum : ∀ k,∑j∈s k,c k j=1)
    (t : ℝ≥0∞) (ν : ExactSLEGenerator.Driver → Measure UpperPlane)
    [∀ b, IsFiniteMeasureOnCompacts (ν b)] (hν : Measurable ν)
    (hconv : ∀ᵐ b ∂W,∀ f : C_c(UpperPlane,ℝ),
      Tendsto (fun k => ∑j∈s k,c k j * ∫z,f z∂actualUpperMass a
        (Real.exp (-2*a*(j+1))) t b) atTop (𝓝 (∫z,f z∂ν b))) :
    ∀ᵐ b ∂W,NullSingletonClass (ν b) :=
  ae_atomless_of_localizations W ν
    (actual_limit_localized_atomless a ha W hW s c hc hsum t ν hν hconv)

end ExactSLEGreen
end
end
 

 
section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

 

theorem actual_raw_atomless_mass_endpoint (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℕ → ℝ≥0∞) :
    ∃ (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ)
      (hc : ∀ k j, j∈s k → 0≤c k j),
      (∀ k j, j∈s k → k≤j) ∧ (∀ k, ∑ j∈s k, c k j=1) ∧
      let μ := recoveredMass a ha s c hc
      (∀ v b, IsFiniteMeasureOnCompacts (μ v b) ∧ (μ v b).Regular) ∧
      (∀ b, μ 0 b=0) ∧
      (∀ v, Measurable (μ v)) ∧
      IsProgressive rawFiltration (fun v : ℝ≥0 => μ v) ∧
      (∀ i (f : C_c(UpperPlane,ℝ)) (m : ℕ),
        MemLp (fun b => ∫z,f z∂μ (t i) b) (m : ℝ≥0∞) W) ∧
      (∀ i (K : Set UpperPlane), IsCompact K → ∀ m : ℕ,
        MemLp (fun b => (μ (t i) b K).toReal) (m : ℝ≥0∞) W) ∧
      (∀ i (f : C_c(UpperPlane,ℝ)),
        Tendsto (fun k => eLpNorm (fun b =>
          (∑ j∈s k, c k j * ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            - ∫z,f z∂μ (t i) b) 1 W) atTop (𝓝 0)) ∧
      (∀ i, t i=∞ → μ (t i) ∘ₘ W=initialGreenMeasure a) ∧
      (∀ i j (v : ℝ≥0), t i=v → t j=∞ →
        ∀ H : ExactSLEGenerator.Driver × UpperPlane → ℝ≥0∞,
        Measurable[(rawFiltration v).prod (inferInstance : MeasurableSpace UpperPlane)] H →
        (∫⁻b, ∫⁻z, H (b,z) ∂μ (t j) b ∂W) = (∫⁻b, ∫⁻z, H (b,z) ∂μ (t i) b ∂W) +
          ∫⁻b, ∫⁻z, H (b,z) * ENNReal.ofReal (survivingGreen a v b z.1) ∂upperArea ∂W) ∧
      ∀ᵐ b ∂W,
        (∀ i j, t i≤t j → μ (t i) b≤μ (t j) b) ∧
        (∀ i (f : C_c(UpperPlane,ℝ)),
          Tendsto (fun k => ∑ j∈s k, c k j *
            ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            atTop (𝓝 (∫z,f z∂μ (t i) b))) ∧
        (∀ i j, t i≠∞ → t j=∞ →
          (μ (t j) b-μ (t i) b) {z : UpperPlane | ¬alive a b.1 (t i).toNNReal z.1}=0) ∧
        (∀ i, NullSingletonClass (μ (t i) b)) := by
  obtain ⟨s,c,hc,hs,hsum,hμ,hzero,hmeas,hprog,hmom,hcompact,hL1,hmean,hH,hconv⟩ :=
    actual_raw_mass_endpoint a ha W hW t
  let μ := recoveredMass a ha s c hc
  let (v : ℝ≥0∞) (b : ExactSLEGenerator.Driver) : IsFiniteMeasureOnCompacts (μ v b) :=
    (hμ v b).1
  have hnon (i : ℕ) : ∀ᵐ b ∂W,NullSingletonClass (μ (t i) b) := by
    apply actual_limit_atomless a ha W hW s c hc hsum (t i) (μ (t i)) (hmeas (t i))
    filter_upwards [hconv] with b hb
    exact hb.2.1 i
  refine ⟨s,c,hc,hs,hsum,hμ,hzero,hmeas,hprog,hmom,hcompact,hL1,hmean,hH,?_⟩
  filter_upwards [hconv,ae_all_iff.mpr hnon] with b hb hn
  exact ⟨hb.1,hb.2.1,hb.2.2,hn⟩

end ExactSLEGreen
end

end OAI
