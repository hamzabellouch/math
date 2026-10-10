import Mathlib
import OAI.Probability.SKFluctuations.OrderedSKRateDirection

namespace OAI

/-! Real S K Pressure L1. -/

noncomputable section


namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem realOrderedSKPathPressure_l1_comparison (n : ℕ) (hn : 0<n)
    (b h b' h' : ℝ → ℝ)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hb' : MonotoneOn b' (Icc (0:ℝ) 1)) (hh' : MonotoneOn h' (Icc (0:ℝ) 1))
    (hb0 : 0≤b 0) (hh0 : 0≤h 0) (hb0' : 0≤b' 0) (hh0' : 0≤h' 0)
    (x : OrderedFeatureIndex n → ℝ) :
    |realOrderedSKPathPressure n b h x-realOrderedSKPathPressure n b' h' x| ≤
      (1/4:ℝ)*(∫ u in (0:ℝ)..1, |b u-b' u|)+
        (1/2:ℝ)*(∫ u in (0:ℝ)..1, |h u-h' u|) := by
  have he {f g : ℝ → ℝ} (hf : MonotoneOn f (Icc (0:ℝ) 1))
      (hg : MonotoneOn g (Icc (0:ℝ) 1)) (hf0 : 0≤f 0) (hg0 : 0≤g 0) :
      (∫ u in (0:ℝ)..1, |(Real.toNNReal (f u):ℝ)-(Real.toNNReal (g u):ℝ)|)=
        ∫ u in (0:ℝ)..1, |f u-g u| := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Icc (0:ℝ) 1 := by simpa using hu
    change |(Real.toNNReal (f u):ℝ)-(Real.toNNReal (g u):ℝ)|=|f u-g u|
    rw [Real.coe_toNNReal _ (hf0.trans (hf (by norm_num) hu' hu'.1)),
      Real.coe_toNNReal _ (hg0.trans (hg (by norm_num) hu' hu'.1))]
  have hh := orderedSKPathPressure_l1_comparison n hn
    (fun u => Real.toNNReal (b u)) (fun u => Real.toNNReal (h u))
    (fun u => Real.toNNReal (b' u)) (fun u => Real.toNNReal (h' u))
    (toNNReal_monotoneOn hb) (toNNReal_monotoneOn hh)
    (toNNReal_monotoneOn hb') (toNNReal_monotoneOn hh') x
  rw [he hb hb' hb0 hb0',he ‹MonotoneOn h _› hh' hh0 hh0'] at hh
  exact hh

 theorem intervalIntegral_abs_le_unit_bound {f : ℝ → ℝ} {C : ℝ}
    (h : ∀ u ∈ Icc (0:ℝ) 1, |f u|≤C) :
    |∫ u in (0:ℝ)..1, f u|≤C := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := C) (f := f) (fun u hu => by
      rw [Real.norm_eq_abs]
      exact h u (by
        have hu' : u ∈ Ioc (0:ℝ) 1 := by simpa using hu
        exact ⟨hu'.1.le,hu'.2⟩))
  simpa using hh

 theorem realOrderedSKPathPressure_uniform_comparison (n : ℕ) (hn : 0<n)
    (b h b' h' : ℝ → ℝ) {B H : ℝ}
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hb' : MonotoneOn b' (Icc (0:ℝ) 1)) (hh' : MonotoneOn h' (Icc (0:ℝ) 1))
    (hb0 : 0≤b 0) (hh0 : 0≤h 0) (hb0' : 0≤b' 0) (hh0' : 0≤h' 0)
    (hB : ∀ u ∈ Icc (0:ℝ) 1, |b u-b' u|≤B)
    (hH : ∀ u ∈ Icc (0:ℝ) 1, |h u-h' u|≤H)
    (x : OrderedFeatureIndex n → ℝ) :
    |realOrderedSKPathPressure n b h x-realOrderedSKPathPressure n b' h' x| ≤ B/4+H/2 := by
  have hbnd := intervalIntegral_abs_le_unit_bound (f := fun u => |b u-b' u|)
    (fun u hu => by simpa only [abs_abs] using hB u hu)
  have hhnd := intervalIntegral_abs_le_unit_bound (f := fun u => |h u-h' u|)
    (fun u hu => by simpa only [abs_abs] using hH u hu)
  have hp := realOrderedSKPathPressure_l1_comparison n hn b h b' h' hb hh hb' hh'
    hb0 hh0 hb0' hh0' x
  have hB' := (le_abs_self _).trans hbnd
  have hH' := (le_abs_self _).trans hhnd
  linarith

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 def omittedExtension {u₀ : ℝ} (hu : u₀≤1) (f : C(Icc u₀ 1,ℝ)) (u : ℝ) : ℝ :=
  (Ici u₀).indicator (IccExtend hu f) u

 theorem omittedExtension_before {u₀ : ℝ} (hu : u₀≤1) (f : C(Icc u₀ 1,ℝ))
    {u : ℝ} (hu' : u<u₀) : omittedExtension hu f u=0 := by
  simp [omittedExtension, not_le.mpr hu']

 theorem omittedExtension_on {u₀ : ℝ} (hu : u₀≤1) (f : C(Icc u₀ 1,ℝ))
    (u : Icc u₀ 1) : omittedExtension hu f u=f u := by
  simp [omittedExtension, IccExtend, u.property.1, projIcc_of_mem]

 theorem omittedExtension_intervalIntegrable {u₀ : ℝ} (hu : u₀≤1) (f : C(Icc u₀ 1,ℝ))
    (a b : ℝ) : IntervalIntegrable (omittedExtension hu f) volume a b := by
  apply intervalIntegrable_iff.mpr
  exact (intervalIntegrable_iff.mp ((f.continuous.comp continuous_projIcc).intervalIntegrable a b)).indicator
    measurableSet_Ici

 theorem omittedExtension_dist {u₀ : ℝ} (hu : u₀≤1) (f g : C(Icc u₀ 1,ℝ)) (u : ℝ) :
    |omittedExtension hu f u-omittedExtension hu g u|≤dist f g := by
  by_cases hh : u₀≤u
  · simpa only [omittedExtension, indicator_of_mem (show u ∈ Ici u₀ from hh), IccExtend,
      Real.dist_eq, Function.comp_apply] using ContinuousMap.dist_apply_le_dist (f := f) (g := g) (projIcc u₀ 1 hu u)
  · simp only [omittedExtension, indicator_of_notMem (show u ∉ Ici u₀ from hh), sub_self,abs_zero]
    exact dist_nonneg

 theorem omittedExtension_integral_dist {u₀ : ℝ} (hu : u₀≤1) (f g : C(Icc u₀ 1,ℝ)) :
    |(∫ u in (0:ℝ)..1, omittedExtension hu f u)-(∫ u in (0:ℝ)..1, omittedExtension hu g u)|≤dist f g := by
  rw [← intervalIntegral.integral_sub (omittedExtension_intervalIntegrable hu f _ _)
    (omittedExtension_intervalIntegrable hu g _ _)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (f := fun u => omittedExtension hu f u-omittedExtension hu g u)
    (C := dist f g) (fun u _ => by simpa only [Real.norm_eq_abs] using omittedExtension_dist hu f g u)
  simpa using h

 theorem omittedExtension_integral_continuous {u₀ : ℝ} (hu : u₀≤1) :
    Continuous (fun f : C(Icc u₀ 1,ℝ) => ∫ u in (0:ℝ)..1, omittedExtension hu f u) := by
  apply (LipschitzWith.of_dist_le_mul (K := (1:ℝ≥0)) ?_).continuous
  intro f g
  simpa only [Real.dist_eq, NNReal.coe_one,one_mul] using omittedExtension_integral_dist hu f g

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

 def coordinateObjective {u₀ : ℝ} (hu : u₀≤1) (n : ℕ) (b h : ℝ → ℝ)
    (z₀ z₁ z₂ : C(Icc u₀ 1,ℝ)) (x : OrderedFeatureIndex n → ℝ) : ℝ :=
  realOrderedSKPathPressure n (fun u => b u-omittedExtension hu z₀ u)
    (fun u => h u+omittedExtension hu z₁ u) x +
    (1/4:ℝ)*(∫ u in (0:ℝ)..1, omittedExtension hu z₂ u)

 theorem coordinateObjective_continuous {X : Type*} [TopologicalSpace X]
    {u₀ : ℝ} (hu : u₀≤1) (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ)
    (z₀ z₁ z₂ : X → C(Icc u₀ 1,ℝ))
    (hz₀ : Continuous z₀) (hz₁ : Continuous z₁) (hz₂ : Continuous z₂)
    (hb : ∀ y, MonotoneOn (fun u => b u-omittedExtension hu (z₀ y) u) (Icc (0:ℝ) 1))
    (hh : ∀ y, MonotoneOn (fun u => h u+omittedExtension hu (z₁ y) u) (Icc (0:ℝ) 1))
    (hb0 : ∀ y, 0≤b 0-omittedExtension hu (z₀ y) 0)
    (hh0 : ∀ y, 0≤h 0+omittedExtension hu (z₁ y) 0)
    (x : OrderedFeatureIndex n → ℝ) :
    Continuous (fun y => coordinateObjective hu n b h (z₀ y) (z₁ y) (z₂ y) x) := by
  have cp : Continuous (fun y => realOrderedSKPathPressure n
      (fun u => b u-omittedExtension hu (z₀ y) u) (fun u => h u+omittedExtension hu (z₁ y) u) x) := by
    rw [continuous_iff_continuousAt]
    intro p
    rw [ContinuousAt,tendsto_iff_dist_tendsto_zero]
    have ht : Tendsto (fun y => dist (z₀ y) (z₀ p)/4+dist (z₁ y) (z₁ p)/2) (𝓝 p) (𝓝 0) := by
      simpa using (((hz₀.dist (continuous_const : Continuous fun _ : X => z₀ p)).tendsto p).div_const 4).add
        (((hz₁.dist (continuous_const : Continuous fun _ : X => z₁ p)).tendsto p).div_const 2)
    apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _ ht
    apply Eventually.of_forall
    intro y
    rw [Real.dist_eq]
    apply realOrderedSKPathPressure_uniform_comparison n hn _ _ _ _ (hb y) (hh y) (hb p) (hh p)
      (hb0 y) (hh0 y) (hb0 p) (hh0 p)
    · intro u _
      have ha : b u-omittedExtension hu (z₀ y) u-(b u-omittedExtension hu (z₀ p) u)=
          -(omittedExtension hu (z₀ y) u-omittedExtension hu (z₀ p) u) := by ring
      rw [ha,abs_neg]
      exact omittedExtension_dist hu (z₀ y) (z₀ p) u
    · intro u _
      have ha : h u+omittedExtension hu (z₁ y) u-(h u+omittedExtension hu (z₁ p) u)=
          omittedExtension hu (z₁ y) u-omittedExtension hu (z₁ p) u := by ring
      rw [ha]
      exact omittedExtension_dist hu (z₁ y) (z₁ p) u
  exact cp.add (((omittedExtension_integral_continuous hu).comp hz₂).const_mul (1/4:ℝ))

 def constrainedCoefficient {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (hr : r₀≤1) (hc : 0<c) (hk : ContinuousOn k (Icc r₀ 1))
    (hkc : ∀ t ∈ Icc r₀ 1, c≤k t) (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)
    (g : ℝ → ℝ) (hg : Continuous g) (α : inverseIntegralConstraints r₀ u₀ k M) : C(Icc u₀ 1,ℝ) :=
  ⟨fun u => g (constrainedQuantile hr hc hk hkc hm hM α u),
    hg.comp (constrainedQuantileMap hr hc hk hkc hm hM α).continuous⟩

 theorem constrainedCoefficient_continuous {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (hr : r₀≤1) (hc : 0<c) (hk : ContinuousOn k (Icc r₀ 1))
    (hkc : ∀ t ∈ Icc r₀ 1, c≤k t) (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)
    (g : ℝ → ℝ) (hg : Continuous g) :
    Continuous (constrainedCoefficient (u₀ := u₀) hr hc hk hkc hm hM g hg) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact hg.comp (constrainedQuantile_joint_continuous hr hc hk hkc hm hM)

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

section
variable {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
variable (hr : r₀≤1) (hu : u₀≤1) (hc : 0<c) (hk : ContinuousOn k (Icc r₀ 1))
variable (hkc : ∀ t ∈ Icc r₀ 1, c≤k t) (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)
variable (g : ℝ → ℝ) (hg : Continuous g)

 def inverseCompensatedPressure (n : ℕ) (b h : ℝ → ℝ)
    (x : OrderedFeatureIndex n → ℝ) (α : inverseIntegralConstraints r₀ u₀ k M) : ℝ :=
  coordinateObjective hu n b h
    (constrainedCoefficient hr hc hk hkc hm hM g hg α)
    (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r) (hg.mul continuous_id) α)
    (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r^2) (hg.mul (continuous_id.pow 2)) α) x

 theorem inverseCompensatedPressure_eq (n : ℕ) (b h : ℝ → ℝ)
    (x : OrderedFeatureIndex n → ℝ) (α : inverseIntegralConstraints r₀ u₀ k M) :
    inverseCompensatedPressure hr hu hc hk hkc hm hM g hg n b h x α=
      pathCompensatedPressure n b h
        (omittedExtension hu (constrainedCoefficient hr hc hk hkc hm hM g hg α))
        (IccExtend hu (constrainedQuantileMap hr hc hk hkc hm hM α)) x := by
  have he₁ : omittedExtension hu
      (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r) (hg.mul continuous_id) α)=
      fun u => omittedExtension hu (constrainedCoefficient hr hc hk hkc hm hM g hg α) u*
        IccExtend hu (constrainedQuantileMap hr hc hk hkc hm hM α) u := by
    funext u
    by_cases hh : u₀≤u <;> simp [omittedExtension,IccExtend,hh,constrainedCoefficient,
      constrainedQuantileMap,Function.comp_def]
  have he₂ : omittedExtension hu
      (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r^2) (hg.mul (continuous_id.pow 2)) α)=
      fun u => omittedExtension hu (constrainedCoefficient hr hc hk hkc hm hM g hg α) u*
        (IccExtend hu (constrainedQuantileMap hr hc hk hkc hm hM α) u)^2 := by
    funext u
    by_cases hh : u₀≤u <;> simp [omittedExtension,IccExtend,hh,constrainedCoefficient,
      constrainedQuantileMap,Function.comp_def]
  unfold inverseCompensatedPressure coordinateObjective pathCompensatedPressure
  rw [he₁,he₂]

 theorem inverseCompensatedPressure_continuous (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ)
    (hb : ∀ α : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => b u-omittedExtension hu (constrainedCoefficient hr hc hk hkc hm hM g hg α) u) (Icc (0:ℝ) 1))
    (hh : ∀ α : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => h u+omittedExtension hu (constrainedCoefficient hr hc hk hkc hm hM
        (fun r => g r*r) (hg.mul continuous_id) α) u) (Icc (0:ℝ) 1))
    (hb0 : ∀ α : inverseIntegralConstraints r₀ u₀ k M,
      0≤b 0-omittedExtension hu (constrainedCoefficient hr hc hk hkc hm hM g hg α) 0)
    (hh0 : ∀ α : inverseIntegralConstraints r₀ u₀ k M,
      0≤h 0+omittedExtension hu (constrainedCoefficient hr hc hk hkc hm hM
        (fun r => g r*r) (hg.mul continuous_id) α) 0)
    (x : OrderedFeatureIndex n → ℝ) :
    Continuous (inverseCompensatedPressure hr hu hc hk hkc hm hM g hg n b h x) := by
  exact coordinateObjective_continuous hu n hn b h _ _ _
    (constrainedCoefficient_continuous hr hc hk hkc hm hM g hg)
    (constrainedCoefficient_continuous hr hc hk hkc hm hM _ _)
    (constrainedCoefficient_continuous hr hc hk hkc hm hM _ _) hb hh hb0 hh0 x

 theorem inverseCompensatedPressure_minimum (hMc : Continuous M)
    (hne : (inverseIntegralConstraints r₀ u₀ k M).Nonempty)
    (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ)
    (hb : ∀ α : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => b u-omittedExtension hu (constrainedCoefficient hr hc hk hkc hm hM g hg α) u) (Icc (0:ℝ) 1))
    (hh : ∀ α : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => h u+omittedExtension hu (constrainedCoefficient hr hc hk hkc hm hM
        (fun r => g r*r) (hg.mul continuous_id) α) u) (Icc (0:ℝ) 1))
    (hb0 : ∀ α : inverseIntegralConstraints r₀ u₀ k M,
      0≤b 0-omittedExtension hu (constrainedCoefficient hr hc hk hkc hm hM g hg α) 0)
    (hh0 : ∀ α : inverseIntegralConstraints r₀ u₀ k M,
      0≤h 0+omittedExtension hu (constrainedCoefficient hr hc hk hkc hm hM
        (fun r => g r*r) (hg.mul continuous_id) α) 0)
    (x : OrderedFeatureIndex n → ℝ) :
    ∃ α : inverseIntegralConstraints r₀ u₀ k M, ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      inverseCompensatedPressure hr hu hc hk hkc hm hM g hg n b h x α≤
        inverseCompensatedPressure hr hu hc hk hkc hm hM g hg n b h x β := by
  let : CompactSpace (inverseIntegralConstraints r₀ u₀ k M) :=
    isCompact_iff_compactSpace.mp (inverseIntegralConstraints_compact r₀ u₀ k M hMc hm)
  obtain ⟨α,hα⟩ := hne
  have hne' : (Set.univ : Set (inverseIntegralConstraints r₀ u₀ k M)).Nonempty := ⟨⟨α,hα⟩,mem_univ _⟩
  obtain ⟨β,_,hβ⟩ := isCompact_univ.exists_isMinOn hne'
    (inverseCompensatedPressure_continuous hr hu hc hk hkc hm hM g hg n hn b h hb hh hb0 hh0 x).continuousOn
  exact ⟨β,fun γ => hβ (mem_univ γ)⟩

end
end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

section
variable {r₀ u₀ c T B : ℝ} {k M ψ g : ℝ → ℝ}
variable (hr : r₀ ≤ 1) (hu : u₀ ∈ Icc (0:ℝ) 1) (hc : 0<c)
variable (hk : ContinuousOn k (Icc r₀ 1)) (hkc : ∀ r ∈ Icc r₀ 1, c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1) (hMc : Continuous M)
variable (α : inverseIntegralConstraints r₀ u₀ k M)
variable (hfeas : ∀ t ∈ Icc (0:ℝ) T,
  sourceInverseConstraints r₀ u₀ k M (fun r => α.val.val r+t*ψ r))

 theorem source_coefficient_curve (F : ℝ → ℝ) (hF : Continuous F) (t : ℝ) :
    omittedCurve u₀ F (sourceForwardCurve hr hu hc hk hkc hm hM hMc α hfeas) t=
      omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM F hF
        (sourceInverseCurve hr hu hc hk hkc hMc α hfeas t)) := by
  funext u
  by_cases hh : u₀ ≤ u <;>
    simp [omittedCurve,sourceForwardCurve,omittedExtension,IccExtend,constrainedCoefficient,hh]

 theorem source_objective_curve_derivative (hT : 0 ≤ T) (hB : 0 ≤ B) {D : ℝ≥0}
    (hψ : LipschitzOnWith D ψ (Icc r₀ 1)) (hψb : ∀ r ∈ Icc r₀ 1, |ψ r| ≤ B)
    (hg : ContDiff ℝ 1 g) (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ)
    (hb : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => b u-omittedExtension hu.2
        (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous β) u) (Icc (0:ℝ) 1))
    (hh : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => h u+omittedExtension hu.2
        (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
          (hg.continuous.mul continuous_id) β) u) (Icc (0:ℝ) 1))
    (hbn : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      0 ≤ b 0-omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous β) 0)
    (hhn : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      0 ≤ h 0+omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
        (hg.continuous.mul continuous_id) β) 0) :
    let R := sourceForwardCurve hr hu hc hk hkc hm hM hMc α hfeas
    let V := fun u => -ψ (R 0 u)/deriv α.val.val (R 0 u)
    HasDerivWithinAt (fun t => inverseCompensatedPressure hr hu.2 hc hk hkc hm hM g hg.continuous n b h 0
        (sourceInverseCurve hr hu hc hk hkc hMc α hfeas t))
      ((1/4:ℝ)*(∫ u in (0:ℝ)..1,
        (if u₀ ≤ u then deriv g (R 0 u)*V u else 0)*
          orderedPathB n (fun u => (b u-omittedCurve u₀ g R 0 u).toNNReal)
            (fun u => (h u+omittedCurve u₀ (fun r => g r*r) R 0 u).toNNReal) u-
        2*((if u₀ ≤ u then deriv (fun r => g r*r) (R 0 u)*V u else 0)*
          orderedPathS n (fun u => (b u-omittedCurve u₀ g R 0 u).toNNReal)
            (fun u => (h u+omittedCurve u₀ (fun r => g r*r) R 0 u).toNNReal) u)+
        (if u₀ ≤ u then deriv (fun r => g r*r^2) (R 0 u)*V u else 0))) (Icc (0:ℝ) T) 0 := by
  dsimp only
  let R := sourceForwardCurve hr hu hc hk hkc hm hM hMc α hfeas
  let V := fun u => -ψ (R 0 u)/deriv α.val.val (R 0 u)
  have hg₁ : ContDiff ℝ 1 (fun r => g r*r) := hg.mul contDiff_id
  have hg₂ : ContDiff ℝ 1 (fun r => g r*r^2) := hg.mul (contDiff_id.pow 2)
  obtain ⟨K₀,hK₀⟩ := hg.contDiffOn.exists_lipschitzOnWith (by norm_num) (convex_Icc r₀ 1) isCompact_Icc
  obtain ⟨K₁,hK₁⟩ := hg₁.contDiffOn.exists_lipschitzOnWith (by norm_num) (convex_Icc r₀ 1) isCompact_Icc
  obtain ⟨K₂,hK₂⟩ := hg₂.contDiffOn.exists_lipschitzOnWith (by norm_num) (convex_Icc r₀ 1) isCompact_Icc
  have he (F : ℝ → ℝ) (hF : Continuous F) (t : ℝ) : omittedCurve u₀ F R t=
      omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM F hF
        (sourceInverseCurve hr hu hc hk hkc hMc α hfeas t)) :=
    source_coefficient_curve hr hu hc hk hkc hm hM hMc α hfeas F hF t
  have hb' (t : ℝ) : MonotoneOn (fun u => b u-omittedCurve u₀ g R t u) (Icc (0:ℝ) 1) := by
    rw [he g hg.continuous]; exact hb _
  have hh' (t : ℝ) : MonotoneOn (fun u => h u+omittedCurve u₀ (fun r => g r*r) R t u) (Icc (0:ℝ) 1) := by
    rw [he (fun r => g r*r) (hg.continuous.mul continuous_id)]; exact hh _
  have hbn' (t u : ℝ) (hu' : u ∈ Icc (0:ℝ) 1) : 0 ≤ b u-omittedCurve u₀ g R t u := by
    have hx : 0 ≤ b 0-omittedCurve u₀ g R t 0 := by rw [he g hg.continuous]; exact hbn _
    exact hx.trans (hb' t ⟨le_rfl,by norm_num⟩ hu' hu'.1)
  have hhn' (t u : ℝ) (hu' : u ∈ Icc (0:ℝ) 1) : 0 ≤ h u+omittedCurve u₀ (fun r => g r*r) R t u := by
    have hx : 0 ≤ h 0+omittedCurve u₀ (fun r => g r*r) R t 0 := by
      rw [he (fun r => g r*r) (hg.continuous.mul continuous_id)]; exact hhn _
    exact hx.trans (hh' t ⟨le_rfl,by norm_num⟩ hu' hu'.1)
  have hd := radius_curve_derivative n hn b h (div_nonneg hB hc.le)
    g (fun r => g r*r) (fun r => g r*r^2) (deriv g) (deriv (fun r => g r*r))
    (deriv (fun r => g r*r^2)) V R hg.continuous hg₁.continuous hg₂.continuous
    hg.continuous_deriv_one.continuousOn hg₁.continuous_deriv_one.continuousOn hg₂.continuous_deriv_one.continuousOn
    (fun x _ => (hg.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hg₁.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hg₂.differentiable (by norm_num) x).hasDerivAt)
    hK₀ hK₁ hK₂ (sourceForwardCurve_continuous hr hu hc hk hkc hm hM hMc α hfeas)
    (sourceForwardCurve_mem hr hu hc hk hkc hm hM hMc α hfeas)
    (by
      filter_upwards [self_mem_nhdsWithin] with t ht u hu'
      exact sourceForwardCurve_displacement hr hu hc hk hkc hm hM hMc α hfeas hT hψb ht.1 hu')
    (sourceForwardCurve_ae_derivative hr hu hc hk hkc hm hM hMc α hfeas hT hψ hψb)
    (source_velocity_measurable hr hu hc hk hkc hm hM hMc α hfeas hψ.continuousOn)
    (source_velocity_bound hr hu hc hk hkc hm hM hMc α hfeas hT hB hψb)
    (hb' 0) (hh' 0) (hbn' 0) (hhn' 0) (Eventually.of_forall hb') (Eventually.of_forall hh')
    (Eventually.of_forall hbn') (Eventually.of_forall hhn')
  convert hd using 1
  funext t
  simp only [inverseCompensatedPressure,coordinateObjective,
    he g hg.continuous t,he (fun r => g r*r) (hg.continuous.mul continuous_id) t,
    he (fun r => g r*r^2) (hg.continuous.mul (continuous_id.pow 2)) t]

end
end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 theorem lipschitz_interval_integral_image {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → ℝ} {C : ℝ≥0} (hf : LipschitzOnWith C f (Icc a b))
    (hinj : InjOn f (Icc a b)) (g : ℝ → ℝ) :
    (∫ u in f '' Icc a b, g u)=∫ x in Icc a b, |deriv f x| *g (f x) := by
  have hac : AbsolutelyContinuousOnInterval f a b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := C)
    simpa only [uIcc_of_le hab] using hf
  let B : Set ℝ := {x | x ∈ Icc a b ∧ ¬DifferentiableAt ℝ f x}
  have hB : volume B=0 := by
    simpa only [B,uIcc_of_le hab,Classical.not_imp_iff_and_not] using ae_iff.mp hac.ae_differentiableAt
  let T := Icc a b \ toMeasurable volume B
  have hT : MeasurableSet T := measurableSet_Icc.diff (measurableSet_toMeasurable _ _)
  have hsub : T ⊆ Icc a b := sdiff_subset
  have hnull : volume (Icc a b \ T)=0 := by
    apply measure_mono_null (show Icc a b \ T ⊆ toMeasurable volume B from ?_)
      (by rw [measure_toMeasurable,hB])
    intro x hx
    by_contra hh
    exact hx.2 ⟨hx.1,hh⟩
  have hae : Icc a b =ᵐ[volume] T := by
    apply ae_eq_set.mpr
    exact ⟨hnull,by simp only [sdiff_eq_empty.mpr hsub,measure_empty]⟩
  have hdiff : ∀ x ∈ T, HasDerivWithinAt f (deriv f x) T x := by
    intro x hx
    have hd : DifferentiableAt ℝ f x := by
      by_contra hh
      exact hx.2 (subset_toMeasurable volume B ⟨hx.1,hh⟩)
    exact hd.hasDerivAt.hasDerivWithinAt
  have himage : f '' Icc a b =ᵐ[volume] f '' T := by
    have he : volume (f '' (Icc a b \ T))=0 := by
      have hh := (hf.mono (show Icc a b \ T ⊆ Icc a b from sdiff_subset)).hausdorffMeasure_image_le
        (show (0:ℝ) ≤ 1 by norm_num)
      rw [hausdorffMeasure_real,hnull,mul_zero] at hh
      exact le_antisymm hh bot_le
    apply ae_eq_set.mpr
    constructor
    · apply measure_mono_null _ he
      rintro u ⟨⟨x,hx,rfl⟩,hu⟩
      exact ⟨x,⟨hx,fun hxt => hu ⟨x,hxt,rfl⟩⟩,rfl⟩
    · simp only [sdiff_eq_empty.mpr (image_mono hsub),measure_empty]
  calc
    (∫ u in f '' Icc a b, g u) = ∫ u in f '' T, g u := setIntegral_congr_set himage
    _ = ∫ x in T, |deriv f x| *g (f x) := by
      simpa only [smul_eq_mul] using integral_image_eq_integral_abs_deriv_smul hT hdiff
        (hinj.mono hsub) g
    _ = ∫ x in Icc a b, |deriv f x| *g (f x) := setIntegral_congr_set hae.symm

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 theorem inverse_gradient_substitution {a b : ℝ} (hab : a ≤ b)
    {α r : ℝ → ℝ} {C : ℝ≥0} (hα : LipschitzOnWith C α (Icc a b))
    (hinj : InjOn α (Icc a b)) (hr : ∀ x ∈ Icc a b, r (α x)=x)
    (hd : ∀ᵐ x, x ∈ Icc a b → 0<deriv α x) (G ψ : ℝ → ℝ) :
    (∫ u in α '' Icc a b, G u*(-ψ (r u)/deriv α (r u)))=
      -(∫ x in Icc a b, G (α x)*ψ x) := by
  rw [lipschitz_interval_integral_image hab hα hinj]
  calc
    (∫ x in Icc a b, |deriv α x| *(G (α x)*(-ψ (r (α x))/deriv α (r (α x)))))=
        ∫ x in Icc a b, -(G (α x)*ψ x) := by
      apply setIntegral_congr_ae measurableSet_Icc
      filter_upwards [hd] with x hx hxi
      rw [hr x hxi,abs_of_pos (hx hxi)]
      field_simp [(hx hxi).ne']
    _ = _ := integral_neg _

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 def radiusComparisonGradient (g α S B : ℝ → ℝ) (r : ℝ) : ℝ :=
   deriv g r*B (α r)-2*(deriv g r*r+g r)*S (α r)+deriv g r*r^2+2*g r*r

 theorem omitted_interval_integral {u₀ : ℝ} (hu : u₀ ∈ Icc (0:ℝ) 1) (f : ℝ → ℝ) :
    (∫ u in (0:ℝ)..1, if u₀ ≤ u then f u else 0)=∫ u in Icc u₀ 1, f u := by
  change (∫ u in (0:ℝ)..1, (Ici u₀).indicator f u)=_
  rw [intervalIntegral.integral_of_le (by norm_num),← integral_Icc_eq_integral_Ioc,
    integral_indicator measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici]
  have he : Ici u₀ ∩ Icc (0:ℝ) 1=Icc u₀ 1 := by
    ext u; constructor
    · intro h; exact ⟨h.1,h.2.2⟩
    · intro h; exact ⟨h.1,hu.1.trans h.1,h.2⟩
  rw [he]

 theorem inverseConstraint_image {r₀ u₀ : ℝ} {k M : ℝ → ℝ}
    (hr : r₀ ≤ 1) (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (α : inverseIntegralConstraints r₀ u₀ k M) : α.val.val '' Icc r₀ 1=Icc u₀ 1 := by
  ext u
  constructor
  · rintro ⟨r,hr',rfl⟩
    exact (inverseConstraintMap α ⟨r,hr'⟩).property
  · intro hu
    obtain ⟨r,he⟩ := inverseConstraintMap_surjective hr hm hM α ⟨u,hu⟩
    exact ⟨r.val,r.property,congrArg Subtype.val he⟩

 theorem comparison_gradient_substitution {r₀ u₀ : ℝ} {C : ℝ≥0}
    {α R ψ g S B : ℝ → ℝ} (hr : r₀ ≤ 1) (hu : u₀ ∈ Icc (0:ℝ) 1)
    (hα : LipschitzOnWith C α (Icc r₀ 1)) (hinj : InjOn α (Icc r₀ 1))
    (himage : α '' Icc r₀ 1=Icc u₀ 1) (hR : ∀ r ∈ Icc r₀ 1, R (α r)=r)
    (hd : ∀ᵐ r, r ∈ Icc r₀ 1 → 0<deriv α r)
    (hg : ∀ r ∈ Icc r₀ 1, DifferentiableAt ℝ g r)
    (hRm : ∀ u ∈ Icc u₀ 1, R u ∈ Icc r₀ 1) :
    (∫ u in (0:ℝ)..1,
      (if u₀ ≤ u then deriv g (R u)*(-ψ (R u)/deriv α (R u)) else 0)*B u-
      2*((if u₀ ≤ u then deriv (fun r => g r*r) (R u)*(-ψ (R u)/deriv α (R u)) else 0)*S u)+
      (if u₀ ≤ u then deriv (fun r => g r*r^2) (R u)*(-ψ (R u)/deriv α (R u)) else 0))=
      -(∫ r in Icc r₀ 1, radiusComparisonGradient g α S B r*ψ r) := by
  let F := fun u => deriv g (R u)*B u-2*(deriv g (R u)*R u+g (R u))*S u+
    deriv g (R u)*(R u)^2+2*g (R u)*R u
  have he : (∫ u in (0:ℝ)..1,
      (if u₀ ≤ u then deriv g (R u)*(-ψ (R u)/deriv α (R u)) else 0)*B u-
      2*((if u₀ ≤ u then deriv (fun r => g r*r) (R u)*(-ψ (R u)/deriv α (R u)) else 0)*S u)+
      (if u₀ ≤ u then deriv (fun r => g r*r^2) (R u)*(-ψ (R u)/deriv α (R u)) else 0))=
      ∫ u in (0:ℝ)..1, if u₀ ≤ u then F u*(-ψ (R u)/deriv α (R u)) else 0 := by
    apply intervalIntegral.integral_congr
    intro u hui
    have hui' : u ∈ Icc (0:ℝ) 1 := by simpa using hui
    by_cases hh : u₀ ≤ u
    · simp only [ite_eq_left hh]
      have hd₁ := ((hg _ (hRm u ⟨hh,hui'.2⟩)).hasDerivAt.mul (hasDerivAt_id (R u))).deriv
      have hd₂ := ((hg _ (hRm u ⟨hh,hui'.2⟩)).hasDerivAt.mul ((hasDerivAt_id (R u)).pow 2)).deriv
      change deriv (fun r => g r*r) (R u)=_ at hd₁
      change deriv (fun r => g r*r^2) (R u)=_ at hd₂
      simp only [id_eq,Pi.pow_apply] at hd₁ hd₂
      rw [hd₁,hd₂]
      dsimp [F]; ring
    · simp [hh]
  rw [he,omitted_interval_integral hu,← himage,inverse_gradient_substitution hr hα hinj hR hd]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro r hri
  simp only [F,hR r hri,radiusComparisonGradient]

 theorem right_derivative_nonneg {T d : ℝ} {f : ℝ → ℝ} (hT : 0<T)
    (hd : HasDerivWithinAt f d (Icc (0:ℝ) T) 0)
    (hmin : ∀ t ∈ Icc (0:ℝ) T, f 0 ≤ f t) : 0 ≤ d := by
  have hl := hasDerivWithinAt_iff_tendsto_slope.mp hd
  rw [Icc_sdiff_left,nhdsWithin_Ioc_eq_nhdsGT hT] at hl
  apply ge_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin, Ioc_mem_nhdsGT hT] with t ht htT
  rw [slope_def_field,sub_zero]
  exact div_nonneg (sub_nonneg.mpr (hmin t ⟨ht.le,htT.2⟩)) ht.le

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

section
variable {r₀ u₀ c T B : ℝ} {k M ψ g : ℝ → ℝ}
variable (hr : r₀ ≤ 1) (hu : u₀ ∈ Icc (0:ℝ) 1) (hc : 0<c)
variable (hk : ContinuousOn k (Icc r₀ 1)) (hkc : ∀ r ∈ Icc r₀ 1, c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1) (hMc : Continuous M)
variable (α : inverseIntegralConstraints r₀ u₀ k M)
variable (hfeas : ∀ t ∈ Icc (0:ℝ) T,
  sourceInverseConstraints r₀ u₀ k M (fun r => α.val.val r+t*ψ r))

 theorem source_coefficient_initial (hT : 0 ≤ T) (F : ℝ → ℝ) (hF : Continuous F) :
    omittedCurve u₀ F (sourceForwardCurve hr hu hc hk hkc hm hM hMc α hfeas) 0=
      omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM F hF α) := by
  funext u
  rw [omittedCurve,sourceForwardCurve_initial_eq hr hu hc hk hkc hm hM hMc α hfeas hT]
  rfl

 theorem source_objective_initial (hT : 0 ≤ T) (hg : Continuous g)
    (n : ℕ) (b h : ℝ → ℝ) :
    inverseCompensatedPressure hr hu.2 hc hk hkc hm hM g hg n b h 0
        (sourceInverseCurve hr hu hc hk hkc hMc α hfeas 0)=
      inverseCompensatedPressure hr hu.2 hc hk hkc hm hM g hg n b h 0 α := by
  have he (F : ℝ → ℝ) (hF : Continuous F) :=
    (source_coefficient_curve hr hu hc hk hkc hm hM hMc α hfeas F hF 0).symm.trans
      (source_coefficient_initial hr hu hc hk hkc hm hM hMc α hfeas hT F hF)
  simp only [inverseCompensatedPressure,coordinateObjective,
    he g hg,he (fun r => g r*r) (hg.mul continuous_id),
    he (fun r => g r*r^2) (hg.mul (continuous_id.pow 2))]

 include hMc hfeas in
 theorem source_minimum_first_variation (hT : 0<T) (hB : 0 ≤ B) {D : ℝ≥0}
    (hψ : LipschitzOnWith D ψ (Icc r₀ 1)) (hψb : ∀ r ∈ Icc r₀ 1, |ψ r| ≤ B)
    (hg : ContDiff ℝ 1 g) (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ)
    (hb : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => b u-omittedExtension hu.2
        (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous β) u) (Icc (0:ℝ) 1))
    (hh : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => h u+omittedExtension hu.2
        (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
          (hg.continuous.mul continuous_id) β) u) (Icc (0:ℝ) 1))
    (hbn : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      0 ≤ b 0-omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous β) 0)
    (hhn : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      0 ≤ h 0+omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
        (hg.continuous.mul continuous_id) β) 0)
    (hmin : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      inverseCompensatedPressure hr hu.2 hc hk hkc hm hM g hg.continuous n b h 0 α ≤
      inverseCompensatedPressure hr hu.2 hc hk hkc hm hM g hg.continuous n b h 0 β) :
    let b' := fun u => (b u-omittedExtension hu.2
      (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous α) u).toNNReal
    let h' := fun u => (h u+omittedExtension hu.2
      (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
        (hg.continuous.mul continuous_id) α) u).toNNReal
    0 ≤ -(∫ r in Icc r₀ 1, radiusComparisonGradient g α.val.val
      (orderedPathS n b' h') (orderedPathB n b' h') r*ψ r) := by
  dsimp only
  let R := sourceForwardCurve hr hu hc hk hkc hm hM hMc α hfeas
  let b' := fun u => (b u-omittedCurve u₀ g R 0 u).toNNReal
  let h' := fun u => (h u+omittedCurve u₀ (fun r => g r*r) R 0 u).toNNReal
  have hα := inverseIntegralConstraints_lipschitz hm hM α.property
  have hi := (inverseConstraint_strictMonoOn hc hk hkc α.property).injOn
  have hR : ∀ r ∈ Icc r₀ 1, R 0 (α.val.val r)=r := by
    intro r hri
    have hur : α.val.val r ∈ Icc u₀ 1 := (inverseConstraintMap α ⟨r,hri⟩).property
    apply hi (sourceForwardCurve_mem hr hu hc hk hkc hm hM hMc α hfeas 0 _) hri
    exact sourceForwardCurve_initial hr hu hc hk hkc hm hM hMc α hfeas hT.le hur
  have hd : ∀ᵐ r, r ∈ Icc r₀ 1 → 0<deriv α.val.val r := by
    have hl := (lipschitz_ae_deriv_lower_iff hr hα hk).mpr
      (fun x hx y hy hxy => (α.property.2.2 x hx y hy hxy).1)
    exact hl.mono fun r hr' hri => hc.trans_le ((hkc r hri).trans (hr' hri))
  have he := comparison_gradient_substitution (ψ := ψ) (S := orderedPathS n b' h')
    (B := orderedPathB n b' h') hr hu hα hi (inverseConstraint_image hr hm hM α) hR hd
    (fun r _ => hg.differentiable (by norm_num) r)
    (fun u _ => sourceForwardCurve_mem hr hu hc hk hkc hm hM hMc α hfeas 0 u)
  have hx := source_objective_curve_derivative hr hu hc hk hkc hm hM hMc α hfeas hT.le hB hψ hψb
    hg n hn b h hb hh hbn hhn
  dsimp only at hx
  change HasDerivWithinAt _ ((1/4:ℝ)*_) _ _ at hx
  rw [he] at hx
  have hnon := right_derivative_nonneg hT hx (fun t _ => by
    rw [source_objective_initial hr hu hc hk hkc hm hM hMc α hfeas hT.le hg.continuous]
    exact hmin _)
  have hpos : 0 ≤ -(∫ r in Icc r₀ 1, radiusComparisonGradient g α.val.val
      (orderedPathS n b' h') (orderedPathB n b' h') r*ψ r) := by linarith
  dsimp only [b',h'] at hpos
  rw [source_coefficient_initial hr hu hc hk hkc hm hM hMc α hfeas hT.le g hg.continuous,
    source_coefficient_initial hr hu hc hk hkc hm hM hMc α hfeas hT.le
      (fun r => g r*r) (hg.continuous.mul continuous_id)] at hpos
  exact hpos

end
end SKFluctuations

end

end OAI
