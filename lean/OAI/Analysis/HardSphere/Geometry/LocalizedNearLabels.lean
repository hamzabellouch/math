import Mathlib
import OAI.Analysis.HardSphere.Thermodynamics.NearGridScale

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate ENNReal

lemma spatialSiteDistance_triangle (L : Length) (A : Finset (Torus L)) (x y : Torus L) :
    spatialSiteDistance L A x≤ spatialSiteDistance L A y+torusDistance L x y := by
  simpa only [spatialSiteDistance,euclideanTorusPoint_dist] using
    (Metric.infDist_le_infDist_add_dist (x:=euclideanTorusPoint L x) (y:=euclideanTorusPoint L y)
      (s:=euclideanTorusPoint L '' (A:Set (Torus L))))

lemma spatialOutside_zero (L : Length) (A : Finset (Torus L)) (H : ℝ) (x : Torus L)
    (hx : spatialSiteDistance L A x≤H) : (spatialOutside L A H).orbital x=0 := by
  have hm := (abs_le.mp (smoothSpatialDistance_approximation L A x)).2
  have h : smoothSpatialDistance L A x-H≤1 := by linarith
  change (Real.cos (Real.pi/2*CellOrbital.profile 1 (smoothSpatialDistance L A x-H)):ℂ)=0
  rw [CellOrbital.profile_one (by norm_num : (0:ℝ)<1) h,mul_one,Real.cos_pi_div_two,Complex.ofReal_zero]

lemma productPartition_norm_unity {n : ℕ} {L : Length} (a c : SmoothMultiplier 1 L)
    (ha : ∀ X, conj (a.toFun X)=a.toFun X) (hc : ∀ X, conj (c.toFun X)=c.toFun X)
    (hp : ∀ x : Torus L, a.orbital x*a.orbital x+c.orbital x*c.orbital x=1)
    (X : Configuration n L) : (∑ σ : Fin n → Bool, ‖(productPartition n L a c σ).toFun X‖^2)=1 := by
  simp_rw [real_norm_sq _ (productPartition_real a c ha hc _ X)]
  rw [← Complex.re_sum,productPartition_unity a c hp,Complex.one_re]

lemma spatialPartition_forces_inside {n : ℕ} (L : Length) (A : Finset (Torus L)) (H : ℝ)
    (σ : Fin n → Bool) (X : Configuration n L)
    (hn : (productPartition n L (spatialInside L A H) (spatialOutside L A H) σ).toFun X≠0)
    (i : Fin n) (hi : spatialSiteDistance L A (X i)≤H) : σ i=true := by
  have hprod : ∏ j : Fin n, (cond (σ j) (spatialInside L A H) (spatialOutside L A H)).orbital (X j)≠0 := hn
  have hh := (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
  cases he : σ i
  · rw [he,Bool.cond_false,spatialOutside_zero L A H (X i) hi] at hh
    exact False.elim (hh rfl)
  · rfl

def localizedNearLabels {n : ℕ} (L : Length) (A : Finset (Torus L)) (s : ℝ)
    (X : Configuration n L) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i ↦ A.Nonempty ∧ spatialSiteDistance L A (X i)≤6 ∧
    ∃ k : Fin n, k≠i ∧ torusDistance L (X k) (X i)≤2*s)

lemma localizedNearLabels_card_le_selected {n : ℕ} (L : Length) (A : Finset (Torus L))
    {H s : ℝ} (hH : 8≤H) (hs : 2*s≤1) (σ : Fin n → Bool) (X : Configuration n L)
    (hn : (productPartition n L (spatialInside L A H) (spatialOutside L A H) σ).toFun X≠0) :
    (localizedNearLabels L A s X).card≤(nearLabels (fun i ↦ σ i=true) s X).card := by
  classical
  have hforce := spatialPartition_forces_inside L A H σ X hn
  have hi {i : Fin n} (hi : i∈localizedNearLabels L A s X) : σ i=true := by
    have hd := (Finset.mem_filter.mp hi).2.2.1
    exact hforce i (by linarith)
  let f : {i // i∈localizedNearLabels L A s X} → {i // i∈nearLabels (fun i ↦ σ i=true) s X} := fun i ↦
    ⟨⟨i.val,hi i.property⟩,by
      obtain ⟨_,hd,k,hki,hkd⟩ := (Finset.mem_filter.mp i.property).2
      have hd' := spatialSiteDistance_triangle L A (X k) (X i.val)
      have hk : σ k=true := hforce k (by linarith)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨⟨k,hk⟩,fun he ↦ hki (congrArg Subtype.val he),hkd⟩⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun x ↦ x.val.val) hij
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

lemma spatialPartition_near_weight {n : ℕ} (L : Length) (A : Finset (Torus L))
    {H s : ℝ} (hH : 8≤H) (hs : 2*s≤1) (X : Configuration n L) :
    ((localizedNearLabels L A s X).card:ℝ)≤
      ∑ σ : Fin n → Bool, ((nearLabels (fun i ↦ σ i=true) s X).card:ℝ)*
        ‖(productPartition n L (spatialInside L A H) (spatialOutside L A H) σ).toFun X‖^2 := by
  have hp := productPartition_norm_unity (spatialInside L A H) (spatialOutside L A H)
    (spatialInside_real L A H) (spatialOutside_real L A H) (spatialPartition_unity L A H) X
  calc
    _ = ((localizedNearLabels L A s X).card:ℝ)*
        (∑ σ : Fin n → Bool, ‖(productPartition n L (spatialInside L A H) (spatialOutside L A H) σ).toFun X‖^2) := by rw [hp,mul_one]
    _ = _ := Finset.mul_sum ..
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro σ _
      by_cases hn : (productPartition n L (spatialInside L A H) (spatialOutside L A H) σ).toFun X=0
      · simp only [hn,norm_zero,zero_pow (by norm_num : 2≠0),mul_zero,le_refl]
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast localizedNearLabels_card_le_selected L A hH hs σ X hn) (sq_nonneg _)

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped ENNReal

lemma measurable_close_predicate {n : ℕ} {L : Length} (s : ℝ) (i k : Fin n) :
    MeasurableSet {X : Configuration n L | torusDistance L (X k) (X i)≤2*s} := by
  have hc : Continuous (fun X : Configuration n L ↦ torusDistance L (X k) (X i)) :=
    by unfold torusDistance; fun_prop
  exact measurableSet_le hc.measurable measurable_const

lemma measurable_near_predicate {n : ℕ} {L : Length} (p : Fin n → Prop) [DecidablePred p]
    (s : ℝ) (i : {i // p i}) :
    MeasurableSet {X : Configuration n L | ∃ k : {k // p k}, k≠i ∧ torusDistance L (X k.val) (X i.val)≤2*s} := by
  simp only [Set.ofPred_exists,Set.ofPred_and]
  exact MeasurableSet.iUnion (fun k ↦ (MeasurableSet.const _).inter (measurable_close_predicate s i.val k.val))

lemma nearLabels_card_measurable {n : ℕ} {L : Length} (p : Fin n → Prop) [DecidablePred p] (s : ℝ) :
    Measurable (fun X : Configuration n L ↦ (nearLabels p s X).card) := by
  classical
  have h (i : {i // p i}) : Measurable (fun X : Configuration n L ↦
      if ∃ k : {k // p k}, k≠i ∧ torusDistance L (X k.val) (X i.val)≤2*s then (1:ℕ) else 0) :=
    Measurable.ite (measurable_near_predicate p s i) measurable_const measurable_const
  have hh := Finset.measurable_sum (s:=Finset.univ) (fun i _ ↦ h i)
  simpa only [nearLabels,Finset.card_eq_sum_ones,Finset.sum_filter] using hh

lemma measurable_localized_near_predicate {n : ℕ} (L : Length) (A : Finset (Torus L)) (s : ℝ) (i : Fin n) :
    MeasurableSet {X : Configuration n L | A.Nonempty ∧ spatialSiteDistance L A (X i)≤6 ∧
      ∃ k : Fin n, k≠i ∧ torusDistance L (X k) (X i)≤2*s} := by
  simp only [Set.ofPred_exists,Set.ofPred_and]
  refine (MeasurableSet.const _).inter ((measurableSet_le
    ((spatialSiteDistance_lipschitz L A).continuous.comp (continuous_apply i)).measurable measurable_const).inter ?_)
  exact MeasurableSet.iUnion (fun k ↦ (MeasurableSet.const _).inter (measurable_close_predicate s i k))

lemma localizedNearLabels_card_measurable {n : ℕ} (L : Length) (A : Finset (Torus L)) (s : ℝ) :
    Measurable (fun X : Configuration n L ↦ (localizedNearLabels L A s X).card) := by
  classical
  have h (i : Fin n) : Measurable (fun X : Configuration n L ↦
      if A.Nonempty ∧ spatialSiteDistance L A (X i)≤6 ∧
        ∃ k : Fin n, k≠i ∧ torusDistance L (X k) (X i)≤2*s then (1:ℕ) else 0) :=
    Measurable.ite (measurable_localized_near_predicate L A s i) measurable_const measurable_const
  have hh := Finset.measurable_sum (s:=Finset.univ) (fun i _ ↦ h i)
  simpa only [localizedNearLabels,Finset.card_eq_sum_ones,Finset.sum_filter] using hh

lemma spatialPartition_near_integral {n : ℕ} (L : Length) (A : Finset (Torus L))
    {H r s : ℝ} (hH : 8≤H) (hs : 0<s) (hs' : 2*s≤1) (hL : 10*s≤L.val) (hr : 0<r)
    (u : Jet n L) (hu : u∈dirichletDomain n L r) :
    ENNReal.ofReal (27/(262144*Real.sqrt 3)*r/s^3)*
      (∫⁻ X, ((localizedNearLabels L A s X).card:ℝ≥0∞)*ENNReal.ofReal (‖u.1 X‖^2))≤
      ENNReal.ofReal (spatialPartitionEnergy L A H u) := by
  let w := fun σ : Fin n → Bool ↦ productPartition n L (spatialInside L A H) (spatialOutside L A H) σ
  have hcoe : ∀ᵐ X ∂volume, ∀ σ, (w σ).onScalar u.1 X=(w σ).toFun X*u.1 X :=
    ae_all_iff.mpr (fun σ ↦ (w σ).coe_onScalar u.1)
  have hm (σ : Fin n → Bool) : Measurable (fun X : Configuration n L ↦
      ((nearLabels (fun i ↦ σ i=true) s X).card:ℝ≥0∞)*ENNReal.ofReal (‖(w σ).onScalar u.1 X‖^2)) :=
    ((measurable_of_countable (fun k : ℕ ↦ (k:ℝ≥0∞))).comp (nearLabels_card_measurable _ s)).mul
      ((Lp.stronglyMeasurable ((w σ).onScalar u.1)).measurable.norm.pow_const 2).ennreal_ofReal
  calc
    _ ≤ ENNReal.ofReal (27/(262144*Real.sqrt 3)*r/s^3)*
        (∫⁻ X, ∑ σ : Fin n → Bool, ((nearLabels (fun i ↦ σ i=true) s X).card:ℝ≥0∞)*
          ENNReal.ofReal (‖(w σ).onScalar u.1 X‖^2)) := by
      apply mul_le_mul_of_nonneg_left _ zero_le
      apply lintegral_mono_ae
      filter_upwards [hcoe] with X hX
      have h := ENNReal.ofReal_le_ofReal (spatialPartition_near_weight L A hH hs' X)
      rw [ENNReal.ofReal_natCast,ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))] at h
      simp_rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast] at h
      simp_rw [hX,norm_mul,mul_pow,ENNReal.ofReal_mul (sq_nonneg _),← mul_assoc,← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right h zero_le
    _ = ∑ σ : Fin n → Bool, ENNReal.ofReal (27/(262144*Real.sqrt 3)*r/s^3)*
        (∫⁻ X, ((nearLabels (fun i ↦ σ i=true) s X).card:ℝ≥0∞)*ENNReal.ofReal (‖(w σ).onScalar u.1 X‖^2)) := by
      rw [lintegral_finsetSum _ (fun σ _ ↦ hm σ),Finset.mul_sum]
    _ ≤ ∑ σ : Fin n → Bool, ENNReal.ofReal (selectedEnergy (fun i ↦ σ i=true) ((w σ).onJet u)) :=
      Finset.sum_le_sum (fun σ _ ↦ dirichlet_near_energy hs hL (fun i ↦ σ i=true) hr ((w σ).onJet u) ((w σ).onJet_mem_domain hu))
    _ = _ := by rw [spatialPartitionEnergy,ENNReal.ofReal_sum_of_nonneg (fun σ _ ↦ selectedEnergy_nonneg _ _)]

theorem spatial_near_average {n : ℕ} (L : Length) (A : Finset (Torus L))
    {r s : ℝ} (hs : 0<s) (hs' : 2*s≤1) (hL : 10*s≤L.val) (hr : 0<r)
    (u : Jet n L) (hu : u∈dirichletDomain n L r) :
    ENNReal.ofReal (Real.exp (-8)*(27/(262144*Real.sqrt 3))*r/s^3)*
      (∫⁻ X, ((localizedNearLabels L A s X).card:ℝ≥0∞)*ENNReal.ofReal (‖u.1 X‖^2))≤
      ∫⁻ H, ENNReal.ofReal (spatialPartitionEnergy L A H u) ∂radiusLaw := by
  let Q := ∫⁻ X, ((localizedNearLabels L A s X).card:ℝ≥0∞)*ENNReal.ofReal (‖u.1 X‖^2)
  let c := ENNReal.ofReal (27/(262144*Real.sqrt 3)*r/s^3)
  have htail : radiusLaw (Ici (8:ℝ))=ENNReal.ofReal (Real.exp (-8)) := by
    rw [←radiusLaw_tail_eq (by norm_num : (0:ℝ)≤8)]
    exact (ENNReal.ofReal_toReal (measure_ne_top radiusLaw _)).symm
  have hbound := lintegral_mono (μ:=radiusLaw) (f:=(Ici (8:ℝ)).indicator (fun _ ↦ c*Q))
    (g:=fun H ↦ ENNReal.ofReal (spatialPartitionEnergy L A H u)) (fun H ↦ by
      by_cases hH : H∈Ici (8:ℝ)
      · rw [indicator_of_mem hH]
        exact spatialPartition_near_integral L A hH hs hs' hL hr u hu
      · rw [indicator_of_notMem hH]; exact zero_le)
  rw [lintegral_indicator_const measurableSet_Ici,htail] at hbound
  apply le_trans _ hbound
  apply le_of_eq
  rw [show Real.exp (-8)*(27/(262144*Real.sqrt 3))*r/s^3=
    Real.exp (-8)*(27/(262144*Real.sqrt 3)*r/s^3) by ring,
    ENNReal.ofReal_mul (Real.exp_pos _).le]
  dsimp [c,Q]
  ac_rfl

end HardSphere

end

end OAI
