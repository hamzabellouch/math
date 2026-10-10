import Mathlib
import OAI.Analysis.HardSphere.FormDomain.HilbertJet
import OAI.Analysis.HardSphere.Bridges.Index

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener

instance configurationBorel (N : ℕ) (L : Length) : BorelSpace (Configuration N L) := by
  unfold Configuration
  exact Pi.borelSpace

abbrev ConfigurationPath (N : ℕ) (L : Length) := C(Time, Configuration N L)
instance configurationPathMeasurable (N : ℕ) (L : Length) : MeasurableSpace (ConfigurationPath N L) := borel _
instance configurationPathBorel (N : ℕ) (L : Length) : BorelSpace (ConfigurationPath N L) := ⟨rfl⟩

def staysAllowed (N : ℕ) (L : Length) (a : ℝ) : Set (ConfigurationPath N L) :=
  {f | Set.range f ⊆ allowed N L a}

lemma staysAllowed_open (N : ℕ) (L : Length) (a : ℝ) : IsOpen (staysAllowed N L a) :=
  ContinuousMap.isOpen_setOfPred_range_subset (isOpen_allowed N L a)

lemma staysAllowed_antitone (N : ℕ) (L : Length) : Antitone (staysAllowed N L) := by
  intro a b hab f hf
  exact hf.trans (allowed_antitone N L hab)

lemma staysAllowed_innerRadius (N : ℕ) (L : Length) (a : ℝ) :
    (⋃ n, staysAllowed N L (innerRadius a n)) = staysAllowed N L a := by
  apply Set.Subset.antisymm
  · exact iUnion_subset fun n ↦ staysAllowed_antitone N L (innerRadius_gt a n).le
  · intro f hf
    have hcompact : IsCompact (Set.range f) := isCompact_range f.continuous
    obtain ⟨n,hn⟩ := hcompact.elim_directed_cover (fun n ↦ allowed N L (innerRadius a n))
      (fun n ↦ isOpen_allowed N L _) (by rw [iUnion_allowed_innerRadius]; exact hf)
      (fun m n ↦ ⟨max m n,allowed_antitone N L (innerRadius_antitone a (le_max_left _ _)),
        allowed_antitone N L (innerRadius_antitone a (le_max_right _ _))⟩)
    exact mem_iUnion.mpr ⟨n,hn⟩

abbrev CoordinatePaths (N : ℕ) := Direction N → C(Time,ℝ)

def coordinateWiener (N : ℕ) : Measure (CoordinatePaths N) := Measure.pi (fun _ ↦ wiener)
instance coordinateWiener_probability (N : ℕ) : IsProbabilityMeasure (coordinateWiener N) := by
  unfold coordinateWiener
  infer_instance

def freeTrajectory (N : ℕ) (L : Length) (s : ℝ) (w : CoordinatePaths N)
    (X : Configuration N L) : ConfigurationPath N L :=
  ⟨fun t i j ↦ X i j + ((Real.sqrt (2*s) * w (i,j) t : ℝ) : AddCircle L.val), by
    continuity⟩

lemma freeTrajectory_continuous (N : ℕ) (L : Length) (s : ℝ) :
    Continuous (fun p : CoordinatePaths N × Configuration N L ↦ freeTrajectory N L s p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  unfold Function.uncurry
  change Continuous (fun p : (CoordinatePaths N × Configuration N L) × Time ↦
    fun i j ↦ p.1.2 i j + ((Real.sqrt (2*s) * p.1.1 (i,j) p.2 : ℝ) : AddCircle L.val))
  fun_prop

def freePathLaw (N : ℕ) (L : Length) (s : ℝ) : Measure (ConfigurationPath N L) :=
  ((coordinateWiener N).prod (volume : Measure (Configuration N L))).map
    (fun p ↦ freeTrajectory N L s p.1 p.2)

lemma freeTrajectory_marginal (N : ℕ) (L : Length) (s : ℝ) (t : Time) :
    MeasurePreserving (fun p : CoordinatePaths N × Configuration N L ↦ freeTrajectory N L s p.1 p.2 t)
      ((coordinateWiener N).prod volume) volume := by
  let : (volume : Measure (Torus L)).IsAddLeftInvariant := by
    rw [volume_pi]
    exact Measure.pi.isAddLeftInvariant _
  let : (volume : Measure (Configuration N L)).IsAddLeftInvariant := by
    rw [volume_pi]
    exact Measure.pi.isAddLeftInvariant _
  let : (volume : Measure (Configuration N L)).IsAddRightInvariant :=
    IsAddLeftInvariant.isAddRightInvariant
  have hm : Measurable (fun p : CoordinatePaths N × Configuration N L ↦ freeTrajectory N L s p.1 p.2 t) :=
    ((freeTrajectory_continuous N L s).eval continuous_const).measurable
  have hskew := (MeasurePreserving.id (coordinateWiener N)).skew_product hm
    (Filter.Eventually.of_forall (fun w : CoordinatePaths N ↦
      map_add_right_eq_self (volume : Measure (Configuration N L))
        (fun i j ↦ ((Real.sqrt (2*s) * w (i,j) t : ℝ) : AddCircle L.val))))
  exact (measurePreserving_snd (μ := coordinateWiener N) (ν := (volume : Measure (Configuration N L)))).comp hskew

lemma freePathLaw_marginal (N : ℕ) (L : Length) (s : ℝ) (t : Time) :
    MeasurePreserving (fun f : ConfigurationPath N L ↦ f t) (freePathLaw N L s) volume := by
  have he : Measurable (fun f : ConfigurationPath N L ↦ f t) :=
    (continuous_id.eval continuous_const).measurable
  refine ⟨he,?_⟩
  rw [freePathLaw,Measure.map_map he (freeTrajectory_continuous N L s).measurable]
  exact (freeTrajectory_marginal N L s t).map_eq

def killedPathLaw (N : ℕ) (L : Length) (a s : ℝ) : Measure (ConfigurationPath N L) :=
  (freePathLaw N L s).restrict (staysAllowed N L a)

end HardSphere

namespace L2Multiplier
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

def apply (f : α → ℂ) (hf : MemLp f ∞ μ) (u : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (hf.mul (Lp.memLp u)).toLp (f * u)

lemma coe_apply (f : α → ℂ) (hf : MemLp f ∞ μ) (u : Lp ℂ 2 μ) :
    apply f hf u =ᵐ[μ] fun x ↦ f x * u x :=
  MemLp.coeFn_toLp _

def linearMap (f : α → ℂ) (hf : MemLp f ∞ μ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := apply f hf
  map_add' u v := by
    apply Lp.ext
    filter_upwards [coe_apply f hf (u + v), coe_apply f hf u, coe_apply f hf v,
      Lp.coeFn_add u v, Lp.coeFn_add (apply f hf u) (apply f hf v)] with x huv hu hv h1 h2
    simp only [huv, h1, h2, Pi.add_apply, hu, hv, mul_add]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [coe_apply f hf (c • u), coe_apply f hf u,
      Lp.coeFn_smul c u, Lp.coeFn_smul c (apply f hf u)] with x h1 h2 h3 h4
    simp only [h1, h3, h4, Pi.smul_apply, h2, smul_eq_mul, RingHom.id_apply]
    ring

lemma norm_apply_le (f : α → ℂ) (hf : MemLp f ∞ μ) (u : Lp ℂ 2 μ) :
    ‖apply f hf u‖ ≤ lpNorm f ∞ μ * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coe_apply f hf u, ae_le_lpNorm_exponent_top hf] with x hx hfx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hfx (norm_nonneg _)

def clm (f : α → ℂ) (hf : MemLp f ∞ μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (linearMap f hf).mkContinuous (lpNorm f ∞ μ) (norm_apply_le f hf)

lemma coe_clm (f : α → ℂ) (hf : MemLp f ∞ μ) (u : Lp ℂ 2 μ) :
    clm f hf u =ᵐ[μ] fun x ↦ f x * u x := coe_apply f hf u

lemma clm_mul (f g : α → ℂ) (hf : MemLp f ∞ μ) (hg : MemLp g ∞ μ)
    (u : Lp ℂ 2 μ) : clm (f * g) (hf.mul hg) u = clm f hf (clm g hg u) := by
  apply Lp.ext
  filter_upwards [coe_clm (f * g) (hf.mul hg) u, coe_clm f hf (clm g hg u),
    coe_clm g hg u] with x h1 h2 h3
  simp only [h1, h2, h3, Pi.mul_apply, mul_assoc]

lemma inner_clm_right (f : α → ℂ) (hf : MemLp f ∞ μ) (u v : Lp ℂ 2 μ) :
    inner ℂ u (clm f hf v) = inner ℂ (clm (fun x ↦ conj (f x)) hf.star u) v := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_clm f hf v, coe_clm (fun x ↦ conj (f x)) hf.star u] with x h1 h2
  simp only [h1, h2, RCLike.inner_apply, map_mul, starRingEnd_self_apply]
  ring

end L2Multiplier

namespace HardSphere
open Wiener
open scoped ComplexConjugate

abbrev FreePathL2 (N : ℕ) (L : Length) (t : ℝ) :=
  Lp ℂ 2 (freePathLaw N L t)

def endpointPull (N : ℕ) (L : Length) (t : ℝ) (s : Time) :
    ScalarL2 N L →ₗᵢ[ℂ] FreePathL2 N L t :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun ω : ConfigurationPath N L ↦ ω s)
    (freePathLaw_marginal N L t s)

lemma endpointPull_ae (N : ℕ) (L : Length) (t : ℝ) (s : Time) (f : ScalarL2 N L) :
    endpointPull N L t s f =ᵐ[freePathLaw N L t] fun ω ↦ f (ω s) :=
  Lp.coeFn_compMeasurePreserving f (freePathLaw_marginal N L t s)

lemma avoidanceIndicator_memLp (N : ℕ) (L : Length) (a t : ℝ) :
    MemLp ((staysAllowed N L a).indicator (fun _ ↦ (1:ℂ))) ∞ (freePathLaw N L t) := by
  exact MemLp.indicator (staysAllowed_open N L a).measurableSet (memLp_top_const (1:ℂ))

def avoidanceMultiplier (N : ℕ) (L : Length) (a t : ℝ) : FreePathL2 N L t →L[ℂ] FreePathL2 N L t :=
  L2Multiplier.clm _ (avoidanceIndicator_memLp N L a t)

lemma avoidanceMultiplier_ae (N : ℕ) (L : Length) (a t : ℝ) (f : FreePathL2 N L t) :
    avoidanceMultiplier N L a t f =ᵐ[freePathLaw N L t] (staysAllowed N L a).indicator f := by
  filter_upwards [L2Multiplier.coe_clm _ (avoidanceIndicator_memLp N L a t) f] with ω hω
  rw [avoidanceMultiplier, hω]
  by_cases h : ω ∈ staysAllowed N L a <;> simp [h]

lemma avoidanceMultiplier_contraction (N : ℕ) (L : Length) (a t : ℝ) (f : FreePathL2 N L t) :
    ‖avoidanceMultiplier N L a t f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [avoidanceMultiplier_ae N L a t f] with ω hω
  rw [hω]
  by_cases h : ω ∈ staysAllowed N L a <;> simp [h]

lemma avoidanceMultiplier_norm_le (N : ℕ) (L : Length) (a t : ℝ) :
    ‖avoidanceMultiplier N L a t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  simpa only [one_mul] using avoidanceMultiplier_contraction N L a t

lemma integrable_killed_endpoints (N : ℕ) (L : Length) (a t : ℝ)
    (f g : ScalarL2 N L) (u v : Time) :
    Integrable (fun ω : ConfigurationPath N L ↦ conj (f (ω u)) * g (ω v))
      (killedPathLaw N L a t) := by
  exact (((Lp.memLp f).comp_measurePreserving (freePathLaw_marginal N L t u)).star.integrable_mul
    ((Lp.memLp g).comp_measurePreserving (freePathLaw_marginal N L t v))).restrict

def killedTransition (N : ℕ) (L : Length) (a t : ℝ) : ScalarL2 N L →L[ℂ] ScalarL2 N L :=
  (endpointPull N L t 0).toContinuousLinearMap.adjoint ∘L
    (avoidanceMultiplier N L a t ∘L (endpointPull N L t 1).toContinuousLinearMap)

lemma killedTransition_pairing (N : ℕ) (L : Length) (a t : ℝ) (f g : ScalarL2 N L) :
    inner ℂ f (killedTransition N L a t g) =
      ∫ ω, conj (f (ω 0)) * g (ω 1) ∂killedPathLaw N L a t := by
  rw [killedTransition,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right]
  rw [L2.inner_def]
  change (∫ ω, inner ℂ (endpointPull N L t 0 f ω)
    (avoidanceMultiplier N L a t (endpointPull N L t 1 g) ω) ∂freePathLaw N L t) = _
  rw [killedPathLaw, ← integral_indicator (staysAllowed_open N L a).measurableSet]
  apply integral_congr_ae
  filter_upwards [endpointPull_ae N L t 0 f,endpointPull_ae N L t 1 g,
    avoidanceMultiplier_ae N L a t (endpointPull N L t 1 g)] with ω hf hg ha
  rw [hf,ha]
  by_cases h : ω ∈ staysAllowed N L a
  · simp only [Set.indicator_of_mem h,hg,RCLike.inner_apply,mul_comm]
  · simp only [Set.indicator_of_notMem h,inner_zero_right]

lemma killedTransition_norm_le (N : ℕ) (L : Length) (a t : ℝ) :
    ‖killedTransition N L a t‖ ≤ 1 := by
  unfold killedTransition
  calc
    _ ≤ ‖(endpointPull N L t 0).toContinuousLinearMap.adjoint‖ *
        (‖avoidanceMultiplier N L a t‖ * ‖(endpointPull N L t 1).toContinuousLinearMap‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1* (1*1) := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact mul_le_mul (LinearIsometry.norm_toContinuousLinearMap_le _) (mul_le_mul
        (avoidanceMultiplier_norm_le N L a t) (LinearIsometry.norm_toContinuousLinearMap_le _)
        (norm_nonneg _) zero_le_one) (by positivity) zero_le_one
    _ = 1 := by norm_num

lemma killedTransition_apply_contraction (N : ℕ) (L : Length) (a t : ℝ) (g : ScalarL2 N L) :
    ‖killedTransition N L a t g‖ ≤ ‖g‖ := by
  simpa only [one_mul] using (ContinuousLinearMap.le_opNorm (killedTransition N L a t) g).trans
    (mul_le_mul_of_nonneg_right (killedTransition_norm_le N L a t) (norm_nonneg g))

end HardSphere

noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate

end
end
end
end
end
end

end OAI
