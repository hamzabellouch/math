import OAI.Probability.DilutedSpin.PoissonSmoothing
import OAI.Probability.DilutedSpin.RegularNodeGeometry

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology
open scoped NNReal BigOperators
noncomputable local instance regularNodeEstimatesDecidableEq (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
variable {p : ℕ}

/-- The old or genuinely delayed proper-child projection cost, in the same
physical scheduled covariance family as the parent. -/
noncomputable def physicalChildMass (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (s : Bool) (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) : ℝ :=
  (k:ℝ)*∑ j, Real.sqrt (physicalScheduledEnergy M θB hB N L u (C j)
    (DepthAverage.coordinateProjection (childCoordinates (hk := hk) j)
      (fun _ => DepthAverage.shiftPerm s) Q))

lemma physicalChildMass_nonneg (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (s : Bool) (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) :
    0≤physicalChildMass M θB hB N L u k hk C s Q := by
  unfold physicalChildMass
  positivity

lemma physicalChildMass_le_square (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (s : Bool) (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) :
    physicalChildMass M θB hB N L u k hk C s Q≤(k:ℝ)^2 := by
  unfold physicalChildMass
  calc
    _ ≤ (k:ℝ)*∑ j : Fin k, (1:ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j _
      exact (Real.sqrt_le_sqrt (physicalScheduledEnergy_le_one M θB hB N L u (C j) _)).trans_eq
        Real.sqrt_one
    _ = _ := by simp; ring

lemma physicalChildMass_le_sqrt (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (s : Bool) (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) :
    physicalChildMass M θB hB N L u k hk C s Q ≤
      (k:ℝ)*Real.sqrt (physicalChildMass M θB hB N L u k hk C s Q) := by
  have h := Real.sqrt_le_sqrt (physicalChildMass_le_square M θB hB N L u k hk C s Q)
  rw [Real.sqrt_sq (by positivity : (0:ℝ)≤k)] at h
  have hm := mul_le_mul_of_nonneg_right h
    (Real.sqrt_nonneg (physicalChildMass M θB hB N L u k hk C s Q))
  simpa only [← sq,Real.sq_sqrt (physicalChildMass_nonneg M θB hB N L u k hk C s Q)] using hm

 
noncomputable def physicalNodeShift (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) : ℝ :=
  ∫ z, projectionShiftError (some none) C (fun j => childBranchCoordinates (hk := hk) j)
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i : Labels L (Site N) => prior i.1.1) (gridExponents L) (physicalBase M θB hB N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u) z)
    (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L x) v))
      (I := Labels L (Site N)) (A := fun i => Alphabet i.1.1) (X := Bond p N) (Y := ℝ) (M := N) z) Q
    ∂fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N)

lemma physicalNodeShift_nonneg (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) :
    0≤physicalNodeShift M θB hB N L u k hk C Q :=
  integral_nonneg (fun _ => projectionShiftError_nonneg _ _ _ _ _ _)

/-- Topology-dependent quadratic energy budget in the depth continuity bound. -/
noncomputable def nodeShiftBudget (k : ℕ+) (C : Fin k → ReducedTopology) : ℝ :=
  8*((k:ℝ)*(∑ j, (Fintype.card (C j).Vertex:ℝ)*
    (∑ v : (C j).Vertex, (vertexArity (C j) v:ℝ)^2))+(k:ℝ)^2)

lemma nodeShiftBudget_nonneg (k : ℕ+) (C : Fin k → ReducedTopology) :
    0≤nodeShiftBudget k C := by unfold nodeShiftBudget; positivity

lemma physicalNodeShift_average (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (η : ℝ) (hlarge : 1<η*(L+1:ℕ)) :
    DepthAverage.average (regularShapeDomain (.node k hk C) (L+1) η)
      (physicalNodeShift M θB hB N L u k hk C)≤Real.sqrt (nodeShiftBudget k C/(L+1:ℕ)) :=
  regular_physical_shift_average M θB hB N L u k hk C η hlarge

lemma multileaf_scalar_bound {η c v δ err w w' h ch pa K P k : ℝ}
    (hc : η≤c) (hc1 : c≤1) (hv : 0≤v) (hw : 0≤w) (hh : 0≤h)
    (hch : ch≤K) (hpa : pa≤P) (hwk : w≤k*Real.sqrt w)
    (hstep : c*v≤2*(2*δ+err+(2*Real.sqrt w'+h)*ch+pa*(2*Real.sqrt w))+c*(16*w)) :
    η*v ≤ 4*δ+2*err+4*K*Real.sqrt w'+2*K*h+(4*P+16*k)*Real.sqrt w := by
  have h₁ := mul_le_mul_of_nonneg_left hch (by positivity : 0≤2*Real.sqrt w'+h)
  have h₂ := mul_le_mul_of_nonneg_right hpa (by positivity : 0≤2*Real.sqrt w)
  have h₃ := mul_le_mul_of_nonneg_right hc1 (by positivity : 0≤16*w)
  have h₄ := mul_le_mul_of_nonneg_left hwk (by norm_num : (0:ℝ)≤16)
  have h₅ := mul_le_mul_of_nonneg_right hc hv
  nlinarith only [hstep,h₁,h₂,h₃,h₄,h₅]

end DilutedSpinGlass.UniversalDictionary

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped NNReal
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]

/-- A bounded-test distance, with the scale written outside the test. -/
def BoundedDistance (μ ν : Measure X) (d : ℝ) : Prop :=
  ∀ (f : X → ℝ), Measurable f → ∀ (B : ℝ), (∀ x, |f x|≤B) →
    |(∫ x, f x ∂μ)-(∫ x, f x ∂ν)|≤B*d

lemma BoundedDistance.symm {μ ν : Measure X} {d : ℝ} (h : BoundedDistance μ ν d) :
    BoundedDistance ν μ d := by
  intro f hm B hf
  rw [abs_sub_comm]
  exact h f hm B hf

lemma BoundedDistance.prod {μ ν : Measure X} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {d : ℝ} (h : BoundedDistance μ ν d)
    (τ : Measure Y) [IsProbabilityMeasure τ] :
    BoundedDistance (μ.prod τ) (ν.prod τ) d := by
  intro f hm B hf
  have hi (κ : Measure X) [IsProbabilityMeasure κ] : Integrable f (κ.prod τ) :=
    (bounded_memLp hm hf 1).integrable le_rfl
  rw [integral_prod _ (hi μ),integral_prod _ (hi ν)]
  exact h _ hm.stronglyMeasurable.integral_prod_right'.measurable B
    (fun x => abs_integral_le_bound (fun y => hf (x,y)))

lemma BoundedDistance.prod_left {μ ν : Measure X} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {d : ℝ} (h : BoundedDistance μ ν d)
    (τ : Measure Y) [IsProbabilityMeasure τ] :
    BoundedDistance (τ.prod μ) (τ.prod ν) d := by
  intro f hm B hf
  have hi (κ : Measure X) [IsProbabilityMeasure κ] : Integrable f (τ.prod κ) :=
    (bounded_memLp hm hf 1).integrable le_rfl
  rw [integral_prod_symm _ (hi μ),integral_prod_symm _ (hi ν)]
  exact h _ hm.stronglyMeasurable.integral_prod_left'.measurable B
    (fun x => abs_integral_le_bound (fun y => hf (y,x)))

lemma poisson_boundedDistance (r s : ℝ≥0) (hr : 0<r) :
    BoundedDistance (ProbabilityTheory.poissonMeasure (r+s))
      (ProbabilityTheory.poissonMeasure r) ((s:ℝ)/Real.sqrt r) := by
  intro f _ B hf
  simpa only [mul_div_assoc] using poisson_bounded_rate_add r s hr hf

lemma BoundedDistance.familyLaw {I : Type} [Countable I] [MeasurableSpace I]
    [MeasurableSingletonClass I] {Z : I → Type} [∀ i, MeasurableSpace (Z i)]
    {μ ν : Measure I} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {d : ℝ} (h : BoundedDistance μ ν d)
    (κ : (i : I) → Measure (Z i)) [∀ i, IsProbabilityMeasure (κ i)] :
    BoundedDistance (familyLaw μ κ) (familyLaw ν κ) d := by
  intro f hm B hf
  have hi (ρ : Measure I) [IsProbabilityMeasure ρ] : Integrable f (DilutedSpinGlass.familyLaw ρ κ) :=
    (bounded_memLp hm hf 1).integrable le_rfl
  rw [integral_familyLaw μ κ (fun i x => f ⟨i,x⟩)
      (fun i => hm.comp (measurable_sigmaMk i)) (hi μ),
    integral_familyLaw ν κ (fun i x => f ⟨i,x⟩)
      (fun i => hm.comp (measurable_sigmaMk i)) (hi ν)]
  exact h _ (measurable_of_countable _) B
    (fun i => abs_integral_le_bound (fun x => hf ⟨i,x⟩))

lemma fullRoot_boundedDistance {M : ℕ} {I : Type} [MeasurableSpace I]
    (ξ : Fin M → Measure Y) [∀ i, IsProbabilityMeasure (ξ i)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s t : ℝ≥0) (hr : 0<r) :
    BoundedDistance (fullRootLaw ξ μ ν (r+s) t) (fullRootLaw ξ μ ν r t)
      ((s:ℝ)/Real.sqrt r) := by
  exact (((poisson_boundedDistance r s hr).familyLaw
    (fun k => rootLaw k (fun _ => μ))).prod (compoundRootLaw ν t)).prod_left (rootLaw M ξ)

end DilutedSpinGlass

end

end OAI
