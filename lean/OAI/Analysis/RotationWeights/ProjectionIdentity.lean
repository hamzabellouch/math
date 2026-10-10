import OAI.Analysis.RotationWeights.GraphTransfer

namespace OAI

noncomputable section

universe uX uE

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace

namespace CircleSampling
open MeasureTheory Set Filter ContinuousCircleWeight
open scoped ComplexInnerProductSpace Topology ENNReal
local instance : MeasurableSpace FiberHilbert := borel FiberHilbert
local instance : BorelSpace FiberHilbert := ⟨rfl⟩

structure ModelProjectionField where
  p : CircleX → FiberOperator
  projection : ∀ x,IsStarProjection (p x)
  norm_le : ∀ x,‖p x‖ ≤ 1
  measurable : ∀ k : ℤ,Measurable (fun x => p x (lp.single 2 k 1))
  invariant : ∀ᵐ x, (1-p x)*fiberCocycleShift (fun k => modelF k x)
    (fun k => modelF_pos k x) (modelF_antitone x)*p x=0
  covariance : ∀ n : ℤ, ∀ᵐ x, p x*(fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap=
    (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap*p (CircleModel.shift modelAngle n x)

def rationalCap (D : ℕ) : ℝ≥0 := ⟨Real.exp (∑ i∈Finset.range D,coordinateDrop i),(Real.exp_pos _).le⟩
lemma rationalCap_ge_one (D : ℕ) : (1:ℝ) ≤ rationalCap D := by
  apply Real.one_le_exp_iff.mpr
  exact Finset.sum_nonneg (fun i _ => dropSize_nonneg _)

lemma stageGraph_ae (j : ℕ) (t : Fin ((scaleState j).1.q (scaleState j).1.d))
    (P : CircleX×CircleX → Prop)
    (hP : ∀ n : (scaleStep j).samples t, ∀ᵐ x,stageWeight true j n.val x≠0 → P (x,orbitEquiv n.val x)) :
    ∀ᵐ z ∂(stageGraph j t:Measure (CircleX×CircleX)), P z := by
  change ∀ᵐ z ∂finiteGraphAverage volume (fun n : (scaleStep j).samples t => stageWeight true j n.val) (fun n => orbitEquiv n.val), P z
  unfold finiteGraphAverage
  apply Measure.ae_smul_measure
  apply ae_finsetSum_measure_iff.mpr
  intro n _
  rw [weightedGraph]
  have he : MeasurableEmbedding (fun x : CircleX => (x,orbitEquiv n.val x)) :=
    (measurable_id.prodMk (orbitEquiv n.val).measurable).measurableEmbedding (fun _ _ h => congrArg Prod.fst h)
  apply he.ae_map_iff.mpr
  rw [weightedMeasure,ae_withDensity_iff (stageWeight_measurable true j n.val).ennreal_ofReal]
  filter_upwards [hP n] with x hx hn
  apply hx
  intro hz
  exact hn (by simp [hz])

lemma rationalGraph_pair (P : ModelProjectionField) (D : ℕ) (a : Fin (frequency (D+1))) (j : ℕ) :
    ∀ᵐ z ∂(rationalGraph D a j:Measure (CircleX×CircleX)),
      (1-P.p z.2)*cappedDiagonal modelF (rationalCap D) z.1 z.2*P.p z.1=0 := by
  let N := D+1+j
  let t := rationalIndex D a j
  have hg : ∀ᵐ z ∂(stageGraph N t:Measure (CircleX×CircleX)), z.1∉graphBad N →
      (1-P.p z.2)*cappedDiagonal modelF (rationalCap D) z.1 z.2*P.p z.1=0 := by
    apply stageGraph_ae N t
    intro n
    filter_upwards [model_good_ae,P.invariant,P.covariance n.val] with x hx hi hc hw hbad
    have hn : (n.val.toNat:ℤ)=n.val := Int.toNat_of_nonneg (sample_bound N n.property).1.le
    have hb (k : ℤ) : modelF k (CircleModel.shift modelAngle n.val x)/modelF k x ≤ rationalCap D :=
      modelF_ratio_tail D hx ((modelGood_shift n.val x).mpr hx)
        (restricted_orbit_order N D (rationalPoint D a) (rational_tail_period D a) t
          (rationalIndex_spec D a j) n.val n.property x hbad hw) k
    have hr (k : ℤ) : modelF (k+(n.val.toNat:ℤ)) x=modelF k (CircleModel.shift modelAngle (n.val.toNat:ℤ) x)*modelF (n.val.toNat:ℤ) x := by
      simpa only [add_comm k] using modelF_add (n.val.toNat:ℤ) k x
    have hh := positive_orbit_capped_pair modelF modelF_pos modelF_antitone x (CircleModel.shift modelAngle n.val x) n.val.toNat
      (by simpa only [hn] using hr) (P.p x) (P.p (CircleModel.shift modelAngle n.val x)) (P.projection x) hi
      (by simpa only [hn] using hc) (rationalCap D) hb
    exact hh
  change ∀ᵐ z ∂(stageGraph N t:Measure (CircleX×CircleX)).restrict (Prod.fst ⁻¹' (graphBad N)ᶜ), _
  rw [ae_restrict_iff' ((graphBad_measurable N).compl.preimage measurable_fst)]
  exact hg

lemma rational_pair_graph (P : ModelProjectionField) (D : ℕ) (a : Fin (frequency (D+1))) :
    ∀ᵐ z ∂(circleProbability.toFiniteMeasure.map (fun x => (x,translation (rationalPoint D a) x)) : Measure (CircleX×CircleX)),
      (1-P.p z.2)*cappedDiagonal modelF (rationalCap D) z.1 z.2*P.p z.1=0 := by
  exact capped_pair_identity_transfer (μ := volume) (νs := rationalGraph D a) P.p P.norm_le P.measurable modelF modelF_measurable modelF_pos
    (rationalCap D) (rationalGraph_convergence D a).1 (rationalGraph_pair P D a) (rationalGraph_convergence D a).2

lemma rational_pair (P : ModelProjectionField) (D : ℕ) (a : Fin (frequency (D+1))) :
    ∀ᵐ x, (1-P.p (x+rationalPoint D a))*cappedDiagonal modelF (rationalCap D) x (x+rationalPoint D a)*P.p x=0 := by
  have hh := rational_pair_graph P D a
  change ∀ᵐ z ∂Measure.map (fun x : CircleX => (x,x+rationalPoint D a)) volume, _ at hh
  exact ae_of_ae_map (p := fun z : CircleX×CircleX =>
    (1-P.p z.2)*cappedDiagonal modelF (rationalCap D) z.1 z.2*P.p z.1=0) (show AEMeasurable (fun x : CircleX => (x,x+rationalPoint D a)) volume from
    (measurable_id.prodMk (measurable_id.add_const _)).aemeasurable) hh
end CircleSampling

namespace ContinuousCircleWeight
open MeasureTheory Filter Set
open scoped Topology ComplexInnerProductSpace
local instance : MeasurableSpace FiberHilbert := borel FiberHilbert
local instance : BorelSpace FiberHilbert := ⟨rfl⟩

lemma stronglyMeasurable_lp_field {X : Type uX} [MeasurableSpace X]
    (A : X → FiberOperator)
    (hc : ∀ k : ℤ, Measurable (fun x ↦ A x (lp.single 2 k 1)))
    (u : FiberHilbert) : StronglyMeasurable (fun x ↦ A x u) := by
  classical
  let v : Finset ℤ → FiberHilbert := fun s ↦ ∑ k ∈ s, lp.single 2 k (u k)
  have hv : Tendsto v atTop (𝓝 u) := lp.hasSum_single (by norm_num) u
  apply stronglyMeasurable_of_tendsto atTop (f := fun s x => A x (v s))
  · intro s
    simp only [v,map_sum]
    apply Finset.stronglyMeasurable_fun_sum
    intro k _
    have he : lp.single (E := fun _ : ℤ ↦ ℂ) 2 k (u k) = (u k) • lp.single 2 k (1 : ℂ) := by
      simpa using (lp.single_smul (E := fun _ : ℤ ↦ ℂ) 2 k (u k) (1 : ℂ))
    simp only [he,map_smul]
    exact (hc k).stronglyMeasurable.const_smul (u k)
  · exact tendsto_pi_nhds.mpr (fun x => (A x).continuous.tendsto u |>.comp hv)

lemma stronglyMeasurable_field_simple {X : Type uX} {E : Type uE} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : X → (E →L[ℂ] E)) (hT : ∀ v, StronglyMeasurable (fun x ↦ T x v)) (s : SimpleFunc X E) :
    StronglyMeasurable (fun x ↦ T x (s x)) := by
  classical
  have he : (fun x ↦ T x (s x)) = ∑ a ∈ s.range, (s ⁻¹' {a}).indicator (fun x ↦ T x a) := by
    funext x
    simp [Set.indicator, s.mem_range_self]
  rw [he]
  exact s.range.stronglyMeasurable_sum fun a _ ↦ (hT a).indicator (s.measurableSet_fiber a)

lemma stronglyMeasurable_field_apply {X : Type uX} {E : Type uE} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : X → (E →L[ℂ] E)) (hT : ∀ v, StronglyMeasurable (fun x ↦ T x v))
    (f : X → E) (hf : StronglyMeasurable f) : StronglyMeasurable (fun x ↦ T x (f x)) := by
  apply stronglyMeasurable_of_tendsto atTop
    (fun n ↦ stronglyMeasurable_field_simple T hT (hf.approx n))
  exact tendsto_pi_nhds.mpr fun x ↦ ((T x).continuous.tendsto (f x)).comp (hf.tendsto_approx x)

lemma measurable_cappedDiagonal {X : Type uX} [MeasurableSpace X]
    (F : ℤ → X → ℝ) (hF : ∀ k,Measurable (F k))
    (B : ℝ≥0) (u : FiberHilbert) :
    Measurable (fun z : X×X => cappedDiagonal F B z.1 z.2 u) := by
  apply (stronglyMeasurable_lp_field _ ?_ u).measurable
  intro k
  have he : (fun z : X × X ↦ cappedDiagonal F B z.1 z.2 (lp.single 2 k 1)) =
      (fun z ↦ (cappedRatio F B z.1 z.2 k : ℂ) • lp.single 2 k 1) := by
    funext z
    ext i
    simp only [cappedDiagonal,lpDiagonal_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
    by_cases hi : i=k
    · subst i; simp
    · simp [lp.single_apply,hi]
  rw [he]
  have hr : Measurable (fun z : X×X => cappedRatio F B z.1 z.2 k) :=
    measurable_const.min (measurable_const.max (((hF k).comp measurable_snd).div ((hF k).comp measurable_fst)))
  exact hr.complex_ofReal.smul measurable_const

lemma measurableSet_cappedPairRelation {X : Type uX} [MeasurableSpace X]
    (p : X → FiberOperator) (hp : ∀ k : ℤ,Measurable (fun x => p x (lp.single 2 k 1)))
    (F : ℤ → X → ℝ) (hF : ∀ k,Measurable (F k)) (B : ℝ≥0) :
    MeasurableSet (cappedPairRelation p F B) := by
  unfold cappedPairRelation
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  have hp' : ∀ u,StronglyMeasurable (fun z : X×X => p z.2 u) := fun u =>
    (stronglyMeasurable_lp_field p hp u).comp_measurable measurable_snd
  have hD : ∀ u,StronglyMeasurable (fun z : X×X => cappedDiagonal F B z.1 z.2 u) := fun u =>
    (measurable_cappedDiagonal F hF B u).stronglyMeasurable
  have hu : StronglyMeasurable (fun z : X×X => cappedDiagonal F B z.1 z.2 (p z.1 (lp.single 2 k 1))) :=
    stronglyMeasurable_field_apply _ hD _ ((hp k).comp measurable_fst).stronglyMeasurable
  have hd := hu.sub (stronglyMeasurable_field_apply _ hp' _ hu)
  exact measurableSet_eq_fun hd.measurable measurable_const
end ContinuousCircleWeight

end

end OAI
