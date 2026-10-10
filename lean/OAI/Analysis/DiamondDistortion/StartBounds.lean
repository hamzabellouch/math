import OAI.Analysis.DiamondDistortion.Descent

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace StartModel

section
open RecursiveModel PathModel
instance repComplete (h : ℕ) : CompleteSpace (Rep h) := by
  induction h with
  | zero => infer_instance
  | succ h ih =>
    change CompleteSpace (WithLp 1 (L1 (h+1) × lp (fun _ : ℕ => Rep h) 2))
    infer_instance

def outputCoordinate (h : ℕ) (r : Coord h) : Rep h →L[ℝ] ℝ :=
  ((LinearMap.proj r).comp (output h)).mkContinuous 1 (by
    intro d
    change ‖output h d r‖ ≤ 1*‖d‖
    simpa only [Real.norm_eq_abs,one_mul] using output_coordinate h d r)
def outputContinuous (h : ℕ) : Rep h →L[ℝ] (Coord h → ℝ) :=
  ContinuousLinearMap.pi (outputCoordinate h)
instance kernelClosed (h : ℕ) : IsClosed (LinearMap.ker (output h) : Set (Rep h)) :=
  (outputContinuous h).isClosed_ker

/-- The complete infimal-cost space of *all* finite-cost coordinate outputs,
    modulo representations with zero output. -/
abbrev FullComponent (h : ℕ) := Rep h ⧸ LinearMap.ker (output h)
instance fullComponentNormed (h : ℕ) : NormedAddCommGroup (FullComponent h) := by
  letI : IsClosed (LinearMap.ker (output h) : Set (Rep h)) := kernelClosed h
  exact Submodule.Quotient.normedAddCommGroup _
-- Help typeclass matching across the recursive successor representation model.
instance fullComponentNormedSucc (h : ℕ) : NormedAddCommGroup (FullComponent (h+1)) := fullComponentNormed (h+1)
instance fullComponentComplete (h : ℕ) : CompleteSpace (FullComponent h) := inferInstance
def componentEmbedding (h : ℕ) : Vec h →ₗ[ℝ] FullComponent h :=
  (LinearMap.ker (output h)).mkQ.comp (finiteSection h)
lemma componentEmbedding_norm (h : ℕ) (v : Vec h) : ‖componentEmbedding h v‖=finiteCost h v := rfl

/-- The dense class of representations whose coordinate output is finite. -/
def finiteOutputs (h : ℕ) : Submodule ℝ (Rep h) :=
  (LinearMap.range (relation h).value).comap (output h)

def rootInjection (h : ℕ) : L1 (h+1) →L[ℝ] Rep (h+1) :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ (L1 (h+1)) (lp (fun _ : ℕ => Rep h) 2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ _ _)
def childrenInjection (h : ℕ) : lp (fun _ : ℕ => Rep h) 2 →L[ℝ] Rep (h+1) :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ (L1 (h+1)) (lp (fun _ : ℕ => Rep h) 2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ _ _)
def childInjection (h i : ℕ) : Rep h →L[ℝ] Rep (h+1) :=
  (childrenInjection h).comp (lp.singleContinuousLinearMap (𝕜 := ℝ) (E := fun _ : ℕ => Rep h) (p := 2) i)
lemma output_rootInjection (h : ℕ) (μ : L1 (h+1)) (r : Coord (h+1)) :
    output (h+1) (rootInjection h μ) r=path (h+1) μ r := by
  cases r with
  | inl u => cases u; rfl
  | inr a =>
    change path (h+1) μ (.inr a)+output h 0 a.2=path (h+1) μ (.inr a)
    simp only [map_zero,Pi.zero_apply,add_zero]
lemma rootInjection_finite (h : ℕ) (s : Coord (h+1)) (c : ℝ) :
    rootInjection h (lp.single 1 s c) ∈ finiteOutputs (h+1) := by
  let v : Vec (h+1) := Finsupp.onFinset (ancestors (h+1) s)
    (fun r => if r ∈ ancestors (h+1) s then c else 0) (fun r hr => by
      by_contra hn
      simp only [hn,ite_false,ne_eq,not_true_eq_false] at hr)
  refine ⟨v,?_⟩
  ext r
  change v r=output (h+1) (rootInjection h (lp.single 1 s c)) r
  rw [output_rootInjection,path_single]
  change (if r ∈ ancestors (h+1) s then c else 0)=c*branch (h+1) s r
  rw [branch_apply]
  split_ifs <;> ring
lemma childInjection_finite (h i : ℕ) (d : Rep h) (hd : d ∈ finiteOutputs h) :
    childInjection h i d ∈ finiteOutputs (h+1) := by
  obtain ⟨v,hv⟩ := hd
  let e : Coord h ↪ Coord (h+1) := ⟨fun r => .inr (i,r),by intro a b hab; exact (Prod.mk.inj (Sum.inr.inj hab)).2⟩
  refine ⟨Finsupp.embDomain e v,?_⟩
  ext r
  cases r with
  | inl u =>
    change (Finsupp.embDomain e v) (.inl u)=path (h+1) 0 (root (h+1))
    rw [map_zero]
    exact Finsupp.embDomain_of_notMem_range e v (.inl u) (by rintro ⟨a,ha⟩; cases ha)
  | inr a =>
    change (Finsupp.embDomain e v) (.inr a)=path (h+1) 0 (.inr a)+output h ((lp.single 2 i d : lp (fun _ : ℕ => Rep h) 2) a.1) a.2
    rw [map_zero]
    change _=0+_
    rw [zero_add]
    by_cases hi : a.1=i
    · obtain ⟨j,r⟩ := a
      change j=i at hi
      subst j
      rw [lp.single_apply_self]
      change (Finsupp.embDomain e v) (e r)=output h d r
      rw [Finsupp.embDomain_apply_self]
      exact congrFun hv r
    · rw [lp.single_apply_ne _ _ _ hi,map_zero]
      apply Finsupp.embDomain_of_notMem_range
      rintro ⟨r,hr⟩
      exact hi (Prod.mk.inj (Sum.inr.inj hr)).1.symm

lemma finiteOutputs_dense (h : ℕ) : Dense (finiteOutputs h : Set (Rep h)) := by
  induction h with
  | zero =>
    intro d
    apply subset_closure
    refine ⟨Finsupp.single () d,?_⟩
    ext r
    cases r
    change (Finsupp.single () d : Vec 0) ()=d
    exact Finsupp.single_eq_same
  | succ h ih =>
    let K := (finiteOutputs (h+1)).topologicalClosure
    have hK : IsClosed (K : Set (Rep (h+1))) := (finiteOutputs (h+1)).isClosed_topologicalClosure
    have hroot (μ : L1 (h+1)) : rootInjection h μ ∈ K := by
      apply hK.mem_of_tendsto ((rootInjection h).hasSum (lp.hasSum_single (by norm_num : (1:ℝ≥0∞) ≠ ⊤) μ))
      exact Filter.Eventually.of_forall (fun S => K.sum_mem (fun s _ => subset_closure (rootInjection_finite h s (μ s))))
    have hchild (i : ℕ) (d : Rep h) : childInjection h i d ∈ K := by
      induction d using ih.denseRange_val.induction_on with
      | hp => exact hK.preimage (childInjection h i).continuous
      | ih d => exact subset_closure (childInjection_finite h i d d.property)
    have hchildren (w : lp (fun _ : ℕ => Rep h) 2) : childrenInjection h w ∈ K := by
      apply hK.mem_of_tendsto ((childrenInjection h).hasSum (lp.hasSum_single (by norm_num : (2:ℝ≥0∞) ≠ ⊤) w))
      exact Filter.Eventually.of_forall (fun S => K.sum_mem (fun i _ => hchild i (w i)))
    intro d
    change d ∈ K
    have he : d=rootInjection h d.fst+childrenInjection h d.snd := by
      change d=WithLp.toLp 1 (d.fst,0)+WithLp.toLp 1 (0,d.snd)
      apply (WithLp.equiv 1 _).injective
      change (d.fst,d.snd)=(d.fst+0,0+d.snd)
      rw [add_zero,zero_add]
    rw [he]
    exact K.add_mem (hroot d.fst) (hchildren d.snd)

lemma componentEmbedding_dense (h : ℕ) : DenseRange (componentEmbedding h) := by
  intro x
  obtain ⟨d,rfl⟩ := (LinearMap.ker (output h)).mkQ_surjective x
  induction d using (finiteOutputs_dense h).denseRange_val.induction_on with
  | hp => exact isClosed_closure.preimage (LinearMap.ker (output h)).mkQL.continuous
  | ih d =>
    obtain ⟨v,hv⟩ := d.property
    apply subset_closure
    refine ⟨v,?_⟩
    exact ((relation h).representation_eq hv.symm).symm
end

open RecursiveModel PathApplications
/-- All countable finite-cost start outputs, componentwise quotient, outer ℓ². -/
abbrev FullSpace := lp (fun h : ℕ => FullComponent (h+1)) 2
def fullEmbedding : ForestVec →ₗ[ℝ] FullSpace :=
  outerEmbedding (fun h => componentEmbedding (h+1))
lemma fullEmbedding_norm (v : ForestVec) : ‖fullEmbedding v‖=forestSeminorm v :=
  outerEmbedding_norm _ _ (fun h v => componentEmbedding_norm (h+1) v) v
lemma fullEmbedding_dense : DenseRange fullEmbedding :=
  outerEmbedding_dense _ (fun h => componentEmbedding_dense (h+1))
def fullEquiv : Space ≃ₗᵢ[ℝ] FullSpace := data.completionEquiv fullEmbedding fullEmbedding_norm fullEmbedding_dense
lemma fullEquiv_embedding (v : ForestVec) : fullEquiv (data.embedding v)=fullEmbedding v :=
  data.completionMap_coe _ _ _
def fullHeads : Midpoint.Heads ForestHead FullSpace := heads.transport fullEquiv

theorem full_graph (hinput : StartInput fullHeads) {D s : ℝ}
    (k : ℕ) (f : Diamond.Vertex k → FullSpace) (hf : Diamond.HasDistortion k f D s) :
    1+(k:ℝ)/128 ≤ D^2 := start_cost fullHeads hinput k f hf
end StartModel

namespace PathModel
open RecursiveModel PathApplications
def linearFullHeads : Midpoint.Heads ForestHead FullLinearSpace := linearHeads.transport linearFullEquiv
def quadraticFullHeads : Midpoint.Heads ForestHead FullQuadraticSpace := quadraticHeads.transport quadraticFullEquiv

theorem linear_full_flow_graph (hinput : FlowInput linearFullHeads (linearC^2))
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → FullLinearSpace) (hf : Diamond.HasDistortion k f D s) :
    1+(k:ℝ)/(2*linearC^2) ≤ D^2 ∧ (k:ℝ) ≤ 2*linearC^2*D^2 :=
  linear_flow linearFullHeads hinput k f hf
theorem linear_full_trimming_graph (hinput : FlowInput linearFullHeads 242)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → FullLinearSpace) (hf : Diamond.HasDistortion k f D s) :
    1+(k:ℝ)/484 ≤ D^2 := linear_trimming linearFullHeads hinput k f hf
theorem linear_full_clipping_graph (hinput : linearFullHeads.ParametricInput (1/2) 4)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → FullLinearSpace) (hf : Diamond.HasDistortion k f D s) :
    1+(k:ℝ)*clippingGamma D/(2*clippingQ D) ≤ D :=
  linear_clipping linearFullHeads hinput k f hf
theorem linear_full_vanishing_graph (hinput : linearFullHeads.TailVanishing) :
    ¬ Diamond.UniformEmbeddings FullLinearSpace := linearFullHeads.vanishing_obstruction hinput

theorem quadratic_full_graph (hinput : ArbitraryTailInput quadraticFullHeads 8)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → FullQuadraticSpace) (hf : Diamond.HasDistortion k f D s) :
    1+(k:ℝ)/64 ≤ D^2 := quadratic_cost quadraticFullHeads hinput k f hf

theorem stopped_full_graph (hinput : StoppedInput quadraticFullHeads)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → FullQuadraticSpace) (hf : Diamond.HasDistortion k f D s) :
    (k:ℝ) ≤ 144*D^2 := stopped_flow quadraticFullHeads hinput k f hf

theorem quadratic_full_component_graph (hinput : ComponentSumInput FullQuadraticSpace)
    {D s e : ℝ} (he : 0 < e) (he16 : e ≤ 1/16) (hsmall : 17*(2*e)^((1:ℝ)/6) < 1/(2*D))
    (k : ℕ) (f : Diamond.Vertex k → FullQuadraticSpace) (hf : Diamond.HasDistortion k f D s) :
    (1+e/2)^k ≤ D := component_sum hinput he he16 hsmall k f hf

theorem quadratic_full_relative_graph (hinput : RelativeInput quadraticFullHeads) {D s : ℝ}
    (k : ℕ) (f : Diamond.Vertex k → FullQuadraticSpace) (hf : Diamond.HasDistortion k f D s) :
    (1+relativeDelta D)^k ≤ D := relative_cost quadraticFullHeads hinput k f hf

theorem quadratic_full_tail_seven_graph (hinput : ArbitraryTailInput quadraticFullHeads 7) {D s : ℝ}
    (k : ℕ) (f : Diamond.Vertex k → FullQuadraticSpace) (hf : Diamond.HasDistortion k f D s) :
    D⁻¹ ≤ (1-D⁻¹^2/2000)^k := tail_seven quadraticFullHeads hinput k f hf

theorem quadratic_full_pruning_graph (hinput : ArbitraryTailInput quadraticFullHeads 9) {D s γ : ℝ}
    (hγ : 0 < γ) (hγhalf : γ < 1/2)
    (hsmall : 9*Real.sqrt ((1+γ)^2-(1-2*γ)^2) < 2*D⁻¹/3)
    (k : ℕ) (f : Diamond.Vertex k → FullQuadraticSpace) (hf : Diamond.HasDistortion k f D s) :
    D⁻¹ ≤ (1-γ)^k := tail_pruning quadraticFullHeads hinput hγ hγhalf hsmall k f hf
end PathModel

namespace Diamond
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A larger separation can use the same unit-lens bound. -/
lemma UnitLensBound.mono_separation {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {ε ε' ρ : ℝ} (h : UnitLensBound X ε ρ)
    (hε : ε ≤ ε') : UnitLensBound X ε' ρ :=
  fun x z hp hm hs => h x z hp hm (fun i j hij => hε.trans (hs i j hij))

lemma QuadraticLens.positive_gap {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (hX : QuadraticLens X) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ,0 < ρ ∧ ρ < 1 ∧ UnitLensBound X ε ρ := by
  let δ : ℝ := min (1/2) (ε^2/16)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδhalf : δ ≤ 1/2 := min_le_left _ _
  have hδε : δ ≤ ε^2/16 := min_le_right _ _
  refine ⟨Real.sqrt (1-δ),Real.sqrt_pos.2 (by linarith),?_,?_⟩
  · exact (Real.sqrt_lt' (by norm_num)).2 (by linarith)
  · intro x z hp hm hs
    have hloss := hX x z 1 ε (by norm_num) hε hp hm hs
    have hsqrt := Real.sq_sqrt (show 0 ≤ 1-δ by linarith)
    have hroot := Real.sqrt_nonneg (1-δ)
    nlinarith [norm_nonneg x]
end Diamond

end DiamondDistortion

end

end OAI
