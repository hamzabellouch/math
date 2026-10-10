import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CentralFiber01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open Topology
open scoped Pointwise
open Topology Set
open MeasureTheory Set Topology
open MeasureTheory Topology Set

 

namespace CompactConvexFixedPoint
open Set Filter Topology
open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]

noncomputable def average (T : E →L[ℝ] E) (x : E) (n : ℕ) : E :=
  ((n+1 : ℝ)⁻¹) • ∑ i ∈ Finset.range (n+1), T^[i] x

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] in
lemma average_mem (T : E →L[ℝ] E) {C : Set E} (hc : Convex ℝ C)
    (hT : MapsTo T C C) {x : E} (hx : x ∈ C) (n : ℕ) : average T x n ∈ C := by
  have hi : ∀ i, T^[i] x ∈ C := by
    intro i
    induction i with
    | zero => simpa using hx
    | succ i ih => simpa only [Function.iterate_succ_apply'] using hT ih
  have hsum : ∑ _i ∈ Finset.range (n+1), (n+1 : ℝ)⁻¹ = 1 := by
    simp [mul_inv_cancel₀ (show (n+1 : ℝ) ≠ 0 by positivity)]
  simpa only [average, Finset.smul_sum] using hc.sum_mem
    (fun i _ => inv_nonneg.mpr (by positivity : (0:ℝ) ≤ n+1)) hsum (fun i _ => hi i)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] in
lemma average_difference (T : E →L[ℝ] E) (x : E) (n : ℕ) :
    T (average T x n) - average T x n =
      (n+1 : ℝ)⁻¹ • (T^[n+1] x - x) := by
  simp only [average, map_smul, map_sum, ← smul_sub, ← Finset.sum_sub_distrib]
  have h : ∀ i, T (T^[i] x) = T^[i+1] x := fun i =>
    (Function.iterate_succ_apply' T i x).symm
  simp_rw [h]
  rw [Finset.sum_range_sub (fun i => T^[i] x) (n+1)]
  rfl

 

theorem exists_fixed (T : E →L[ℝ] E) {C : Set E} (hk : IsCompact C)
    (hc : Convex ℝ C) (hne : C.Nonempty) (hT : MapsTo T C C) :
    ∃ x ∈ C, T x = x := by
  obtain ⟨x,hx⟩ := hne
  have hi : ∀ n, T^[n] x ∈ C := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih => simpa only [Function.iterate_succ_apply'] using hT ih
  let u : Ultrafilter ℕ := Ultrafilter.of atTop
  let f : ℕ → E × E := fun n => (average T x n, T^[n+1] x)
  have hm : (u.map f : Filter (E×E)) ≤ 𝓟 (C ×ˢ C) := by
    rw [Ultrafilter.coe_map, Filter.map_le_iff_le_comap,Filter.comap_principal]
    exact Filter.le_principal_iff.mpr (Eventually.of_forall fun n =>
      ⟨average_mem T hc hT hx n, hi (n+1)⟩)
  obtain ⟨z,hz,hlim⟩ := (hk.prod hk).ultrafilter_le_nhds (u.map f) hm
  change Tendsto f (u : Filter ℕ) (𝓝 z) at hlim
  have ha : Tendsto (average T x) (u : Filter ℕ) (𝓝 z.1) :=
    (continuous_fst.tendsto z).comp hlim
  have hb : Tendsto (fun n => T^[n+1] x - x) (u : Filter ℕ) (𝓝 (z.2-x)) :=
    ((continuous_snd.tendsto z).comp hlim).sub_const x
  have hz0 : Tendsto (fun n : ℕ => (n+1 : ℝ)⁻¹) (u : Filter ℕ) (𝓝 0) := by
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mono_left
        (Ultrafilter.of_le atTop)
  have hdiff : Tendsto (fun n => T (average T x n) - average T x n)
      (u : Filter ℕ) (𝓝 (0:E)) := by
    simpa only [average_difference,zero_smul] using hz0.smul hb
  have ht := (T.continuous.tendsto z.1).comp ha
  have he : T z.1 - z.1 = 0 := tendsto_nhds_unique (ht.sub ha) hdiff
  exact ⟨z.1,hz.1,sub_eq_zero.mp he⟩

 

theorem exists_common_fixed {ι : Type*} (T : ι → E →L[ℝ] E) {C : Set E}
    (hk : IsCompact C) (hc : Convex ℝ C) (hne : C.Nonempty)
    (hT : ∀ i, MapsTo (T i) C C)
    (hcomm : ∀ i j x, x ∈ C → T i (T j x) = T j (T i x)) :
    ∃ x ∈ C, ∀ i, T i x = x := by
  classical
  let F : ι → Set E := fun i => {x | T i x = x}
  have hclosed : ∀ i, IsClosed (F i) := fun i =>
    isClosed_eq (T i).continuous continuous_id
  have hfinite : ∀ s : Finset ι, (C ∩ ⋂ i ∈ s, F i).Nonempty := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hne
    | @insert i s his ih =>
      let S := C ∩ ⋂ j ∈ s, F j
      have hsk : IsCompact S := hk.inter_right (isClosed_iInter fun j => isClosed_iInter fun _ => hclosed j)
      have hsc : Convex ℝ S := by
        intro x hx y hy a b ha hb hab
        refine ⟨hc hx.1 hy.1 ha hb hab, ?_⟩
        simp only [S,mem_inter_iff,mem_iInter,F,mem_ofPred_eq] at hx
        simp only [S,mem_inter_iff,mem_iInter,F,mem_ofPred_eq] at hy
        simp only [mem_iInter]
        intro j hj
        change T j (a • x + b • y) = a • x + b • y
        simp only [map_add,map_smul,hx.2 j hj,hy.2 j hj]
      have hsi : MapsTo (T i) S S := by
        intro x hx
        refine ⟨hT i hx.1,?_⟩
        simp only [S,mem_inter_iff,mem_iInter,F,mem_ofPred_eq] at hx
        simp only [mem_iInter]
        intro j hj
        change T j (T i x) = T i x
        rw [hcomm j i x hx.1,hx.2 j hj]
      obtain ⟨x,hxs,hxi⟩ := exists_fixed (T i) hsk hsc ih hsi
      refine ⟨x,hxs.1,?_⟩
      simp only [S,mem_inter_iff,mem_iInter,F,mem_ofPred_eq] at hxs
      simp only [mem_iInter]
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl|hj
      · exact hxi
      · exact hxs.2 j hj
  obtain ⟨x,hx,hfix⟩ := hk.inter_iInter_nonempty F hclosed hfinite
  exact ⟨x,hx,fun i => mem_iInter.mp hfix i⟩

variable {G : Type*} [Group G]

def fixedSet (ρ : G →* (E →L[ℝ] E)) (C : Set E) (H : Subgroup G) : Set E :=
  {x | x ∈ C ∧ ∀ g ∈ H, ρ g x = x}

omit [ContinuousSMul ℝ E] in
lemma fixedSet_compact (ρ : G →* (E →L[ℝ] E)) {C : Set E} (hk : IsCompact C)
    (H : Subgroup G) : IsCompact (fixedSet ρ C H) := by
  have he : fixedSet ρ C H = C ∩ ⋂ g ∈ H, {x | ρ g x = x} := by
    ext x; simp [fixedSet]
  rw [he]
  apply hk.inter_right
  exact isClosed_iInter fun g => isClosed_iInter fun _ =>
    isClosed_eq (ρ g).continuous continuous_id

omit [ContinuousSMul ℝ E] [T2Space E] in
lemma fixedSet_convex (ρ : G →* (E →L[ℝ] E)) {C : Set E} (hc : Convex ℝ C)
    (H : Subgroup G) : Convex ℝ (fixedSet ρ C H) := by
  intro x hx y hy a b ha hb hab
  refine ⟨hc hx.1 hy.1 ha hb hab, ?_⟩
  intro g hg
  simp only [map_add,map_smul,hx.2 g hg,hy.2 g hg]

omit [ContinuousSMul ℝ E] [T2Space E] in
lemma fixedSet_invariant (ρ : G →* (E →L[ℝ] E)) {C : Set E}
    (hρ : ∀ g, MapsTo (ρ g) C C) (N : Subgroup G) [N.Normal] (g : G) :
    MapsTo (ρ g) (fixedSet ρ C N) (fixedSet ρ C N) := by
  intro x hx
  refine ⟨hρ g hx.1, ?_⟩
  intro h hh
  have hi : g⁻¹*h*g ∈ N := (inferInstance : N.Normal).conj_mem' h hh g
  have he : h*g = g*(g⁻¹*h*g) := by group
  calc
    ρ h (ρ g x) = ρ (h*g) x := by simp only [map_mul,mul_apply_eq_comp]
    _ = ρ (g*(g⁻¹*h*g)) x := congrArg (fun a => ρ a x) he
    _ = ρ g x := by rw [map_mul,mul_apply_eq_comp,hx.2 _ hi]

lemma fixedSet_step (ρ : G →* (E →L[ℝ] E)) {C : Set E}
    (hk : IsCompact C) (hc : Convex ℝ C) (hρ : ∀ g, MapsTo (ρ g) C C)
    (H N : Subgroup G) [N.Normal] (hHN : ⁅H,H⁆ ≤ N)
    (hne : (fixedSet ρ C N).Nonempty) : (fixedSet ρ C H).Nonempty := by
  have hcomm : ∀ (a b : H) x, x ∈ fixedSet ρ C N →
      ρ a (ρ b x) = ρ b (ρ a x) := by
    intro a b x hx
    let c : G := a.val⁻¹*b.val⁻¹*a.val*b.val
    have hcm : c ∈ N := by
      apply hHN
      simpa only [commutatorElement_def,inv_inv] using
        Subgroup.commutator_mem_commutator (H.inv_mem a.property) (H.inv_mem b.property)
    have he : a.val*b.val = (b.val*a.val)*c := by dsimp [c]; group
    calc
      ρ a (ρ b x) = ρ (a.val*b.val) x := by simp only [map_mul,mul_apply_eq_comp]
      _ = ρ ((b.val*a.val)*c) x := congrArg (fun z => ρ z x) he
      _ = ρ b (ρ a x) := by
        simp only [map_mul,mul_apply_eq_comp]
        rw [hx.2 c hcm]
  obtain ⟨x,hx,hfix⟩ := exists_common_fixed (fun g : H => ρ g)
    (fixedSet_compact ρ hk N) (fixedSet_convex ρ hc N) hne
    (fun g => fixedSet_invariant ρ hρ N g) hcomm
  exact ⟨x,hx.1,fun g hg => hfix ⟨g,hg⟩⟩

 

theorem exists_solvable_fixed [Group.IsSolvable G] (ρ : G →* (E →L[ℝ] E))
    {C : Set E} (hk : IsCompact C) (hc : Convex ℝ C) (hne : C.Nonempty)
    (hρ : ∀ g, MapsTo (ρ g) C C) : ∃ x ∈ C, ∀ g, ρ g x = x := by
  obtain ⟨n,hn⟩ := Group.IsSolvable.solvable (G := G)
  have hdown : ∀ k, (fixedSet ρ C (derivedSeries G k)).Nonempty →
      (fixedSet ρ C (derivedSeries G 0)).Nonempty := by
    intro k
    induction k with
    | zero => exact id
    | succ k ih =>
      intro h
      apply ih
      exact fixedSet_step ρ hk hc hρ (derivedSeries G k) (derivedSeries G (k+1))
        (by rw [derivedSeries_succ]) h
  have hstart : (fixedSet ρ C (derivedSeries G n)).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    refine ⟨x,hx,?_⟩
    intro g hg
    rw [hn,Subgroup.mem_bot] at hg
    subst g
    simp
  obtain ⟨x,hx,hfix⟩ := hdown n hstart
  exact ⟨x,hx,fun g => hfix g (by simp)⟩

end CompactConvexFixedPoint

namespace SolvableInvariantMeasure
open Set MeasureTheory Topology

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

noncomputable def evaluations (μ : ProbabilityMeasure X) : C(X,ℝ) → ℝ :=
  fun f => ∫ x, f x ∂(μ : Measure X)

omit [T2Space X] in
lemma continuous_evaluations : Continuous (evaluations (X := X)) := by
  apply continuous_pi
  intro f
  exact ProbabilityMeasure.continuous_integral_continuousMap f

lemma compact_evaluations : IsCompact (range (evaluations (X := X))) :=
  isCompact_range continuous_evaluations

omit [T2Space X] in
lemma convex_evaluations : Convex ℝ (range (evaluations (X := X))) := by
  intro v hv w hw a b ha hb hab
  obtain ⟨μ,rfl⟩ := hv
  obtain ⟨ν,rfl⟩ := hw
  let θ : Measure X := ENNReal.ofReal a • (μ : Measure X) + ENNReal.ofReal b • (ν : Measure X)
  have hθ : IsProbabilityMeasure θ := by
    constructor
    simp only [θ,Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
    rw [← ENNReal.ofReal_add ha hb,hab,ENNReal.ofReal_one]
  refine ⟨⟨θ,hθ⟩,?_⟩
  ext f
  change (∫ x, f x ∂θ) = a * (∫ x, f x ∂(μ : Measure X)) +
    b * (∫ x, f x ∂(ν : Measure X))
  dsimp [θ]
  rw [integral_add_measure,integral_smul_measure,integral_smul_measure]
  · simp only [ENNReal.toReal_ofReal ha,ENNReal.toReal_ofReal hb,smul_eq_mul]
  · exact (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)).smul_measure
      ENNReal.ofReal_ne_top
  · exact (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)).smul_measure
      ENNReal.ofReal_ne_top

variable {G : Type*} [Group G] [MulAction G X] [ContinuousConstSMul G X]

 

noncomputable def pushRep : G →* ((C(X,ℝ) → ℝ) →L[ℝ] (C(X,ℝ) → ℝ)) where
  toFun g := ContinuousLinearMap.pi fun f =>
    ContinuousLinearMap.proj (f.comp ⟨(g • ·),continuous_const_smul g⟩)
  map_one' := by
    ext L f
    change L (f.comp ⟨((1:G) • ·),continuous_const_smul (1:G)⟩) = L f
    congr 1
    ext x
    simp
  map_mul' g h := by
    ext L f
    change L (f.comp ⟨((g*h) • ·),continuous_const_smul (g*h)⟩) =
      L ((f.comp ⟨(g • ·),continuous_const_smul g⟩).comp
        ⟨(h • ·),continuous_const_smul h⟩)
    congr 1
    ext x
    simp [mul_smul]

omit [CompactSpace X] [T2Space X] in
lemma pushRep_evaluations (g : G) (μ : ProbabilityMeasure X) :
    pushRep g (evaluations μ) =
      evaluations (μ.map (g • ·)) := by
  ext f
  change (∫ x, f (g • x) ∂(μ : Measure X)) =
    ∫ x, f x ∂(Measure.map (g • ·) (μ : Measure X))
  exact (integral_map (measurable_const_smul g).aemeasurable f.continuous.aestronglyMeasurable).symm

 

theorem exists_invariant_integrals [Group.IsSolvable G] [Nonempty X] :
    ∃ μ : ProbabilityMeasure X, ∀ (g : G) (f : C(X,ℝ)),
      (∫ x, f (g • x) ∂(μ : Measure X)) = ∫ x, f x ∂(μ : Measure X) := by
  have hne : (range (evaluations (X := X))).Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨evaluations ⟨Measure.dirac x,inferInstance⟩,mem_range_self _⟩
  have hm : ∀ g : G, MapsTo (pushRep g) (range (evaluations (X := X)))
      (range evaluations) := by
    intro g v hv
    obtain ⟨μ,rfl⟩ := hv
    rw [pushRep_evaluations]
    exact mem_range_self _
  obtain ⟨v,⟨μ,rfl⟩,hfix⟩ := CompactConvexFixedPoint.exists_solvable_fixed
    (pushRep (G := G) (X := X)) compact_evaluations convex_evaluations hne hm
  exact ⟨μ,fun g f => congrFun (hfix g) f⟩

 

theorem exists_invariant_measure [Group.IsSolvable G] [Nonempty X]
    [HasOuterApproxClosed X] :
    ∃ μ : ProbabilityMeasure X, SMulInvariantMeasure G X (μ : Measure X) := by
  obtain ⟨μ,hμ⟩ := exists_invariant_integrals (G := G) (X := X)
  refine ⟨μ,⟨?_⟩⟩
  intro g s hs
  let ν := μ.map (g • ·)
  have he : ν.toFiniteMeasure = μ.toFiniteMeasure := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro f
    change (∫ x, f x ∂Measure.map (g • ·) (μ : Measure X)) =
      ∫ x, f x ∂(μ : Measure X)
    rw [integral_map (measurable_const_smul g).aemeasurable f.continuous.aestronglyMeasurable]
    exact hμ g f.toContinuousMap
  have he' : Measure.map (g • ·) (μ : Measure X) = (μ : Measure X) :=
    congrArg (fun m : FiniteMeasure X => (m : Measure X)) he
  rw [← Measure.map_apply (measurable_const_smul g) hs,he']

 

theorem exists_invariant_fullSupport [Group.IsSolvable G] [Nonempty X]
    [HasOuterApproxClosed X] [MulAction.IsMinimal G X] :
    ∃ μ : ProbabilityMeasure X, SMulInvariantMeasure G X (μ : Measure X) ∧
      (μ : Measure X).IsOpenPosMeasure := by
  obtain ⟨μ,hμ⟩ := exists_invariant_measure (G := G) (X := X)
  let := hμ
  refine ⟨μ,hμ,⟨?_⟩⟩
  intro U hU hne
  exact ne_of_gt (measure_isOpen_pos_of_smulInvariant_of_compact_ne_zero G
    isCompact_univ (by simp) hU hne)

end SolvableInvariantMeasure

end
end
end
end

end OAI
