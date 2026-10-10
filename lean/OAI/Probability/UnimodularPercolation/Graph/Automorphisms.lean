import Mathlib
import OAI.Probability.UnimodularPercolation.Escape.Labels
import OAI.Probability.UnimodularPercolation.Graph.Topology
import OAI.Probability.UnimodularPercolation.Transport.Haar

namespace OAI

/-! Locally compact graph automorphism groups and unimodular root data. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory Topology
open scoped ENNReal
universe u v
variable {V : Type u} {E : Type v}

 
def graphAut (G : BondGraph V E) : Subgroup (Equiv.Perm V) where
  carrier := vertexAut G
  one_mem' := ⟨Equiv.refl E, isAut_refl G⟩
  mul_mem' := by
    rintro a c ⟨b,hb⟩ ⟨d,hd⟩
    exact ⟨d.trans b, isAut_trans G hd hb⟩
  inv_mem' := by
    rintro a ⟨b,hb⟩
    exact ⟨b.symm,isAut_symm G hb⟩

 

theorem mem_vertexAut_iff (G : BondGraph V E) (hG : Function.Injective G)
    (a : Equiv.Perm V) :
    a ∈ vertexAut G ↔ ∀ x y, Adj G (a x) (a y) ↔ Adj G x y := by
  constructor
  · rintro ⟨b,hb⟩ x y
    exact ⟨fun h => by simpa using adj_aut G (isAut_symm G hb) h,adj_aut G hb⟩
  · intro ha
    have he (s : Sym2 V) : s ∈ Set.range G ↔ s.map a ∈ Set.range G := by
      induction s using Sym2.inductionOn with
      | _ x y => exact (ha x y).symm
    let a₂ : Equiv.Perm (Sym2 V) :=
      ⟨Sym2.map a,Sym2.map a.symm,
        fun s => by simp only [Sym2.map_map,Equiv.symm_comp_self,Sym2.map_id',id_eq],
        fun s => by simp only [Sym2.map_map,Equiv.self_comp_symm,Sym2.map_id',id_eq]⟩
    let e : E ≃ Set.range G := Equiv.ofInjective G hG
    let b : E ≃ E := (e.trans (a₂.subtypeEquiv he)).trans e.symm
    refine ⟨b,?_⟩
    intro z
    have hb : e (b z) = a₂.subtypeEquiv he (e z) := by
      exact e.apply_symm_apply _
    exact congrArg Subtype.val hb

 

abbrev graphOrbitType (G : BondGraph V E) := Quotient (MulAction.orbitRel (graphAut G) V)

instance graphOrbitType_nonempty [Nonempty V] (G : BondGraph V E) :
    Nonempty (graphOrbitType G) := ⟨Quotient.mk _ (Classical.arbitrary V)⟩

noncomputable def graphOrbitRoot (G : BondGraph V E) : graphOrbitType G → V := Quotient.out

theorem graphOrbitRoot_cover (G : BondGraph V E) (x : V) :
    ∃ i : graphOrbitType G, x ∈ actionOrbit (H := graphAut G) (graphOrbitRoot G i) := by
  refine ⟨Quotient.mk _ x,?_⟩
  apply (MulAction.mem_orbit_iff).mp
  apply MulAction.orbitRel_apply.mp
  apply Quotient.exact
  exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel (graphAut G) V) x)).symm

theorem graphOrbitRoot_separate (G : BondGraph V E) (i j : graphOrbitType G)
    (h : graphOrbitRoot G j ∈ actionOrbit (H := graphAut G) (graphOrbitRoot G i)) : i = j := by
  have he : (Quotient.mk _ (graphOrbitRoot G j) : graphOrbitType G) =
      Quotient.mk _ (graphOrbitRoot G i) :=
    Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr h))
  simpa only [graphOrbitRoot,Quotient.out_eq] using he.symm

theorem finite_graphOrbitType (G : BondGraph V E) (hqt : QuasiTransitive G) :
    Finite (graphOrbitType G) := by
  classical
  obtain ⟨R,hR⟩ := hqt
  apply Finite.of_surjective (fun r : R => (Quotient.mk _ r.val : graphOrbitType G))
  intro i
  induction i using Quotient.inductionOn with
  | _ x =>
    obtain ⟨r,hr,a,b,hab,hax⟩ := hR x
    refine ⟨⟨r,hr⟩,?_⟩
    symm
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    exact ⟨⟨a,⟨b,hab⟩⟩,hax⟩

section Topology
variable [TopologicalSpace V] [DiscreteTopology V]

theorem isClosed_vertexAut (G : BondGraph V E) (hG : Function.Injective G) :
    IsClosed (vertexAut G) := by
  have h (x y : V) : IsClosed {a : Equiv.Perm V | Adj G (a x) (a y) ↔ Adj G x y} := by
    have hf : Continuous (fun a : Equiv.Perm V => (a x,a y)) :=
      (PointwisePerm.continuous_apply x).prodMk (PointwisePerm.continuous_apply y)
    exact (isClosed_discrete {p : V × V | Adj G p.1 p.2 ↔ Adj G x y}).preimage hf
  convert isClosed_iInter (fun x => isClosed_iInter (h x)) using 1
  ext a
  simp only [Set.mem_iInter,Set.mem_ofPred_eq,mem_vertexAut_iff G hG]

 
theorem isCompact_vertexStabilizer (G : BondGraph V E) (hG : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G) (x : V) :
    IsCompact {a : Equiv.Perm V | a ∈ vertexAut G ∧ a x = x} := by
  apply PointwisePerm.isCompact_of_finite_images _
    ((isClosed_vertexAut G hG).inter (PointwisePerm.isClosed_fixed x x))
  · intro y
    obtain ⟨n,hn⟩ := exists_mem_reachBall (hconn x y)
    apply (finite_reachBall hloc x n).subset
    rintro z ⟨a,⟨⟨b,hb⟩,hx⟩,rfl⟩
    change a x = x at hx
    simpa only [hx] using mem_reachBall_aut G hb hn
  · intro y
    obtain ⟨n,hn⟩ := exists_mem_reachBall (hconn x y)
    apply (finite_reachBall hloc x n).subset
    rintro z ⟨a,⟨⟨b,hb⟩,hx⟩,rfl⟩
    have hx' : a.symm x = x := by rw [Equiv.symm_apply_eq,hx]
    simpa only [hx'] using mem_reachBall_aut G (isAut_symm G hb) hn

 
omit [DiscreteTopology V] in
theorem graphAut_continuous_apply (G : BondGraph V E) (x : V) :
    Continuous (fun g : graphAut G => g • x) :=
  (PointwisePerm.continuous_apply x).comp continuous_subtype_val

theorem graphAut_isOpen_stabilizer (G : BondGraph V E) (x : V) :
    IsOpen (actionStabilizer (H := graphAut G) x) :=
  (isOpen_discrete ({x} : Set V)).preimage (graphAut_continuous_apply G x)

theorem graphAut_isCompact_stabilizer (G : BondGraph V E) (hG : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G) (x : V) :
    IsCompact (actionStabilizer (H := graphAut G) x) := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  convert isCompact_vertexStabilizer G hG hconn hloc x using 1
  ext a
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact ⟨g.property,hg⟩
  · rintro ⟨ha,hax⟩
    exact ⟨⟨a,ha⟩,hax,rfl⟩

 

theorem graphAut_locallyCompact [Nonempty V] (G : BondGraph V E)
    (hG : Function.Injective G) (hconn : Connected G) (hloc : LocallyFinite G) :
    LocallyCompactSpace (graphAut G) := by
  let x : V := Classical.arbitrary V
  have hK := graphAut_isCompact_stabilizer G hG hconn hloc x
  have hKo := graphAut_isOpen_stabilizer G x
  have hw : WeaklyLocallyCompactSpace (graphAut G) := by
    refine ⟨fun g => ?_⟩
    refine ⟨(fun h : graphAut G => g * h) '' actionStabilizer (H := graphAut G) x,
      hK.image (continuous_const.mul continuous_id),?_⟩
    have h1 : actionStabilizer (H := graphAut G) x ∈ nhds (1 : graphAut G) :=
      hKo.mem_nhds (one_smul _ _)
    have he := (Homeomorph.mulLeft g).map_nhds_eq (1 : graphAut G)
    change Filter.map (fun h : graphAut G => g * h) (nhds 1) = nhds (g * 1) at he
    rw [mul_one] at he
    rw [←he]
    exact Filter.image_mem_map h1
  let := hw
  infer_instance

instance graphAutSecondCountable [Countable V] (G : BondGraph V E) :
    SecondCountableTopology (graphAut G) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

instance graphAutMeasurableSpace (G : BondGraph V E) : MeasurableSpace (graphAut G) :=
  borel (graphAut G)

instance graphAutBorelSpace (G : BondGraph V E) : BorelSpace (graphAut G) := ⟨rfl⟩

 
noncomputable def graphHaar [Nonempty V] (G : BondGraph V E)
    (hG : Function.Injective G) (hconn : Connected G) (hloc : LocallyFinite G) :
    Measure (graphAut G) := by
  letI := graphAut_locallyCompact G hG hconn hloc
  exact Measure.haar

theorem graphHaar_isHaar [Nonempty V] (G : BondGraph V E)
    (hG : Function.Injective G) (hconn : Connected G) (hloc : LocallyFinite G) :
    (graphHaar G hG hconn hloc).IsHaarMeasure := by
  let := graphAut_locallyCompact G hG hconn hloc
  exact inferInstanceAs ((Measure.haar : Measure (graphAut G)).IsHaarMeasure)

theorem graphHaar_regular [Nonempty V] (G : BondGraph V E)
    (hG : Function.Injective G) (hconn : Connected G) (hloc : LocallyFinite G) :
    (graphHaar G hG hconn hloc).Regular := by
  let := graphAut_locallyCompact G hG hconn hloc
  exact inferInstanceAs ((Measure.haar : Measure (graphAut G)).Regular)

 
theorem graphStabilizer_volume_pos (G : BondGraph V E) (hG : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G)
    (μ : Measure (graphAut G)) [μ.IsHaarMeasure] (x : V) :
    0 < μ.real (actionStabilizer (H := graphAut G) x) := by
  apply ENNReal.toReal_pos
  · exact ((graphAut_isOpen_stabilizer G x).measure_pos μ ⟨1,one_smul _ _⟩).ne'
  · exact (graphAut_isCompact_stabilizer G hG hconn hloc x).measure_lt_top.ne

section Countable
variable [Countable V] [MeasurableSpace V] [BorelSpace V]

 

theorem graphHaar_rootTransport (G : BondGraph V E) (hG : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G)
    [Fintype (graphOrbitType G)] [Nonempty V]
    (μ : Measure (graphAut G)) [μ.IsHaarMeasure] [μ.IsInvInvariant] :
    RootTransport (graphOrbitRoot G) (inverseStabilizerWeight μ (graphOrbitRoot G)) (vertexAut G) := by
  apply rootTransport_of_invariant_measure μ
    (fun x => (graphAut_continuous_apply G x).measurable)
    (graphOrbitRoot G)
    (fun i => graphStabilizer_volume_pos G hG hconn hloc μ (graphOrbitRoot G i))
    (fun i => (graphAut_isCompact_stabilizer G hG hconn hloc (graphOrbitRoot G i)).measure_lt_top.ne)
    (graphOrbitRoot_cover G) (graphOrbitRoot_separate G) (vertexAut G)
  intro g
  exact g.property

 

theorem exists_graphHaar_rootData [Nonempty V] (G : BondGraph V E)
    (hG : Function.Injective G) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G)
    (μ : Measure (graphAut G)) [μ.IsHaarMeasure] [μ.IsInvInvariant] :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : Nonempty ι) (root : ι → V) (weight : ι → ℝ),
      RootTransport root weight (vertexAut G) ∧
      (∀ x, ∃ i, ∃ g ∈ vertexAut G, g (root i) = x) ∧
      (∀ i, 0 < weight i) ∧ ∑ i, weight i = 1 := by
  let := finite_graphOrbitType G hqt
  let := Fintype.ofFinite (graphOrbitType G)
  refine ⟨graphOrbitType G,inferInstance,inferInstance,graphOrbitRoot G,
    inverseStabilizerWeight μ (graphOrbitRoot G),
    graphHaar_rootTransport G hG hconn hloc μ,?_,?_,?_⟩
  · intro x
    obtain ⟨i,g,hg⟩ := graphOrbitRoot_cover G x
    exact ⟨i,g.val,g.property,hg⟩
  · exact inverseStabilizerWeight_pos μ (graphOrbitRoot G)
      (fun i => graphStabilizer_volume_pos G hG hconn hloc μ (graphOrbitRoot G i))
  · exact inverseStabilizerWeight_sum μ (graphOrbitRoot G)
      (fun i => graphStabilizer_volume_pos G hG hconn hloc μ (graphOrbitRoot G i))

 

theorem exists_rootData_of_unimodular [Nonempty V] (G : BondGraph V E)
    (hG : Function.Injective G) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G)
    (huni : (graphHaar G hG hconn hloc).IsMulRightInvariant) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : Nonempty ι) (root : ι → V) (weight : ι → ℝ),
      RootTransport root weight (vertexAut G) ∧
      (∀ x, ∃ i, ∃ g ∈ vertexAut G, g (root i) = x) ∧
      (∀ i, 0 < weight i) ∧ ∑ i, weight i = 1 := by
  let := graphAut_locallyCompact G hG hconn hloc
  let μ := graphHaar G hG hconn hloc
  let : μ.IsHaarMeasure := graphHaar_isHaar G hG hconn hloc
  let : μ.Regular := graphHaar_regular G hG hconn hloc
  let : μ.IsMulRightInvariant := huni
  let : μ.IsInvInvariant := haar_invInvariant_of_rightInvariant μ
  exact exists_graphHaar_rootData G hG hconn hloc hqt μ

end Countable

end Topology
end Percolation

end OAI
