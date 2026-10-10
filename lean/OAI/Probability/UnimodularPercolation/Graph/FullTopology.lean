import Mathlib
import OAI.Probability.UnimodularPercolation.Main

namespace OAI

/-! The automorphism group with its topology of pointwise convergence. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open Topology
universe u v
variable {V : Type u} {E : Type v}

noncomputable def graphAutSubgroup (G : BondGraph V E) : Subgroup (Equiv.Perm V) where
  carrier := vertexAut G
  one_mem' := ⟨Equiv.refl E, isAut_refl G⟩
  mul_mem' := by
    rintro a b ⟨c,hc⟩ ⟨d,hd⟩
    exact ⟨d.trans c,isAut_trans G hd hc⟩
  inv_mem' := by
    rintro a ⟨b,hb⟩
    exact ⟨b.symm,isAut_symm G hb⟩

def GraphAut (G : BondGraph V E) := ↥(graphAutSubgroup G)

noncomputable instance (G : BondGraph V E) : Group (GraphAut G) :=
  inferInstanceAs (Group ↥(graphAutSubgroup G))

noncomputable instance (G : BondGraph V E) : MulAction (GraphAut G) V :=
  inferInstanceAs (MulAction ↥(graphAutSubgroup G) V)

noncomputable def graphAutPerm (G : BondGraph V E) : GraphAut G →* Equiv.Perm V :=
  (graphAutSubgroup G).subtype

theorem graphAutPerm_mem (G : BondGraph V E) (g : GraphAut G) :
    graphAutPerm G g ∈ vertexAut G := g.property

theorem mem_vertexAut_iff_adj (G : BondGraph V E) (hG : Function.Injective G)
    (a : V ≃ V) : a ∈ vertexAut G ↔ ∀ x y, Adj G (a x) (a y) ↔ Adj G x y := by
  classical
  constructor
  · rintro ⟨b,hb⟩ x y
    refine ⟨fun h => ?_,adj_aut G hb⟩
    simpa only [Equiv.symm_apply_apply] using adj_aut G (isAut_symm G hb) h
  · intro ha
    have hex (e : E) : ∃ f : E, G f = (G e).map a := by
      obtain ⟨x,y,hxy⟩ := Sym2.exists.mp (show ∃ t : Sym2 V, t = G e from ⟨_,rfl⟩)
      have h := (ha x y).mpr ⟨e,hxy.symm⟩
      simpa only [←hxy,Sym2.map_mk] using (show ∃ f, G f = s(a x,a y) from h)
    let f : E → E := fun e => Classical.choose (hex e)
    have hf (e : E) : G (f e) = (G e).map a := Classical.choose_spec (hex e)
    have hfi : Function.Injective f := by
      intro e d hed
      apply hG
      have heq := congrArg (fun z => z.map a.symm) (congrArg G hed)
      simpa only [hf,Sym2.map_map,Function.comp_def,Equiv.symm_apply_apply,Sym2.map_id',id_eq] using heq
    have hfs : Function.Surjective f := by
      intro e
      obtain ⟨x,y,hxy⟩ := Sym2.exists.mp (show ∃ t : Sym2 V, t = G e from ⟨_,rfl⟩)
      have h : Adj G (a.symm x) (a.symm y) := (ha _ _).mp (by
        simpa only [Equiv.apply_symm_apply] using (show Adj G x y from ⟨e,hxy.symm⟩))
      obtain ⟨d,hd⟩ := h
      refine ⟨d,hG ?_⟩
      rw [hf,hd,Sym2.map_mk,Equiv.apply_symm_apply,Equiv.apply_symm_apply,hxy]
    exact ⟨Equiv.ofBijective f ⟨hfi,hfs⟩,hf⟩

section Topology
variable [TopologicalSpace V] [DiscreteTopology V]

noncomputable def autCoordinates (G : BondGraph V E) (g : GraphAut G) :
    (V → V) × (V → V) := (graphAutPerm G g,graphAutPerm G (g⁻¹))

noncomputable instance graphAutTopology (G : BondGraph V E) : TopologicalSpace (GraphAut G) :=
  TopologicalSpace.induced (autCoordinates G) inferInstance

omit [DiscreteTopology V] in
theorem inducing_autCoordinates (G : BondGraph V E) :
    IsInducing (autCoordinates G) := ⟨rfl⟩

omit [DiscreteTopology V] in
theorem embedding_autCoordinates (G : BondGraph V E) :
    IsEmbedding (autCoordinates G) := by
  refine ⟨inducing_autCoordinates G,?_⟩
  intro f g h
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact congrFun (congrArg Prod.fst h) x

noncomputable instance graphAutT2 (G : BondGraph V E) : T2Space (GraphAut G) :=
  (embedding_autCoordinates G).t2Space

omit [DiscreteTopology V] in
theorem continuous_aut_apply (G : BondGraph V E) (x : V) :
    Continuous (fun g : GraphAut G => graphAutPerm G g x) :=
  (continuous_apply x).comp ((inducing_autCoordinates G).continuous.fst)

omit [DiscreteTopology V] in
theorem continuous_aut_inv_apply (G : BondGraph V E) (x : V) :
    Continuous (fun g : GraphAut G => graphAutPerm G (g⁻¹) x) :=
  (continuous_apply x).comp ((inducing_autCoordinates G).continuous.snd)

theorem continuous_discrete_eval : Continuous (fun p : (V → V) × V => p.1 p.2) :=
  continuous_prod_of_discrete_right.mpr fun x => continuous_apply x

noncomputable instance graphAutTopologicalGroup (G : BondGraph V E) :
    IsTopologicalGroup (GraphAut G) where
  continuous_mul := by
    apply (inducing_autCoordinates G).continuous_iff.mpr
    apply Continuous.prodMk
    · apply continuous_pi
      intro x
      exact continuous_discrete_eval.comp
        (((inducing_autCoordinates G).continuous.fst.comp continuous_fst).prodMk
          ((continuous_aut_apply G x).comp continuous_snd))
    · apply continuous_pi
      intro x
      exact continuous_discrete_eval.comp
        (((inducing_autCoordinates G).continuous.snd.comp continuous_snd).prodMk
          ((continuous_aut_inv_apply G x).comp continuous_fst))
  continuous_inv := by
    apply (inducing_autCoordinates G).continuous_iff.mpr
    simpa only [Function.comp_def,autCoordinates,inv_inv] using ((inducing_autCoordinates G).continuous.snd.prodMk (inducing_autCoordinates G).continuous.fst)

def autCoordinateSet (G : BondGraph V E) : Set ((V → V) × (V → V)) :=
  {p | (∀ x, p.1 (p.2 x) = x) ∧ (∀ x, p.2 (p.1 x) = x) ∧
    ∀ x y, Adj G (p.1 x) (p.1 y) ↔ Adj G x y}

omit [TopologicalSpace V] [DiscreteTopology V] in
theorem range_autCoordinates (G : BondGraph V E) (hG : Function.Injective G) :
    Set.range (autCoordinates G) = autCoordinateSet G := by
  classical
  ext p
  constructor
  · rintro ⟨g,rfl⟩
    refine ⟨fun x => ?_,fun x => ?_,?_⟩
    · exact Equiv.apply_symm_apply (graphAutPerm G g) x
    · exact Equiv.symm_apply_apply (graphAutPerm G g) x
    · exact (mem_vertexAut_iff_adj G hG _).mp (graphAutPerm_mem G g)
  · rintro ⟨h₁,h₂,hA⟩
    let a : Equiv.Perm V := ⟨p.1,p.2,h₂,h₁⟩
    let g : GraphAut G := ⟨a,(mem_vertexAut_iff_adj G hG a).mpr hA⟩
    exact ⟨g,rfl⟩

theorem continuous_coordinate_forward_inverse (x : V) :
    Continuous (fun p : (V → V) × (V → V) => p.1 (p.2 x)) := by
  have h₁ : Continuous (fun p : (V → V) × (V → V) => p.1) := continuous_fst
  have h₂ : Continuous (fun p : (V → V) × (V → V) => p.2 x) :=
    (continuous_apply x).comp continuous_snd
  exact (continuous_discrete_eval (V := V)).comp (h₁.prodMk h₂)

theorem continuous_coordinate_inverse_forward (x : V) :
    Continuous (fun p : (V → V) × (V → V) => p.2 (p.1 x)) := by
  have h₁ : Continuous (fun p : (V → V) × (V → V) => p.2) := continuous_snd
  have h₂ : Continuous (fun p : (V → V) × (V → V) => p.1 x) :=
    (continuous_apply x).comp continuous_fst
  exact (continuous_discrete_eval (V := V)).comp (h₁.prodMk h₂)

theorem isClosed_coordinate_forward_inverse :
    IsClosed {p : (V → V) × (V → V) | ∀ x, p.1 (p.2 x) = x} := by
  have h (x : V) : IsClosed {p : (V → V) × (V → V) | p.1 (p.2 x) = x} :=
    isClosed_eq (continuous_coordinate_forward_inverse x) continuous_const
  convert isClosed_iInter h using 1
  ext p
  simp only [Set.mem_iInter,Set.mem_ofPred_eq]

theorem isClosed_coordinate_inverse_forward :
    IsClosed {p : (V → V) × (V → V) | ∀ x, p.2 (p.1 x) = x} := by
  have h (x : V) : IsClosed {p : (V → V) × (V → V) | p.2 (p.1 x) = x} :=
    isClosed_eq (continuous_coordinate_inverse_forward x) continuous_const
  convert isClosed_iInter h using 1
  ext p
  simp only [Set.mem_iInter,Set.mem_ofPred_eq]

theorem isClosed_coordinate_adjacency (G : BondGraph V E) :
    IsClosed {p : (V → V) × (V → V) |
      ∀ x y, Adj G (p.1 x) (p.1 y) ↔ Adj G x y} := by
  have h (x y : V) : IsClosed {p : (V → V) × (V → V) |
      Adj G (p.1 x) (p.1 y) ↔ Adj G x y} := by
    have hx : Continuous (fun p : (V → V) × (V → V) => p.1 x) :=
      (continuous_apply x).comp continuous_fst
    have hy : Continuous (fun p : (V → V) × (V → V) => p.1 y) :=
      (continuous_apply y).comp continuous_fst
    exact (isClosed_discrete {q : V × V | Adj G q.1 q.2 ↔ Adj G x y}).preimage
      (hx.prodMk hy)
  convert isClosed_iInter (fun x => isClosed_iInter (h x)) using 1
  ext p
  simp only [Set.mem_iInter,Set.mem_ofPred_eq]

theorem isClosed_autCoordinateSet (G : BondGraph V E) :
    IsClosed (autCoordinateSet G) :=
  isClosed_coordinate_forward_inverse.inter
    (isClosed_coordinate_inverse_forward.inter (isClosed_coordinate_adjacency G))

def graphStabilizer (G : BondGraph V E) (x : V) : Set (GraphAut G) :=
  {g | graphAutPerm G g x = x}

theorem isOpen_graphStabilizer (G : BondGraph V E) (x : V) :
    IsOpen (graphStabilizer G x) :=
  (isOpen_discrete {x}).preimage (continuous_aut_apply G x)

theorem isClosed_stabilizer_coordinates (G : BondGraph V E)
    (hG : Function.Injective G) (x : V) :
    IsClosed (autCoordinates G '' graphStabilizer G x) := by
  have he : autCoordinates G '' graphStabilizer G x =
      autCoordinateSet G ∩ {p | p.1 x = x} := by
    ext p
    constructor
    · rintro ⟨g,hg,rfl⟩
      refine ⟨?_,hg⟩
      rw [←range_autCoordinates G hG]
      exact ⟨g,rfl⟩
    · rintro ⟨hp,hpx⟩
      rw [←range_autCoordinates G hG] at hp
      obtain ⟨g,rfl⟩ := hp
      exact ⟨g,hpx,rfl⟩
  rw [he]
  exact (isClosed_autCoordinateSet G).inter
    (isClosed_eq ((continuous_apply x).comp continuous_fst) continuous_const)

theorem isCompact_graphStabilizer (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (hconn : Connected G) (x : V) :
    IsCompact (graphStabilizer G x) := by
  classical
  choose n hn using fun y => exists_mem_reachBall (hconn x y)
  let K : Set (V → V) := {f | ∀ y, f y ∈ reachBall G x (n y)}
  have hK : IsCompact K := isCompact_pi_infinite fun y =>
    (finite_reachBall hloc x (n y)).isCompact
  apply (embedding_autCoordinates G).isCompact_iff.mpr
  apply (hK.prod hK).of_isClosed_subset (isClosed_stabilizer_coordinates G hG x)
  rintro p ⟨g,hg,rfl⟩
  have hball (g : GraphAut G) (hg : graphAutPerm G g x = x) (y : V) :
      graphAutPerm G g y ∈ reachBall G x (n y) := by
    obtain ⟨b,hb⟩ := graphAutPerm_mem G g
    simpa only [hg] using mem_reachBall_aut G hb (hn y)
  refine ⟨fun y => hball g hg y,fun y => hball g⁻¹ ?_ y⟩
  have he := congrArg (graphAutPerm G (g⁻¹)) hg
  exact he.symm.trans (Equiv.symm_apply_apply (graphAutPerm G g) x)

theorem locallyCompact_graphAut (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (hconn : Connected G) (x : V) :
    LocallyCompactSpace (GraphAut G) :=
  (isCompact_graphStabilizer G hG hloc hconn x).locallyCompactSpace_of_mem_nhds_of_group
    ((isOpen_graphStabilizer G x).mem_nhds (show (1 : GraphAut G) ∈ graphStabilizer G x from rfl))

theorem graphAutTopology_eq_pointwise (G : BondGraph V E) :
    graphAutTopology G = TopologicalSpace.induced
      (fun g : GraphAut G => (graphAutPerm G g : V → V)) inferInstance := by
  apply le_antisymm
  · apply continuous_iff_le_induced.mp
    exact continuous_pi fun x => continuous_aut_apply G x
  · let : TopologicalSpace (GraphAut G) := TopologicalSpace.induced
      (fun g : GraphAut G => (graphAutPerm G g : V → V)) inferInstance
    have hf : Continuous (fun g : GraphAut G => (graphAutPerm G g : V → V)) :=
      continuous_induced_dom
    have hi : Continuous (fun g : GraphAut G => (graphAutPerm G (g⁻¹) : V → V)) := by
      apply continuous_pi
      intro x
      apply continuous_discrete_rng.mpr
      intro y
      have he : (fun g : GraphAut G => graphAutPerm G (g⁻¹) x) ⁻¹' {y} =
          (fun g : GraphAut G => graphAutPerm G g y) ⁻¹' {x} := by
        ext g
        change (graphAutPerm G g).symm x = y ↔ graphAutPerm G g y = x
        rw [Equiv.symm_apply_eq,eq_comm]
      rw [he]
      exact (isOpen_discrete {x}).preimage ((continuous_apply y).comp hf)
    exact continuous_iff_le_induced.mp (hf.prodMk hi)

instance fullGraphAutSecondCountable (G : BondGraph V E) [Countable V] :
    SecondCountableTopology (GraphAut G) :=
  (inducing_autCoordinates G).secondCountableTopology

end Topology

abbrev GraphOrbit (G : BondGraph V E) := MulAction.orbitRel.Quotient (GraphAut G) V

theorem finite_graphOrbit (G : BondGraph V E) (hqt : QuasiTransitive G) :
    Finite (GraphOrbit G) := by
  classical
  obtain ⟨R,hR⟩ := hqt
  apply Finite.of_surjective (fun o : (R : Set V) =>
    (Quotient.mk'' o.1 : GraphOrbit G))
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    obtain ⟨o,ho,a,b,hab,hao⟩ := hR x
    refine ⟨⟨o,ho⟩,?_⟩
    symm
    exact Quotient.sound (show MulAction.orbitRel (GraphAut G) V x o from
      ⟨(⟨a,⟨b,hab⟩⟩ : GraphAut G),hao⟩)

noncomputable def fullGraphOrbitRoot (G : BondGraph V E) (q : GraphOrbit G) : V := q.out

theorem graphOrbitRoot_covers (G : BondGraph V E) (x : V) :
    ∃ i : GraphOrbit G, ∃ g : GraphAut G, g • fullGraphOrbitRoot G i = x := by
  refine ⟨Quotient.mk'' x,?_⟩
  exact Quotient.exact (Quotient.out_eq' (Quotient.mk'' x : GraphOrbit G)).symm

theorem graphOrbitRoot_separates (G : BondGraph V E) (i j : GraphOrbit G)
    (h : ∃ g : GraphAut G, g • fullGraphOrbitRoot G i = fullGraphOrbitRoot G j) : i = j := by
  have he : (Quotient.mk'' (fullGraphOrbitRoot G j) : GraphOrbit G) =
      Quotient.mk'' (fullGraphOrbitRoot G i) := Quotient.sound h
  simpa only [fullGraphOrbitRoot,Quotient.out_eq'] using he.symm

end Percolation

end OAI
