import Mathlib
import OAI.GroupTheory.FiniteType.TwistedBrinSeparated

namespace OAI

section
noncomputable section
namespace StageGeometry
open StageConstruction
variable {R Y W G : Type} [Ring R] [Nontrivial R] [Group W] [MulAction W Y]
  [DecidableEq Y] [Group G]
variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
variable (e : R) (S T : Y → R)
variable (hTS : ∀ y y', T y*S y'=if y=y' then e else 0) (hSe : ∀ y, S y*e=S y)
variable (ρ : W →* Rˣ) (ι : Q R →* W) (point : X R → Y)
variable (hρS : ∀ w y, (ρ w).val*S y=S (w • y))
variable (hTρ : ∀ w y, T y*(ρ w).val=T (w⁻¹ • y))
variable (hpoint : ∀ q x, ι q • point x=point (q • x))
variable (hφ : Function.Injective φ) (hρ : Function.Injective ρ)
variable (hι : Function.Injective ι) (hpt : Function.Injective point) (he : e≠0)
variable (F₂ : PairDiagrams (ZMod 2) ι point) (F₃ : PairDiagrams (ZMod 3) ι point)

include φ D e S T ρ ι point hρS hTρ hpoint hφ hρ hι hpt he hTS hSe F₂ F₃ in

theorem simple_geometric_overgroup_of_binary_ring_data
    (A : Type) [Finite A] (π : FreeAlgebra (ZMod 2) A →+* R)
    (hπ : Function.Surjective π) (rel : Set (FreeAlgebra (ZMod 2) A))
    (hrel : rel.Finite) (hker : TwoSidedIdeal.ker π=TwoSidedIdeal.span rel)
    (g : G →* Rˣ) (hg : Function.Injective g) :
    ∃ (H : Type) (_ : Group H), Nontrivial H ∧ IsSimpleGroup H ∧
      SimpleFInftyOvergroups.HasTypeFInfty H ∧
        ∃ ν : G →* H, Function.Injective ν := by
  let σ := limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι
  let := limitPoints_infinite φ e S T hTS point hφ hpt he
  obtain ⟨hf,ν,hν⟩ := localGroup_overgroup_of_binary_ring_data φ D e S T hTS hSe ρ ι point
    hρS hTρ hpoint hφ hρ hι hpt he F₂ F₃ A π hπ rel hrel hker g hg
  exact ⟨TwistedBrin.localGroup σ,inferInstance,TwistedBrin.localGroup_nontrivial σ,
    TwistedBrin.localGroup_simple σ,hf,ν,hν⟩
end StageGeometry

end
end

section

noncomputable section
namespace SimpleFInftyOvergroups
universe u

def evalWord {G : Type u} [Group G] {n : ℕ} (g : Fin n → G)
    (w : List (Fin n × Bool)) : G :=
  (w.map fun x => if x.2 then g x.1 else (g x.1)⁻¹).prod

def HasDecidableWordProblem (G : Type u) [Group G] : Prop :=
  ∃ (n : ℕ) (g : Fin n → G), Subgroup.closure (Set.range g) = ⊤ ∧
    ComputablePred (fun w : List (Fin n × Bool) => evalWord g w = 1)

lemma evalWord_map {G : Type u} {H : Type*} [Group G] [Group H]
    (f : G →* H) {n : ℕ} (g : Fin n → G) (w : List (Fin n × Bool)) :
    evalWord (fun i => f (g i)) w = f (evalWord g w) := by
  simp only [evalWord,map_list_prod,List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  split <;> simp_all

lemma wordProblem_of_equiv {G : Type u} {H : Type*} [Group G] [Group H]
    (e : G ≃* H) (h : HasDecidableWordProblem G) : HasDecidableWordProblem H := by
  obtain ⟨n,g,hg,hc⟩ := h
  refine ⟨n,(fun i => e (g i)),?_,?_⟩
  · apply top_unique
    intro y hy
    clear hy
    obtain ⟨x,rfl⟩ := e.surjective y
    have hx : x ∈ Subgroup.closure (Set.range g) := by rw [hg]; trivial
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i,rfl⟩ := hx
      exact Subgroup.subset_closure ⟨i,rfl⟩
    | one => simp
    | mul x y _ _ hx hy => simpa using Subgroup.mul_mem _ hx hy
    | inv x _ hx => simpa using Subgroup.inv_mem _ hx
  · have he : (fun w : List (Fin n × Bool) => evalWord (fun i => e (g i)) w = 1) =
        (fun w => evalWord g w = 1) := by
      funext w
      apply propext
      change evalWord (fun i => e.toMonoidHom (g i)) w = 1 ↔ _
      rw [evalWord_map]
      exact e.map_eq_one_iff
    rw [he]
    exact hc

lemma small_model (G : Type u) [Group G] (h : HasDecidableWordProblem G) :
    ∃ (G₀ : Type) (_ : Group G₀), Nonempty (G₀ ≃* G) ∧ HasDecidableWordProblem G₀ := by
  obtain ⟨n,g,hg,hc⟩ := h
  let p : FreeGroup (Fin n) →* G := FreeGroup.lift g
  have hp : Function.Surjective p := by
    rw [← MonoidHom.range_eq_top]
    change (FreeGroup.lift g).range = ⊤
    apply top_unique
    rw [← hg]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨FreeGroup.of i,by simp⟩
  let e := QuotientGroup.quotientKerEquivOfSurjective p hp
  exact ⟨FreeGroup (Fin n) ⧸ p.ker,inferInstance,⟨e⟩,
    wordProblem_of_equiv e.symm ⟨n,g,hg,hc⟩⟩
end SimpleFInftyOvergroups

namespace CWUniverse
open Set Metric Topology
universe u
variable {X : Type} [TopologicalSpace X] [CWComplex (univ : Set X)]

def chart {A : Type} (p : PartialEquiv A X) : PartialEquiv A (ULift.{u} X) where
  toFun a := ⟨p a⟩
  invFun x := p.symm x.down
  source := p.source
  target := ULift.down ⁻¹' p.target
  map_source' _ h := p.map_source h
  map_target' _ h := p.map_target h
  left_inv' _ h := p.left_inv h
  right_inv' _ h := ULift.ext _ _ (p.right_inv h)

omit [TopologicalSpace X] [CWComplex (univ : Set X)] in
lemma chart_image [TopologicalSpace X] [CWComplex (univ : Set X)]
    {A : Type} (p : PartialEquiv A X) (s : Set A) :
    chart.{u} p '' s = ULift.up '' (p '' s) := by
  rw [Set.image_image]; rfl

omit [CWComplex (univ : Set X)] in
lemma chart_continuous [CWComplex (univ : Set X)]
    {A : Type} [TopologicalSpace A] (p : PartialEquiv A X)
    (s : Set A) (h : ContinuousOn p s) : ContinuousOn (chart.{u} p) s :=
  Homeomorph.ulift.symm.continuous.comp_continuousOn h

omit [CWComplex (univ : Set X)] in
lemma chart_symm_continuous [CWComplex (univ : Set X)]
    {A : Type} [TopologicalSpace A] (p : PartialEquiv A X)
    (h : ContinuousOn p.symm p.target) :
    ContinuousOn (chart.{u} p).symm (chart.{u} p).target :=
  h.comp Homeomorph.ulift.continuous.continuousOn (fun _ hx => hx)

@[instance_reducible] def cw : CWComplex (univ : Set (ULift.{u} X)) where
  cell n := ULift.{u} (Topology.CWComplex.cell (univ : Set X) n)
  map n i := chart (Topology.CWComplex.map n i.down)
  source_eq n i := Topology.CWComplex.source_eq n i.down
  continuousOn n i := chart_continuous _ _ (Topology.CWComplex.continuousOn n i.down)
  continuousOn_symm n i := chart_symm_continuous _ (Topology.CWComplex.continuousOn_symm n i.down)
  pairwiseDisjoint' := by
    rintro ⟨n,⟨i⟩⟩ _ ⟨m,⟨j⟩⟩ _ hij
    have hne : (⟨n,i⟩ : Σ n, Topology.CWComplex.cell (univ : Set X) n) ≠ ⟨m,j⟩ := by
      intro h
      cases h
      exact hij rfl
    have hd := @Topology.CWComplex.pairwiseDisjoint' X _ (univ : Set X) _
      ⟨n,i⟩ (mem_univ _) ⟨m,j⟩ (mem_univ _) hne
    apply Set.disjoint_left.mpr
    rintro z ⟨a,ha,he⟩ ⟨b,hb,hf⟩
    exact Set.disjoint_left.mp hd ⟨a,ha,congrArg ULift.down he⟩ ⟨b,hb,congrArg ULift.down hf⟩
  mapsTo' n i := by
    classical
    obtain ⟨I,hI⟩ := Topology.CWComplex.mapsTo' n i.down
    refine ⟨fun m => (I m).map ⟨ULift.up,ULift.up_injective⟩,?_⟩
    intro a ha
    have hh := hI ha
    simp only [Set.mem_iUnion,Set.mem_image] at hh ⊢
    obtain ⟨m,hm,j,hj,b,hb,hba⟩ := hh
    refine ⟨m,hm,⟨j⟩,Finset.mem_map.mpr ⟨j,hj,rfl⟩,b,hb,?_⟩
    exact congrArg ULift.up hba
  closed' A _ hA := by
    have h : IsClosed (ULift.up ⁻¹' A : Set X) := by
      apply Topology.CWComplex.closed' _ (subset_univ _)
      intro n i
      have h' := (hA n ⟨i⟩).preimage Homeomorph.ulift.symm.continuous
      change IsClosed (ULift.up ⁻¹' (A ∩ chart.{u} (Topology.CWComplex.map n i) '' closedBall 0 1)) at h'
      simpa only [chart_image,Set.preimage_inter,Set.preimage_image_eq _ ULift.up_injective] using h'
    have h' := Homeomorph.ulift.symm.isClosedMap _ h
    change IsClosed (ULift.up '' (ULift.up ⁻¹' A) : Set (ULift.{u} X)) at h'
    rwa [Set.image_preimage_eq _ ULift.up_surjective] at h'
  union' := by
    apply Set.Subset.antisymm (subset_univ _)
    rintro ⟨x⟩ _
    have hx : x ∈ ⋃ n, ⋃ i : Topology.CWComplex.cell (univ : Set X) n,
        Topology.CWComplex.map n i '' closedBall 0 1 := by rw [Topology.CWComplex.union']; trivial
    simp only [Set.mem_iUnion,Set.mem_image] at hx ⊢
    obtain ⟨n,i,a,ha,rfl⟩ := hx
    exact ⟨n,⟨i⟩,a,ha,rfl⟩
end CWUniverse

namespace CWUniverse
open Set Topology
universe u
variable {X : Type} [TopologicalSpace X] [CWComplex (univ : Set X)]

lemma finiteType [Topology.CWComplex.FiniteType (univ : Set X)] :
    letI := cw.{u} (X:=X)
    Topology.CWComplex.FiniteType (univ : Set (ULift.{u} X)) := by
  let := cw.{u} (X:=X)
  refine ⟨fun n => ?_⟩
  change Finite (ULift.{u} (Topology.CWComplex.cell (univ : Set X) n))
  let : Finite (Topology.CWComplex.cell (univ : Set X) n) :=
    Topology.CWComplex.FiniteType.finite_cell (C:=(univ : Set X)) (D:=∅) n
  infer_instance

variable (x : X)
def piOne : FundamentalGroup X x ≃* FundamentalGroup (ULift.{u} X) (ULift.up x) := by
  let e := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (Homeomorph.ulift (X:=X)).symm.toHomotopyEquiv
  let f := FundamentalGroup.map (⟨ULift.up,Homeomorph.ulift.symm.continuous⟩ : C(X,ULift.{u} X)) x
  exact { e.fullyFaithfulFunctor.homEquiv (X:=FundamentalGroupoid.mk x)
           (Y:=FundamentalGroupoid.mk x) with
    map_mul' := f.map_mul }
end CWUniverse

namespace SimpleFInftyOvergroups
universe u
lemma HasTypeFInfty.ulift {H : Type} [Group H] (h : HasTypeFInfty H) :
    HasTypeFInfty (ULift.{u} H) := by
  obtain ⟨X,t,cw,ht,hc,hf,x,⟨e⟩,E,tE,p,hp,hs,hE⟩ := h
  let := t
  let := tE
  let := cw
  let := ht
  let := hc
  let := hf
  let := hE
  let := CWUniverse.cw.{u} (X:=X)
  let : ContractibleSpace (ULift.{u} E) := Homeomorph.ulift.contractibleSpace
  refine ⟨ULift.{u} X,inferInstance,inferInstance,inferInstance,?_,
    CWUniverse.finiteType,ULift.up x,⟨MulEquiv.ulift.trans (e.trans (CWUniverse.piOne x))⟩,
    ULift.{u} E,inferInstance,ULift.up ∘ p ∘ ULift.down,?_,?_,inferInstance⟩
  · exact Homeomorph.ulift.symm.surjective.connectedSpace Homeomorph.ulift.symm.continuous
  · exact (hp.comp_homeomorph Homeomorph.ulift).homeomorph_comp Homeomorph.ulift.symm
  · exact ULift.up_surjective.comp (hs.comp ULift.down_surjective)

lemma lift_explicit_overgroup {G : Type u} [Group G] {G₀ H : Type} [Group G₀] [Group H]
    (e : G₀ ≃* G) (f : G₀ →* H) (hinj : Function.Injective f)
    (hnt : Nontrivial H) (hsi : IsSimpleGroup H) (hf : HasTypeFInfty H) :
    Nontrivial (ULift.{u} H) ∧ IsSimpleGroup (ULift.{u} H) ∧
      HasTypeFInfty (ULift.{u} H) ∧
        ∃ f' : G →* ULift.{u} H, Function.Injective f' := by
  let := hnt
  let := hsi
  refine ⟨inferInstance,MulEquiv.ulift.isSimpleGroup,hf.ulift,?_,?_⟩
  · exact MulEquiv.ulift.symm.toMonoidHom.comp (f.comp e.symm.toMonoidHom)
  · exact MulEquiv.ulift.symm.injective.comp (hinj.comp e.symm.injective)
end SimpleFInftyOvergroups

end
end

section

noncomputable section
namespace SimpleFInftyOvergroups
open StageConstruction

structure RequiredRingWitness (G : Type) [Group G] where
  R : Type
  [ringR : Ring R]
  [nontrivialR : Nontrivial R]
  Y : Type
  W : Type
  [groupW : Group W]
  [action : MulAction W Y]
  [decY : DecidableEq Y]
  φ : R →ₙ+* R
  binary : CompressedSplittings.BinaryData φ
  e : R
  S : Y → R
  T : Y → R
  hTS : ∀ y y', T y*S y'=if y=y' then e else 0
  hSe : ∀ y, S y*e=S y
  ρ : W →* Rˣ
  ι : Q R →* W
  point : X R → Y
  hρS : ∀ w y, (ρ w).val*S y=S (w • y)
  hTρ : ∀ w y, T y*(ρ w).val=T (w⁻¹ • y)
  hpoint : ∀ q x, ι q • point x=point (q • x)
  hφ : Function.Injective φ
  hρ : Function.Injective ρ
  hι : Function.Injective ι
  hpt : Function.Injective point
  he : e ≠ 0
  F₂ : StageGeometry.PairDiagrams (ZMod 2) ι point
  F₃ : StageGeometry.PairDiagrams (ZMod 3) ι point
  A : Type
  [finiteA : Finite A]
  π : FreeAlgebra (ZMod 2) A →+* R
  hπ : Function.Surjective π
  rel : Set (FreeAlgebra (ZMod 2) A)
  hrel : rel.Finite
  hker : TwoSidedIdeal.ker π = TwoSidedIdeal.span rel
  g : G →* Rˣ
  hg : Function.Injective g

def RingProducerObligation : Prop :=
  ∀ (G : Type) [Group G], HasDecidableWordProblem G → Nonempty (RequiredRingWitness G)

namespace RequiredRingWitness
variable {G : Type} [Group G]

theorem realize (d : RequiredRingWitness G) :
    ∃ (H : Type) (_ : Group H), Nontrivial H ∧ IsSimpleGroup H ∧
      HasTypeFInfty H ∧ ∃ f : G →* H, Function.Injective f := by
  let := d.ringR
  let := d.nontrivialR
  let := d.groupW
  let := d.action
  let := d.decY
  let := d.finiteA
  exact StageGeometry.simple_geometric_overgroup_of_binary_ring_data
    d.φ d.binary d.e d.S d.T d.hTS d.hSe d.ρ d.ι d.point d.hρS d.hTρ d.hpoint
    d.hφ d.hρ d.hι d.hpt d.he d.F₂ d.F₃ d.A d.π d.hπ d.rel d.hrel d.hker d.g d.hg

universe u

theorem realize_in_input_universe {G' : Type u} [Group G']
    (e : G ≃* G') (d : RequiredRingWitness G) :
    ∃ (H : Type u) (_ : Group H), Nontrivial H ∧ IsSimpleGroup H ∧
      HasTypeFInfty H ∧ ∃ f : G' →* H, Function.Injective f := by
  obtain ⟨H,iH,hnt,hsi,hf,f,hinj⟩ := d.realize
  let := iH
  exact ⟨ULift.{u} H,inferInstance,lift_explicit_overgroup e f hinj hnt hsi hf⟩
end RequiredRingWitness
end SimpleFInftyOvergroups

end
end

section

noncomputable section

end
end

end OAI
