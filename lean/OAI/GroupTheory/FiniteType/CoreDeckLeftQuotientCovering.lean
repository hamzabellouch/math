import Mathlib
import OAI.GroupTheory.FiniteType.PresentationGeometryRose

namespace OAI

noncomputable section
namespace CoreDeck
open Set Topology
variable {ι X Q : Type} [TopologicalSpace X] [Group Q] [TopologicalSpace Q]
  [DiscreteTopology Q] (Z : FiberBundleCore ι X Q)
  (hZ : ∀ i j x a q, Z.coordChange i j x (a*q) = Z.coordChange i j x a * q)

include hZ in
theorem leftQuotientCovering :
    letI := leftAction Z
    IsQuotientCoveringMap Z.proj Q := by
  let := leftAction Z
  let := continuousLeftAction Z hZ
  let cov := DiscreteCoverCharts.covering Z
  exact {
    toIsQuotientMap := cov.isQuotientMap (fun x => ⟨⟨x,(1:Q)⟩,rfl⟩)
    continuous_const_smul := continuous_const_smul
    apply_eq_iff_mem_orbit := by
      intro a b
      constructor
      · intro h
        obtain ⟨q,hq⟩ := left_transitive Z b a h.symm
        exact ⟨q,hq⟩
      · rintro ⟨q,rfl⟩
        rfl
    disjoint := by
      intro x
      obtain ⟨t,hxt,hpt⟩ := cov.isLocalHomeomorph x
      refine ⟨t.source,t.open_source.mem_nhds hxt,?_⟩
      intro q hq
      rcases hq with ⟨z,⟨y,hy,rfl⟩,hqy⟩
      have he : q • y = y := t.injOn hqy hy (by rw [← hpt]; rfl)
      exact left_free Z q 1 y (he.trans (one_smul Q y).symm) }

def leftFundamentalEquiv [SimplyConnectedSpace Z.TotalSpace] (x : X) :
    Q ≃* FundamentalGroup X x := by
  letI := leftAction Z
  exact (MulEquiv.inv' Q).trans
    ((leftQuotientCovering Z hZ).fundamentalGroupEquiv ⟨⟨x,(1:Q)⟩,rfl⟩).symm
end CoreDeck

namespace PresentationGeometry.FiniteStage
attribute [-instance] AddCommGroup.toIntModule
open Set Topology Metric CategoryTheory CategoryTheory.Limits Cells CWExtension CellCoverExtension
open HurewiczConstruction
variable (Q : Type) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]

structure Stage (n : ℕ) where
  X : Type
  [topology : TopologicalSpace X]
  [t2 : T2Space X]
  [compact : CompactSpace X]
  [cw : CWComplex (univ : Set X)]
  [finite : RelCWComplex.Finite (univ : Set X)]
  point : X
  dimension : ∀ m, RelCWComplex.cell (univ : Set X) m → m < n+3
  I : Type
  core : FiberBundleCore I X Q
  pot : I → X → Q
  coord : ∀ i j x q, core.coordChange i j x q = pot j x * (pot i x)⁻¹ * q
  [simply : SimplyConnectedSpace core.TotalSpace]
  connectivity : ∀ p ≤ n+1, ∀ z : core.TotalSpace,
    Subsingleton (HomotopyGroup (Fin p) core.TotalSpace z)

attribute [instance] Stage.topology Stage.t2 Stage.compact Stage.cw Stage.finite Stage.simply
instance {n : ℕ} (S : Stage Q n) : Nonempty S.X := ⟨S.point⟩

variable {Q} {n : ℕ} (S : Stage Q n)

def sphereFamily {k d : ℕ} {E : Type} [TopologicalSpace E]
    (s : Fin k → C(Boundary d,E)) : C(boundary k d,E) := by
  let t : C(Fin k × Boundary d,E) := ⟨fun z => s z.1 z.2,by
    apply continuous_iff_continuousAt.mpr
    intro z
    have hf : ∀ᶠ w : Fin k × Boundary d in nhds z, w.1 = z.1 :=
      (continuous_fst.tendsto z).eventually (isOpen_discrete {z.1} |>.mem_nhds (by rfl))
    apply ((s z.1).continuous.comp continuous_snd).continuousAt.congr_of_eventuallyEq
    filter_upwards [hf] with w hw
    simp only [hw,Function.comp_apply]⟩
  exact t.comp ⟨boundaryProductEquiv k d,(boundaryProductEquiv k d).continuous⟩

@[simp] lemma sphereFamily_slice {k d : ℕ} {E : Type} [TopologicalSpace E]
    (s : Fin k → C(Boundary d,E)) (i : Fin k) :
    (sphereFamily s).comp (boundarySlice i) = s i := rfl

structure Attachment where
  k : ℕ
  sphere : C(boundary k (n+3),S.core.TotalSpace)
  generates :
    letI := CoreDeck.leftAction S.core
    letI := CoreDeck.continuousLeftAction S.core (CoreDeck.of_potential S.core S.pot S.coord)
    Submodule.span (MonoidAlgebra ℤ Q)
      (Set.range (fun i : Fin k => sphereModuleClass (G:=Q) (n+2) (sphere.comp (boundarySlice i)))) = ⊤

lemma attachment_exists
    (hzero : ∀ I : Type, IsZero (groupHomology (RegularProductR.rep ℤ Q I) (n+2))) :
    Nonempty (Attachment S) := by
  let := CoreDeck.leftAction S.core
  let := CoreDeck.continuousLeftAction S.core (CoreDeck.of_potential S.core S.pot S.coord)
  let : Finite (RelCWComplex.cell (univ : Set S.X) (n+2)) :=
    RelCWComplex.FiniteType.finite_cell (n+2)
  have : Module.Finite (MonoidAlgebra ℤ Q)
      (homologyModule (G:=Q) (X:=S.core.TotalSpace) (n+2)) :=
    CoreDeck.critical_finite S.core (CoreDeck.of_potential S.core S.pot S.coord) n S.connectivity hzero
  obtain ⟨k,s,hs⟩ := finite_sphere_generators (G:=Q) (n:=n+1)
    (fun p hp z => S.connectivity p (by omega) z) ⟨S.point,(1:Q)⟩
  exact ⟨⟨k,sphereFamily s,by simpa only [sphereFamily_slice] using hs⟩⟩

noncomputable def attachment
    (hzero : ∀ I : Type, IsZero (groupHomology (RegularProductR.rep ℤ Q I) (n+2))) :
    Attachment S := Classical.choice (attachment_exists S hzero)

def Attachment.base (A : Attachment S) : C(boundary A.k (n+3),S.X) :=
  (⟨S.core.proj,S.core.continuous_proj⟩ : C(S.core.TotalSpace,S.X)).comp A.sphere

noncomputable def next (A : Attachment S) : Stage Q (n+1) where
  X := Cells.Space (A.base S)
  topology := inferInstance
  t2 := inferInstance
  compact := inferInstance
  cw := Cells.cwComplex (A.base S) S.dimension
  finite := Cells.cwComplex_finite (A.base S) S.dimension
  point := Adjunction.old (A.base S) S.point
  dimension := by
    intro m c
    change NewCell (X:=S.X) (k:=A.k) (d:=n+3) m at c
    rcases c with c | ⟨i,⟨h⟩⟩
    · have := S.dimension m c
      omega
    · omega
  I := S.I ⊕ Fin A.k
  core := coveringCore (A.base S) S.point S.core S.pot A.sphere (fun _ => rfl) S.coord
  pot := potential (A.base S) S.point S.core S.pot A.sphere
  coord := fun _ _ _ _ => rfl
  simply := coveringCore_simplyConnected (A.base S) S.point S.core S.pot A.sphere
    (fun _ => rfl) S.coord (by omega)
  connectivity := coveringCore_connectivity_left (A.base S) S.point S.core S.pot A.sphere
    (fun _ => rfl) S.coord S.dimension S.connectivity A.generates

attribute [instance] AddCommGroup.toIntModule
end PresentationGeometry.FiniteStage

namespace PresentationGeometry.PresentationComplex
open DiscreteCoverCharts
variable {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
variable {k r : ℕ} (w : Fin r → List (Fin k × Bool))
variable (eQ : Q ≃* PresentedGroup (relatorSet w))
def transportedGenerators : Fin k → Q := fun i => eQ.symm (PresentedGroup.of i)
omit [TopologicalSpace Q] [DiscreteTopology Q] in
lemma lift_transportedGenerators : FreeGroup.lift (transportedGenerators w eQ) =
    eQ.symm.toMonoidHom.comp (PresentedGroup.mk (relatorSet w)) := by
  apply FreeGroup.ext_hom
  intro i
  rw [FreeGroup.lift_apply_of]
  rfl
omit [TopologicalSpace Q] [DiscreteTopology Q] in
lemma transported_relators (i : Fin r) :
    FreeGroup.lift (transportedGenerators w eQ) (FreeGroup.mk (w i)) = 1 := by
  have h : PresentedGroup.mk (relatorSet w) (FreeGroup.mk (w i)) = 1 :=
    PresentedGroup.one_of_mem ⟨i,rfl⟩
  rw [lift_transportedGenerators,MonoidHom.comp_apply,h,map_one]
def transportedCore := coveringCore w (transportedGenerators w eQ) (transported_relators w eQ)
def transportedBasepoint : (transportedCore w eQ).TotalSpace :=
  point (transportedCore w eQ) (.inl none) (basepoint w) 1
lemma transported_monodromyRepresentation (a : PresentedGroup (relatorSet w)) (q : Q) :
    monodromyRepresentation w (transportedGenerators w eQ) (transported_relators w eQ)
      (presentationEquiv w a) q = eQ.symm a * q := by
  obtain ⟨z,rfl⟩ := PresentedGroup.mk_surjective (relatorSet w) a
  have h := DFunLike.congr_fun
    (monodromyRepresentation_comp w (transportedGenerators w eQ) (transported_relators w eQ)) z
  rw [lift_transportedGenerators] at h
  change monodromyRepresentation w (transportedGenerators w eQ) (transported_relators w eQ)
    (freeToFundamental w z) = _ at h
  change monodromyRepresentation w (transportedGenerators w eQ) (transported_relators w eQ)
    (presentedToFundamental w (PresentedGroup.mk _ z)) q = _
  rw [presentedToFundamental_mk,h]
  rfl
lemma transported_monodromy_bijective : Function.Bijective
    (fun γ : FundamentalGroup (Space w) (basepoint w) =>
      (covering (transportedCore w eQ)).monodromy γ ⟨transportedBasepoint w eQ,rfl⟩) := by
  let e := fiberEquiv (transportedCore w eQ) (.inl none) (basepoint w)
    (basepoint_mem_coveringCore w (transportedGenerators w eQ) (transported_relators w eQ))
  have h (γ : FundamentalGroup (Space w) (basepoint w)) :
      (covering (transportedCore w eQ)).monodromy γ ⟨transportedBasepoint w eQ,rfl⟩ =
        e (eQ.symm ((presentationEquiv w).symm γ)) := by
    have hm := transported_monodromyRepresentation w eQ ((presentationEquiv w).symm γ) 1
    rw [(presentationEquiv w).apply_symm_apply] at hm
    have he := congrArg e (hm.trans (mul_one _))
    exact (e.apply_symm_apply _).symm.trans he
  have heq : (fun γ : FundamentalGroup (Space w) (basepoint w) =>
      (covering (transportedCore w eQ)).monodromy γ ⟨transportedBasepoint w eQ,rfl⟩) =
      e ∘ eQ.symm ∘ (presentationEquiv w).symm := funext h
  rw [heq]
  exact e.bijective.comp (eQ.symm.bijective.comp (presentationEquiv w).symm.bijective)
instance transported_simplyConnected : SimplyConnectedSpace (transportedCore w eQ).TotalSpace :=
  RegularCoverGeometry.simplyConnected_of_monodromy_bijective
    (covering (transportedCore w eQ)) (transportedBasepoint w eQ) (transported_monodromy_bijective w eQ)
noncomputable def initialStage : FiniteStage.Stage Q 0 where
  X := Space w
  topology := inferInstance
  t2 := inferInstance
  compact := inferInstance
  cw := inferInstance
  finite := inferInstance
  point := basepoint w
  dimension := dimension w
  I := Option (Fin k) ⊕ Fin r
  core := transportedCore w eQ
  pot := CellCoverExtension.potential (AttachingLoops.relators w) (Rose.basepoint k)
    (Rose.coveringCore (transportedGenerators w eQ)) (Rose.potential (transportedGenerators w eQ))
    (AttachingLoops.relatorSection w (transportedGenerators w eQ) (transported_relators w eQ))
  coord := fun _ _ _ _ => rfl
  simply := inferInstance
  connectivity := by
    intro p hp z
    interval_cases p
    · exact HurewiczConstruction.homotopy_zero z
    · exact HurewiczConstruction.homotopy_one z
end PresentationGeometry.PresentationComplex
namespace PresentationGeometry.FiniteStage
section
variable (Q : Type) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
lemma initialStage_exists [Group.IsFinitelyPresented Q] : Nonempty (Stage Q 0) := by
  obtain ⟨k,r,w,⟨e⟩⟩ := exists_word_presentation Q
  exact ⟨PresentationComplex.initialStage w e⟩
end

section
open Set Topology Metric Cells CWExtension CellCoverExtension
variable {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
variable {n : ℕ} (S : Stage Q n) (A : Attachment S)

def step : C(S.X,(next S A).X) := ⟨Adjunction.old (A.base S),Adjunction.continuous_old _⟩
lemma step_closed : IsClosedEmbedding (step S A) :=
  Adjunction.old_isClosedEmbedding (boundary_closed _ _) _
def cellStep (d : ℕ) : RelCWComplex.cell (univ : Set S.X) d ↪
    RelCWComplex.cell (univ : Set (next S A).X) d := ⟨Sum.inl,Sum.inl_injective⟩
lemma step_chart (d : ℕ) (c : RelCWComplex.cell (univ : Set S.X) d) (v : Fin d → ℝ) :
    step S A (RelCWComplex.map d c v) = RelCWComplex.map d (cellStep S A d c) v := rfl
lemma cellStep_surjective (d : ℕ) (hd : d ≠ n+3) : Function.Surjective (cellStep S A d) := by
  intro c
  change NewCell (X:=S.X) (k:=A.k) (d:=n+3) d at c
  rcases c with c | ⟨i,⟨he⟩⟩
  · exact ⟨c,rfl⟩
  · exact (hd he).elim

def indexStep : S.I ↪ (next S A).I := ⟨Sum.inl,Sum.inl_injective⟩
lemma step_base (a : S.I) (x : S.X) :
    x ∈ S.core.baseSet a ↔ step S A x ∈ (next S A).core.baseSet (indexStep S A a) :=
  (mem_coveringCore_old (A.base S) S.point S.core S.pot A.sphere
    (fun _ => rfl) S.coord a x).symm
lemma step_pot (a : S.I) (x : S.X) :
    (next S A).pot (indexStep S A a) (step S A x) = S.pot a x := by
  change S.pot a (retractAt (A.base S) S.point (Adjunction.old (A.base S) x)) = _
  rw [retractAt_old]

variable (S₀ : Stage Q 0)
variable (hzero : ∀ I : Type, ∀ m ≥ 2, CategoryTheory.Limits.IsZero
  (groupHomology (RegularProductR.rep ℤ Q I) m))
noncomputable def stages : (n : ℕ) → Stage Q n
  | 0 => S₀
  | n+1 => next (stages n) (attachment (stages n) (fun I => hzero I (n+2) (by omega)))
noncomputable def attachments (n : ℕ) : Attachment (stages S₀ hzero n) :=
  attachment (stages S₀ hzero n) (fun I => hzero I (n+2) (by omega))
abbrev stageX (n : ℕ) := (stages S₀ hzero n).X
abbrev stageI (n : ℕ) := (stages S₀ hzero n).I
noncomputable def succMap (n : ℕ) : C(stageX S₀ hzero n,stageX S₀ hzero (n+1)) :=
  step _ (attachments S₀ hzero n)
noncomputable def succIndex (n : ℕ) : stageI S₀ hzero n ↪ stageI S₀ hzero (n+1) :=
  indexStep _ (attachments S₀ hzero n)
noncomputable def succCell (n d : ℕ) : RelCWComplex.cell (univ : Set (stageX S₀ hzero n)) d ↪
    RelCWComplex.cell (univ : Set (stageX S₀ hzero (n+1))) d :=
  cellStep _ (attachments S₀ hzero n) d
end

open Set Topology Metric
variable {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
variable (S₀ : Stage Q 0)
variable (hzero : ∀ I : Type, ∀ m ≥ 2, CategoryTheory.Limits.IsZero
  (groupHomology (RegularProductR.rep ℤ Q I) m))

noncomputable def stageMap (i j : ℕ) (h : i ≤ j) : C(stageX S₀ hzero i,stageX S₀ hzero j) :=
  ⟨Nat.leRecOn h (fun {k} x => succMap S₀ hzero k x),by
    induction j,h using Nat.le_induction with
    | base =>
      convert (continuous_id (X:=stageX S₀ hzero i)) using 1
      ext x
      exact Nat.leRecOn_self x
    | succ j h ih =>
      simpa only [Nat.leRecOn_succ h,Function.comp_def] using (succMap S₀ hzero j).continuous.comp ih⟩
instance mapSystem : DirectedSystem (stageX S₀ hzero) (stageMap S₀ hzero · · ·) where
  map_self {_} x := Nat.leRecOn_self x
  map_map {_ _ _} h₁ h₂ x := (Nat.leRecOn_trans h₁ h₂ x).symm
lemma stageMap_succ (i j : ℕ) (h : i ≤ j) (h' : i ≤ j+1) (x : stageX S₀ hzero i) :
    stageMap S₀ hzero i (j+1) h' x = succMap S₀ hzero j (stageMap S₀ hzero i j h x) :=
  Nat.leRecOn_succ h x
lemma stageMap_closed (i j : ℕ) (h : i ≤ j) : IsClosedEmbedding (stageMap S₀ hzero i j h) := by
  induction j,h using Nat.le_induction with
  | base =>
    convert (IsClosedEmbedding.id (X:=stageX S₀ hzero i)) using 1
    ext x
    exact Nat.leRecOn_self x
  | succ j h ih =>
    have he : (stageMap S₀ hzero i (j+1) (by omega) : _) =
        (succMap S₀ hzero j).comp (stageMap S₀ hzero i j h) := by
      ext x; exact stageMap_succ S₀ hzero i j h _ x
    rw [he]
    exact (step_closed _ (attachments S₀ hzero j)).comp ih
noncomputable def stageIndex (i j : ℕ) (h : i ≤ j) : stageI S₀ hzero i ↪ stageI S₀ hzero j :=
  ⟨Nat.leRecOn h (fun {k} x => succIndex S₀ hzero k x),
    Nat.leRecOn_injective h _ (fun k => (succIndex S₀ hzero k).injective)⟩
instance indexSystem : DirectedSystem (stageI S₀ hzero) (stageIndex S₀ hzero · · ·) where
  map_self {_} x := Nat.leRecOn_self x
  map_map {_ _ _} h₁ h₂ x := (Nat.leRecOn_trans h₁ h₂ x).symm
lemma stageIndex_succ (i j : ℕ) (h : i ≤ j) (h' : i ≤ j+1) (a : stageI S₀ hzero i) :
    stageIndex S₀ hzero i (j+1) h' a = succIndex S₀ hzero j (stageIndex S₀ hzero i j h a) :=
  Nat.leRecOn_succ h a
noncomputable def stageCell (i j : ℕ) (h : i ≤ j) (d : ℕ) :
    RelCWComplex.cell (univ : Set (stageX S₀ hzero i)) d ↪
    RelCWComplex.cell (univ : Set (stageX S₀ hzero j)) d :=
  ⟨Nat.leRecOn h (fun {k} x => succCell S₀ hzero k d x),
    Nat.leRecOn_injective h _ (fun k => (succCell S₀ hzero k d).injective)⟩
instance cellSystem (d : ℕ) : DirectedSystem
    (fun i => RelCWComplex.cell (univ : Set (stageX S₀ hzero i)) d)
    (fun i j h => stageCell S₀ hzero i j h d) where
  map_self {_} x := Nat.leRecOn_self (C:=fun i => RelCWComplex.cell (univ : Set (stageX S₀ hzero i)) d) x
  map_map {_ _ _} h₁ h₂ x := (Nat.leRecOn_trans (C:=fun i => RelCWComplex.cell (univ : Set (stageX S₀ hzero i)) d) h₁ h₂ x).symm
lemma stageCell_succ (i j : ℕ) (h : i ≤ j) (h' : i ≤ j+1) (d : ℕ)
    (c : RelCWComplex.cell (univ : Set (stageX S₀ hzero i)) d) :
    stageCell S₀ hzero i (j+1) h' d c = succCell S₀ hzero j d (stageCell S₀ hzero i j h d c) :=
  Nat.leRecOn_succ (C:=fun i => RelCWComplex.cell (univ : Set (stageX S₀ hzero i)) d) h c
lemma stageMap_chart (i j : ℕ) (h : i ≤ j) (d : ℕ)
    (c : RelCWComplex.cell (univ : Set (stageX S₀ hzero i)) d) (v : Fin d → ℝ) :
    stageMap S₀ hzero i j h (RelCWComplex.map d c v) =
      RelCWComplex.map d (stageCell S₀ hzero i j h d c) v := by
  induction j,h using Nat.le_induction with
  | base =>
    simp only [stageMap,stageCell,ContinuousMap.coe_mk,Function.Embedding.coeFn_mk,Nat.leRecOn_self]
  | succ j h ih =>
    rw [stageMap_succ S₀ hzero i j h,stageCell_succ S₀ hzero i j h,ih]
    exact step_chart _ (attachments S₀ hzero j) d _ v
lemma stage_base (i j : ℕ) (h : i ≤ j) (a : stageI S₀ hzero i) (x : stageX S₀ hzero i) :
    x ∈ (stages S₀ hzero i).core.baseSet a ↔
      stageMap S₀ hzero i j h x ∈ (stages S₀ hzero j).core.baseSet (stageIndex S₀ hzero i j h a) := by
  induction j,h using Nat.le_induction with
  | base => simp only [DirectedSystem.map_self']
  | succ j h ih =>
    rw [stageMap_succ S₀ hzero i j h,stageIndex_succ S₀ hzero i j h]
    exact ih.trans (step_base _ (attachments S₀ hzero j) _ _)
lemma stage_pot (i j : ℕ) (h : i ≤ j) (a : stageI S₀ hzero i) (x : stageX S₀ hzero i) :
    (stages S₀ hzero j).pot (stageIndex S₀ hzero i j h a) (stageMap S₀ hzero i j h x) =
      (stages S₀ hzero i).pot a x := by
  induction j,h using Nat.le_induction with
  | base => simp only [DirectedSystem.map_self']
  | succ j h ih =>
    rw [stageMap_succ S₀ hzero i j h,stageIndex_succ S₀ hzero i j h]
    exact (step_pot _ (attachments S₀ hzero j) _ _).trans ih
lemma stageCell_stable (d i : ℕ) (h : d ≤ i) : Function.Surjective (stageCell S₀ hzero d i h d) := by
  induction i,h using Nat.le_induction with
  | base =>
    intro c; refine ⟨c,?_⟩
    simp only [stageCell,Function.Embedding.coeFn_mk,Nat.leRecOn_self]
  | succ i h ih =>
    intro c
    obtain ⟨c,rfl⟩ := cellStep_surjective (stages S₀ hzero i) (attachments S₀ hzero i) d (by omega) c
    obtain ⟨c,rfl⟩ := ih c
    exact ⟨c,stageCell_succ S₀ hzero d i h _ d c⟩
end PresentationGeometry.FiniteStage

end

end OAI
