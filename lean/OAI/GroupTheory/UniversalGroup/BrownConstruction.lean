import OAI.GroupTheory.UniversalGroup.TowerCoverings

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.Brown

section
open Set Metric Topology Cellular Attachment
universe u
variable (G : Type u) [Group G]

structure Stage (n : ℕ) where
  E : Type u
  B : Type u
  [topE : TopologicalSpace E]
  [topB : TopologicalSpace B]
  [nonemptyE : Nonempty E]
  [nonemptyB : Nonempty B]
  sepE : RealSeparated E
  sepB : RealSeparated B
  [cwE : CWComplex (univ : Set E)]
  [cwB : CWComplex (univ : Set B)]
  [action : MulAction G E]
  [continuousAction : ContinuousConstSMul G E]
  orbits : ℕ → Type u
  orbitFinite : ∀ m,Finite (orbits m)
  equiv : ∀ m,(G × orbits m) ≃ cwE.cell m
  equiv_map : ∀ m (g h : G) (i : orbits m) (x : Fin m → ℝ),
    cwE.map m (equiv m (g*h,i)) x = g • cwE.map m (equiv m (h,i)) x
  dimE : ∀ m (_ : cwE.cell m), m ≤ n
  dimB : ∀ m (_ : cwB.cell m), m ≤ n
  finiteB : ∀ m,Finite (cwB.cell m)
  fill : LowFillable E n
  p : C(E,B)
  covering : IsQuotientCoveringMap p G

attribute [instance] Stage.topE Stage.topB Stage.nonemptyE Stage.nonemptyB
  Stage.cwE Stage.cwB Stage.action Stage.continuousAction Stage.orbitFinite Stage.finiteB

instance {n : ℕ} (S : Stage G n) : T2Space S.E := S.sepE.t2Space
instance {n : ℕ} (S : Stage G n) : T2Space S.B := S.sepB.t2Space

variable {G}

def ZeroOrbits : ℕ → Type u
  | 0 => PUnit
  | _+1 => PEmpty
instance (m : ℕ) : Finite (ZeroOrbits.{u} m) := by cases m <;> dsimp [ZeroOrbits] <;> infer_instance

section Zero
variable [TopologicalSpace G] [DiscreteTopology G]
def zeroEquiv (m : ℕ) : (G × ZeroOrbits.{u} m) ≃ RelCWComplex.cell (univ : Set G) m := by
  cases m with
  | zero =>
    exact { toFun := fun p => ⟨p.1,trivial⟩
            invFun := fun p => (p.1,PUnit.unit)
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  | succ m =>
    change (G × PEmpty.{u+1}) ≃ PEmpty
    exact Equiv.equivOfIsEmpty _ _
lemma zeroEquiv_map (m : ℕ) (g h : G) (i : ZeroOrbits.{u} m) (x : Fin m → ℝ) :
    RelCWComplex.map m (zeroEquiv m (g*h,i)) x = g • RelCWComplex.map m (zeroEquiv m (h,i)) x := by
  cases m with
  | zero => rfl
  | succ m => exact i.elim
lemma discrete_dim {X : Type u} [TopologicalSpace X] [DiscreteTopology X]
    (m : ℕ) (i : RelCWComplex.cell (univ : Set X) m) : m ≤ 0 := by
  cases m with
  | zero => exact le_rfl
  | succ m => exact i.elim

def pointCover : C(G,PUnit.{u+1}) := .const _ PUnit.unit
lemma pointCover_quotient : IsQuotientCoveringMap (pointCover (G := G)) G where
  __ := show IsQuotientMap (pointCover (G := G)) from
    (show IsOpenMap (pointCover (G := G)) from fun _ _ => isOpen_discrete _).isQuotientMap
      (by fun_prop) (fun _ => ⟨1,rfl⟩)
  __ := (inferInstance : ContinuousConstSMul G G)
  apply_eq_iff_mem_orbit := by
    intro x y
    constructor
    · intro _; exact ⟨x*y⁻¹,by simp [smul_eq_mul]⟩
    · intro _; rfl
  disjoint x := by
    refine ⟨{x},(isOpen_discrete _).mem_nhds (Set.mem_singleton x),?_⟩
    rintro g ⟨z,⟨y,hy,rfl⟩,h⟩
    simp only [Set.mem_singleton_iff] at hy h
    rw [hy] at h
    exact mul_right_cancel (show g*x=1*x by simpa only [smul_eq_mul,one_mul] using h)

def zeroStage : Stage G 0 where
  E := G
  B := PUnit.{u+1}
  topE := inferInstance
  topB := inferInstance
  nonemptyE := inferInstance
  nonemptyB := inferInstance
  sepE := realSeparated_of_tychonoff
  sepB := realSeparated_of_tychonoff
  cwE := inferInstance
  cwB := inferInstance
  action := inferInstance
  continuousAction := inferInstance
  orbits := ZeroOrbits
  orbitFinite := inferInstance
  equiv := zeroEquiv
  equiv_map := zeroEquiv_map
  dimE := discrete_dim
  dimB := discrete_dim
  finiteB m := by
    cases m with
    | zero =>
      change Finite (univ : Set PUnit.{u+1})
      infer_instance
    | succ m =>
      change Finite PEmpty
      infer_instance
  fill m hm a := by
    have hm : m = 0 := Nat.eq_zero_of_le_zero hm
    subst m
    obtain ⟨e,he⟩ := SphereTopology.fill_zero a
    exact ⟨e,he⟩
  p := pointCover
  covering := pointCover_quotient
end Zero

variable (hunif : ∀ S : Milnor.Shapes G, ∃ (T : Milnor.Shapes G) (hST : S ⊆ T),
      (Milnor.stageIncl G S T hST).Nullhomotopic)
variable {n : ℕ} (S : Stage G n)

def nextIndex : Type u := (exists_finite_brown_attachment S.equiv S.equiv_map hunif n S.fill S.dimE S.sepE).choose
instance : Finite (nextIndex hunif S) :=
  (exists_finite_brown_attachment S.equiv S.equiv_map hunif n S.fill S.dimE S.sepE).choose_spec.choose

def attaching : nextIndex hunif S → C(Cellular.Sphere (n+1),S.E) :=
  (exists_finite_brown_attachment S.equiv S.equiv_map hunif n S.fill S.dimE S.sepE).choose_spec.choose_spec.choose
lemma attaching_fill : LowFillable (Space (equivariantFamily (G := G) (attaching hunif S))) (n+1) :=
  (exists_finite_brown_attachment S.equiv S.equiv_map hunif n S.fill S.dimE S.sepE).choose_spec.choose_spec.choose_spec

def downstairs (i : nextIndex hunif S) : C(Cellular.Sphere (n+1),S.B) := S.p.comp (attaching hunif S i)

instance nextE_nonempty : Nonempty (Space (equivariantFamily (G := G) (attaching hunif S))) :=
  ⟨base _ (Classical.choice S.nonemptyE)⟩
instance nextB_nonempty : Nonempty (Space (downstairs hunif S)) := ⟨base _ (Classical.choice S.nonemptyB)⟩
instance nextE_t2 : T2Space (Space (equivariantFamily (G := G) (attaching hunif S))) :=
  (realSeparated _ S.sepE).t2Space
instance nextB_t2 : T2Space (Space (downstairs hunif S)) := (realSeparated _ S.sepB).t2Space

def nextStage : Stage G (n+1) where
  E := Space (equivariantFamily (G := G) (attaching hunif S))
  B := Space (downstairs hunif S)
  topE := inferInstance
  topB := inferInstance
  nonemptyE := inferInstance
  nonemptyB := inferInstance
  sepE := realSeparated _ S.sepE
  sepB := realSeparated _ S.sepB
  cwE := equivariantLayerCW S.equiv S.equiv_map (attaching hunif S) (fun m i => Nat.lt_succ_of_le (S.dimE m i))
  cwB := layerCW (downstairs hunif S) (fun m i => Nat.lt_succ_of_le (S.dimB m i))
  action := inferInstance
  continuousAction := inferInstance
  orbits := LayerOrbits (ι := S.orbits) (I := nextIndex hunif S) (n := n+1)
  orbitFinite m := by dsimp [LayerOrbits]; infer_instance
  equiv _ := Equiv.refl _
  equiv_map := equivariantLayerCW_smul S.equiv S.equiv_map (attaching hunif S) _
  dimE m i := Nat.le_of_lt_succ (equivariantLayerCW_dims S.equiv S.equiv_map (attaching hunif S) _ m i)
  dimB m i := Nat.le_of_lt_succ (layerCW_dimensions (downstairs hunif S) _ m i)
  finiteB := layerCW_finite_cells (downstairs hunif S) S.finiteB _
  fill := attaching_fill hunif S
  p := coverMap (attaching hunif S) S.p S.covering (downstairs hunif S) (fun _ _ => rfl)
  covering := coverMap_isQuotientCovering _ _ _ _ _
end

section
open Set Metric Topology Cellular Attachment
universe u
variable {G : Type u} [Group G]
variable (hunif : ∀ S : Milnor.Shapes G, ∃ (T : Milnor.Shapes G) (hST : S ⊆ T),
      (Milnor.stageIncl G S T hST).Nullhomotopic)
variable {n : ℕ} (S : Stage G n)

def nextInE : C(S.E,(nextStage hunif S).E) := ⟨base _,continuous_base _⟩
def nextInB : C(S.B,(nextStage hunif S).B) := ⟨base _,continuous_base _⟩
lemma nextInE_closed : IsClosedEmbedding (nextInE hunif S) := base_closedEmbedding _
lemma nextInB_closed : IsClosedEmbedding (nextInB hunif S) := base_closedEmbedding _
lemma nextInE_smul (g : G) (x : S.E) : nextInE hunif S (g • x) = g • nextInE hunif S x := rfl
lemma next_square (x : S.E) :
    (nextStage hunif S).p (nextInE hunif S x) = nextInB hunif S (S.p x) := rfl

def nextCellE (m : ℕ) : S.cwE.cell m → (nextStage hunif S).cwE.cell m :=
  layerOld S.equiv S.equiv_map (attaching hunif S) _ m
lemma nextCellE_injective (m : ℕ) : Function.Injective (nextCellE hunif S m) :=
  layerOld_injective _ _ _ _ m
lemma nextCellE_exhaustive (m : ℕ) (hm : m ≠ n+1) (i : (nextStage hunif S).cwE.cell m) :
    ∃ j,nextCellE hunif S m j = i := layerOld_exhaustive _ _ _ _ m hm i
lemma nextCellE_map (m : ℕ) (i : S.cwE.cell m) (x : Fin m → ℝ) :
    nextInE hunif S (S.cwE.map m i x) = (nextStage hunif S).cwE.map m (nextCellE hunif S m i) x :=
  (layerOld_map _ _ _ _ m i x).symm

def nextCellB (m : ℕ) : S.cwB.cell m → (nextStage hunif S).cwB.cell m := Sum.inl
lemma nextCellB_injective (m : ℕ) : Function.Injective (nextCellB hunif S m) := Sum.inl_injective
lemma nextCellB_exhaustive (m : ℕ) (hm : m ≠ n+1) (i : (nextStage hunif S).cwB.cell m) :
    ∃ j,nextCellB hunif S m j = i := by
  cases i with
  | inl i => exact ⟨i,rfl⟩
  | inr i => exact (hm i.down.1.down).elim
lemma nextCellB_map (m : ℕ) (i : S.cwB.cell m) (x : Fin m → ℝ) :
    nextInB hunif S (S.cwB.map m i x) = (nextStage hunif S).cwB.map m (nextCellB hunif S m i) x := rfl

lemma nextE_extendsReal (f : C(S.E,ℝ)) : ∃ F : C((nextStage hunif S).E,ℝ),
    ∀ x,F (nextInE hunif S x) = f x := exists_real_extension _ f
lemma nextB_extendsReal (f : C(S.B,ℝ)) : ∃ F : C((nextStage hunif S).B,ℝ),
    ∀ x,F (nextInB hunif S x) = f x := exists_real_extension _ f
lemma nextE_extendsSlice (U : Set S.E) (hU : IsOpen U)
    (hd : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) :
    ∃ V : Set (nextStage hunif S).E, IsOpen V ∧ (nextInE hunif S) ⁻¹' V = U ∧
      ∀ g : G,((g • ·) '' V ∩ V).Nonempty → g = 1 :=
  ⟨thickening _ U,thickening_isOpen _ hU,rfl,
    thickening_disjoint _ (equivariantFamily_smul (attaching hunif S)) hd⟩
end

open Set Metric Topology Cellular Attachment
universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (hunif : ∀ S : Milnor.Shapes G, ∃ (T : Milnor.Shapes G) (hST : S ⊆ T),
      (Milnor.stageIncl G S T hST).Nullhomotopic)

def stages : (n : ℕ) → Stage G n
  | 0 => zeroStage
  | n+1 => nextStage hunif (stages n)
abbrev E (n : ℕ) := (stages hunif n).E
abbrev B (n : ℕ) := (stages hunif n).B

def eStep (n : ℕ) : C(E hunif n,E hunif (n+1)) := nextInE hunif (stages hunif n)
def bStep (n : ℕ) : C(B hunif n,B hunif (n+1)) := nextInB hunif (stages hunif n)
abbrev eMap := Sequential.map (E hunif) (eStep hunif)
abbrev bMap := Sequential.map (B hunif) (bStep hunif)
lemma eMap_closed : ∀ i j h,IsClosedEmbedding (eMap hunif i j h) :=
  Sequential.map_closedEmbedding _ _ (fun n => nextInE_closed hunif (stages hunif n))
lemma bMap_closed : ∀ i j h,IsClosedEmbedding (bMap hunif i j h) :=
  Sequential.map_closedEmbedding _ _ (fun n => nextInB_closed hunif (stages hunif n))

instance : TopologicalTower.EquivariantSystem (G := G) (E hunif) (eMap hunif) where
  map_smul i j h g x := by
    induction j,h using Nat.le_induction with
    | base => simp only [eMap,Sequential.map_self,ContinuousMap.id_apply]
    | succ j h ih =>
      simp only [eMap,Sequential.map_succ _ _ i j h,ContinuousMap.comp_apply]
      change eStep hunif j (eMap hunif i j h (g • x)) = g • eStep hunif j (eMap hunif i j h x)
      rw [ih]
      exact nextInE_smul hunif (stages hunif j) g _

def eCells : Sequential.CellSteps (E hunif) (eStep hunif) where
  cell n := nextCellE hunif (stages hunif n)
  injective n := nextCellE_injective hunif (stages hunif n)
  dim n := (stages hunif n).dimE
  exhaustive n := nextCellE_exhaustive hunif (stages hunif n)
  compatibility n := nextCellE_map hunif (stages hunif n)
def bCells : Sequential.CellSteps (B hunif) (bStep hunif) where
  cell n := nextCellB hunif (stages hunif n)
  injective n := nextCellB_injective hunif (stages hunif n)
  dim n := (stages hunif n).dimB
  exhaustive n := nextCellB_exhaustive hunif (stages hunif n)
  compatibility n := nextCellB_map hunif (stages hunif n)

abbrev Total := TopologicalTower.Space (E hunif) (eMap hunif)
abbrev Base := TopologicalTower.Space (B hunif) (bMap hunif)
instance : Nonempty (Total hunif) := ⟨TopologicalTower.of (E hunif) (eMap hunif) 0 (1:G)⟩
instance : Nonempty (Base hunif) := ⟨TopologicalTower.of (B hunif) (bMap hunif) 0 PUnit.unit⟩

lemma e_extendsReal : TopologicalTower.ExtendsReals (E hunif) (eMap hunif) := by
  intro n f
  obtain ⟨extension, hextension⟩ := nextE_extendsReal hunif (stages hunif n) f
  refine ⟨extension, ?_⟩
  intro point
  rw [eMap, Sequential.map_step]
  exact hextension point
lemma b_extendsReal : TopologicalTower.ExtendsReals (B hunif) (bMap hunif) := by
  intro n f
  obtain ⟨extension, hextension⟩ := nextB_extendsReal hunif (stages hunif n) f
  refine ⟨extension, ?_⟩
  intro point
  rw [bMap, Sequential.map_step]
  exact hextension point
instance totalT2 : T2Space (Total hunif) :=
  TopologicalTower.t2Space _ _ (eMap_closed hunif) (e_extendsReal hunif) (fun n => (stages hunif n).sepE)
instance baseT2 : T2Space (Base hunif) :=
  TopologicalTower.t2Space _ _ (bMap_closed hunif) (b_extendsReal hunif) (fun n => (stages hunif n).sepB)
instance totalCW : CWComplex (univ : Set (Total hunif)) :=
  CellularTower.cwComplex _ _ (eMap_closed hunif) (Sequential.cellSystem _ _ (eCells hunif))
instance baseCW : CWComplex (univ : Set (Base hunif)) :=
  CellularTower.cwComplex _ _ (bMap_closed hunif) (Sequential.cellSystem _ _ (bCells hunif))
lemma base_finite (n : ℕ) : Finite ((baseCW hunif).cell n) :=
  (stages hunif n).finiteB n

lemma eventually_fills : TopologicalTower.EventuallyFills (E hunif) (eMap hunif) := by
  intro n k a
  let j := max n k
  obtain ⟨F,hF⟩ := (stages hunif j).fill n (le_max_left n k)
    ((eMap hunif k j (le_max_right n k)).comp a)
  exact ⟨j,le_max_right n k,F,hF⟩
instance totalContractible : ContractibleSpace (Total hunif) :=
  TopologicalTower.contractible _ _ (eMap_closed hunif) (eventually_fills hunif)

lemma e_extendsSlices : TopologicalTower.ExtendsSlices (G := G) (E hunif) (eMap hunif) := by
  intro n U
  obtain ⟨V,hV,hpre,hdis⟩ := nextE_extendsSlice hunif (stages hunif n) U.carrier U.isOpen U.disjoint
  refine ⟨⟨V,hV,hdis⟩,?_⟩
  rw [eMap, Sequential.map_step]
  exact hpre

def pStage (n : ℕ) : C(E hunif n,B hunif n) := (stages hunif n).p
lemma p_compat (i j : ℕ) (h : i ≤ j) (x : E hunif i) :
    pStage hunif j (eMap hunif i j h x) = bMap hunif i j h (pStage hunif i x) := by
  induction j,h using Nat.le_induction with
  | base => simp only [eMap,bMap,Sequential.map_self,ContinuousMap.id_apply]
  | succ j h ih =>
    simp only [eMap,bMap,Sequential.map_succ _ _ i j h,ContinuousMap.comp_apply]
    change pStage hunif (j+1) (eStep hunif j (eMap hunif i j h x)) = bStep hunif j (bMap hunif i j h (pStage hunif i x))
    exact (next_square hunif (stages hunif j) _).trans (congrArg (bStep hunif j) ih)

def pLimit : C(Total hunif,Base hunif) :=
  TopologicalTower.limitMap _ _ _ _ (pStage hunif) (p_compat hunif)
lemma pLimit_covering : IsQuotientCoveringMap (pLimit hunif) G :=
  TopologicalTower.limitMap_isQuotientCovering _ _ _ _ (pStage hunif) (p_compat hunif)
    (eMap_closed hunif) (bMap_closed hunif) (fun n => (stages hunif n).covering) (e_extendsSlices hunif)

instance baseConnected : ConnectedSpace (Base hunif) :=
  (pLimit_covering hunif).surjective.connectedSpace (pLimit hunif).continuous

include hunif in

theorem geometric_of_uniform : HasTypeFInfinity G := by
  refine ⟨Base hunif,inferInstance,inferInstance,inferInstance,baseCW hunif,base_finite hunif,?_,?_⟩
  · let e : Total hunif := Classical.choice inferInstance
    refine ⟨pLimit hunif e,⟨?_⟩⟩
    exact ((pLimit_covering hunif).fundamentalGroupEquiv ⟨e,rfl⟩).trans (MulEquiv.inv' G).symm
  · exact ⟨Total hunif,inferInstance,inferInstance,pLimit hunif,
      (pLimit_covering hunif).surjective,(pLimit_covering hunif).isCoveringMap⟩
end UniversalFInfinity.Brown

end

end OAI
