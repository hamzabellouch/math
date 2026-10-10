import OAI.Analysis.SegmentLenses.Subspaces

namespace OAI

/-!
# Hilbertian congruences and forest identifications
-/

noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace SegmentLenses

attribute [local instance] instDecidableEqForestVertex


section L2Congruence
open scoped ENNReal
variable {I : Type*} {E F : I → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, NormedSpace ℝ (F i)]


def l2Congr (e : ∀ i, E i ≃ₗᵢ[ℝ] F i) : L2Sum E ≃ₗᵢ[ℝ] L2Sum F where
  toFun x := ⟨fun i => e i (x i), x.property.mono' (fun i => (e i).norm_map (x i) |>.le)⟩
  invFun y := ⟨fun i => (e i).symm (y i), y.property.mono' (fun i => (e i).symm.norm_map (y i) |>.le)⟩
  left_inv x := by apply Subtype.ext; funext i; exact (e i).symm_apply_apply _
  right_inv y := by apply Subtype.ext; funext i; exact (e i).apply_symm_apply _
  map_add' x y := by apply Subtype.ext; funext i; exact (e i).map_add _ _
  map_smul' c x := by apply Subtype.ext; funext i; exact (e i).map_smul c _
  norm_map' x := by
    apply le_antisymm
    · exact lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) (fun i => (e i).norm_map (x i) |>.le)
    · exact lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) (fun i => (e i).norm_map (x i) |>.ge)

@[simp] theorem l2Congr_apply (e : ∀ i, E i ≃ₗᵢ[ℝ] F i) (x : L2Sum E) (i : I) :
    l2Congr e x i = e i (x i) := rfl

end L2Congruence

namespace SegmentEmbedding
variable {V W : Type*} [DecidableEq V] [DecidableEq W] [SegmentSystem V] [SegmentSystem W]



def testEquivOfSurjective (e : SegmentEmbedding (V := V) (W := W))
    (he : Function.Surjective e.toEmbedding) : Test V ≃ₗᵢ[ℝ] Test W :=
  LinearIsometryEquiv.ofSurjective e.testIsometry (fun u => ⟨e.testRestriction u,
    e.testMap_testRestriction u (fun w hw => False.elim (hw (he w)))⟩)

def primalEquivOfSurjective (e : SegmentEmbedding (V := V) (W := W))
    (he : Function.Surjective e.toEmbedding) : Primal V ≃ₗᵢ[ℝ] Primal W :=
  completionIsometry (e.testEquivOfSurjective he)

@[simp] theorem primalEquivOfSurjective_test (e : SegmentEmbedding (V := V) (W := W))
    (he : Function.Surjective e.toEmbedding) (u : Test V) :
    e.primalEquivOfSurjective he (u : Primal V) = (e.testMap u : Primal W) :=
  completionIsometry_coe _ _

end SegmentEmbedding

namespace ComponentPartition
open scoped Classical
variable {V I : Type*} [DecidableEq V] [decidableEqI : DecidableEq I] [PartialOrder V]
  [LocallyFiniteOrder V] [locallyFiniteOrderBotV : LocallyFiniteOrderBot V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V] (p : ComponentPartition (V := V) (I := I))

abbrev BlockVertex (i : I) := Region.Vertex (fun v => p.index v = i)
local instance (i : I) : DecidableEq (BlockVertex p i) := Classical.decEq _

def regionEmbedding (i : I) : SegmentEmbedding (V := BlockVertex p i) (W := V) :=
  Region.embedding (fun _a _b _v ha _hb hav _hvb => (p.comparable hav).symm.trans ha)

@[simp] theorem regionEmbedding_range (i : I) :
    Set.range (regionEmbedding p i).toEmbedding = {v | p.index v = i} := by
  have _ := decidableEqI
  have _ := locallyFiniteOrderBotV
  exact
    Region.range_inclusion



def regionTestMap (i : I) : Test (BlockVertex p i) →ₗᵢ[ℝ] blockTests (p := p) i where
  toLinearMap := (regionEmbedding p i).testMap.codRestrict (blockTests (p := p) i) (by
    intro u
    apply mem_blockTests.mpr
    apply Finsupp.ext
    intro v
    change (blockTest (p := p) i ((regionEmbedding p i).testMap u)).coeff v =
      ((regionEmbedding p i).testMap u).coeff v
    rw [blockTest_apply]
    split_ifs with hv
    · rfl
    · symm
      apply Finsupp.embDomain_of_notMem_range
      simpa only [regionEmbedding_range, Set.mem_ofPred_eq] using hv)
  norm_map' u := (regionEmbedding p i).norm_testMap u

theorem regionTestMap_surjective (i : I) : Function.Surjective (regionTestMap p i) := by
  intro u
  refine ⟨(regionEmbedding p i).testRestriction u.val, Subtype.ext ?_⟩
  apply (regionEmbedding p i).testMap_testRestriction
  intro v hv
  have hn : p.index v ≠ i := by simpa only [regionEmbedding_range, Set.mem_ofPred_eq] using hv
  have h := congrArg (fun u : Test V => u.coeff v) (mem_blockTests.mp u.property)
  rw [blockTest_apply, ite_eq_right hn] at h
  exact h.symm

def regionTestEquiv (i : I) : Test (BlockVertex p i) ≃ₗᵢ[ℝ] blockTests (p := p) i :=
  LinearIsometryEquiv.ofSurjective (regionTestMap p i) (regionTestMap_surjective p i)

def regionPrimalEquiv (i : I) : Primal (BlockVertex p i) ≃ₗᵢ[ℝ] BlockPrimal (p := p) i :=
  completionIsometry (regionTestEquiv p i)

@[simp] theorem regionPrimalEquiv_test (i : I) (u : Test (BlockVertex p i)) :
    regionPrimalEquiv p i (u : Primal (BlockVertex p i)) =
      ((regionTestMap p i u) : BlockPrimal (p := p) i) :=
  completionIsometry_coe _ _


def regionL2Equiv : Primal V ≃ₗᵢ[ℝ] L2Sum (fun i => Primal (BlockVertex p i)) :=
  (l2Equiv (p := p)).trans (l2Congr (fun i => (regionPrimalEquiv p i).symm))



def regionDualL2Equiv : FullDual V ≃ₗᵢ[ℝ] L2Sum (fun i => FullDual (BlockVertex p i)) :=
  (dualTransport (regionL2Equiv p)).trans
    (l2DualEquiv (fun i => Primal (BlockVertex p i))).symm

end ComponentPartition



namespace SingleTree

def Vertex (h : ℕ) := Region.Vertex (fun w : InfiniteVertex => w.length ≤ h)
instance (h : ℕ) : PartialOrder (Vertex h) := inferInstanceAs (PartialOrder (Region.Vertex _))
instance (h : ℕ) : TreeOrder (Vertex h) := inferInstanceAs (TreeOrder (Region.Vertex _))
instance (h : ℕ) : SegmentSystem (Vertex h) := inferInstanceAs (SegmentSystem (Region.Vertex _))
instance (h : ℕ) : IntervalSegments (Vertex h) := inferInstanceAs (IntervalSegments (Region.Vertex _))
instance (h : ℕ) : LocallyFiniteOrder (Vertex h) := inferInstanceAs (LocallyFiniteOrder (Region.Vertex _))
instance (h : ℕ) : LocallyFiniteOrderBot (Vertex h) := inferInstanceAs (LocallyFiniteOrderBot (Region.Vertex _))
instance (h : ℕ) : Countable (Vertex h) := inferInstanceAs (Countable (Region.Vertex _))
local instance (h : ℕ) : DecidableEq (Vertex h) := Classical.decEq _


abbrev J (h : ℕ) := Primal (Vertex h)
abbrev X (h : ℕ) := FullDual (Vertex h)

variable {I : Type*} [decidableEqI : DecidableEq I] {height : I → ℕ}
local instance : DecidableEq (IndexedForest.Vertex height) := Classical.decEq _

def componentOrderEmbedding (i : I) : Vertex (height i) ↪o IndexedForest.Vertex height where
  toFun w := ⟨(i,w.val),w.property⟩
  inj' := by intro v w h; exact Subtype.ext (congrArg (fun u : IndexedForest.Vertex height => u.val.2) h)
  map_rel_iff' := by intro v w; change (i=i ∧ v.val.IsPrefix w.val) ↔ v.val.IsPrefix w.val; simp

@[simp] theorem componentEmbedding_range (i : I) :
    Set.range (componentOrderEmbedding (height := height) i) = {v | v.val.1 = i} := by
  have _ := decidableEqI
  ext v
  constructor
  · rintro ⟨w,rfl⟩; rfl
  · intro hv
    change v.val.1 = i at hv
    refine ⟨⟨v.val.2,?_⟩,?_⟩
    · simpa only [← hv] using v.property
    · exact Subtype.ext (Prod.ext hv.symm rfl)

def componentEmbedding (i : I) :
    SegmentEmbedding (V := Vertex (height i)) (W := IndexedForest.Vertex height) :=
  convexSegmentEmbedding (componentOrderEmbedding i) (by
    intro a b v ha hb hav hvb
    rw [componentEmbedding_range] at ha hb ⊢
    exact hav.1.symm.trans ha)

@[simp] theorem componentEmbedding_apply (i : I) (w : Vertex (height i)) :
    (componentEmbedding (height := height) i).toEmbedding w = ⟨(i,w.val),w.property⟩ := rfl

def componentTestMap (i : I) : Test (Vertex (height i)) →ₗᵢ[ℝ] IndexedForest.heightTests (height := height) i where
  toLinearMap := (componentEmbedding i).testMap.codRestrict (IndexedForest.heightTests i) (by
    intro u
    apply IndexedForest.mem_heightTests.mpr
    apply Finsupp.ext
    intro v
    change (IndexedForest.heightTest i ((componentEmbedding i).testMap u)).coeff v =
      ((componentEmbedding i).testMap u).coeff v
    rw [IndexedForest.heightTest_apply]
    split_ifs with hv
    · rfl
    · symm
      apply Finsupp.embDomain_of_notMem_range
      change v ∉ Set.range (componentOrderEmbedding i)
      simpa only [componentEmbedding_range,Set.mem_ofPred_eq] using hv)
  norm_map' u := (componentEmbedding i).norm_testMap u

theorem componentTestMap_surjective (i : I) : Function.Surjective (componentTestMap (height := height) i) := by
  intro u
  refine ⟨(componentEmbedding i).testRestriction u.val, Subtype.ext ?_⟩
  apply (componentEmbedding i).testMap_testRestriction
  intro v hv
  have hn : v.val.1 ≠ i := by
    change v ∉ Set.range (componentOrderEmbedding i) at hv
    simpa only [componentEmbedding_range,Set.mem_ofPred_eq] using hv
  have he := congrArg (fun k : Test (IndexedForest.Vertex height) => k.coeff v)
    (IndexedForest.mem_heightTests.mp u.property)
  rw [IndexedForest.heightTest_apply,ite_eq_right hn] at he
  exact he.symm

def componentTestEquiv (i : I) : Test (Vertex (height i)) ≃ₗᵢ[ℝ] IndexedForest.heightTests (height := height) i :=
  LinearIsometryEquiv.ofSurjective (componentTestMap i) (componentTestMap_surjective i)



def componentPrimalEquiv (i : I) : J (height i) ≃ₗᵢ[ℝ] IndexedForest.HeightPrimal (height := height) i :=
  completionIsometry (componentTestEquiv i)

@[simp] theorem componentPrimalEquiv_test (i : I) (u : Test (Vertex (height i))) :
    componentPrimalEquiv (height := height) i (u : J (height i)) =
      ((componentTestMap i u) : IndexedForest.HeightPrimal (height := height) i) :=
  completionIsometry_coe _ _

end SingleTree

namespace IndexedForest
variable {I : Type*} [DecidableEq I] {height : I → ℕ}
local instance : DecidableEq (Vertex height) := Classical.decEq _
local instance : ∀ i, NormedAddCommGroup (HeightPrimal (height := height) i) := fun _i => inferInstance
local instance : ∀ i, NormedSpace ℝ (HeightPrimal (height := height) i) := fun _i => inferInstance


def singleTreeL2Equiv : J height ≃ₗᵢ[ℝ] L2Sum (fun i => SingleTree.J (height i)) :=
  (forestL2Equiv (height := height)).trans
    (l2Congr (fun i => (SingleTree.componentPrimalEquiv (height := height) i).symm))


def singleTreeDualL2Equiv : X height ≃ₗᵢ[ℝ] L2Sum (fun i => SingleTree.X (height i)) :=
  (dualL2Equiv (height := height)).trans
    (l2Congr (fun i => dualTransport (SingleTree.componentPrimalEquiv (height := height) i).symm))


@[simp] theorem singleTreeDualL2Equiv_on_test (f : X height) (i : I)
    (u : Test (SingleTree.Vertex (height i))) :
    singleTreeDualL2Equiv f i (u : SingleTree.J (height i)) =
      f ((SingleTree.componentEmbedding (height := height) i).testMap u : J height) := by
  change dualL2Equiv f i (SingleTree.componentPrimalEquiv i (u : SingleTree.J (height i))) = _
  rw [SingleTree.componentPrimalEquiv_test,dualL2Equiv_on_test]
  rfl

end IndexedForest



end SegmentLenses

end

end OAI
