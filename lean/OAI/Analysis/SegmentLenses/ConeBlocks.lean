import OAI.Analysis.SegmentLenses.Gates

namespace OAI

/-!
# Component and cone decompositions
-/

noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace SegmentLenses

attribute [local instance] instDecidableEqForestVertex


namespace SegmentEmbedding
variable {V W : Type*} [DecidableEq V] [DecidableEq W] [SegmentSystem V] [SegmentSystem W]

theorem norm_testL2_map (e : SegmentEmbedding (V := V) (W := W)) (u : Test V) :
    ‖testL2 (e.testMap u)‖ = ‖testL2 u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_testL2_sq,norm_testL2_sq]
  change (∑ w ∈ (u.coeff.embDomain e.toEmbedding).support, (e.testMap u).coeff w ^ 2) = _
  rw [Finsupp.support_embDomain,Finset.sum_map]
  simp only [e.testMap_apply]

end SegmentEmbedding

namespace SingleTree
local instance (h : ℕ) : DecidableEq (Vertex h) := Classical.decEq _


theorem component_estimate (h : ℕ) (u : Test (Vertex h)) :
    ‖testL2 u‖ ≤ ‖u‖ ∧ ‖u‖ ≤ Real.sqrt (h+1) * ‖testL2 u‖ := by
  classical
  refine ⟨norm_testL2_le u,?_⟩
  let e := componentEmbedding (height := fun _ : Unit => h) ()
  have hs := IndexedForest.height_hilbert_upper (height := fun _ : Unit => h) () (e.testMap u)
    (IndexedForest.mem_heightTests.mp (componentTestMap (height := fun _ : Unit => h) () u).property)
  rw [← norm_testL2_sq, e.norm_testMap,e.norm_testL2_map] at hs
  have hr : Real.sqrt (h+1) ^ 2 = (h+1 : ℝ) := Real.sq_sqrt (by positivity)
  have hn : 0 ≤ Real.sqrt (h+1) * ‖testL2 u‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) hn).mp
  rw [mul_pow,hr]
  exact hs


theorem levels_component_estimate {n : ℕ} (hn : 1 ≤ n) (u : Test (Vertex (n-1))) :
    ‖testL2 u‖ ≤ ‖u‖ ∧ ‖u‖ ≤ Real.sqrt n * ‖testL2 u‖ := by
  have h := component_estimate (n-1) u
  have he : (n-1 : ℕ) + 1 = n := Nat.sub_add_cancel hn
  have her : (↑(n-1) + 1 : ℝ) = n := by exact_mod_cast he
  simpa only [her] using h



def extensionSteps {h : ℕ} (v : Vertex h) : ℕ := v.val.length

def root (h : ℕ) : Vertex h := ⟨[],by simp⟩

def zeroLeaf (h : ℕ) : Vertex h := ⟨List.replicate h 0,by simp⟩

@[simp] theorem root_steps (h : ℕ) : extensionSteps (root h) = 0 := rfl
@[simp] theorem leaf_steps (h : ℕ) : extensionSteps (zeroLeaf h) = h := List.length_replicate

theorem child_steps {h : ℕ} (v w : Vertex h) (n : ℕ) (hw : w.val = v.val ++ [n]) :
    extensionSteps w = extensionSteps v + 1 := by simp [extensionSteps,hw]

theorem n_levels_path {n : ℕ} (hn : 1 ≤ n) :
    extensionSteps (zeroLeaf (n-1)) = n-1 ∧
      extensionSteps (zeroLeaf (n-1)) + 1 = n := by
  rw [leaf_steps]
  exact ⟨rfl,Nat.sub_add_cancel hn⟩

end SingleTree


namespace ComponentPartition
open scoped Classical
variable {V I : Type*} [DecidableEq V] [DecidableEq I] [PartialOrder V]
  [LocallyFiniteOrder V] [LocallyFiniteOrderBot V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V] (p : ComponentPartition (V := V) (I := I))
local instance : ∀ i, NormedAddCommGroup (BlockPrimal (p := p) i) := fun _i => inferInstance
local instance : ∀ i, NormedSpace ℝ (BlockPrimal (p := p) i) := fun _i => inferInstance

@[simp] theorem regionL2Equiv_regionMap (i : I) (u : Primal (BlockVertex p i)) :
    regionL2Equiv p ((regionEmbedding p i).primalMap u) = lp.single 2 i u := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq ((regionL2Equiv p).continuous.comp (regionEmbedding p i).primalMap.continuous)
      (lp.singleContinuousLinearMap ℝ (fun j => Primal (BlockVertex p j)) 2 i).continuous) ?_
  intro u
  rw [SegmentEmbedding.primalMap_test]
  change l2Congr (fun j => (regionPrimalEquiv p j).symm)
    (l2Equiv (p := p) (((regionTestMap p i u).val) : Primal V)) = _
  rw [l2Equiv_test,testBlocks_of_height]
  apply Subtype.ext
  funext j
  rw [l2Congr_apply]
  by_cases hji : j=i
  · subst j
    rw [lp.single_apply_self,lp.single_apply_self,← regionPrimalEquiv_test,
      LinearIsometryEquiv.symm_apply_apply]
  · rw [lp.single_apply_ne _ _ _ hji,lp.single_apply_ne _ _ _ hji,map_zero]

@[simp] theorem regionDualL2Equiv_apply (z : FullDual V) (i : I) (u : Primal (BlockVertex p i)) :
    regionDualL2Equiv p z i u = z ((regionEmbedding p i).primalMap u) := by
  change ((l2DualEquiv (fun j => Primal (BlockVertex p j))).symm
    (dualTransport (regionL2Equiv p) z)) i u = _
  rw [l2DualEquiv_symm_apply]
  change z ((regionL2Equiv p).symm (lp.single 2 i u)) = _
  rw [← regionL2Equiv_regionMap p i u,LinearIsometryEquiv.symm_apply_apply]

end ComponentPartition

section ConeDecomposition
open scoped Classical ENNReal
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]


abbrev ConeVertex (g : V) := Region.Vertex (fun v => g ≤ v)

def coneEmbedding (g : V) : SegmentEmbedding (V := ConeVertex g) (W := V) :=
  Region.embedding (fun _a _b _v ha _hb hav _hvb => ha.trans hav)


def coneBlockOrderEmbedding (H : Finset V) (hH : Ancestral (· ≤ ·) H) (g : {g // Gate H g}) :
    ConeVertex g.val ↪o ComponentPartition.BlockVertex (exteriorPartition H) g where
  toFun v := ⟨⟨v.val,fun hv => g.property.1 (hH hv v.property)⟩,
    (exteriorGate_eq_iff H _ g).mpr v.property⟩
  inj' := by
    intro v w he
    exact Subtype.ext (congrArg (fun q : ComponentPartition.BlockVertex (exteriorPartition H) g => q.val.val) he)
  map_rel_iff' := Iff.rfl

theorem coneBlockOrderEmbedding_surjective (H : Finset V) (hH : Ancestral (· ≤ ·) H) (g : {g // Gate H g}) :
    Function.Surjective (coneBlockOrderEmbedding H hH g) := by
  intro v
  refine ⟨⟨v.val.val,(exteriorGate_eq_iff H v.val g).mp v.property⟩,?_⟩
  rfl

def coneBlockEmbedding (H : Finset V) (hH : Ancestral (· ≤ ·) H) (g : {g // Gate H g}) :
    SegmentEmbedding (V := ConeVertex g.val)
      (W := ComponentPartition.BlockVertex (exteriorPartition H) g) :=
  convexSegmentEmbedding (coneBlockOrderEmbedding H hH g)
    (fun {_ _ w} _ _ _ _ => coneBlockOrderEmbedding_surjective H hH g w)

def coneBlockEquiv (H : Finset V) (hH : Ancestral (· ≤ ·) H) (g : {g // Gate H g}) :
    Primal (ConeVertex g.val) ≃ₗᵢ[ℝ] Primal (ComponentPartition.BlockVertex (exteriorPartition H) g) :=
  (coneBlockEmbedding H hH g).primalEquivOfSurjective (coneBlockOrderEmbedding_surjective H hH g)



def exteriorConeL2Equiv (H : Finset V) (hH : Ancestral (· ≤ ·) H) :
    Primal (ExteriorVertex H) ≃ₗᵢ[ℝ] L2Sum (fun g : {g // Gate H g} => Primal (ConeVertex g.val)) :=
  (ComponentPartition.regionL2Equiv (exteriorPartition H)).trans
    (l2Congr (fun g => (coneBlockEquiv H hH g).symm))

def exteriorConeDualL2Equiv (H : Finset V) (hH : Ancestral (· ≤ ·) H) :
    FullDual (ExteriorVertex H) ≃ₗᵢ[ℝ] L2Sum (fun g : {g // Gate H g} => FullDual (ConeVertex g.val)) :=
  (ComponentPartition.regionDualL2Equiv (exteriorPartition H)).trans
    (l2Congr (fun g => dualTransport (coneBlockEquiv H hH g).symm))

end ConeDecomposition



end SegmentLenses

end

end OAI
