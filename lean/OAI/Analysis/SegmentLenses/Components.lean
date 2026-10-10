import OAI.Analysis.SegmentLenses.EndpointBounds

namespace OAI

/-!
# Component partitions and completion decompositions
-/

noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace SegmentLenses

attribute [local instance] instDecidableEqForestVertex


section ComponentPartitions
variable {V I : Type*} [PartialOrder V]



structure ComponentPartition where
  index : V → I
  comparable : ∀ {v w : V}, v ≤ w → index v = index w

end ComponentPartitions

namespace ComponentPartition
open scoped Classical
variable {V I : Type*} [decidableEqV : DecidableEq V] [decidableEqI : DecidableEq I] [PartialOrder V]
  [locallyFiniteOrderV : LocallyFiniteOrder V] [locallyFiniteOrderBotV : LocallyFiniteOrderBot V] [treeOrderV : TreeOrder V]
  [segmentSystemV : SegmentSystem V] [intervalSegmentsV : IntervalSegments V] {p : ComponentPartition (V := V) (I := I)}

section Blocks


def blockTest (h : I) : Test V →ₗ[ℝ] Test V where
  toFun u := Test.ofFinsupp (u.coeff.filter (fun v => p.index v = h))
  map_add' _u _v := Finsupp.filter_add
  map_smul' _c _u := Finsupp.filter_smul

@[simp] theorem blockTest_apply (h : I) (u : Test V) (v : V) :
    ((blockTest (p := p)) h u).coeff v = if p.index v = h then u.coeff v else 0 := by
  have _ := decidableEqV
  have _ := locallyFiniteOrderV
  have _ := locallyFiniteOrderBotV
  have _ := treeOrderV
  have _ := segmentSystemV
  have _ := intervalSegmentsV
  exact Finsupp.filter_apply _ _ _

theorem norm_blockTest_le (h : I) (u : Test V) : ‖(blockTest (p := p)) h u‖ ≤ ‖u‖ := by
  have _ := locallyFiniteOrderBotV
  classical
  apply norm_filter_le
  intro a b v ha hb hav hvb
  exact (p.comparable hav).symm.trans ha


theorem segment_same_index {S : Finset V} (hS : SegmentSystem.isSegment S)
    {v w : V} (hv : v ∈ S) (hw : w ∈ S) : p.index v = p.index w := by
  have _ := decidableEqV
  have _ := decidableEqI
  have _ := locallyFiniteOrderV
  have _ := locallyFiniteOrderBotV
  have _ := treeOrderV
  obtain ⟨a, b, hab, hs⟩ := (IntervalSegments.iff_interval _).mp hS
  exact (p.comparable ((hs v).mp hv).1).symm.trans (p.comparable ((hs w).mp hw).1)

def familyAtBlock (F : SegmentFamily V) (h : I) :
    SegmentFamily V where
  sets := F.sets.filter (fun S => ∀ v ∈ S, p.index v = h)
  segment S hS := F.segment S (Finset.mem_filter.mp hS).1
  disjoint := by
    intro S hS T hT hne
    exact F.disjoint (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hT).1 hne

theorem atBlock_seminorm (F : SegmentFamily V) (h : I) (u : Test V) :
    ((familyAtBlock (p := p)) F h).seminorm u.coeff = F.seminorm ((blockTest (p := p)) h u).coeff := by
  have he : ((familyAtBlock (p := p)) F h).seminorm u.coeff ^ 2 = F.seminorm ((blockTest (p := p)) h u).coeff ^ 2 := by
    rw [SegmentFamily.seminorm_sq, SegmentFamily.seminorm_sq]
    rw [Finset.sum_coe_sort ((familyAtBlock (p := p)) F h).sets (fun S => (∑ v ∈ S, u.coeff v) ^ 2),
      Finset.sum_coe_sort F.sets (fun S => (∑ v ∈ S, ((blockTest (p := p)) h u).coeff v) ^ 2)]
    change (∑ S ∈ F.sets.filter _, _) = ∑ S ∈ F.sets, _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S hS
    split_ifs with hc
    · congr 1
      apply Finset.sum_congr rfl
      intro v hv
      simp only [(blockTest_apply (p := p)), hc v hv, ite_true]
    · have hz : ∀ v ∈ S, p.index v ≠ h := by
        intro v hv heq
        apply hc
        intro w hw
        exact ((segment_same_index (p := p)) (F.segment S hS) hw hv).trans heq
      simp only [(blockTest_apply (p := p))]
      simp only [Finset.sum_eq_zero (fun v hv => ite_eq_right (hz v hv)), zero_pow (by decide : 2 ≠ 0)]
  nlinarith [apply_nonneg ((familyAtBlock (p := p)) F h).seminorm u.coeff,
    apply_nonneg F.seminorm ((blockTest (p := p)) h u).coeff]

end Blocks

section NormDecomposition

def testIndices (u : Test V) : Finset I := u.coeff.support.image p.index

theorem blockTest_eq_zero {u : Test V} {h : I} (hh : h ∉ (testIndices (p := p)) u) :
    (blockTest (p := p)) h u = 0 := by
  apply Finsupp.ext
  intro v
  change ((blockTest (p := p)) h u).coeff v = 0
  rw [(blockTest_apply (p := p))]
  split_ifs with hv
  · apply Finsupp.notMem_support_iff.mp
    intro hs
    exact hh (Finset.mem_image.mpr ⟨v, hs, hv⟩)
  · rfl

theorem blockTest_idem (h : I) (u : Test V) :
    (blockTest (p := p)) h ((blockTest (p := p)) h u) = (blockTest (p := p)) h u := by
  apply Finsupp.ext
  intro v
  change ((blockTest (p := p)) h ((blockTest (p := p)) h u)).coeff v = ((blockTest (p := p)) h u).coeff v
  by_cases hv : p.index v = h <;> simp [(blockTest_apply (p := p)), hv]

theorem blockTest_ne {h k : I} (hk : h ≠ k) (u : Test V) :
    (blockTest (p := p)) h ((blockTest (p := p)) k u) = 0 := by
  apply Finsupp.ext
  intro v
  change ((blockTest (p := p)) h ((blockTest (p := p)) k u)).coeff v = 0
  simp only [(blockTest_apply (p := p))]
  split_ifs with hv hv'
  · exact (hk (hv.symm.trans hv')).elim
  · rfl
  · rfl


theorem norm_sq_decomposition (u : Test V) :
    ‖u‖ ^ 2 = ∑ h ∈ (testIndices (p := p)) u, ‖(blockTest (p := p)) h u‖ ^ 2 := by
  classical
  apply le_antisymm
  · obtain ⟨F, hF⟩ := exists_norming_family u
    have he : F.seminorm u.coeff ^ 2 =
        ∑ h ∈ (testIndices (p := p)) u, F.seminorm ((blockTest (p := p)) h u).coeff ^ 2 := by
      simp_rw [F.seminorm_sq]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S hS
      obtain ⟨a, b, hab, hs⟩ := (IntervalSegments.iff_interval _).mp (F.segment S.val S.property)
      have hc : ∀ v ∈ S.val, p.index v = p.index a := fun v hv => (p.comparable ((hs v).mp hv).1).symm
      have hv : ∀ h, (∑ v ∈ S.val, ((blockTest (p := p)) h u).coeff v) ^ 2 =
          if h = p.index a then (∑ v ∈ S.val, u.coeff v) ^ 2 else 0 := by
        intro h
        by_cases hh : h = p.index a
        · subst h
          simp only [(blockTest_apply (p := p)), Finset.sum_congr rfl (fun v hv => ite_eq_left (hc v hv)), ite_true]
        · have hn : ∀ v ∈ S.val, p.index v ≠ h := fun v hv he => hh (he.symm.trans (hc v hv))
          simp only [(blockTest_apply (p := p)), Finset.sum_congr rfl (fun v hv => ite_eq_right (hn v hv)), Finset.sum_const_zero,
            zero_pow (by decide : 2 ≠ 0), ite_eq_right hh]
      simp_rw [hv]
      by_cases ha : p.index a ∈ (testIndices (p := p)) u
      · simp only [Finset.sum_ite_eq', ite_eq_left ha]
      · have hz : ∑ v ∈ S.val, u.coeff v = 0 := by
          apply Finset.sum_eq_zero
          intro v hv
          apply Finsupp.notMem_support_iff.mp
          intro hvs
          exact ha (Finset.mem_image.mpr ⟨v, hvs, hc v hv⟩)
        simp [hz]
    rw [← hF, he]
    exact Finset.sum_le_sum (fun h _ => sq_le_sq₀ (apply_nonneg _ _) (norm_nonneg _) |>.mpr
      (le_segmentSeminorm _ _))
  · have hex : ∀ h : (testIndices (p := p)) u, ∃ F : SegmentFamily V,
        F.seminorm ((blockTest (p := p)) h.val u).coeff = ‖(blockTest (p := p)) h.val u‖ :=
      fun h => exists_norming_family _
    choose F hF using hex
    let G : (testIndices (p := p)) u → SegmentFamily V := fun h => (familyAtBlock (p := p)) (F h) h.val
    have hn : ∀ h, (G h).seminorm u.coeff = ‖(blockTest (p := p)) h.val u‖ := by
      intro h
      exact ((atBlock_seminorm (p := p)) (F h) h.val u).trans (hF h)
    let pieces : (h : (testIndices (p := p)) u) × (G h).sets → Finset V := fun j => j.2.val
    have hseg : ∀ j, pieces j = ∅ ∨ SegmentSystem.isSegment (pieces j) := fun j =>
      Or.inr ((G j.1).segment _ j.2.property)
    have hd : Pairwise fun i j => Disjoint (pieces i) (pieces j) := by
      intro i j hij
      by_cases hh : i.1 = j.1
      · rcases i with ⟨i, S⟩
        rcases j with ⟨j, T⟩
        dsimp at hh
        subst j
        exact (G i).disjoint S.property T.property (fun he => hij (by cases Subtype.ext he; rfl))
      · apply Finset.disjoint_left.mpr
        intro v hv hw
        have hvh := (Finset.mem_filter.mp i.2.property).2 v hv
        have hwh := (Finset.mem_filter.mp j.2.property).2 v hw
        exact hh (Subtype.ext (hvh.symm.trans hwh))
    have hb := indexed_test_bound u.coeff pieces hseg hd
    change (∑ j, (∑ v ∈ pieces j, u.coeff v) ^ 2) ≤ ‖u‖ ^ 2 at hb
    rw [Fintype.sum_sigma] at hb
    have he : (∑ h : (testIndices (p := p)) u, ∑ S : (G h).sets, (∑ v ∈ S.val, u.coeff v) ^ 2) =
        ∑ h ∈ (testIndices (p := p)) u, ‖(blockTest (p := p)) h u‖ ^ 2 := by
      rw [← Finset.sum_coe_sort ((testIndices (p := p)) u) (fun h => ‖(blockTest (p := p)) h u‖ ^ 2)]
      apply Finset.sum_congr rfl
      intro h hh
      rw [← (G h).seminorm_sq, hn]
    exact he ▸ hb

end NormDecomposition

def blockTests (h : I) : Submodule ℝ (Test V) := LinearMap.range ((blockTest (p := p)) h)

theorem mem_blockTests {h : I} {u : Test V} :
    u ∈ (blockTests (p := p)) h ↔ (blockTest (p := p)) h u = u := by
  constructor
  · rintro ⟨v, rfl⟩
    exact (blockTest_idem (p := p)) h v
  · intro hu
    exact ⟨u, hu⟩

abbrev BlockPrimal (h : I) := UniformSpace.Completion ((blockTests (p := p)) h)

section CompletionIdentification

local instance heightPrimalFamilyNormed : ∀ h, NormedAddCommGroup ((BlockPrimal (p := p)) h) := fun _h => inferInstance
local instance blockPrimalFamilySpace : ∀ h, NormedSpace ℝ ((BlockPrimal (p := p)) h) := fun _h => inferInstance
local instance : Module ℝ (Primal V) := (inferInstance : NormedSpace ℝ (Primal V)).toModule
local instance : Module ℝ (L2Sum (BlockPrimal (p := p))) := (inferInstance : NormedSpace ℝ (L2Sum (BlockPrimal (p := p)))).toModule
local instance : AddCommMonoid (L2Sum (BlockPrimal (p := p))) :=
  (inferInstance : NormedAddCommGroup (L2Sum (BlockPrimal (p := p)))).toAddCommMonoid


def completedBlockTest (h : I) : Test V →ₗ[ℝ] (BlockPrimal (p := p)) h :=
  (UniformSpace.Completion.toComplL : (blockTests (p := p)) h →L[ℝ] (BlockPrimal (p := p)) h).toLinearMap.comp
    ((blockTest (p := p)) h).rangeRestrict

@[simp] theorem norm_completedBlockTest (h : I) (u : Test V) :
    ‖(completedBlockTest (p := p)) h u‖ = ‖(blockTest (p := p)) h u‖ := by
  have _ := decidableEqV
  have _ := locallyFiniteOrderV
  have _ := locallyFiniteOrderBotV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  exact UniformSpace.Completion.norm_coe _

theorem completedBlockTest_zero {h : I} {u : Test V} (hz : (blockTest (p := p)) h u = 0) :
    (completedBlockTest (p := p)) h u = 0 := by
  apply norm_eq_zero.mp
  exact ((norm_completedBlockTest (p := p)) h u).trans (by rw [hz, norm_zero])

def blockVector (u : Test V) : L2Sum (BlockPrimal (p := p)) :=
  ∑ h ∈ (testIndices (p := p)) u, lp.single 2 h ((completedBlockTest (p := p)) h u)

@[simp] theorem blockVector_apply (u : Test V) (h : I) :
    (blockVector (p := p)) u h = (completedBlockTest (p := p)) h u := by
  classical
  simp only [blockVector, lp.coeFn_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single h]
  · exact lp.single_apply_self _ _ _
  · intro k hk hkh
    exact lp.single_apply_ne _ _ _ hkh.symm
  · intro hh
    simp only [(completedBlockTest_zero (p := p)) ((blockTest_eq_zero (p := p)) hh), lp.single_zero, lp.coeFn_zero, Pi.zero_apply]

def testBlocks : Test V →ₗ[ℝ] L2Sum (BlockPrimal (p := p)) where
  toFun := (blockVector (p := p))
  map_add' u v := by
    apply Subtype.ext
    funext h
    simp only [(blockVector_apply (p := p)), lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' c u := by
    apply Subtype.ext
    funext h
    simp only [(blockVector_apply (p := p)), lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply]

@[simp] theorem testBlocks_apply (u : Test V) (h : I) :
    (testBlocks (p := p)) u h = (completedBlockTest (p := p)) h u := (blockVector_apply (p := p)) u h

theorem norm_testBlocks (u : Test V) : ‖(testBlocks (p := p)) u‖ = ‖u‖ := by
  have he : ‖(testBlocks (p := p)) u‖ ^ 2 = ‖u‖ ^ 2 := by
    change ‖∑ h ∈ (testIndices (p := p)) u, lp.single 2 h ((completedBlockTest (p := p)) h u)‖ ^ 2 = _
    rw [l2_norm_sum_single_sq, (norm_sq_decomposition (p := p))]
    simp only [(norm_completedBlockTest (p := p))]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he



theorem testBlocks_of_height (h : I) (u : (blockTests (p := p)) h) :
    (testBlocks (p := p)) u.val = lp.single 2 h (u : (BlockPrimal (p := p)) h) := by
  classical
  apply Subtype.ext
  funext k
  rw [(testBlocks_apply (p := p))]
  by_cases hk : k = h
  · subst k
    rw [lp.single_apply_self]
    change ((⟨(blockTest (p := p)) h u.val, _⟩ : (blockTests (p := p)) h) : (BlockPrimal (p := p)) h) = _
    congr 1
    exact Subtype.ext ((mem_blockTests (p := p)).mp u.property)
  · rw [lp.single_apply_ne _ _ _ hk]
    apply (completedBlockTest_zero (p := p))
    rw [← (mem_blockTests (p := p)).mp u.property]
    exact (blockTest_ne (p := p)) hk u.val



theorem testBlocks_dense : DenseRange (testBlocks (p := p)) := by
  classical
  let M := (LinearMap.range (testBlocks (p := p))).topologicalClosure
  have hclosed : IsClosed (M : Set (L2Sum (BlockPrimal (p := p)))) := Submodule.isClosed_topologicalClosure _
  have hs : ∀ h (x : (BlockPrimal (p := p)) h), lp.single 2 h x ∈ M := by
    intro h x
    refine UniformSpace.Completion.induction_on x
      (p := fun x => lp.single 2 h x ∈ M)
      (by exact hclosed.preimage (lp.singleContinuousLinearMap ℝ (BlockPrimal (p := p)) 2 h).continuous) ?_
    intro u
    apply Submodule.le_topologicalClosure
    exact ⟨u.val, (testBlocks_of_height (p := p)) h u⟩
  intro x
  change x ∈ M
  apply hclosed.mem_of_tendsto (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x)
  exact Filter.Eventually.of_forall (fun s => M.sum_mem (fun h hh => hs h (x h)))


def l2Equiv : (Primal V) ≃ₗᵢ[ℝ] L2Sum (BlockPrimal (p := p)) :=
  (LinearEquiv.refl ℝ (Test V)).extendOfIsometry
    (UniformSpace.Completion.toComplL : Test V →L[ℝ] (Primal V)).toLinearMap
    (testBlocks (p := p)) UniformSpace.Completion.denseRange_coe (testBlocks_dense (p := p))
    (fun u => by
      change ‖(testBlocks (p := p)) u‖ = ‖(u : (Primal V))‖
      rw [UniformSpace.Completion.norm_coe]
      exact (norm_testBlocks (p := p)) u)

@[simp] theorem l2Equiv_test (u : Test V) :
    (l2Equiv (p := p)) (u : (Primal V)) = (testBlocks (p := p)) u :=
  by
    change (l2Equiv (p := p)) ((UniformSpace.Completion.toComplL : Test V →L[ℝ] (Primal V)) u) = _
    unfold l2Equiv
    exact
      (LinearEquiv.extendOfIsometry_eq (LinearEquiv.refl ℝ (Test V))
        (UniformSpace.Completion.toComplL : Test V →L[ℝ] (Primal V)).toLinearMap
        (testBlocks (p := p)) UniformSpace.Completion.denseRange_coe (testBlocks_dense (p := p))
        (fun u => by change ‖(testBlocks (p := p)) u‖ = ‖(u : (Primal V))‖; rw [UniformSpace.Completion.norm_coe]; exact (norm_testBlocks (p := p)) u) u)


end CompletionIdentification
end ComponentPartition




end SegmentLenses

end

end OAI
