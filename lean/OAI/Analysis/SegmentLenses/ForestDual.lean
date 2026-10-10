import OAI.Analysis.SegmentLenses.ForestBlocks

namespace OAI

/-!
# Full-forest reflexivity and coordinate identification
-/

noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace SegmentLenses

attribute [local instance] instDecidableEqForestVertex

section HeightHilbertEquivalence



def heightTests (h : ℕ) : Submodule ℝ (Test ForestVertex) := LinearMap.range (heightTest h)

theorem mem_heightTests {h : ℕ} {u : Test ForestVertex} :
    u ∈ heightTests h ↔ heightTest h u = u := by
  constructor
  · rintro ⟨v, rfl⟩
    exact heightTest_idem h v
  · intro hu
    exact ⟨u, hu⟩

abbrev HeightPrimal (h : ℕ) := UniformSpace.Completion (heightTests h)

def heightHilbert (h : ℕ) : Submodule ℝ (lp (fun _ : ForestVertex => ℝ) 2) where
  carrier := {x | ∀ v : ForestVertex, v.val.1 ≠ h → x v = 0}
  zero_mem' := by intro v hv; rfl
  add_mem' := by intro x y hx hy v hv; simp only [lp.coeFn_add, Pi.add_apply, hx v hv, hy v hv, add_zero]
  smul_mem' := by intro c x hx v hv; simp only [lp.coeFn_smul, Pi.smul_apply, hx v hv, smul_zero]

theorem heightHilbert_closed (h : ℕ) : IsClosed (heightHilbert h : Set (lp (fun _ : ForestVertex => ℝ) 2)) := by
  change IsClosed {x : lp (fun _ : ForestVertex => ℝ) 2 | ∀ v, v.val.1 ≠ h → x v = 0}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro v
  apply isClosed_iInter
  intro hv
  exact isClosed_eq (lp.evalCLM ℝ (fun _ : ForestVertex => ℝ) 2 v).continuous continuous_const

instance (h : ℕ) : CompleteSpace (heightHilbert h) := (heightHilbert_closed h).completeSpace_coe


def heightToHilbert (h : ℕ) : heightTests h →ₗ[ℝ] heightHilbert h where
  toFun u := ⟨testL2 u.val, by
    intro v hv
    rw [testL2_apply, ← mem_heightTests.mp u.property]
    exact ite_eq_right hv⟩
  map_add' u v := Subtype.ext (testL2.map_add u.val v.val)
  map_smul' c u := Subtype.ext (testL2.map_smul c u.val)

@[simp] theorem heightToHilbert_apply (h : ℕ) (u : heightTests h) (v : ForestVertex) :
    (heightToHilbert h u).val v = u.val.coeff v := testL2_apply _ _


theorem heightToHilbert_dense (h : ℕ) : DenseRange (heightToHilbert h) := by
  classical
  intro x
  let u : Finset ForestVertex → heightTests h := fun s =>
    ⟨heightTest h (Test.ofFinite s (fun v => x.val v)), ⟨_, rfl⟩⟩
  have he : ∀ s, (heightToHilbert h (u s)).val = ∑ v ∈ s, lp.single 2 v (x.val v) := by
    intro s
    apply Subtype.ext
    funext v
    simp only [heightToHilbert_apply, u, heightTest_apply]
    rw [Test.coeff_ofFinite]
    have hs : (∑ w ∈ s, lp.single 2 w (x.val w)) v = if v ∈ s then x.val v else 0 := by
      simp only [lp.coeFn_sum, Finset.sum_apply]
      by_cases hv : v ∈ s
      · rw [Finset.sum_eq_single v]
        · simp only [lp.single_apply_self, ite_eq_left hv]
        · intro w hw hwv; exact lp.single_apply_ne _ _ _ hwv.symm
        · exact fun hn => (hn hv).elim
      · rw [ite_eq_right hv]
        apply Finset.sum_eq_zero
        intro w hw
        exact lp.single_apply_ne _ _ _ (fun he => hv (he ▸ hw))
    rw [hs]
    by_cases hv : v.val.1 = h
    · simp [hv]
    · simp [hv, x.property v hv]
  have ht : Filter.Tendsto (fun s => heightToHilbert h (u s)) Filter.atTop (nhds x) := by
    apply tendsto_subtype_rng.mpr
    simpa only [HasSum, SummationFilter.unconditional_filter, he] using (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x.val)
  exact isClosed_closure.mem_of_tendsto ht (Filter.Eventually.of_forall (fun s =>
    subset_closure ⟨u s, rfl⟩))


def heightHilbertEquiv (h : ℕ) : HeightPrimal h ≃L[ℝ] heightHilbert h :=
  (LinearEquiv.refl ℝ (heightTests h)).extend
    (UniformSpace.Completion.toComplL : heightTests h →L[ℝ] HeightPrimal h).toLinearMap
    (heightToHilbert h)
    UniformSpace.Completion.denseRange_coe
    ⟨1, fun u => by
      change ‖testL2 u.val‖ ≤ 1 * ‖(u : HeightPrimal h)‖
      rw [one_mul, UniformSpace.Completion.norm_coe]
      exact norm_testL2_le u.val⟩
    (heightToHilbert_dense h)
    ⟨Real.sqrt (h + 1), fun u => by
      change ‖(u : HeightPrimal h)‖ ≤ Real.sqrt (h + 1) * ‖testL2 u.val‖
      rw [UniformSpace.Completion.norm_coe]
      have hb := height_hilbert_upper h u.val (mem_heightTests.mp u.property)
      change ‖u.val‖ ≤ _
      rw [← norm_testL2_sq] at hb
      have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ h + 1)
      nlinarith [norm_nonneg u, norm_nonneg (testL2 u.val), Real.sqrt_nonneg (h + 1),
        mul_nonneg (Real.sqrt_nonneg (h + 1)) (norm_nonneg (testL2 u.val))]⟩

theorem heightPrimal_reflexive (h : ℕ) : Reflexive (HeightPrimal h) :=
  (hilbert_reflexive (heightHilbert h)).of_equiv (heightHilbertEquiv h).symm

end HeightHilbertEquivalence

section ForestCompletionIdentification

local instance heightPrimalFamilyNormed : ∀ h, NormedAddCommGroup (HeightPrimal h) := fun _h => inferInstance
local instance heightPrimalFamilySpace : ∀ h, NormedSpace ℝ (HeightPrimal h) := fun _h => inferInstance
local instance : Module ℝ J := (inferInstance : NormedSpace ℝ J).toModule
local instance : Module ℝ (L2Sum HeightPrimal) := (inferInstance : NormedSpace ℝ (L2Sum HeightPrimal)).toModule
local instance : AddCommMonoid (L2Sum HeightPrimal) :=
  (inferInstance : NormedAddCommGroup (L2Sum HeightPrimal)).toAddCommMonoid


def heightBlockTest (h : ℕ) : Test ForestVertex →ₗ[ℝ] HeightPrimal h :=
  (UniformSpace.Completion.toComplL : heightTests h →L[ℝ] HeightPrimal h).toLinearMap.comp
    (heightTest h).rangeRestrict

@[simp] theorem norm_heightBlockTest (h : ℕ) (u : Test ForestVertex) :
    ‖heightBlockTest h u‖ = ‖heightTest h u‖ := UniformSpace.Completion.norm_coe _

theorem heightBlockTest_zero {h : ℕ} {u : Test ForestVertex} (hz : heightTest h u = 0) :
    heightBlockTest h u = 0 := by
  apply norm_eq_zero.mp
  exact (norm_heightBlockTest h u).trans (by rw [hz, norm_zero])

def forestBlockVector (u : Test ForestVertex) : L2Sum HeightPrimal :=
  ∑ h ∈ testHeights u, lp.single 2 h (heightBlockTest h u)

@[simp] theorem forestBlockVector_apply (u : Test ForestVertex) (h : ℕ) :
    forestBlockVector u h = heightBlockTest h u := by
  classical
  simp only [forestBlockVector, lp.coeFn_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single h]
  · exact lp.single_apply_self _ _ _
  · intro k hk hkh
    exact lp.single_apply_ne _ _ _ hkh.symm
  · intro hh
    simp only [heightBlockTest_zero (heightTest_eq_zero hh), lp.single_zero, lp.coeFn_zero, Pi.zero_apply]

def forestTestBlocks : Test ForestVertex →ₗ[ℝ] L2Sum HeightPrimal where
  toFun := forestBlockVector
  map_add' u v := by
    apply Subtype.ext
    funext h
    simp only [forestBlockVector_apply, lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' c u := by
    apply Subtype.ext
    funext h
    simp only [forestBlockVector_apply, lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply]

@[simp] theorem forestTestBlocks_apply (u : Test ForestVertex) (h : ℕ) :
    forestTestBlocks u h = heightBlockTest h u := forestBlockVector_apply u h

theorem norm_forestTestBlocks (u : Test ForestVertex) : ‖forestTestBlocks u‖ = ‖u‖ := by
  have he : ‖forestTestBlocks u‖ ^ 2 = ‖u‖ ^ 2 := by
    change ‖∑ h ∈ testHeights u, lp.single 2 h (heightBlockTest h u)‖ ^ 2 = _
    rw [l2_norm_sum_single_sq, forest_norm_sq_decomposition]
    simp only [norm_heightBlockTest]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he



theorem forestTestBlocks_of_height (h : ℕ) (u : heightTests h) :
    forestTestBlocks u.val = lp.single 2 h (u : HeightPrimal h) := by
  classical
  apply Subtype.ext
  funext k
  rw [forestTestBlocks_apply]
  by_cases hk : k = h
  · subst k
    rw [lp.single_apply_self]
    change ((⟨heightTest h u.val, _⟩ : heightTests h) : HeightPrimal h) = _
    congr 1
    exact Subtype.ext (mem_heightTests.mp u.property)
  · rw [lp.single_apply_ne _ _ _ hk]
    apply heightBlockTest_zero
    rw [← mem_heightTests.mp u.property]
    exact heightTest_ne hk u.val



theorem forestTestBlocks_dense : DenseRange forestTestBlocks := by
  classical
  let M := (LinearMap.range forestTestBlocks).topologicalClosure
  have hclosed : IsClosed (M : Set (L2Sum HeightPrimal)) := Submodule.isClosed_topologicalClosure _
  have hs : ∀ h (x : HeightPrimal h), lp.single 2 h x ∈ M := by
    intro h x
    refine UniformSpace.Completion.induction_on x
      (p := fun x => lp.single 2 h x ∈ M)
      (by exact hclosed.preimage (lp.singleContinuousLinearMap ℝ HeightPrimal 2 h).continuous) ?_
    intro u
    apply Submodule.le_topologicalClosure
    exact ⟨u.val, forestTestBlocks_of_height h u⟩
  intro x
  change x ∈ M
  apply hclosed.mem_of_tendsto (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x)
  exact Filter.Eventually.of_forall (fun s => M.sum_mem (fun h hh => hs h (x h)))


def forestL2Equiv : J ≃ₗᵢ[ℝ] L2Sum HeightPrimal :=
  (LinearEquiv.refl ℝ (Test ForestVertex)).extendOfIsometry
    (UniformSpace.Completion.toComplL : Test ForestVertex →L[ℝ] J).toLinearMap
    forestTestBlocks UniformSpace.Completion.denseRange_coe forestTestBlocks_dense
    (fun u => by
      change ‖forestTestBlocks u‖ = ‖(u : J)‖
      rw [UniformSpace.Completion.norm_coe]
      exact norm_forestTestBlocks u)

@[simp] theorem forestL2Equiv_test (u : Test ForestVertex) :
    forestL2Equiv (u : J) = forestTestBlocks u :=
  by
    change forestL2Equiv ((UniformSpace.Completion.toComplL : Test ForestVertex →L[ℝ] J) u) = _
    unfold forestL2Equiv
    exact
      (LinearEquiv.extendOfIsometry_eq (LinearEquiv.refl ℝ (Test ForestVertex))
        (UniformSpace.Completion.toComplL : Test ForestVertex →L[ℝ] J).toLinearMap
        forestTestBlocks UniformSpace.Completion.denseRange_coe forestTestBlocks_dense
        (fun u => by change ‖forestTestBlocks u‖ = ‖(u : J)‖; rw [UniformSpace.Completion.norm_coe]; exact norm_forestTestBlocks u) u)


theorem forest_primal_reflexive : Reflexive J :=
  (l2Sum_reflexive HeightPrimal heightPrimal_reflexive).of_equiv
    forestL2Equiv.symm.toContinuousLinearEquiv


theorem forest_dual_reflexive : Reflexive X := forest_primal_reflexive.dual

end ForestCompletionIdentification



end SegmentLenses

end

end OAI
