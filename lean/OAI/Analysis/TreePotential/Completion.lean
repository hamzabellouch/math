import OAI.Analysis.TreePotential.Inward

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section TestCompletions
open scoped Classical
variable {I : Type*}

def testVectorEquiv (K : TestFamily I) : TestVector K ≃ₗ[ℝ] (I →₀ ℝ) :=
  { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

lemma norm_testVector_equiv (K : TestFamily I) (x : TestVector K) :
    ‖x‖ = testNorm K ((testVectorEquiv K) x) := rfl

lemma norm_test_single (K : TestFamily I) (i : I) :
    ‖(testVectorEquiv K).symm (Finsupp.single i 1)‖ = 1 := by
  apply le_antisymm
  · change testNorm K (Finsupp.single i 1) ≤ 1
    simpa using testNorm_le_l1 K (Finsupp.single i 1)
  · change 1 ≤ testNorm K (Finsupp.single i 1)
    simpa using coordinate_le_testNorm K (Finsupp.single i 1) i

def finiteTestFunctional (K : TestFamily I) (f : K) : TestVector K →L[ℝ] ℝ :=
  ((finitePairing f.val).comp (testVectorEquiv K).toLinearMap).mkContinuous 1 fun x => by
    change |finitePairing f.val ((testVectorEquiv K) x)| ≤ 1 * testNorm K ((testVectorEquiv K) x)
    simpa only [one_mul] using finitePairing_le_testNorm K f ((testVectorEquiv K) x)

@[simp] lemma finiteTestFunctional_apply (K : TestFamily I) (f : K) (x : TestVector K) :
    finiteTestFunctional K f x = finitePairing f.val x := rfl

lemma finiteTestFunctional_norm_le (K : TestFamily I) (f : K) : ‖finiteTestFunctional K f‖ ≤ 1 := by
  refine (finiteTestFunctional K f).opNorm_le_bound zero_le_one ?_
  intro x
  change |finitePairing f.val ((testVectorEquiv K) x)| ≤ 1 * testNorm K ((testVectorEquiv K) x)
  simpa only [one_mul] using finitePairing_le_testNorm K f ((testVectorEquiv K) x)

/-- The completion used in the test-space constructions. -/
abbrev TestCompletion (K : TestFamily I) := UniformSpace.Completion (TestVector K)

def completedTestFunctional (K : TestFamily I) (f : K) : TestCompletion K →L[ℝ] ℝ :=
  (finiteTestFunctional K f).extend UniformSpace.Completion.toComplL

@[simp] lemma completedTestFunctional_coe (K : TestFamily I) (f : K) (x : TestVector K) :
    completedTestFunctional K f (x : TestCompletion K) = finitePairing f.val x := by
  exact (finiteTestFunctional K f).extend_eq UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformEmbedding_coe _).isUniformInducing x

lemma completedTestFunctional_norm_le (K : TestFamily I) (f : K) :
    ‖completedTestFunctional K f‖ ≤ 1 := by
  have h := (finiteTestFunctional K f).opNorm_extend_le (N := 1)
    (e := UniformSpace.Completion.toComplL) UniformSpace.Completion.denseRange_coe
    (fun x => by simp)
  have h' : ‖completedTestFunctional K f‖ ≤ ‖finiteTestFunctional K f‖ := by
    simpa only [NNReal.coe_one, one_mul, completedTestFunctional] using h
  exact h'.trans (finiteTestFunctional_norm_le K f)

lemma completedTestFunctional_abs_le (K : TestFamily I) (f : K) (x : TestCompletion K) :
    |completedTestFunctional K f x| ≤ ‖x‖ := by
  simpa only [one_mul, Real.norm_eq_abs] using
    (completedTestFunctional K f).le_of_opNorm_le (completedTestFunctional_norm_le K f) x

/-- Extended tests really remain norming; this is established, not postulated
    as an extra hypothesis on the completion. -/
lemma exists_completed_test_near_norm (K : TestFamily I) (x : TestCompletion K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : K, ‖x‖ - ε < completedTestFunctional K f x := by
  obtain ⟨w, hw⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt x
    (show 0 < ε / 3 by linarith)
  have hw' : ‖x - (w : TestCompletion K)‖ < ε / 3 := by simpa only [dist_eq_norm] using hw
  have hn : ‖x‖ - ‖w‖ < ε / 3 := by
    have h := norm_sub_norm_le x (w : TestCompletion K)
    rw [UniformSpace.Completion.norm_coe] at h
    exact h.trans_lt hw'
  have hu : testNorm K ((testVectorEquiv K) w) - ε / 3 <
      ⨆ f : K, finitePairing f.val ((testVectorEquiv K) w) := by
    rw [← testNorm_signed_sup K ((testVectorEquiv K) w)]
    linarith
  obtain ⟨f, hf⟩ := exists_lt_of_lt_ciSup hu
  refine ⟨f, ?_⟩
  have hd := completedTestFunctional_abs_le K f (x - (w : TestCompletion K))
  rw [map_sub, completedTestFunctional_coe] at hd
  have hl := (abs_le.mp hd).1
  change ‖w‖ - ε / 3 < finitePairing f.val w at hf
  linarith

theorem completed_tests_norming (K : TestFamily I) (x : TestCompletion K) :
    ‖x‖ = ⨆ f : K, completedTestFunctional K f x := by
  have hb : BddAbove (range fun f : K => completedTestFunctional K f x) :=
    ⟨‖x‖, by rintro _ ⟨f, rfl⟩; exact (le_abs_self _).trans (completedTestFunctional_abs_le K f x)⟩
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨f, hf⟩ := exists_completed_test_near_norm K x hε
    have := le_ciSup hb f
    linarith
  · apply ciSup_le
    intro f
    exact (le_abs_self _).trans (completedTestFunctional_abs_le K f x)

end TestCompletions


end BoundedTreePotentials

end

end OAI
