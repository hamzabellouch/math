import OAI.NumberTheory.DukePrimeDegree.Dynamics.SmallReturns

namespace OAI

/-!
# Simultaneous strong returns

The fixed-parameter small-return theorem extends to a whole subgroup by
separability and closedness. This removes the parameter-dependent null
sets in the exceptional-return argument of EKL (2006), Lemma 4.2.
-/

noncomputable section
open Filter Set Matrix MeasureTheory
open scoped Topology Classical BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def singleRootCentralizer {n : ℕ} {i j : Fin n} (hij : i ≠ j) : Subgroup (G n) :=
  Subgroup.centralizer {Matrix.SpecialLinearGroup.transvection hij 1}

lemma mem_singleRootCentralizer {n : ℕ} {i j : Fin n} (hij : i ≠ j) (g : G n) :
    g ∈ singleRootCentralizer hij ↔ g * Matrix.SpecialLinearGroup.transvection hij 1 =
      Matrix.SpecialLinearGroup.transvection hij 1 * g := by
  simp only [singleRootCentralizer, Subgroup.mem_centralizer_iff, mem_singleton_iff,
    forall_eq, eq_comm]

lemma matrixBall_subset_matrixClosedBall {n : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    matrixBall n r ⊆ matrixClosedBall n r := by
  intro g hg
  exact (mem_matrixClosedBall_iff hr g).mpr fun a b => (hg a b).le

/-- On a fixed injectivity chart, one conull set works for every parameter
in any subgroup commuting with the contracting diagonal and the root. -/
theorem ae_strong_returns_on_chart
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (H : Subgroup (G (d + 1)))
    (hHroot : ∀ b : H, (b : G (d + 1)) ∈ singleRootCentralizer hij)
    (hHdiag : ∀ b : H, ∀ t : ℝ,
      (b : G (d + 1)) * diagonalOneParameter (rootContractionWeights i j)
        (rootContractionWeights_sum i j) t =
      diagonalOneParameter (rootContractionWeights i j) (rootContractionWeights_sum i j) t * b)
    (r R : ℝ) (hr : 0 ≤ r) (hrR : r < R)
    (U : Set (X (d + 1))) (hU : MeasurableSet U)
    (hinj : ∀ x ∈ U, Set.InjOn (fun g => rightAction x g) (matrixBall (d + 1) R)) :
    ∀ᵐ x ∂μ, x ∈ U → ∀ b : H, ∀ g ∈ matrixBall (d + 1) r,
      g ∈ singleRootCentralizer hij → rightAction x g = rightAction x b →
        g ∈ rootPairCentralizer hij := by
  let : SecondCountableTopology H := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense H
  let K : Set (G (d + 1)) := matrixClosedBall (d + 1) r ∩ singleRootCentralizer hij
  have hK : IsCompact K := (isCompact_matrixClosedBall (d + 1) r).inter_right
    (Set.isClosed_centralizer _)
  have hfixed : ∀ b : H, ∀ᵐ x ∂μ, x ∈ U → ∀ g ∈ K,
      rightAction x g = rightAction x b → g ∈ rootPairCentralizer hij := by
    intro b
    apply ae_small_rootCentralizer_return_in_pair d hij μ hA b (hHdiag b) r R hr hrR U hU hinj K hK
    intro g hg
    exact ⟨hg.1, (mem_singleRootCentralizer hij g).mp hg.2⟩
  have hall : ∀ᵐ x ∂μ, ∀ b ∈ S, x ∈ U → ∀ g ∈ K,
      rightAction x g = rightAction x b → g ∈ rootPairCentralizer hij :=
    (ae_ball_iff hSc).mpr fun b _ => hfixed b
  filter_upwards [hall] with x hx
  intro hxU b g hgball hgroot hret
  let f : H → G (d + 1) := fun c => g * (b : G (d + 1))⁻¹ * c
  have hf : Continuous f := (continuous_const.mul continuous_const).mul continuous_subtype_val
  have hfb : f b = g := by dsimp [f]; group
  let W : Set H := f ⁻¹' matrixBall (d + 1) r
  have hW : IsOpen W := (matrixBall_isOpen _ _).preimage hf
  have hbW : b ∈ W := by change f b ∈ matrixBall (d + 1) r; rwa [hfb]
  have hbcl : b ∈ closure (S ∩ W) := by
    apply mem_closure_iff.mpr
    intro V hV hbV
    obtain ⟨c, hcS, hcV, hcW⟩ := hSd.exists_mem_open (hV.inter hW) ⟨b, hbV, hbW⟩
    exact ⟨c, hcV, hcS, hcW⟩
  have hsub : S ∩ W ⊆ f ⁻¹' (rootPairCentralizer hij : Set (G (d + 1))) := by
    rintro c ⟨hcS, hcW⟩
    apply hx c hcS hxU (f c)
    · refine ⟨matrixBall_subset_matrixClosedBall hr hcW, ?_⟩
      exact (singleRootCentralizer hij).mul_mem
        ((singleRootCentralizer hij).mul_mem hgroot
          ((singleRootCentralizer hij).inv_mem (hHroot b))) (hHroot c)
    · dsimp only [f]
      rw [← rightAction_mul, ← rightAction_mul, hret, rightAction_mul, rightAction_mul]
      congr 1
      group
  have hclosed : IsClosed (f ⁻¹' (rootPairCentralizer hij : Set (G (d + 1)))) :=
    (rootPairCentralizer_isClosed hij).preimage hf
  have hmem := hclosed.closure_subset_iff.mpr hsub hbcl
  change f b ∈ rootPairCentralizer hij at hmem
  rwa [hfb] at hmem

end DukePrimeDegree

end

end OAI
