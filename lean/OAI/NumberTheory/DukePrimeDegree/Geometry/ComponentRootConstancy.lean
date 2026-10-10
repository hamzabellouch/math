import OAI.NumberTheory.DukePrimeDegree.Geometry.ComponentRootPattern

namespace OAI

/-!
# No new invariant roots on the component base

Diagonal covariance makes each full-root invariance event invariant on
the parameter space. Diagonal ergodicity makes that event null or conull.
In the conull case, integration of the actual conditional measures gives
root invariance of the original measure. This conclusion does not assume
that the individual conditional measures are diagonal invariant.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma translation_mem_of_ae_kernel_invariant
    {Z : Type*} [MeasurableSpace Z] {n : ℕ}
    (τ : Measure Z) (κ : Kernel Z (X n)) (g : G n)
    (hκ : ∀ᵐ z ∂τ, g ∈ invariantRightSubgroup (κ z)) :
    g ∈ invariantRightSubgroup (κ ∘ₘ τ) := by
  change (κ ∘ₘ τ).map (fun x => rightAction x g) = κ ∘ₘ τ
  rw [Measure.map_comp τ κ (continuous_rightAction g).measurable]
  apply Measure.comp_congr
  filter_upwards [hκ] with z hz
  change (κ z).map (fun x => rightAction x g) = κ z at hz
  simpa only [Kernel.map_apply _ (continuous_rightAction g).measurable] using hz

lemma root_mem_of_ae_kernel_invariant
    {Z : Type*} [MeasurableSpace Z] {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (τ : Measure Z) (κ : Kernel Z (X n))
    (hκ : ∀ᵐ z ∂τ, ∀ t : ℝ,
      Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup (κ z)) :
    ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈
      invariantRightSubgroup (κ ∘ₘ τ) := by
  intro t
  exact translation_mem_of_ae_kernel_invariant τ κ _ (hκ.mono fun z hz => hz t)

/-- On the actual invariant-sigma conditional measures, a root can be
present on a positive set of parameters only if it fixes the ambient
diagonal-ergodic measure. The normalizer condition concerns the subgroup
used for conditioning, not the stabilizer of each component. -/
theorem ae_component_root_implies_ambient_root
    (d : ℕ) (H : Subgroup (G (d + 1)))
    (hAH : ∀ u : LogCoordinates d,
      diagonalFlow u ∈ Subgroup.normalizer (H : Set (G (d + 1))))
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    {i j : Fin (d + 1)} (hij : i ≠ j) :
    ∀ᵐ z ∂μ.trim (actionInvariantSigma_le H (X (d + 1))),
      (∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup
        (condExpKernel μ (actionInvariantSigma H (X (d + 1))) z)) →
      ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup μ := by
  let m := actionInvariantSigma H (X (d + 1))
  let : MeasurableSpace (X (d + 1)) := xMeasurableSpace (d + 1)
  have hm : m ≤ xMeasurableSpace (d + 1) := actionInvariantSigma_le H (X (d + 1))
  let κ := condExpKernel μ m
  let E : Set (X (d + 1)) := {z | ∀ t : ℝ,
    Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup (κ z)}
  have hE : @MeasurableSet (X (d + 1)) m E :=
    @measurableSet_kernel_root_invariant (X (d + 1)) m (d + 1) i j hij κ inferInstance
  have hEinv (u : Multiplicative (LogCoordinates d)) :
      (u • ·) ⁻¹' E =ᵐ[μ] E := by
    let ell : Fin (d + 1) → ℝ := Fin.snoc u.toAdd (-∑ k, u.toAdd k)
    have hell : ∑ k, ell k = 0 := by simp [ell, Fin.sum_univ_castSucc]
    have ha : diagonalOneParameter ell hell 1 = diagonalFlow u.toAdd := by
      rw [diagonalOneParameter_eq_diagonalFlow]
      congr 1
      funext k
      simp [ell]
    have hμ : μ.map (fun x => rightAction x (diagonalFlow u.toAdd)) = μ :=
      (measurePreserving_smul u μ).map_eq
    have hc := lattice_normalizer_component_covariance H
      (diagonalFlow u.toAdd) (hAH u.toAdd) μ hμ
    apply Filter.Eventually.set_eq
    filter_upwards [ae_of_ae_trim hm hc] with z hz
    change (∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈
      invariantRightSubgroup (κ (rightAction z (diagonalFlow u.toAdd)))) ↔
      ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup (κ z)
    change (κ z).map (fun x => rightAction x (diagonalFlow u.toAdd)) =
      κ (rightAction z (diagonalFlow u.toAdd)) at hz
    rw [← hz, ← ha]
    exact all_root_mem_map_diagonal_iff hij (κ z) ell hell 1
  have hconst := ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq
    (G := Multiplicative (LogCoordinates d)) (hm E hE) hEinv
  rcases eventuallyEmptyOrUniv_iff.mp hconst with hall | hnone
  · have halltrim : ∀ᵐ z ∂μ.trim hm, z ∈ E := by
      rw [ae_iff] at hall ⊢
      change μ Eᶜ = 0 at hall
      change μ.trim hm Eᶜ = 0
      rwa [trim_measurableSet_eq hm hE.compl]
    have hroot := @root_mem_of_ae_kernel_invariant (X (d + 1)) m (d + 1) i j
      hij (μ.trim hm) κ halltrim
    have hdec : κ ∘ₘ μ.trim hm = μ := condExpKernel_comp_trim hm
    rw [hdec] at hroot
    exact Eventually.of_forall fun _ _ => hroot
  · have hnonetrim : ∀ᵐ z ∂μ.trim hm, z ∉ E := by
      rw [ae_iff] at hnone ⊢
      have he : {a | ¬a ∉ E} = E := by ext a; simp only [mem_ofPred_eq, not_not]
      rw [he] at hnone ⊢
      rwa [trim_measurableSet_eq hm hE]
    exact hnonetrim.mono fun _ hz h => (hz h).elim

/-- The subgroup generated by the ambient invariant roots has the
normalizer property needed above by the explicit diagonal conjugation
formula. Thus conditioning on it introduces no new roots almost surely. -/
theorem ae_rootGenerated_component_no_new_roots
    (d : ℕ) (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    {i j : Fin (d + 1)} (hij : i ≠ j) :
    ∀ᵐ z ∂μ.trim (actionInvariantSigma_le (invariantRootGeneratedGroup μ) (X (d + 1))),
      (∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup
        (condExpKernel μ (actionInvariantSigma (invariantRootGeneratedGroup μ) (X (d + 1))) z)) →
      ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup μ := by
  apply ae_component_root_implies_ambient_root d (invariantRootGeneratedGroup μ) ?_ μ hij
  intro u
  let ell : Fin (d + 1) → ℝ := Fin.snoc u (-∑ k, u k)
  have hell : ∑ k, ell k = 0 := by simp [ell, Fin.sum_univ_castSucc]
  have ha : diagonalOneParameter ell hell 1 = diagonalFlow u := by
    rw [diagonalOneParameter_eq_diagonalFlow]
    congr 1
    funext k
    simp [ell]
  rw [← ha]
  exact diagonal_normalizes_rootGeneratedGroup μ ell hell 1

/-- Roots in the conditioning subgroup also preserve the conditional
measures. Countably many rational times suffice because each actual
measure stabilizer is closed. -/
theorem ae_conditional_root_invariant_of_subgroup_root
    {n : ℕ} (H : Subgroup (G n)) (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hH : H ≤ invariantRightSubgroup μ) {i j : Fin n} (hij : i ≠ j)
    (hU : ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ H) :
    ∀ᵐ z ∂μ.trim (actionInvariantSigma_le H (X n)),
      ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup
        (condExpKernel μ (actionInvariantSigma H (X n)) z) := by
  have hq (q : ℚ) : ∀ᵐ z ∂μ.trim (actionInvariantSigma_le H (X n)),
      Matrix.SpecialLinearGroup.transvection hij (q : ℝ) ∈ invariantRightSubgroup
        (condExpKernel μ (actionInvariantSigma H (X n)) z) := by
    have hfix : actionInvariantSigma H (X n) ≤ MeasurableSpace.invariants
        (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij (q : ℝ))) := by
      have hh := iInf_le (fun h : H => MeasurableSpace.invariants (fun x : X n => h • x))
        (⟨(Matrix.SpecialLinearGroup.transvection hij (q : ℝ))⁻¹, H.inv_mem (hU q)⟩ : H)
      change actionInvariantSigma H (X n) ≤ MeasurableSpace.invariants
        (fun x => rightAction x ((Matrix.SpecialLinearGroup.transvection hij (q : ℝ))⁻¹)⁻¹) at hh
      simpa only [inv_inv] using hh
    exact condExpKernel_invariant (actionInvariantSigma H (X n)) μ
      (actionInvariantSigma_le H (X n))
      ⟨(continuous_rightAction _).measurable, hH (hU q)⟩ hfix
  filter_upwards [ae_all_iff.mpr hq] with z hz
  exact (all_root_mem_iff_rational_root_mem hij _).mpr hz

/-- The full-root pattern of the actual invariant-sigma conditional
measures agrees almost everywhere with the ambient pattern. This is
stronger than a measurable root-pattern assertion and still does not
assert diagonal invariance or homogeneity of individual components. -/
theorem ae_rootGenerated_component_root_iff
    (d : ℕ) (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    {i j : Fin (d + 1)} (hij : i ≠ j) :
    ∀ᵐ z ∂μ.trim (actionInvariantSigma_le (invariantRootGeneratedGroup μ) (X (d + 1))),
      (∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup
        (condExpKernel μ (actionInvariantSigma (invariantRootGeneratedGroup μ) (X (d + 1))) z)) ↔
      ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup μ := by
  by_cases hroot : ∀ t : ℝ,
      Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup μ
  · have hc := ae_conditional_root_invariant_of_subgroup_root (invariantRootGeneratedGroup μ)
      μ (invariantRootGeneratedGroup_le μ) hij
      (root_mem_invariantRootGeneratedGroup μ hij (Or.inr ⟨hij, hroot⟩))
    exact hc.mono fun _ hz => ⟨fun _ => hroot, fun _ => hz⟩
  · exact (ae_rootGenerated_component_no_new_roots d μ hij).mono
      fun _ hz => ⟨hz, fun h => (hroot h).elim⟩

end DukePrimeDegree

end

end OAI
