import OAI.NumberTheory.DukePrimeDegree.Dynamics.MautnerLatticeL2
import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootFlowGeneric

namespace OAI

/-!
# Ergodicity of a root inside its actual two-root group

The chosen root is ergodic on an ergodic component of the group generated
by it and its opposite. This follows from the concrete Mautner argument,
not from an implication from diagonal ergodicity. Only the two-root group
is required to preserve the measure.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal Pointwise

namespace DukePrimeDegree
open PrimeDegreePackets

def oppositeRootPairGroup {n : ℕ} {i j : Fin n} (hij : i ≠ j) : Subgroup (G n) :=
  Subgroup.closure ({g | ∃ t : ℝ, g = Matrix.SpecialLinearGroup.transvection hij t} ∪
    {g | ∃ t : ℝ, g = Matrix.SpecialLinearGroup.transvection hij.symm t})

lemma root_mem_oppositeRootPairGroup {n : ℕ} {i j : Fin n} (hij : i ≠ j) (t : ℝ) :
    Matrix.SpecialLinearGroup.transvection hij t ∈ oppositeRootPairGroup hij :=
  Subgroup.subset_closure (Or.inl ⟨t, rfl⟩)

lemma opposite_root_mem_oppositeRootPairGroup {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (t : ℝ) :
    Matrix.SpecialLinearGroup.transvection hij.symm t ∈ oppositeRootPairGroup hij :=
  Subgroup.subset_closure (Or.inr ⟨t, rfl⟩)

lemma subgroup_le_invariantRightSubgroup_of_invariant_action {n : ℕ}
    (H : Subgroup (G n)) (μ : Measure (X n)) [SMulInvariantMeasure H (X n) μ] :
    H ≤ invariantRightSubgroup μ := by
  intro g hg
  have hp := (measurePreserving_smul (⟨g, hg⟩ : H)⁻¹ μ).map_eq
  change μ.map (fun x => rightAction x ((g⁻¹)⁻¹)) = μ at hp
  change μ.map (fun x => rightAction x g) = μ
  simpa only [inv_inv] using hp

theorem root_ergodic_of_opposite_root_pair_ergodic {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (μ : Measure (X n)) [IsFiniteMeasure μ]
    [ErgodicSMul (oppositeRootPairGroup hij) (X n) μ] :
    let := rootTranslationAction hij
    ErgodicSMul (Multiplicative ℝ) (X n) μ := by
  classical
  let H := oppositeRootPairGroup hij
  have hH : H ≤ invariantRightSubgroup μ :=
    subgroup_le_invariantRightSubgroup_of_invariant_action H μ
  have hU (t : ℝ) : Matrix.SpecialLinearGroup.transvection hij t ∈ H :=
    root_mem_oppositeRootPairGroup hij t
  have hV (t : ℝ) : Matrix.SpecialLinearGroup.transvection hij.symm t ∈ H :=
    opposite_root_mem_oppositeRootPairGroup hij t
  have hpU (t : ℝ) : MeasurePreserving (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij t)) μ μ :=
    ⟨(continuous_rightAction _).measurable, hH (hU t)⟩
  have hpV (t : ℝ) : MeasurePreserving (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij.symm t)) μ μ :=
    ⟨(continuous_rightAction _).measurable, hH (hV t)⟩
  let := rootTranslationAction hij
  refine { measure_preimage_smul := ?_, aeconst_of_forall_preimage_smul_ae_eq := ?_ }
  · intro t s hs
    exact (hpU t.toAdd).measure_preimage hs.nullMeasurableSet
  · intro s hs hsU
    let q : X n → ℝ := s.indicator (fun _ => (1 : ℝ))
    have hq : MemLp q 2 μ := (memLp_const (1 : ℝ)).indicator hs
    let F : Lp ℝ 2 μ := hq.toLp q
    have hF : (F : X n → ℝ) =ᵐ[μ] q := hq.coeFn_toLp
    have hsroot (t : ℝ) : (fun x => rightAction x
        (Matrix.SpecialLinearGroup.transvection hij t)) ⁻¹' s =ᵐ[μ] s :=
      hsU (Multiplicative.ofAdd t)
    have hFroot (t : ℝ) : (fun x => F (rightAction x
        (Matrix.SpecialLinearGroup.transvection hij t))) =ᵐ[μ] F := by
      filter_upwards [(hpU t).quasiMeasurePreserving.ae_eq_comp hF,
        hF, (hsroot t).mem_iff] with x hleft hright hmem
      change F (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
        q (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) at hleft
      rw [hleft, hright]
      have hm : rightAction x (Matrix.SpecialLinearGroup.transvection hij t) ∈ s ↔ x ∈ s :=
        hmem
      simp only [q, Set.indicator_apply, hm]
    have hsopposite (t : ℝ) : (fun x => rightAction x
        (Matrix.SpecialLinearGroup.transvection hij.symm t)) ⁻¹' s =ᵐ[μ] s := by
      have hFV := ae_opposite_root_fixed_of_L2_root_fixed hij H μ hH hU hV F hFroot t
      have hqV : (fun x => q (rightAction x
          (Matrix.SpecialLinearGroup.transvection hij.symm t))) =ᵐ[μ] q :=
        ((hpV t).quasiMeasurePreserving.ae_eq_comp hF).symm.trans (hFV.trans hF)
      apply Filter.Eventually.set_eq
      filter_upwards [hqV] with x hx
      change (rightAction x (Matrix.SpecialLinearGroup.transvection hij.symm t) ∈ s ↔ x ∈ s)
      by_cases hleft : rightAction x (Matrix.SpecialLinearGroup.transvection hij.symm t) ∈ s <;>
        by_cases hright : x ∈ s <;> simp_all [q]
    let K := (MulAction.aestabilizer H μ s).map H.subtype
    have hUK (t : ℝ) : Matrix.SpecialLinearGroup.transvection hij t ∈ K := by
      refine Subgroup.mem_map.mpr ⟨⟨_, hU t⟩, ?_, rfl⟩
      rw [MulAction.mem_aestabilizer, ← preimage_smul_inv]
      change (fun x => rightAction x
        ((Matrix.SpecialLinearGroup.transvection hij t)⁻¹)⁻¹) ⁻¹' s =ᵐ[μ] s
      simpa only [inv_inv] using hsroot t
    have hVK (t : ℝ) : Matrix.SpecialLinearGroup.transvection hij.symm t ∈ K := by
      refine Subgroup.mem_map.mpr ⟨⟨_, hV t⟩, ?_, rfl⟩
      rw [MulAction.mem_aestabilizer, ← preimage_smul_inv]
      change (fun x => rightAction x
        ((Matrix.SpecialLinearGroup.transvection hij.symm t)⁻¹)⁻¹) ⁻¹' s =ᵐ[μ] s
      simpa only [inv_inv] using hsopposite t
    have hHK : H ≤ K := by
      apply (Subgroup.closure_le K).mpr
      rintro g (⟨t, rfl⟩ | ⟨t, rfl⟩)
      · exact hUK t
      · exact hVK t
    apply aeconst_of_forall_smul_ae_eq H hs.nullMeasurableSet
    intro h
    obtain ⟨k, hk, hkval⟩ := Subgroup.mem_map.mp (hHK h.property)
    have hkh : k = h := Subtype.ext hkval
    exact MulAction.mem_aestabilizer.mp (hkh ▸ hk)

/-- The existing measurable decomposition can be taken over the actual
two-root group. Each resulting component is then ergodic for the full
root flow as well. No invariance under the rest of the diagonal group is
asserted for these components. -/
theorem opposite_root_pair_ergodic_decomposition {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hH : oppositeRootPairGroup hij ≤ invariantRightSubgroup μ) :
    let := rootTranslationAction hij
    ∃ (m : MeasurableSpace (X n)) (hm : m ≤ xMeasurableSpace n),
      letI : MeasurableSpace (X n) := xMeasurableSpace n
      condExpKernel μ m ∘ₘ μ.trim hm = μ ∧
        ∀ᵐ z ∂μ.trim hm,
          ErgodicSMul (oppositeRootPairGroup hij) (X n) (condExpKernel μ m z) ∧
          ErgodicSMul (Multiplicative ℝ) (X n) (condExpKernel μ m z) := by
  let := rootTranslationAction hij
  obtain ⟨m, hm, hdec, hcomp⟩ :=
    lattice_subgroup_ergodic_decomposition (oppositeRootPairGroup hij) μ hH
  let : MeasurableSpace (X n) := xMeasurableSpace n
  refine ⟨m, hm, hdec, ?_⟩
  filter_upwards [hcomp] with z hz
  let : ErgodicSMul (oppositeRootPairGroup hij) (X n) (condExpKernel μ m z) := hz
  exact ⟨hz, root_ergodic_of_opposite_root_pair_ergodic hij _⟩

end DukePrimeDegree

end

end OAI
