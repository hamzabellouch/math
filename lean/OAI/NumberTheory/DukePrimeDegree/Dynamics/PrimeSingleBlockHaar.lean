import OAI.NumberTheory.DukePrimeDegree.Dynamics.SingleBlockOrbitExistence
import OAI.NumberTheory.DukePrimeDegree.Dynamics.SingleBlockComponents
import OAI.NumberTheory.DukePrimeDegree.Dynamics.SingleBlockLocalStabilizer
import OAI.NumberTheory.DukePrimeDegree.Dynamics.BlockOrbitMass
import OAI.NumberTheory.DukePrimeDegree.Dynamics.OrbitGenericity
import OAI.NumberTheory.DukePrimeDegree.Dynamics.InvariantRootExistence
import OAI.NumberTheory.DukePrimeDegree.MainConditional

namespace OAI

/-!
# Prime-degree Haar rigidity from a nontrivial invariant-root partition

The canonical component is genuinely ergodic for its chosen root block.
The shearing argument constructs a positive-mass block orbit, and the
rational stabilizer argument forces that block to be the full coordinate
set.  The root partition is supplied explicitly here: producing its
symmetry and nontriviality from positive entropy is the separate entropy
step, not a hidden homogeneous-orbit hypothesis.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem singleBlock_eq_univ_of_generic_local_stabilizer {n : ℕ}
    (hn : n.Prime) (S : Set (Fin n))
    (k l : Fin n) (hkl : k ≠ l) (hk : k ∈ S) (hl : l ∈ S)
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    [ErgodicSMul (singleBlockRootGroup S) (X n) μ]
    (hlocal : {g : invariantRightSubgroup μ |
      g.val ∈ blockMatrixGroup (blockComplementSetoid S)} ∈
        𝓝 (1 : invariantRightSubgroup μ))
    (hgeneric : ∀ᵐ x ∂μ, ∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0) :
    S = univ := by
  classical
  let Sf := Finset.univ.filter (fun i => i ∈ S)
  have hSf : (↑Sf : Set (Fin n)) = S := by ext i; simp [Sf]
  have hSfE : ErgodicSMul (singleBlockRootGroup (Sf : Set (Fin n))) (X n) μ := by
    rw [hSf]
    infer_instance
  let := hSfE
  obtain ⟨g, hmass⟩ := exists_positive_singleBlock_orbit Sf k l hkl
    (by simpa only [← hSf, Finset.mem_coe] using hk)
    (by simpa only [← hSf, Finset.mem_coe] using hl) μ
    (by simpa only [hSf] using hlocal)
  rw [hSf] at hmass
  have hH : singleBlockRootGroup S ≤ invariantRightSubgroup μ :=
    subgroup_le_invariantRightSubgroup_of_invariant_action _ μ
  have hpair : blockComplementSetoid S k l := ⟨fun _ => hl, fun _ => hk⟩
  have hall := partition_universal_of_positive_block_orbit_mass hn g
    (blockComplementSetoid S) k l hkl hpair μ hmass
    (hH (root_mem_singleBlockRootGroup S k hk l hl hkl (-1)))
    (hH (root_mem_singleBlockRootGroup S l hl k hk hkl.symm (-1))) hgeneric
  apply Set.eq_univ_of_forall
  intro i
  exact (hall i k).mpr hk

/-- The orbit-existence conclusion is proved inside the argument. The
only remaining dynamical premise is the actual equivalence relation of
invariant roots with at least one nontrivial class. -/
theorem isHaar_of_prime_nontrivial_root_partition
    (d : ℕ) (hprime : (d + 1).Prime)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (r : Setoid (Fin (d + 1)))
    (hr : ∀ i j, r i j ↔ rootInvarianceRelation μ i j)
    (hnontrivial : ∃ k l, k ≠ l ∧ r k l) :
    IsHaarProbability μ := by
  obtain ⟨k, l, hkl, hrkl⟩ := hnontrivial
  let S : Set (Fin (d + 1)) := {i | r i k}
  let H := singleBlockRootGroup S
  have hk : k ∈ S := r.refl k
  have hl : l ∈ S := r.symm hrkl
  have hH : H ≤ invariantRightSubgroup μ := by
    apply singleBlockRootGroup_le_of_roots
    intro i hi j hj hij t
    exact ((rootInvarianceRelation_iff_full_root hij μ).mp
      ((hr i j).mp (r.trans hi (r.symm hj)))) t
  let m := actionInvariantSigma H (X (d + 1))
  let : MeasurableSpace (X (d + 1)) := xMeasurableSpace (d + 1)
  have hm : m ≤ xMeasurableSpace (d + 1) := actionInvariantSigma_le H _
  let κ := condExpKernel μ m
  let τ := μ.trim hm
  have hdec : κ ∘ₘ τ = μ := (lattice_canonical_subgroup_ergodic_decomposition H μ hH).1
  have hA (u : LogCoordinates d) :
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hgen : ∀ᵐ z ∂τ, ∀ᵐ x ∂κ z,
      ∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0 := by
    apply Measure.ae_ae_of_ae_comp
    rw [hdec]
    exact ae_no_coordinate_zero d μ hA
  have hcomp := ae_singleBlock_component_ergodic_and_locally_block_preserving
    d μ r hr k l hkl hrkl
  let : @IsProbabilityMeasure (X (d + 1)) m τ := by
    constructor
    rw [trim_measurableSet_eq hm (@MeasurableSet.univ _ m)]
    exact measure_univ
  obtain ⟨z, hz, hzg⟩ := (hcomp.and hgen).exists
  let : ErgodicSMul H (X (d + 1)) (κ z) := hz.1
  have hlocal := local_singleBlock_of_fixed_projection (invariantRightSubgroup (κ z))
    S k hk hz.2.2
  have hSuniv : S = univ := singleBlock_eq_univ_of_generic_local_stabilizer
    hprime S k l hkl hk hl (κ z) hlocal hzg
  have hall (i j : Fin (d + 1)) : r i j := by
    have hi : i ∈ S := by rw [hSuniv]; trivial
    have hj : j ∈ S := by rw [hSuniv]; trivial
    exact r.trans hi (r.symm hj)
  refine ⟨inferInstance, right_invariant_of_all_roots (by have := hprime.two_le; omega) μ ?_⟩
  intro i j hij t
  exact ((rootInvarianceRelation_iff_full_root hij μ).mp ((hr i j).mp (hall i j))) t

/-- The geometric application requires symmetry of the actual root
invariance relation. Reflexivity and transitivity are already proved
from the concrete root group identities. -/
theorem isHaar_of_prime_symmetric_invariant_roots
    (d : ℕ) (hprime : (d + 1).Prime)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (hsymm : Std.Symm (rootInvarianceRelation μ))
    (hroot : ∃ i j, i ≠ j ∧ rootInvarianceRelation μ i j) :
    IsHaarProbability μ := by
  let r : Setoid (Fin (d + 1)) :=
    { r := rootInvarianceRelation μ
      iseqv := {
        refl := fun _ => Or.inl rfl
        symm := fun {i j} h => hsymm.symm i j h
        trans := fun {_ _ _} hij hjk => rootInvarianceRelation_trans μ hij hjk } }
  exact isHaar_of_prime_nontrivial_root_partition d hprime μ r
    (fun _ _ => Iff.rfl) hroot

/-- Symmetry of the invariant-root relation, together with the existence
of a nontrivial invariant root from positive entropy, gives prime-degree
Haar rigidity. -/
theorem eklPrimeInput_of_root_symmetry (d : ℕ)
    (hsymm : ∀ (μ : Measure (X (d + 1))), IsProbabilityMeasure μ →
      ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ →
        Std.Symm (rootInvarianceRelation μ)) :
    EKLPrimeInput d := by
  intro hprime hthree μ hμ hμerg hpos
  let : IsProbabilityMeasure μ := hμ
  let : ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ := hμerg
  obtain ⟨i, j, hij, hroot⟩ :=
    exists_invariant_root_of_positive_regular_entropy d (by omega) μ hpos
  apply isHaar_of_prime_symmetric_invariant_roots d hprime μ (hsymm μ hμ hμerg)
  exact ⟨i, j, hij, (rootInvarianceRelation_iff_full_root hij μ).mpr hroot⟩

end DukePrimeDegree

end

end OAI
