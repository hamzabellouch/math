import OAI.NumberTheory.DukePrimeDegree.Dynamics.BlockIncidentMautner
import OAI.NumberTheory.DukePrimeDegree.Dynamics.AlmostInvariantComponents
import OAI.NumberTheory.DukePrimeDegree.Dynamics.KernelStabilizerMeasurable

namespace OAI

/-!
# Incident invariant roots preserve canonical block components

Mautner fixes every block-invariant L² indicator along an incident
ambient invariant root. Almost invariance of the conditioning sigma
algebra then implies invariance of the same canonical component kernel.
No normalizer assertion and no reverse-root invariance is inserted.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma ae_incident_root_fixes_block_invariant_set {n : ℕ}
    (S : Set (Fin n)) (k l : Fin n) (hkl : k ≠ l) (hk : k ∈ S) (hl : l ∈ S)
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hSL : singleBlockRootGroup S ≤ invariantRightSubgroup μ)
    (p q : Fin n) (hpq : p ≠ q) (htouch : p ∈ S ∨ q ∈ S)
    (hU : ∀ t : ℝ, μ.map (fun x => rightAction x
      (SpecialLinearGroup.transvection hpq t)) = μ)
    (A : Set (X n)) (hA : MeasurableSet[actionInvariantSigma
      (singleBlockRootGroup S) (X n)] A) (t : ℝ) :
    (fun x => rightAction x (SpecialLinearGroup.transvection hpq t)) ⁻¹' A =ᵐ[μ] A := by
  let H := singleBlockRootGroup S
  have hAm : MeasurableSet A := (actionInvariantSigma_le H (X n)) A hA
  let f : X n → ℝ := A.indicator (fun _ => 1)
  have hf : MemLp f 2 μ := (memLp_const (1 : ℝ)).indicator hAm
  let F : Lp ℝ 2 μ := hf.toLp f
  have hF : (F : X n → ℝ) =ᵐ[μ] f := hf.coeFn_toLp
  have hHfix (h : H) : (fun x => F (rightAction x h.val)) =ᵐ[μ] F := by
    have hpH : MeasurePreserving (fun x => rightAction x h.val) μ μ :=
      ⟨(continuous_rightAction _).measurable, hSL h.property⟩
    have hpre : (fun x => rightAction x h.val) ⁻¹' A = A := by
      have he := ((iInf_le (fun g : H => MeasurableSpace.invariants
        (fun x : X n => g • x)) h⁻¹) A hA).2
      change (fun x => rightAction x ((h⁻¹).val)⁻¹) ⁻¹' A = A at he
      simpa only [Subgroup.coe_inv, inv_inv] using he
    filter_upwards [hpH.quasiMeasurePreserving.ae_eq_comp hF, hF] with x hleft hright
    simp only [Function.comp_apply] at hleft
    rw [hleft, hright]
    have hmem := Set.ext_iff.mp hpre x
    change (rightAction x h.val ∈ A ↔ x ∈ A) at hmem
    simp only [f, Set.indicator_apply, hmem]
  have hfixed := ae_incident_root_fixed_of_L2_block_fixed S k l hkl hk hl μ hSL
    F hHfix p q hpq htouch hU t
  have hpU : MeasurePreserving (fun x => rightAction x
      (SpecialLinearGroup.transvection hpq t)) μ μ :=
    ⟨(continuous_rightAction _).measurable, hU t⟩
  have hfU : (fun x => f (rightAction x (SpecialLinearGroup.transvection hpq t))) =ᵐ[μ] f :=
    (hpU.quasiMeasurePreserving.ae_eq_comp hF).symm.trans (hfixed.trans hF)
  apply Filter.Eventually.set_eq
  filter_upwards [hfU] with x hx
  change (rightAction x (SpecialLinearGroup.transvection hpq t) ∈ A ↔ x ∈ A)
  by_cases hleft : rightAction x (SpecialLinearGroup.transvection hpq t) ∈ A <;>
    by_cases hright : x ∈ A <;> simp_all [f]

/-- The same full-subgroup conditional measures used by the geometric
endpoint inherit all real parameters of the incident invariant root. -/
theorem ae_block_component_incident_root_invariant {n : ℕ}
    (S : Set (Fin n)) (k l : Fin n) (hkl : k ≠ l) (hk : k ∈ S) (hl : l ∈ S)
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hSL : singleBlockRootGroup S ≤ invariantRightSubgroup μ)
    (p q : Fin n) (hpq : p ≠ q) (htouch : p ∈ S ∨ q ∈ S)
    (hU : ∀ t : ℝ, μ.map (fun x => rightAction x
      (SpecialLinearGroup.transvection hpq t)) = μ) :
    ∀ᵐ z ∂μ.trim (actionInvariantSigma_le (singleBlockRootGroup S) (X n)),
      ∀ t : ℝ, (condExpKernel μ (actionInvariantSigma (singleBlockRootGroup S) (X n)) z).map
        (fun x => rightAction x (SpecialLinearGroup.transvection hpq t)) =
        condExpKernel μ (actionInvariantSigma (singleBlockRootGroup S) (X n)) z := by
  let m := actionInvariantSigma (singleBlockRootGroup S) (X n)
  let : MeasurableSpace (X n) := xMeasurableSpace n
  have hm : m ≤ xMeasurableSpace n := actionInvariantSigma_le (singleBlockRootGroup S) (X n)
  have hrat (r : ℚ) : ∀ᵐ z ∂μ.trim hm, (condExpKernel μ m z).map
      (fun x => rightAction x (SpecialLinearGroup.transvection hpq (r : ℝ))) =
      condExpKernel μ m z := by
    exact condExpKernel_invariant_of_ae_invariant_sets m μ hm
      ⟨(continuous_rightAction _).measurable, hU r⟩
      (fun A hA => ae_incident_root_fixes_block_invariant_set S k l hkl hk hl μ hSL
        p q hpq htouch hU A hA r)
  filter_upwards [ae_all_iff.mpr hrat] with z hz
  exact (all_root_mem_iff_rational_root_mem hpq (condExpKernel μ m z)).mpr hz

end DukePrimeDegree

end

end OAI
