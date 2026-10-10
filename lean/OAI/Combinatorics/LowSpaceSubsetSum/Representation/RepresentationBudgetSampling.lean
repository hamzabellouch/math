import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationBudgets

namespace OAI

/-! # The resource bound for the actual dependent sampling experiment -/

noncomputable section

namespace LowSpaceSubsetSum

theorem prefix_floor_modulus_lower {a b c u : ℕ} (hu : 256 ≤ u)
    (ha : a ≤ u) (hb : b ≤ u) (hc : c ≤ u)
    (z : ↥(tripleRange a b c)) (i : Fin 3) :
    (2 : ℝ) ^ (prefixExponent a b c i : ℝ) / (u : ℝ) ^ 5 ≤ prefixModulus z.val i := by
  obtain ⟨hab, hcz⟩ := Finset.mem_product.mp z.property
  obtain ⟨haz, _hbz⟩ := Finset.mem_product.mp hab
  fin_cases i
  · have h := nested_size_bounds (L := ((a + b + c : ℕ) : ℝ)) hu ha hb hc
      le_rfl (by push_cast; linarith) z.property
    exact h.1
  · have hz : (z.val.1, 1) ∈ tripleRange a b 0 := by
      exact Finset.mem_product.mpr ⟨hab, by simp [factorRange]⟩
    have h := nested_size_bounds (L := ((a + b : ℕ) : ℝ)) hu ha hb (by omega)
      (by simp) (by push_cast; linarith) hz
    change (2 : ℝ) ^ ((a + b : ℕ) : ℝ) / (u : ℝ) ^ 5 ≤ (z.val.1.1 * z.val.1.2 : ℕ)
    simpa only [tripleModulus, mul_one] using h.1
  · have hz : ((z.val.1.1, 1), 1) ∈ tripleRange a 0 0 := by
      exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨haz, by simp [factorRange]⟩, by simp [factorRange]⟩
    have h := nested_size_bounds (L := (a : ℝ)) hu ha (by omega) (by omega)
      (by simp) (by push_cast; linarith) hz
    change (2 : ℝ) ^ (a : ℝ) / (u : ℝ) ^ 5 ≤ z.val.1.1
    simpa only [tripleModulus, mul_one] using h.1

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

theorem actual_modulus_floor_lower (z : Layout n) (p : R.PrimeSpace z)
    (hu : 256 ≤ inputScale R.input) (i : Fin 3) :
    (2 : ℝ) ^ (⌊R.lowExponent z i⌋₊ : ℝ) / (inputScale R.input : ℝ) ^ 5 ≤
      prefixModulus p.val i := by
  have h := prefix_floor_modulus_lower hu (R.factorExponents_le_scale z 0)
    (R.factorExponents_le_scale z 1) (R.factorExponents_le_scale z 2) p i
  rw [R.prefixExponent_eq_floor] at h
  exact h

def AllocatedResourceGood (hn : 20000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (h : R.TrialHistory) : Prop :=
  let z := h.1.1.1.1
  let g := h.1.1.1.2
  let f := h.1.1.2
  let p := h.1.2
  let B := R.allocatedBackground z g (by omega) hlog
  RepresentationMoments.GoodResource (prefixModulus_pos p 0) (prefixModulus_pos p 1)
    (prefixModulus_pos p 2) (R.signedWeights z) (R.rawLeaf z g f B 0)
    (R.rawLeaf z g f B 1) (R.signedTarget z) (inputScale R.input)
    (R.resourceGamma z) (R.resourceLambda z g) ((n : ℝ) / 2) h.2

/-- Every actual prime history has the resource tail estimate before observing
its independently uniform low residues. -/
theorem actual_history_resource_failure (hn : 20000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hu : 256 ≤ inputScale R.input) (h : R.PrimeHistory) :
    finiteUniformProbability (fun r : R.Residues h.2 =>
      ¬R.AllocatedResourceGood hn hlog ⟨h, r⟩) <
      (1 / 10 : ℝ) / (inputScale R.input : ℝ) ^ 100 := by
  exact R.allocated_resource_failure (prefixModulus_pos h.2 0) (prefixModulus_pos h.2 1)
    (prefixModulus_pos h.2 2) h.1.1.1 h.1.1.2 h.1.2 hn hlog
    (by exact_mod_cast (show 8 ≤ inputScale R.input by omega)) R.mixerSize_add_one_le_scale
    (R.actual_modulus_floor_lower h.1.1.1 h.2 hu 0)
    (R.actual_modulus_floor_lower h.1.1.1 h.2 hu 1)
    (R.actual_modulus_floor_lower h.1.1.1 h.2 hu 2)

/-- Joint failure with any event fixed before the low residues is small.
In particular this applies to the spread-test event, without conditioning
on the rare surviving representation. -/
theorem actual_joint_resource_failure (hn : 20000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hu : 256 ≤ inputScale R.input) (passing : R.PrimeHistory → Prop) :
    R.trialLaw.probability (fun h => passing h.1 ∧ ¬R.AllocatedResourceGood hn hlog h) ≤
      (1 / 10 : ℝ) / (inputScale R.input : ℝ) ^ 100 := by
  exact RepresentationMoments.joint_failure_average R.primeLaw (fun h => R.Residues h.2)
    passing (fun h r => ¬R.AllocatedResourceGood hn hlog ⟨h, r⟩) (by positivity)
    (fun h _ => (R.actual_history_resource_failure hn hlog hu h).le)

end RepresentationSetup

end LowSpaceSubsetSum

end

end OAI
