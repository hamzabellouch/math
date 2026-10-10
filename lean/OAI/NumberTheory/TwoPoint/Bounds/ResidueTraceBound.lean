import OAI.NumberTheory.TwoPoint.Bounds.UniformResidues
import OAI.NumberTheory.TwoPoint.Bounds.DesignationWeights

namespace OAI

/-! The manuscript's designated-term majorant for actual uniform residues. -/

namespace TwoPointCorrelations

open Finset

variable {ι τ : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- The exact reciprocal coefficient of one lit/unlit designation,
including the singleton atoms. -/
noncomputable def designatedReciprocal (p : ι → ℕ) (S : Finset ι)
    (L U : Finset τ) (label : τ → ι) : ℝ :=
  (∏ t ∈ U, (p (label t) : ℝ)⁻¹) *
    (∏ i ∈ L.image label, (p i : ℝ)⁻¹) * (∏ i ∈ S, (p i : ℝ)⁻¹)

/-- Singleton integration and lit forcing are carried out on one common
residue sample. The unlit slots impose no further residue condition. -/
theorem uniform_designated_trace_bound (B : ℕ) (p : ι → ℕ)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (S : Finset ι) (L U : Finset τ) (label : τ → ι) (target : τ → Fin B)
    (a base : ι → Fin B) (R : ℝ) (G : (ι → Fin B) → ℝ)
    (hR : 0 ≤ R) (hL : LitConsistent L label target)
    (hSL : Disjoint S (L.image label))
    (ha : ∀ i ∈ S, (a i).val < p i)
    (htarget : ∀ t ∈ L, (target t).val < p (label t)) :
    |(FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun x => (R * ((-1 : ℝ) ^ U.card * ∏ t ∈ U, (p (label t) : ℝ)⁻¹)) *
        ((∏ t ∈ L, if x (label t) = target t then (1 : ℝ) else 0) *
          ((∏ i ∈ S, ((if x i = a i then (1 : ℝ) else 0) - (p i : ℝ)⁻¹)) * G x)))| ≤
      R * designatedReciprocal p S L U label *
        (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
          (fun x => |selectedMixedDifference S a
            (fun x => G (forceCoordinates (L.image label)
              (litForcedTarget L label target base) x)) x|) := by
  let μ := fun i => uniformResidueLaw B (p i) (hp i) (hpB i)
  have hs : ∀ x : ι → Fin B,
      (∏ i ∈ S, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i))) =
        ∏ i ∈ S, ((if x i = a i then (1 : ℝ) else 0) - (p i : ℝ)⁻¹) := by
    intro x
    apply prod_congr rfl
    intro i hi
    rw [uniformResidueLaw_weight B (p i) (hp i) (hpB i) (a i) (ha i hi)]
  have hsp : (∏ i ∈ S, (μ i).weight (a i)) = ∏ i ∈ S, (p i : ℝ)⁻¹ := by
    apply prod_congr rfl
    intro i hi
    exact uniformResidueLaw_weight B (p i) (hp i) (hpB i) (a i) (ha i hi)
  have hlp : (∏ i ∈ L.image label, (μ i).weight (litForcedTarget L label target base i)) =
      ∏ i ∈ L.image label, (p i : ℝ)⁻¹ := by
    apply prod_congr rfl
    intro i hi
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hi
    rw [litForcedTarget_at L label target base hL t ht]
    exact uniformResidueLaw_weight B (p (label t)) (hp _) (hpB _) _ (htarget t ht)
  have hc : |R * ((-1 : ℝ) ^ U.card * ∏ t ∈ U, (p (label t) : ℝ)⁻¹)| =
      R * ∏ t ∈ U, (p (label t) : ℝ)⁻¹ := by
    rw [abs_mul, abs_of_nonneg hR,
      absolute_unlit_coefficient U label (fun i => (p i : ℝ)⁻¹)
        (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _))]
  have hb := designated_residue_bound μ S L label target a base
    (R * ((-1 : ℝ) ^ U.card * ∏ t ∈ U, (p (label t) : ℝ)⁻¹)) G hL hSL
  simp only [hs, hc, hsp, hlp] at hb
  simpa only [designatedReciprocal, mul_assoc] using hb

end TwoPointCorrelations

end OAI
