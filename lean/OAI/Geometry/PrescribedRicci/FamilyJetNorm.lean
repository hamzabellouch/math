import Mathlib
import OAI.Geometry.PrescribedRicci.DiscreteManyProduct
import OAI.Geometry.PrescribedRicci.JetTameProduct

namespace OAI

/-! Family Jet Norm. -/

section

 

noncomputable section
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Classical BigOperators
namespace TameInterpolation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]

def familyJetNorm (e : ι → E) (f : κ → E → ℝ) (j : ℕ) (p : ℝ≥0∞) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a : κ => jetNorm e (f a) j p)

lemma jetNorm_le_family (e : ι → E) (f : κ → E → ℝ) (a : κ) (j : ℕ) (p : ℝ≥0∞) :
    jetNorm e (f a) j p ≤ familyJetNorm e f j p := by
  exact Finset.le_sup' (fun a : κ => jetNorm e (f a) j p) (Finset.mem_univ a)

lemma familyJetNorm_nonneg (e : ι → E) (f : κ → E → ℝ) (j : ℕ) (p : ℝ≥0∞) :
    0 ≤ familyJetNorm e f j p :=
  (jetNorm_nonneg e (f (Classical.choice ‹Nonempty κ›)) j p).trans (jetNorm_le_family _ _ _ _ _)

lemma familyJetNorm_attained (e : ι → E) (f : κ → E → ℝ) (j : ℕ) (p : ℝ≥0∞) :
    ∃ a : κ, familyJetNorm e f j p = jetNorm e (f a) j p := by
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_sup' (s:=Finset.univ) Finset.univ_nonempty
    (fun a : κ => jetNorm e (f a) j p)
  exact ⟨a,ha⟩

lemma familyJetNorm_recurrence (e : ι → E) (f : κ → E → ℝ)
    (hf : ∀ a, ContDiff ℝ ∞ (f a)) (hc : ∀ a, HasCompactSupport (f a))
    (m : ℕ) (hm : 0 < m) (j : ℕ) (hj : j+2 ≤ m) :
    (familyJetNorm e f (j+1) (exponent m (j+1)))^2 ≤
    (2*(m:ℝ))*familyJetNorm e f j (exponent m j)*familyJetNorm e f (j+2) (exponent m (j+2)) := by
  obtain ⟨a,ha⟩ := familyJetNorm_attained e f (j+1) (exponent m (j+1))
  rw [ha]
  apply (jet_exponent_recurrence e (hf a) (hc a) m hm j hj).trans
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (jetNorm_le_family _ _ _ _ _) (by positivity))
    (jetNorm_le_family _ _ _ _ _) (jetNorm_nonneg _ _ _ _) (mul_nonneg (by positivity) (familyJetNorm_nonneg _ _ _ _))

lemma exponent_top {m : ℕ} (hm : 0 < m) : exponent m m = 2 := by
  rw [exponent_of_pos hm hm]
  have hmn : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [mul_div_cancel_right₀ _ hmn]
  norm_num

theorem family_jet_tame_many (e : ι → E) (f : κ → E → ℝ)
    (hf : ∀ a, ContDiff ℝ ∞ (f a)) (hc : ∀ a, HasCompactSupport (f a))
    (m : ℕ) (hm : 0 < m) {ν : Type*} (s : Finset ν) (j : ν → ℕ)
    (hs : ∑ i ∈ s, j i = m) :
    ∏ i ∈ s, familyJetNorm e f (j i) (exponent m (j i)) ≤
    (2*(m:ℝ))^(∑ i ∈ s, j i*(m-j i))*(familyJetNorm e f 0 ∞)^(s.card-1)*familyJetNorm e f m 2 := by
  have hC : 1 ≤ 2*(m:ℝ) := by
    have : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    linarith only [this]
  simpa only [exponent_zero,exponent_top hm] using nonnegative_sequence_many m hm
    (fun i => familyJetNorm e f i (exponent m i)) (fun _ => familyJetNorm_nonneg _ _ _ _)
    (2*(m:ℝ)) hC (familyJetNorm_recurrence e f hf hc m hm) s j hs
end TameInterpolation

end
end

end OAI
