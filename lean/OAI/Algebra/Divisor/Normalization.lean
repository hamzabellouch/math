import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
namespace ControlledBoundary.FormalDivisor

variable {Prime : Type*}

def positivePart (D : Prime →₀ ℚ) : Prime →₀ ℚ :=
  D.mapRange (fun x => max x 0) (by simp)

def negativePart (D : Prime →₀ ℚ) : Prime →₀ ℚ :=
  D.mapRange (fun x => max (-x) 0) (by simp)

lemma positivePart_nonneg (D : Prime →₀ ℚ) : 0 ≤ positivePart D :=
  fun _ => le_max_right _ _

lemma negativePart_nonneg (D : Prime →₀ ℚ) : 0 ≤ negativePart D :=
  fun _ => le_max_right _ _

lemma signed_decomposition (D : Prime →₀ ℚ) :
    positivePart D - negativePart D = D := by
  ext p
  change max (D p) 0 - max (-D p) 0 = D p
  rcases le_total 0 (D p) with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
    ring

lemma positivePart_coeff_lt_one (D : Prime →₀ ℚ) (h : ∀ p, D p < 1) :
    ∀ p, positivePart D p < 1 := by
  intro p
  exact max_lt (h p) zero_lt_one

 

lemma negativePart_support_subset (D : Prime →₀ ℚ) (S : Finset Prime)
    (h : ∀ p, p ∉ S → 0 ≤ D p) : (negativePart D).support ⊆ S := by
  intro p hp
  by_contra hn
  have hz : negativePart D p = 0 := max_eq_right (neg_nonpos.mpr (h p hn))
  exact (Finsupp.mem_support_iff.mp hp) hz

 

lemma negativePart_signed_support [DecidableEq Prime] (G J K : Prime →₀ ℚ)
    (s : ℚ) (hs : 0 ≤ s) (hG : 0 ≤ G) :
    (negativePart (s • G - J - K)).support ⊆ J.support ∪ K.support := by
  classical
  apply negativePart_support_subset
  intro p hp
  have hJ : J p = 0 := Finsupp.notMem_support_iff.mp (fun h =>
    hp (Finset.mem_union_left _ h))
  have hK : K p = 0 := Finsupp.notMem_support_iff.mp (fun h =>
    hp (Finset.mem_union_right _ h))
  simpa only [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, hJ, hK, sub_zero]
    using mul_nonneg hs (hG p)

 

theorem normalize_correction {n : ℕ}
    (M F E C : Prime →₀ ℚ) (P : Fin n → Prime →₀ ℚ) (a : Fin n → ℚ)
    (t : ℚ) (ht : 0 < t) (hF : 0 ≤ F) (hE : 0 ≤ E)
    (hSupp : F.support ⊆ C.support)
    (hrep : E = t • M + F + ∑ j, a j • P j) :
    ∃ C₀ E₀ : Prime →₀ ℚ,
      0 ≤ C₀ ∧ C₀.support ⊆ C.support ∧ 0 ≤ E₀ ∧
      E₀ = M + C₀ + ∑ j, (t⁻¹ * a j) • P j := by
  refine ⟨t⁻¹ • F, t⁻¹ • E, ?_, ?_, ?_, ?_⟩
  · intro p
    exact mul_nonneg (inv_nonneg.mpr ht.le) (hF p)
  · exact (Finsupp.support_smul).trans hSupp
  · intro p
    exact mul_nonneg (inv_nonneg.mpr ht.le) (hE p)
  · rw [hrep, smul_add, smul_add, smul_smul, inv_mul_cancel₀ (ne_of_gt ht),
      one_smul, Finset.smul_sum]
    simp only [smul_smul]

end ControlledBoundary.FormalDivisor

end

end OAI
