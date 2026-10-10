import Mathlib
import OAI.Probability.BinarySweep.FiniteLaws.LightLineBound

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {L A B : Type*} [Fintype L] [Fintype A] [Fintype B]

def occurrences (f : A → L) (l : L) : ℕ := Fintype.card {a : A // f a = l}

lemma sum_occurrences (f : A → L) : ∑ l, occurrences f l = Fintype.card A := by
  simpa only [occurrences,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using
    (Fintype.sum_fiberwise' f (fun _ : L => (1:ℕ)))

lemma prod_occurrences {R : Type*} [CommMonoid R] (f : A → L) (x : L → R) :
    (∏ a, x (f a)) = ∏ l, x l ^ occurrences f l := by
  simpa only [occurrences,Finset.prod_const,Finset.card_univ] using
    (Fintype.prod_fiberwise' f x).symm

lemma occurrenceMoment_eq (m h : L → ℕ) (f : A → L) (g : B → L) :
    multilineMoment m h ((∏ a, ((MvPolynomial.X (f a) : MvPolynomial L ℝ)-1)) *
      ∏ b, MvPolynomial.X (g b)) =
        ∏ l, centeredLineMoment (m l) (h l) (occurrences f l) (occurrences g l) := by
  rw [prod_occurrences (R := MvPolynomial L ℝ) f (fun l => MvPolynomial.X l-1), prod_occurrences (R := MvPolynomial L ℝ) g MvPolynomial.X,
    ← Finset.prod_mul_distrib]
  calc
    _ = multilineMoment m h (∏ l, (MvPolynomial.X l : MvPolynomial L ℝ)^occurrences g l *
        (MvPolynomial.X l-1)^occurrences f l) :=
      congrArg (multilineMoment m h) (Finset.prod_congr rfl (fun l _ => mul_comm _ _))
    _ = _ := multilineMoment_centered m h _ _

theorem occurrenceMoment_light (m h : L → ℕ) (f : A → L) (g : B → L)
    {η : ℝ} (hm : ∀ l, 0 < m l) (hη0 : 0 ≤ η) (hη : η ≤ 1/4)
    (hl : ∀ l, (h l:ℝ)+occurrences f l+occurrences g l ≤ m l*η) :
    0 ≤ multilineMoment m h ((∏ a, ((MvPolynomial.X (f a) : MvPolynomial L ℝ)-1)) *
      ∏ b, MvPolynomial.X (g b)) ∧
    multilineMoment m h ((∏ a, ((MvPolynomial.X (f a) : MvPolynomial L ℝ)-1)) *
      ∏ b, MvPolynomial.X (g b)) ≤
        2^(Fintype.card B) * (4*Real.sqrt η)^(Fintype.card A) := by
  rw [occurrenceMoment_eq]
  have hb (l : L) := centeredLineMoment_light (u := occurrences f l) (v := occurrences g l)
    (hm l) hη0 hη (hl l)
  refine ⟨Finset.prod_nonneg (fun l _ => (hb l).1), ?_⟩
  calc
    _ ≤ ∏ l, (2:ℝ)^occurrences g l * (4*Real.sqrt η)^occurrences f l :=
      Finset.prod_le_prod₀ (fun l _ => (hb l).1) (fun l _ => (hb l).2)
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,Finset.prod_pow_eq_pow_sum,
        sum_occurrences,sum_occurrences]

end BinaryCoordinateSweeps.Sparse

end

end OAI
