import OAI.NumberTheory.CubicMoment.Estimates.SievedDispersion
import OAI.NumberTheory.CubicMoment.Estimates.SieveResidue

namespace OAI

/-! Exact finite sieve assembly and its error norm. These identities
retain the actual joined square divisors and their Möbius weights. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma collectedSieve_weighted_sum (C : Finset Eisenstein) (F : Eisenstein → ℂ) :
    (∑ d ∈ (C.product C).image (fun t => primarySquarefreeJoin t.1 t.2),
      (collectedSquarefreeSieveCoefficient C d:ℂ)*F d) =
    ∑ c ∈ C, ∑ d ∈ C, (idealMoebius c:ℂ)*(idealMoebius d:ℂ)*F (primarySquarefreeJoin c d) := by
  let J := fun t : Eisenstein × Eisenstein => primarySquarefreeJoin t.1 t.2
  let v := fun t : Eisenstein × Eisenstein => (idealMoebius t.1:ℂ)*(idealMoebius t.2:ℂ)
  have hf := Finset.sum_fiberwise_of_maps_to (s := C.product C) (t := (C.product C).image J)
    (g := J) (fun t ht => Finset.mem_image_of_mem J ht) (fun t => v t*F (J t))
  calc
    _ = ∑ d ∈ (C.product C).image J,
        ∑ t ∈ (C.product C).filter (fun t => J t = d), v t*F (J t) := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [collectedSquarefreeSieveCoefficient,Complex.ofReal_sum,Complex.ofReal_mul,
        Complex.ofReal_intCast,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t ht
      dsimp only [v,J]
      rw [(Finset.mem_filter.mp ht).2]
    _ = ∑ t ∈ C.product C, v t*F (J t) := hf
    _ = _ := Finset.sum_product _ _ _

lemma sievedDispersionVariance_pair_sum (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c)
    (S : Finset Eisenstein) (hS : ∀ a ∈ S, primary a)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {A : ℝ} (hA : 0 < A) :
    sievedDispersionVariance C S β u W A =
      ∑ c ∈ C, ∑ d ∈ C, (idealMoebius c:ℂ)*(idealMoebius d:ℂ)*
        divisorDispersionVariance (primarySquarefreeJoin c d) S β u W A := by
  rw [sievedDispersionVariance_eq C hC S hS β u W hW hW' hA]
  exact collectedSieve_weighted_sum C _

def finiteSieveDensity (C : Finset Eisenstein) : ℝ :=
  ∑ c ∈ C, ∑ d ∈ C, (idealMoebius c:ℝ)*(idealMoebius d:ℝ)/
    (norm (primarySquarefreeJoin c d))^2

lemma finiteSieve_model_identity (C : Finset Eisenstein) (M : ℂ) :
    (finiteSieveDensity C:ℂ)*M =
      ∑ c ∈ C, ∑ d ∈ C, (idealMoebius c:ℂ)*(idealMoebius d:ℂ)*
        ((1/(norm (primarySquarefreeJoin c d))^2:ℝ):ℂ)*M := by
  simp only [finiteSieveDensity,Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_mul,
    Complex.ofReal_intCast,Complex.ofReal_one,Complex.ofReal_pow,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  ring

lemma sieved_model_error_bound (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c)
    (S : Finset Eisenstein) (hS : ∀ a ∈ S, primary a)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {A : ℝ} (hA : 0 < A)
    (M : ℂ) {E : ℝ}
    (herror : ∀ c ∈ C, ∀ d ∈ C,
      ‖divisorDispersionVariance (primarySquarefreeJoin c d) S β u W A-
        ((1/(norm (primarySquarefreeJoin c d))^2:ℝ):ℂ)*M‖ ≤ E) :
    ‖sievedDispersionVariance C S β u W A-(finiteSieveDensity C:ℂ)*M‖ ≤
      (C.card:ℝ)^2*E := by
  rw [sievedDispersionVariance_pair_sum C hC S hS β u W hW hW' hA,
    finiteSieve_model_identity,← Finset.sum_sub_distrib]
  have hs (c : Eisenstein) (hc : c ∈ C) :
      ‖(∑ d ∈ C, (idealMoebius c:ℂ)*(idealMoebius d:ℂ)*
        divisorDispersionVariance (primarySquarefreeJoin c d) S β u W A)-
        ∑ d ∈ C, (idealMoebius c:ℂ)*(idealMoebius d:ℂ)*
          ((1/(norm (primarySquarefreeJoin c d))^2:ℝ):ℂ)*M‖ ≤ ∑ _d ∈ C, E := by
    rw [← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro d hd
    rw [show (idealMoebius c:ℂ)*(idealMoebius d:ℂ)*
        divisorDispersionVariance (primarySquarefreeJoin c d) S β u W A-
        (idealMoebius c:ℂ)*(idealMoebius d:ℂ)*
          ((1/(norm (primarySquarefreeJoin c d))^2:ℝ):ℂ)*M =
        ((idealMoebius c:ℂ)*(idealMoebius d:ℂ))*
          (divisorDispersionVariance (primarySquarefreeJoin c d) S β u W A-
            ((1/(norm (primarySquarefreeJoin c d))^2:ℝ):ℂ)*M) by ring,
      norm_mul,norm_mul]
    apply (mul_le_of_le_one_left (_root_.norm_nonneg _) _).trans (herror c hc d hd)
    simpa only [one_mul] using mul_le_mul (norm_idealMoebius_le_one c)
      (norm_idealMoebius_le_one d) (_root_.norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum hs).trans_eq
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

end CubicFirstMoment

end

end OAI
