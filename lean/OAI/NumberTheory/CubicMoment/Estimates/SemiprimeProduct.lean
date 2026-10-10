import OAI.NumberTheory.CubicMoment.Decomposition.PrimeProductDetector
import OAI.NumberTheory.CubicMoment.Estimates.PrimeTupleFiber
import OAI.NumberTheory.CubicMoment.Estimates.RoughPrimeTuples

namespace OAI

/-! The semiprime term in the exact detector is a genuine bilinear sum
over independent primary primes. The factor one half counts their two
orderings; repeated primes vanish in the original centered kernel. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma semiprime_ordered_coefficient {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) {B : ℝ} (hB : norm n ≤ B) (ψ : ℝ → ℝ) (y : ℝ) :
    (1/2:ℂ)*orderedConvolution (fun _ : Fin 2 => primeCutoff B)
      (fun _ p => 1-(ψ (norm p/y):ℂ)) n =
      if (primeFactors n).card = 2 then (roughProduct ψ y n:ℂ) else 0 := by
  rw [orderedConvolution_prime_fiber hn hs hB]
  by_cases hc : (primaryPrimeFactors n).card = 2
  · rw [← primaryPrimeFactors_card n,ite_eq_left hc]
    have he := roughProduct_ordered_primary_factors ψ y n
    rw [hc] at he
    simpa using he.symm
  · rw [← primaryPrimeFactors_card n,ite_eq_right hc]
    have he : IsEmpty (Fin 2 ≃ primaryPrimeFactors n) := ⟨fun e =>
      hc (by simpa using (Fintype.card_congr e).symm)⟩
    simp

lemma centeredHeightKernel_outside_primeProductSupport (ℓ : ℤ) (H T : ℝ)
    {X : ℝ} (hX : 0 < X) {n : Eisenstein} (hn : primary n)
    (hout : n ∉ primeProductSupport X) :
    centeredHeightKernel ℓ primeProductEnvelope H T X X n = 0 := by
  by_cases hs : Squarefree n
  · have hz : primeProductEnvelope (norm n/X) = 0 := by
      by_cases hu : norm n ≤ 3*X
      · have hl : norm n < X/2 := lt_of_not_ge (fun hl => hout (Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr ⟨hn,hu⟩,hs⟩,hl⟩))
        exact primeProductEnvelope_zero_lower ((div_le_iff₀ hX).mpr (by linarith))
      · exact primeProductEnvelope_zero ((le_div_iff₀ hX).mpr (le_of_lt (lt_of_not_ge hu)))
    simp only [centeredHeightKernel,hz,mul_zero,zero_mul]
  · simp only [centeredHeightKernel,centeredGauss_vanishes hn hs,mul_zero,zero_mul]

theorem centralSemiprimeProduct_eq_ordered (ℓ : ℤ) (H T : ℝ)
    {X : ℝ} (hX : 0 < X) :
    centralSemiprimeProduct ℓ H T X =
      (1/2:ℂ)*∑ f ∈ Fintype.piFinset (fun _ : Fin 2 => primeCutoff (3*X)),
        (∏ i, (1-(primeDetectorCutoff (norm (f i)/(X^(2/5:ℝ))):ℂ)))*
          centeredHeightKernel ℓ primeProductEnvelope H T X X (∏ i, f i) := by
  let S : Fin 2 → Finset Eisenstein := fun _ => primeCutoff (3*X)
  let w : Fin 2 → Eisenstein → ℂ := fun _ p =>
    1-(primeDetectorCutoff (norm p/(X^(2/5:ℝ))):ℂ)
  let K := centeredHeightKernel ℓ primeProductEnvelope H T X X
  have he : (∑ n ∈ primeProductSupport X, orderedConvolution S w n*K n) =
      ∑ n ∈ orderedConvolutionSupport S, orderedConvolution S w n*K n := by
    apply Finset.sum_congr_of_eq_on_inter
    · intro n _ hn
      rw [orderedConvolution_eq_zero_of_not_mem S w hn,zero_mul]
    · intro n hn hout
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hn
      have hp : primary (∏ i, f i) := primary_finset_prod _ _ (fun i _ =>
        (mem_primeCutoff.mp (Fintype.mem_piFinset.mp hf i)).1.1)
      dsimp only [K]
      rw [centeredHeightKernel_outside_primeProductSupport ℓ H T hX hp hout,mul_zero]
    · intro n _ _
      rfl
  calc
    _ = ∑ n ∈ primeProductSupport X,
        ((1/2:ℂ)*orderedConvolution S w n)*K n := by
      unfold centralSemiprimeProduct
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      have hp := primeProductSupport_spec hn
      rw [semiprime_ordered_coefficient hp.1 hp.2.1 hp.2.2.2]
      split_ifs
      · rfl
      · exact (zero_mul _).symm
    _ = (1/2:ℂ)*∑ n ∈ orderedConvolutionSupport S, orderedConvolution S w n*K n := by
      rw [← he,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = _ := by rw [orderedConvolution_sum]

end CubicFirstMoment

end

end OAI
