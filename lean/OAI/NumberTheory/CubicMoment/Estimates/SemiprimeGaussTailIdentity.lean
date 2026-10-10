import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeBilinear
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstTailDecomposition

namespace OAI

/-! Exact independent-prime reconstruction of the actual Gauss-tail semiprime
term. Repeated primes vanish through the original Gauss kernel. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma scaleFirstTailKernel_outside_primeProductSupport (ℓ : ℤ) (H T : ℝ)
    {X : ℝ} (hX : 0 < X) {n : Eisenstein} (hn : primary n)
    (hout : n ∉ primeProductSupport X) :
    scaleFirstTailKernel ℓ H T X n = 0 := by
  by_cases hs : Squarefree n
  · have hz : primeProductEnvelope (norm n/X) = 0 := by
      by_cases hu : norm n ≤ 3*X
      · have hl : norm n < X/2 := lt_of_not_ge (fun hl => hout (Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr ⟨hn,hu⟩,hs⟩,hl⟩))
        exact primeProductEnvelope_zero_lower ((div_le_iff₀ hX).mpr (by linarith))
      · exact primeProductEnvelope_zero ((le_div_iff₀ hX).mpr (le_of_lt (lt_of_not_ge hu)))
    simp only [scaleFirstTailKernel,hz,mul_zero,zero_mul]
  · simp only [scaleFirstTailKernel,gauss_eq_zero_of_not_squarefree hn hs,mul_zero,zero_mul]

theorem scaleFirstTailSemiprimeWindow_eq_ordered (ℓ : ℤ) (H T : ℝ)
    {X : ℝ} (hX : 0 < X) :
    scaleFirstTailSemiprimeWindow ℓ H T X =
      (1/2:ℂ)*∑ f ∈ Fintype.piFinset (fun _ : Fin 2 => primeCutoff (3*X)),
        (∏ i, (1-(primeDetectorCutoff (norm (f i)/(X^(2/5:ℝ))):ℂ)))*
          scaleFirstTailKernel ℓ H T X (∏ i, f i) := by
  let S : Fin 2 → Finset Eisenstein := fun _ => primeCutoff (3*X)
  let w : Fin 2 → Eisenstein → ℂ := fun _ p =>
    1-(primeDetectorCutoff (norm p/(X^(2/5:ℝ))):ℂ)
  let K := scaleFirstTailKernel ℓ H T X
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
      rw [scaleFirstTailKernel_outside_primeProductSupport ℓ H T hX hp hout,mul_zero]
    · intro n _ _
      rfl
  calc
    _ = ∑ n ∈ primeProductSupport X,
        ((1/2:ℂ)*orderedConvolution S w n)*K n := by
      unfold scaleFirstTailSemiprimeWindow
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

theorem scaleFirstTailSemiprimeWindow_eq_bilinear (ℓ : ℤ) (H T : ℝ)
    {X : ℝ} (hX : 0 < X) :
    scaleFirstTailSemiprimeWindow ℓ H T X =
      (1/2:ℂ)*∑ p ∈ primeCutoff (3*X), ∑ q ∈ primeCutoff (3*X),
        semiprimeRoughWeight X p*semiprimeRoughWeight X q*
          scaleFirstTailKernel ℓ H T X (p*q) := by
  rw [scaleFirstTailSemiprimeWindow_eq_ordered ℓ H T hX]
  congr 1
  convert prime_pair_tuple_sum (primeCutoff (3*X))
    (fun p q => semiprimeRoughWeight X p*semiprimeRoughWeight X q*
      scaleFirstTailKernel ℓ H T X (p*q)) using 1
  apply Finset.sum_congr rfl
  intro f _
  simp only [Fin.prod_univ_two,semiprimeRoughWeight]


end CubicFirstMoment

end

end OAI
