import OAI.NumberTheory.CubicMoment.Angular.AngularSemiprimeSmoothed
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralAngularPrimeProductSmoothedBilinear

namespace OAI

noncomputable section
open Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)


theorem angular_semiprime_smoothed_log_saving_actual
    (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (k U : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ (H T : ℝ) (i j : ℕ) (u : ℝ),
      semiprimePartitionPiece ℓ H T X i j ≠ 0 → |u| ≤ (1+Real.log X)^U →
      ‖angularSemiprimeSmoothedPolynomial ℓ X i j u‖ ≤ K*X^(5/6:ℝ)/(1+Real.log X)^k := by
  let Γ := (Ici (0:ℝ) × Ici (1:ℝ)) × (Ici (0:ℝ) × Ici (1:ℝ))
  let LA : Γ → ℝ := fun z => z.1.2
  let LB : Γ → ℝ := fun z => z.2.2
  let WA : Γ → Unit → ℝ → ℂ := fun z _ => semiprimeSmoothWeight z.1.1
  let WB : Γ → Unit → ℝ → ℂ := fun z _ => semiprimeSmoothWeight z.2.1
  have hLA (z : Γ) : 1 ≤ LA z := z.1.2.property
  have hLB (z : Γ) : 1 ≤ LB z := z.2.2.property
  have hWA := uniformLogWeights_prime_coordinates LA
    (fun z : Γ => semiprimeSmoothWeight z.1.1) hLA
    (semiprimeSmoothWeights.reindex (fun z : Γ => z.1.1))
  have hWB := uniformLogWeights_prime_coordinates LB
    (fun z : Γ => semiprimeSmoothWeight z.2.1) hLB
    (semiprimeSmoothWeights.reindex (fun z : Γ => z.2.1))
  obtain ⟨η,G,K₀,B₀,hη,hη1,hK₀,hbound⟩ := angular_full_prime_centered_smoothed_bilinear_actual ℓ
    hSW hℓ hpub hHuxley hperiod hMV hC (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (1/2:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 2) hGI hGQ  hGamma
    LA LB WA WB hLA hLB hWA hWB
    (fun z _ _x hx => semiprimeSmoothWeight_low z.1.1 hx)
    (fun z _ _x hx => semiprimeSmoothWeight_high z.1.1 hx)
    (fun z _ _x hx => semiprimeSmoothWeight_low z.2.1 hx)
    (fun z _ _x hx => semiprimeSmoothWeight_high z.2.1 hx)
    (fun z _ x => semiprimeSmoothWeight_norm z.1.1 x)
    (fun z _ x => semiprimeSmoothWeight_norm z.2.1 x) k (U+1)
  refine ⟨K₀*3^(5/6:ℝ)/(39/100:ℝ)^k,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_semiprime_admissible hη G B₀,
    eventually_semiprime_height_comparison U,
    eventually_const_mul_rpow_le (by norm_num : (39/100:ℝ) < 2/5) 2]
    with X hX hadm hheight hlower
  intro H T i j u hne hu
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hordered (i j : ℕ) (hji : semiprimePartitionScale j ≤ semiprimePartitionScale i)
      (hne : semiprimePartitionPiece ℓ H T X i j ≠ 0) :
      ‖angularSemiprimeSmoothedPolynomial ℓ X i j u‖ ≤
        (K₀*3^(5/6:ℝ)/(39/100:ℝ)^k)*X^(5/6:ℝ)/(1+Real.log X)^k := by
    let A := semiprimePartitionScale i
    let B := semiprimePartitionScale j
    have hAp : 0 < A := semiprimePartitionScale_pos i
    have hBp : 0 < B := semiprimePartitionScale_pos j
    obtain ⟨hB₀,hrough,hAlo,hAhi⟩ := hadm ℓ H T i j hji hne
    obtain ⟨_,hAB,_,hBL⟩ := semiprimePartitionPiece_nonzero_lengths ℓ H T hXp hne
    have hBX : X^(39/100:ℝ) ≤ B := by dsimp [B]; linarith
    have hB1 : 1 ≤ B := (Real.one_le_rpow hX (by norm_num : (0:ℝ) ≤ 39/100)).trans hBX
    have hA1 : 1 ≤ A := hB1.trans hji
    let z : Γ := ((⟨A/X^(2/5:ℝ),by change 0 ≤ A/X^(2/5:ℝ); positivity⟩,⟨A,hA1⟩),
      (⟨B/X^(2/5:ℝ),by change 0 ≤ B/X^(2/5:ℝ); positivity⟩,⟨B,hB1⟩))
    have hb := hbound z (fun _ => A) (fun _ => B) X u hB₀ (by simp [LA,z])
      (by simp [LB,z]) (fun _ => hA1) (fun _ => hrough) hAlo hAhi hXp
      (hu.trans (hheight B hBX))
    rw [angularSemiprimeSmoothedPolynomial_full]
    apply le_trans (by simpa only [WA,WB,LA,LB,z,Fintype.prod_unique] using hb)
    exact semiprime_bilinear_scale hX hAp.le hBX hK₀.le hAB k
  by_cases hji : semiprimePartitionScale j ≤ semiprimePartitionScale i
  · exact hordered i j hji hne
  · rw [angularSemiprimeSmoothedPolynomial_symm]
    apply hordered j i (le_of_not_ge hji)
    rwa [semiprimePartitionPiece_symm ℓ H T X j i]

end CubicFirstMoment

end

end OAI
