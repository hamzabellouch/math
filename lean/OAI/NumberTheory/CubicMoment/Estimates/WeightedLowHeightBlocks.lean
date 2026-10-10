import OAI.NumberTheory.CubicMoment.Estimates.SmallBCoreHybrid
import OAI.NumberTheory.CubicMoment.Estimates.WeightedSquarefreeMean

namespace OAI

/-! The low-height noncube moment with an explicit core cutoff. The small
cores use a summed divisor moment; no length-to-a-small-power loss remains. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem smallB_noncube_weighted_blocks
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ (K : ℝ), 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B V T u : ℝ) (ℓ : ℤ), 65536 ≤ (Z:ℝ) → 0 ≤ B → 0 < V → 0 < T →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      8*B ≤ (Z:ℝ)^(3/4:ℝ) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ a : Eisenstein, a^3 = h) →
      dyadicHeightMean (fun t => ∑ h ∈ H,
        ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
        K*B^(1/3:ℝ)*((∑ b ∈ S, (4:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2)*(1+(Z:ℝ)/T)*V+
          ((largeCoreDyadicIndices V B).card:ℝ)*
            ((Z:ℝ)*(V/5832)^(-(1/4:ℝ))+(Z:ℝ)^(1-1/20000:ℝ))*
              ∑ b ∈ S, ‖β b‖^2) := by
  obtain ⟨Kh,hKh,hcore⟩ := smallB_core_hybrid_sieve hHuxley
  refine ⟨648*C+2*Kh,by positivity,?_⟩
  intro S H β Z B V T u ℓ hZ hB hV hT hS hsize hH
  let N : ℝ := Z
  let E := ∑ b ∈ S, ‖β b‖^2
  let E₄ := ∑ b ∈ S, (4:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2
  let I := largeCoreDyadicIndices V B
  let HS := H.filter (fun h => h ∈ lowNoncubeSupport V (B^(1/3:ℝ)))
  let P := fun h t => ∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)
  let F := fun (J : Finset Eisenstein) t => ∑ h ∈ J, ‖P h t‖^2
  let A := E₄*(1+N/T)*V
  let R := (I.card:ℝ)*(N*(V/5832)^(-(1/4:ℝ))+N^(1-1/20000:ℝ))*E
  have hNp : 0 < N := by dsimp [N]; linarith
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hE₄ : 0 ≤ E₄ := Finset.sum_nonneg (fun _ _ => by positivity)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hcont (J : Finset Eisenstein) : Continuous (F J) := by
    exact continuous_finsetSum J (fun h _ => (continuous_finite_character_height S β h ℓ u).norm.pow 2)
  have hsmall : dyadicHeightMean (F HS) T ≤ (648*C)*B^(1/3:ℝ)*A := by
    have hm := squarefree_weighted_character_height hMV hC hT S HS β Z hS u ℓ
    have hcard : (HS.card:ℝ) ≤ 324*V*B^(1/3:ℝ) :=
      (Nat.cast_le.mpr (Finset.card_le_card (fun h hh => (Finset.mem_filter.mp hh).2))).trans
        (lowNoncubeSupport_card hV.le (Real.rpow_nonneg hB _))
    have hp := mul_le_mul_of_nonneg_left hcard
      (show 0 ≤ 2*C*(1+(Z:ℝ)/T)*E₄ by positivity)
    apply hm.trans
    convert hp using 1; dsimp [A,N,E₄]; ring
  have hrow (z : ℕ × ℕ) (hz : z ∈ I) :
      dyadicHeightMean (F (coreDyadicBlock B z.1 z.2)) T ≤
        2*Kh*B^(1/3:ℝ)*(N*(V/5832)^(-(1/4:ℝ))+N^(1-1/20000:ℝ))*E := by
    have hd := (Finset.mem_filter.mp hz).2
    apply (dyadicHeightMean_le_const (hcont _) hT
      (C := Kh*B^(1/3:ℝ)*(N*(V/5832)^(-(1/4:ℝ))+N^(1-1/20000:ℝ))*E)
      (fun t _ => ?_)).trans_eq (by ring)
    let γ := fun b => β b*theta ℓ b*mellinPhase (t+u) (norm b)
    have hγ : (∑ b ∈ S, ‖γ b‖^2) = E := by
      apply Finset.sum_congr rfl
      intro b hb
      simp only [γ,norm_mul,norm_theta (primary_ne_zero (hS b hb).1),mellinPhase_norm,mul_one]
    have heq (h : Eisenstein) : (∑ b ∈ S, γ b*cubicSymbol b h) = P h t := by
      apply Finset.sum_congr rfl
      intro b _
      dsimp [γ,P]
      ring
    have hh := hcore S (coreDyadicBlock B z.1 z.2) γ N B V z.1 z.2 hZ hB hV hS hd.1.le
      ((mul_le_mul_of_nonneg_left hd.2 (by norm_num : (0:ℝ) ≤ 8)).trans hsize)
      (Finset.Subset.refl _)
    simp_rw [heq] at hh
    rw [hγ] at hh
    exact hh
  have hlarge : (∑ z ∈ I, dyadicHeightMean (F (coreDyadicBlock B z.1 z.2)) T) ≤
      (2*Kh)*B^(1/3:ℝ)*R := by
    apply (Finset.sum_le_sum (fun z hz => hrow z hz)).trans_eq
    simp only [Finset.sum_const,nsmul_eq_mul]
    dsimp [R]
    ring
  have hsplit : dyadicHeightMean (F H) T ≤ dyadicHeightMean (F HS) T+
      ∑ z ∈ I, dyadicHeightMean (F (coreDyadicBlock B z.1 z.2)) T := by
    have hm := dyadicHeightMean_mono (hcont H)
      ((hcont HS).add (continuous_finsetSum I (fun z _ => hcont _))) hT
      (g := fun t => F HS t+∑ z ∈ I, F (coreDyadicBlock B z.1 z.2) t)
      (fun t _ => noncube_frequency_mass_split H hH (fun h => ‖P h t‖^2) (fun _ => sq_nonneg _))
    rw [dyadicHeightMean_add (hcont HS) (continuous_finsetSum I (fun z _ => hcont _)),
      dyadicHeightMean_sum I (fun z => F (coreDyadicBlock B z.1 z.2)) (fun z _ => hcont _)] at hm
    exact hm
  apply hsplit.trans ((add_le_add hsmall hlarge).trans ?_)
  change (648*C)*B^(1/3:ℝ)*A+(2*Kh)*B^(1/3:ℝ)*R ≤
    (648*C+2*Kh)*B^(1/3:ℝ)*(A+R)
  nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 648*C) (Real.rpow_nonneg hB (1/3:ℝ))) hR,
    mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2*Kh) (Real.rpow_nonneg hB (1/3:ℝ))) hA]

end CubicFirstMoment

end

end OAI
