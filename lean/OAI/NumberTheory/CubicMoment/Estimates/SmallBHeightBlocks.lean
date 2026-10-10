import OAI.NumberTheory.CubicMoment.Estimates.SmallBCoreBlock
import OAI.NumberTheory.CubicMoment.Estimates.ArbitraryHeightMean

namespace OAI

/-! Combining the actual small-core height mean and the uniform remaining
core estimate. Sharp coefficient supports and arbitrary height shifts remain. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem smallB_noncube_height_blocks
    {C ε : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B V T u : ℝ) (ℓ : ℤ), 1 ≤ (Z:ℝ) → 0 ≤ B → 0 < V → 0 < T →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      8*B ≤ (Z:ℝ)^(3/4:ℝ) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ a : Eisenstein, a^3 = h) →
      dyadicHeightMean (fun t => ∑ h ∈ H,
        ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
      K*B^(1/3:ℝ)*(∑ b ∈ S, ‖β b‖^2)*
        ((Z:ℝ)^ε*V*(1+(Z:ℝ)/T)+
          ((largeCoreDyadicIndices V B).card:ℝ)*(Z:ℝ)^(2*ε)*
            ((Z:ℝ)/(V/5832)^(1/3:ℝ)+(Z:ℝ)^(23/24:ℝ))) := by
  obtain ⟨D,hD,hmean⟩ := arbitrary_primary_height_mean hMV hC hε
  obtain ⟨K,hK,hcore⟩ := smallB_core_block_sieve hHuxley hε
  let K₀ := 648*C*D+2*K
  refine ⟨K₀,by dsimp [K₀]; positivity,?_⟩
  intro S H β Z B V T u ℓ hZ hB hV hT hS hsize hH
  let N : ℝ := Z
  let E := ∑ b ∈ S, ‖β b‖^2
  let I := largeCoreDyadicIndices V B
  let HS := H.filter (fun h => h ∈ lowNoncubeSupport V (B^(1/3:ℝ)))
  let P := fun h t => ∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)
  let F := fun (J : Finset Eisenstein) t => ∑ h ∈ J, ‖P h t‖^2
  have hN : 0 ≤ N := Nat.cast_nonneg Z
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcont (J : Finset Eisenstein) : Continuous (F J) := by
    exact continuous_finsetSum J (fun h _ => (continuous_finite_character_height S β h ℓ u).norm.pow 2)
  have hNorm : ∀ b ∈ S, normNat b ∈ Finset.Icc 1 Z := by
    intro b hb
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr (normNat_ne_zero (primary_ne_zero (hS b hb).1))
    · have hbN := (hS b hb).2.2
      rw [← normNat_cast b] at hbN
      exact_mod_cast hbN
  have hsmall : dyadicHeightMean (F HS) T ≤
      (648*C*D)*B^(1/3:ℝ)*E*(N^ε*V*(1+N/T)) := by
    have hm := hmean S HS β Z (fun b hb => (hS b hb).1) hNorm ℓ u T hT
    have hcard : (HS.card:ℝ) ≤ 324*V*B^(1/3:ℝ) :=
      (Nat.cast_le.mpr (Finset.card_le_card (fun h hh => (Finset.mem_filter.mp hh).2))).trans
        (lowNoncubeSupport_card hV.le (Real.rpow_nonneg hB _))
    have hm' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcard (show 0 ≤ 2*C*D*(1+N/T)*N^ε by positivity)) hE
    apply hm.trans
    convert hm' using 1
    dsimp [N,E]
    ring
  have hrow (z : ℕ × ℕ) (hz : z ∈ I) :
      dyadicHeightMean (F (coreDyadicBlock B z.1 z.2)) T ≤
        2*K*N^(2*ε)*B^(1/3:ℝ)*
          (N/(V/5832)^(1/3:ℝ)+N^(23/24:ℝ))*E := by
    have hd := (Finset.mem_filter.mp hz).2
    have hp : 0 < V/5832 := by positivity
    have hroot := Real.rpow_le_rpow hp.le hd.1.le (by norm_num : (0:ℝ) ≤ 1/3)
    have hratio : N/(coreDyadicConductor z.1 z.2)^(1/3:ℝ) ≤ N/(V/5832)^(1/3:ℝ) :=
      div_le_div_of_nonneg_left hN (Real.rpow_pos_of_pos hp _) hroot
    have havg : dyadicHeightMean (F (coreDyadicBlock B z.1 z.2)) T ≤
        2*(K*N^(2*ε)*B^(1/3:ℝ)*(N/(V/5832)^(1/3:ℝ)+N^(23/24:ℝ))*E) := by
      apply dyadicHeightMean_le_const (hcont _) hT
      intro t _
      let γ := fun b => β b*theta ℓ b*mellinPhase (t+u) (norm b)
      have hγ : (∑ b ∈ S, ‖γ b‖^2) = E := by
        apply Finset.sum_congr rfl
        intro b hb
        simp only [γ,norm_mul,norm_theta (primary_ne_zero (hS b hb).1),mellinPhase_norm,mul_one]
      have heq (h : Eisenstein) : (∑ b ∈ S, γ b*cubicSymbol b h) = P h t := by
        apply Finset.sum_congr rfl
        intro b hb
        dsimp [γ,P]
        ring
      have hh := hcore S (coreDyadicBlock B z.1 z.2) γ N B z.1 z.2 hZ hB hS
        ((mul_le_mul_of_nonneg_left hd.2 (by norm_num : (0:ℝ) ≤ 8)).trans hsize)
        (Finset.Subset.refl _)
      simp_rw [heq] at hh
      rw [hγ] at hh
      change F (coreDyadicBlock B z.1 z.2) t ≤ _ at hh
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add hratio (le_refl (N^(23/24:ℝ))))
          (show 0 ≤ K*N^(2*ε)*B^(1/3:ℝ) by positivity)) hE
      exact hh.trans hm
    exact havg.trans_eq (by ring)
  have hlarge : (∑ z ∈ I, dyadicHeightMean (F (coreDyadicBlock B z.1 z.2)) T) ≤
      (2*K)*B^(1/3:ℝ)*E*((I.card:ℝ)*N^(2*ε)*(N/(V/5832)^(1/3:ℝ)+N^(23/24:ℝ))) := by
    apply (Finset.sum_le_sum (fun z hz => hrow z hz)).trans_eq
    simp only [Finset.sum_const,nsmul_eq_mul]
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
  have hc₁ : 648*C*D ≤ K₀ := by dsimp [K₀]; linarith
  have hc₂ : 2*K ≤ K₀ := by dsimp [K₀]; nlinarith
  have hs := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₁ (Real.rpow_nonneg hB (1/3:ℝ))) hE)
    (show 0 ≤ N^ε*V*(1+N/T) by positivity)
  have hl := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₂ (Real.rpow_nonneg hB (1/3:ℝ))) hE)
    (show 0 ≤ (I.card:ℝ)*N^(2*ε)*(N/(V/5832)^(1/3:ℝ)+N^(23/24:ℝ)) by positivity)
  have hbound := (add_le_add hs hl).trans_eq (by
    show K₀*B^(1/3:ℝ)*E*(N^ε*V*(1+N/T))+
      K₀*B^(1/3:ℝ)*E*((I.card:ℝ)*N^(2*ε)*(N/(V/5832)^(1/3:ℝ)+N^(23/24:ℝ))) =
      K₀*B^(1/3:ℝ)*E*(N^ε*V*(1+N/T)+
        (I.card:ℝ)*N^(2*ε)*(N/(V/5832)^(1/3:ℝ)+N^(23/24:ℝ)))
    ring)
  exact hsplit.trans ((add_le_add hsmall hlarge).trans hbound)

end CubicFirstMoment

end

end OAI
