import OAI.NumberTheory.CubicMoment.Estimates.ConductorNeighborhoods
import OAI.NumberTheory.CubicMoment.Estimates.AllShortMoments

namespace OAI

/-! The conductor-neighborhood savings for the literal short factors,
with cardinality and amplitude bounds derived from their finite supports. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma short_neighborhood_length {X Y δ : ℝ} (hY : 1 ≤ Y) (hδ : 0 ≤ δ)
    (hX : X ≤ Y^(1-δ)) : X ≤ Y := by
  simpa only [Real.rpow_one] using hX.trans
    (Real.rpow_le_rpow_of_exponent_le hY (by linarith : 1-δ ≤ 1))

lemma neighborhood_cubic_card (S : Finset Eisenstein) {Y N : ℝ}
    (hY : 36 ≤ Y) (hN : 1 ≤ N) (hNY : N ≤ Y^2)
    (hS : ∀ p ∈ S, gramDyad N p) : (S.card:ℝ) ≤ Y^4 := by
  have hsub : S ⊆ nonzeroNormBall (2*N) := fun p hp =>
    mem_nonzeroNormBall.mpr ⟨(hS p hp).2.2.2.le,primary_ne_zero (hS p hp).1⟩
  have hc := (Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)).trans
    (nonzeroNormBall_card_le (show 0 ≤ 2*N by positivity))
  calc
    _ ≤ 36*N := by linarith
    _ ≤ 36*Y^2 := by gcongr
    _ ≤ Y^2*Y^2 := by gcongr; nlinarith
    _ = _ := by ring

lemma neighborhood_balanced_card (S : Finset (Eisenstein × Eisenstein))
    {Y L : ℝ} (hY : 324 ≤ Y) (hL : 0 ≤ L) (hLY : L ≤ Y)
    (hS : ∀ p ∈ S, PrimarySquarefreePair p ∧ norm p.1 ≤ L ∧ norm p.2 ≤ L) :
    (S.card:ℝ) ≤ Y^4 := by
  have hc := balanced_pair_card S hL
    (fun p hp => ⟨(hS p hp).1.1,(hS p hp).1.2.1,(hS p hp).2⟩)
  calc
    _ ≤ 324*L^2 := hc
    _ ≤ 324*Y^2 := by gcongr
    _ ≤ Y^2*Y^2 := by gcongr; nlinarith
    _ = _ := by ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem all_short_cubic_neighborhood {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/2 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ,
      ∀ (F : ShortFactorFamily ι) (j : ℕ) (Y N : ℝ) (S : Finset Eisenstein),
      Y₀ ≤ Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) →
      (∀ i, F.length j i ≤ Y^(1-δ)) →
      Y/C ≤ ∏ i, F.length j i → (∏ i, F.length j i) ≤ C*Y →
      (∀ p ∈ S, gramDyad N p) →
      (∑ p ∈ S, ‖∏ i, F.cubicValue j i p‖^2) ≤ Y^(7/3-ε) := by
  obtain ⟨κ,hκ,ε,hε,T₀,huniform⟩ := cubic_short_neighborhood_power (ι := ι)
    (H := 2) (D := 4) hδ (by norm_num) (by norm_num) hC
  obtain ⟨T,hT,hsize⟩ := shortFactorPolynomial_uniform_quadratic_size
  refine ⟨min κ (1/2),by positivity,min_le_right _ _,ε,hε,max T₀ (max T 36),?_⟩
  intro F j Y N S hY hNlo hNhi hshort hlo hhi hS
  have hYT : T ≤ Y := (le_max_left T 36).trans ((le_max_right _ _).trans hY)
  have hY₁ : 1 ≤ Y := hT.trans hYT
  have hY₃₆ : 36 ≤ Y := (le_max_right T 36).trans ((le_max_right _ _).trans hY)
  have hN : 1 ≤ N := (Real.one_le_rpow hY₁
    (by have := min_le_right κ (1/2); linarith)).trans hNlo
  have hNY : N ≤ Y^2 := by
    simpa only [Real.rpow_two] using hNhi.trans
      (Real.rpow_le_rpow_of_exponent_le hY₁
        (by have := min_le_right κ (1/2); linarith : 1+min κ (1/2) ≤ 2))
  let x : ConductorMomentInstance ι Eisenstein := ⟨⟨Y,F.comp (fun _ => j),S⟩,N⟩
  have hx : cubicNeighborhoodAdmissible δ 2 4 C κ x := by
    refine ⟨hshort,hlo,hhi,hN,⟨?_,?_⟩,hS,?_,?_⟩
    · exact (Real.rpow_le_rpow_of_exponent_le hY₁
        (by have := min_le_left κ (1/2); linarith)).trans hNlo
    · exact hNhi.trans (Real.rpow_le_rpow_of_exponent_le hY₁
        (by have := min_le_left κ (1/2); linarith))
    · change (S.card:ℝ) ≤ Y^(4:ℝ)
      convert neighborhood_cubic_card S hY₃₆ hN hNY hS using 1
      norm_num
    · intro p hp i
      change ‖F.cubicValue j i p‖ ≤ Y^(2:ℝ)
      rw [Real.rpow_two]
      apply hsize (F.cutoff j) (F.length j i) Y (F.coefficient j i)
        (fun n => F.twist j i n*cubicSymbol p n) (F.factor_spec j i)
        (F.length_ge_one j i) (short_neighborhood_length hY₁ hδ.le (hshort i)) hYT
      intro n hn
      rw [norm_mul]
      exact (mul_le_mul (F.twist_bound j i n hn) (norm_cubicSymbol_le_one (hS p hp).1 n)
        (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  exact huniform x hx ((le_max_left _ _).trans hY)

theorem all_short_mixed_neighborhood (hHuxley : HuxleyAdditiveLargeSieve)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/3 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ,
      ∀ (F : ShortFactorFamily ι) (j : ℕ) (Y : ℝ)
        (S : Finset (Eisenstein × Eisenstein)), Y₀ ≤ Y →
      (∀ i, F.length j i ≤ Y^(1-δ)) →
      Y/C ≤ ∏ i, F.length j i → (∏ i, F.length j i) ≤ C*Y →
      (∀ p ∈ S, PrimarySquarefreePair p ∧ norm p.1 ≤ Y^(1/3+κ) ∧
        norm p.2 ≤ Y^(1/3+κ)) →
      (∑ p ∈ S, ‖∏ i, F.mixedValue j i p‖^2) ≤ Y^(7/3-ε) := by
  obtain ⟨κ,hκ,ε,hε,T₀,huniform⟩ := mixed_short_neighborhood_power (ι := ι) hHuxley
    (H := 2) (D := 4) hδ (by norm_num) (by norm_num) hC
  obtain ⟨T,hT,hsize⟩ := shortFactorPolynomial_uniform_quadratic_size
  refine ⟨min κ (1/3),by positivity,min_le_right _ _,ε,hε,max T₀ (max T 324),?_⟩
  intro F j Y S hY hshort hlo hhi hS
  have hYT : T ≤ Y := (le_max_left T 324).trans ((le_max_right _ _).trans hY)
  have hY₁ : 1 ≤ Y := hT.trans hYT
  have hY₃₂₄ : 324 ≤ Y := (le_max_right T 324).trans ((le_max_right _ _).trans hY)
  let L : ℝ := Y^(1/3+min κ (1/3))
  have hL : 1 ≤ L := Real.one_le_rpow hY₁ (by have := lt_min hκ (by norm_num : (0:ℝ) < 1/3); linarith)
  have hLY : L ≤ Y := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hY₁
      (by have := min_le_right κ (1/3); linarith : 1/3+min κ (1/3) ≤ 1)
  let x : ConductorMomentInstance ι (Eisenstein × Eisenstein) :=
    ⟨⟨Y,F.comp (fun _ => j),S⟩,L⟩
  have hx : mixedNeighborhoodAdmissible δ 2 4 C κ x := by
    refine ⟨hshort,hlo,hhi,hL,⟨?_,?_⟩,hS,?_,?_⟩
    · change Y^(1/3-κ) ≤ Y^(1/3+min κ (1/3))
      apply Real.rpow_le_rpow_of_exponent_le hY₁
      have hm := lt_min hκ (by norm_num : (0:ℝ) < 1/3)
      linarith
    · exact Real.rpow_le_rpow_of_exponent_le hY₁
        (by have := min_le_left κ (1/3); linarith)
    · change (S.card:ℝ) ≤ Y^(4:ℝ)
      convert neighborhood_balanced_card S hY₃₂₄ (zero_le_one.trans hL) hLY hS using 1
      norm_num
    · intro p hp i
      change ‖F.mixedValue j i p‖ ≤ Y^(2:ℝ)
      rw [Real.rpow_two]
      apply hsize (F.cutoff j) (F.length j i) Y (F.coefficient j i)
        (fun n => F.twist j i n*mixedCubic p.1 p.2 n) (F.factor_spec j i)
        (F.length_ge_one j i) (short_neighborhood_length hY₁ hδ.le (hshort i)) hYT
      intro n hn
      rw [norm_mul]
      exact (mul_le_mul (F.twist_bound j i n hn)
        (norm_mixedCubic_le_one (hS p hp).1.1 (hS p hp).1.2.1 n)
        (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  exact huniform x hx ((le_max_left _ _).trans hY)

end CubicFirstMoment

end

end OAI
