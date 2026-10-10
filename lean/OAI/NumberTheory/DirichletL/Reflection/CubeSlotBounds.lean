import OAI.NumberTheory.DirichletL.Reflection.CubeSlotSource

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
open IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma cubeDivList_card (H : Ideal Eis) (hH : H≠0) (L : Finset (Ideal Eis)) :
    (cubeDivList H L).card≤(idealDivisors H).card := by
  apply Finset.card_le_card
  intro P hP
  exact (mem_idealDivisors hH).mpr (Finset.mem_filter.mp hP).2

lemma cube_divisor_card_one (H : Ideal Eis) (hH : H≠0) :
    (1:ℝ)≤(idealDivisors H).card := by
  exact_mod_cast Finset.card_pos.mpr ⟨1,(mem_idealDivisors hH).mpr (one_dvd H)⟩

lemma cubeAbsorbedCoefficient_norm (H : Ideal Eis) (hH : H≠0)
    (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ)
    (hw : ∀ i P,‖w i P‖≤1) (T : Finset σ) (rmax : ℕ)
    (hr : Fintype.card σ≤rmax) :
    ‖cubeAbsorbedCoefficient H L w T‖≤((idealDivisors H).card:ℝ)^rmax := by
  rw [cubeAbsorbedCoefficient_product,norm_prod]
  calc
    _ ≤ ∏ i : {i // i∉T},((idealDivisors H).card:ℝ) := by
      apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
      intro i hi
      calc
        _ ≤ ∑ P : cubeDivList H (L i.val),‖w i.val ⟨P.val,(Finset.mem_filter.mp P.property).1⟩‖ := norm_sum_le _ _
        _ ≤ ∑ _P : cubeDivList H (L i.val),(1:ℝ) := Finset.sum_le_sum (fun P _ => hw _ _)
        _ = ((cubeDivList H (L i.val)).card:ℝ) := by simp
        _ ≤ _ := Nat.cast_le.mpr (cubeDivList_card H hH _)
    _ = ((idealDivisors H).card:ℝ)^(Fintype.card {i // i∉T}) := by simp
    _ ≤ _ := pow_le_pow_right₀ (cube_divisor_card_one H hH)
      ((Fintype.card_subtype_le _).trans hr)

lemma cubeAbsorbedCoefficient_mass (H : Ideal Eis) (hH : H≠0)
    (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ)
    (hw : ∀ i P,‖w i P‖≤1) (rmax : ℕ) (hr : Fintype.card σ≤rmax) :
    (∑ T : Finset σ,‖cubeAbsorbedCoefficient H L w T‖)≤
      (2:ℝ)^rmax*((idealDivisors H).card:ℝ)^rmax := by
  calc
    _ ≤ ∑ _T : Finset σ,((idealDivisors H).card:ℝ)^rmax :=
      Finset.sum_le_sum (fun T _ => cubeAbsorbedCoefficient_norm H hH L w hw T rmax hr)
    _ = (2:ℝ)^(Fintype.card σ)*((idealDivisors H).card:ℝ)^rmax := by
      simp [Fintype.card_finset]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hr) (by positivity)

theorem cubeAbsorbedCoefficient_small_power (rmax : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {σ : Type*} [Fintype σ] [DecidableEq σ]
      (H : Ideal Eis),H≠0 → ∀ (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ),
      (∀ i P,‖w i P‖≤1) → Fintype.card σ≤rmax →
      (∑ T : Finset σ,‖cubeAbsorbedCoefficient H L w T‖)^2≤C*(Ideal.absNorm H:ℝ)^ε := by
  let δ : ℝ := ε/(2*rmax+1)
  have hδ : 0<δ := div_pos hε (by positivity)
  obtain ⟨D,hD,hd⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨((2:ℝ)^rmax*D^rmax)^2,by positivity,?_⟩
  intro σ _ _ H hH L w hw hr
  have hn : (1:ℝ)≤Ideal.absNorm H := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hH (Ideal.absNorm_eq_zero_iff.mp h))
  have hn0 : 0<(Ideal.absNorm H:ℝ) := lt_of_lt_of_le zero_lt_one hn
  have hde : δ*(rmax:ℝ)*2≤ε := by
    dsimp [δ]
    have hp : (0:ℝ)<2*rmax+1 := by positivity
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  calc
    _ ≤ ((2:ℝ)^rmax*((idealDivisors H).card:ℝ)^rmax)^2 := by
      exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
        (cubeAbsorbedCoefficient_mass H hH L w hw rmax hr) 2
    _ ≤ ((2:ℝ)^rmax*(D*(Ideal.absNorm H:ℝ)^δ)^rmax)^2 := by gcongr; exact hd H hH
    _ = ((2:ℝ)^rmax*D^rmax)^2*(Ideal.absNorm H:ℝ)^(δ*(rmax:ℝ)*2) := by
      have he := Real.rpow_mul_natCast hn0.le (δ*(rmax:ℝ)) 2
      norm_num only [Nat.cast_ofNat] at he
      rw [he,Real.rpow_mul_natCast hn0.le δ rmax]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn hde) (by positivity)
end
end SevenEighths.InverseReflectedPhase

end OAI
