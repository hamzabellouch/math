import OAI.MeasureTheory.Falconer.Recursion.ProfileApplicationBudget

namespace OAI

/-! Quantitative choices for the final profile application. These scalar
bounds keep the gain, rounding error and recursive losses independent. -/
namespace Falconer

theorem exists_profile_gain_accuracy {κ η eg : ℝ} (hκ : 0 < κ) (hη : 0 < η) (heg : 0 < eg) :
    ∃ α : ℝ, 0 < α ∧ α ≤ κ/100 ∧ α ≤ η*κ/100 ∧ 6*α ≤ eg/4 := by
  let α := min κ (min (η*κ) eg)/100
  have ha : 0 < α := div_pos (lt_min hκ (lt_min (mul_pos hη hκ) heg)) (by norm_num)
  refine ⟨α,ha,?_,?_,?_⟩
  · exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  · exact div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)
  · have hh : α ≤ eg/100 := div_le_div_of_nonneg_right
      ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
    linarith

theorem exists_profile_gain_budget {α κ η eg τ : ℝ}
    (hα : 0 < α) (hκ : 0 < κ) (hη : 0 < η) (heg : 0 < eg) (hτ : 0 < τ) (J : ℕ) :
    ∃ β : ℝ, 0 < β ∧ β ≤ α*κ ∧ β*(13*(J:ℝ)+1) ≤ η*κ/4 ∧ 4*β ≤ eg*τ/8 := by
  let β := min (α*κ) (min (η*κ/(4*(13*(J:ℝ)+1))) (eg*τ/32))/2
  have hden : 0 < 4*(13*(J:ℝ)+1) := by positivity
  have hp : 0 < min (α*κ) (min (η*κ/(4*(13*(J:ℝ)+1))) (eg*τ/32)) :=
    lt_min (mul_pos hα hκ) (lt_min (div_pos (mul_pos hη hκ) hden) (by positivity))
  have hb : 0 < β := half_pos hp
  have hb1 : β ≤ α*κ := by
    have hh := min_le_left (α*κ) (min (η*κ/(4*(13*(J:ℝ)+1))) (eg*τ/32))
    dsimp [β]
    linarith
  have hb2 : β ≤ η*κ/(4*(13*(J:ℝ)+1)) := by
    have hh := (min_le_right (α*κ) (min (η*κ/(4*(13*(J:ℝ)+1))) (eg*τ/32))).trans (min_le_left _ _)
    dsimp [β]
    linarith
  have hb3 : β ≤ eg*τ/32 := by
    have hh := (min_le_right (α*κ) (min (η*κ/(4*(13*(J:ℝ)+1))) (eg*τ/32))).trans (min_le_right _ _)
    dsimp [β]
    linarith
  refine ⟨β,hb,hb1,?_,by linarith⟩
  have hh := (le_div_iff₀ hden).mp hb2
  nlinarith only [hh]

theorem profile_gain_parameters_close {κ η α β lam s t : ℝ} {J : ℕ}
    (_hκ : 0 < κ) (hκ1 : κ ≤ 1/100) (hα : 0 < α) (hακ : α ≤ κ/100)
    (hαη : α ≤ η*κ/100)
    (hβα : β ≤ α*κ) (hβη : β*(13*(J:ℝ)+1) ≤ η*κ/4)
    (hlam : 0 ≤ lam) (hlamb : lam ≤ β) (hs1 : s ≤ 1)
    (ht : s+8*κ ≤ t) :
    let χ := α^2+α+lam/(t-(s+κ));
    lam+2*χ ≤ κ ∧
      s+(η*κ/2)+β ≤ s*(1-χ-α)+η*κ-18*α-13*β*(J:ℝ) := by
  dsimp only
  have ha1 : α ≤ 1 := by linarith
  have hak : α*κ ≤ α := mul_le_of_le_one_right hα.le (by linarith)
  have hd : 0 < t-(s+κ) := by linarith
  have hdiv : lam/(t-(s+κ)) ≤ α/7 := by
    apply (div_le_iff₀ hd).2
    have hh := mul_le_mul_of_nonneg_left (show 7*κ ≤ t-(s+κ) by linarith) (show 0 ≤ α/7 by positivity)
    nlinarith only [hh,hlamb,hβα]
  have hχ : α^2+α+lam/(t-(s+κ)) ≤ 3*α := by
    have hsquare : α^2 ≤ α := by nlinarith only [hα.le,ha1]
    linarith
  have hχ0 : 0 ≤ α^2+α+lam/(t-(s+κ)) := by positivity
  have hprod : s*(α^2+α+lam/(t-(s+κ))+α) ≤ 4*α := by
    exact (mul_le_mul_of_nonneg_right hs1 (by positivity)).trans (by linarith only [hχ])
  constructor
  · linarith only [hlamb,hβα,hak,hχ,hακ,hα.le]
  · nlinarith only [hprod,hβη,hαη,hα.le]

theorem exists_incidence_profile_grid_threshold {α τ κ : ℝ} (hα : 0 < α) (hτ : 0 < τ) (hκ : 0 < κ)
    (Ng N0 : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ m : ℕ, M ≤ m → ∀ B : ℕ, 0 < B →
      N0 ≤ B*m ∧ 2/(m:ℝ) ≤ τ/2 ∧ 4/(m:ℝ) ≤ α*τ ∧
      16/((m:ℝ)*τ) ≤ κ/2 ∧ 2/((m:ℝ)*τ) ≤ α ∧ 4*(Ng:ℝ) ≤ τ*(m*B:ℕ) := by
  obtain ⟨M,hM⟩ := exists_nat_gt ((N0:ℝ)+1+4/τ+4/(α*τ)+32/(κ*τ)+4*(Ng:ℝ)/τ)
  have hterms : 0 ≤ 4/τ ∧ 0 ≤ 4/(α*τ) ∧ 0 ≤ 32/(κ*τ) ∧ 0 ≤ 4*(Ng:ℝ)/τ := by
    exact ⟨by positivity,by positivity,by positivity,by positivity⟩
  have hMpos : 0 < M := by
    have : (0:ℝ) < M := by linarith only [hM,hterms.1,hterms.2.1,hterms.2.2.1,hterms.2.2.2,Nat.cast_nonneg (α := ℝ) N0]
    exact_mod_cast this
  refine ⟨M,hMpos,?_⟩
  intro m hm B hB
  have hm0 : 0 < m := hMpos.trans_le hm
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm0
  have hbound := hM.trans_le (Nat.cast_le.mpr hm)
  have hNm : (N0:ℝ) ≤ m := by linarith only [hbound,hterms.1,hterms.2.1,hterms.2.2.1,hterms.2.2.2]
  have h1 : 4/τ ≤ (m:ℝ) := by linarith only [hbound,hterms.2.1,hterms.2.2.1,hterms.2.2.2,Nat.cast_nonneg (α := ℝ) N0]
  have h2 : 4/(α*τ) ≤ (m:ℝ) := by linarith only [hbound,hterms.1,hterms.2.2.1,hterms.2.2.2,Nat.cast_nonneg (α := ℝ) N0]
  have h3 : 32/(κ*τ) ≤ (m:ℝ) := by linarith only [hbound,hterms.1,hterms.2.1,hterms.2.2.2,Nat.cast_nonneg (α := ℝ) N0]
  have h4 : 4*(Ng:ℝ)/τ ≤ (m:ℝ) := by linarith only [hbound,hterms.1,hterms.2.1,hterms.2.2.1,Nat.cast_nonneg (α := ℝ) N0]
  have hmB : m ≤ m*B := Nat.le_mul_of_pos_right m hB
  have hmBR : (m:ℝ) ≤ (m*B:ℕ) := Nat.cast_le.mpr hmB
  have h1' := (div_le_iff₀ hτ).mp h1
  have h2' := (div_le_iff₀ (mul_pos hα hτ)).mp h2
  have h3' := (div_le_iff₀ (mul_pos hκ hτ)).mp h3
  have h4' := (div_le_iff₀ hτ).mp h4
  refine ⟨(Nat.cast_le.mp hNm).trans (by simpa only [Nat.mul_comm] using hmB),?_,?_,?_,?_,?_⟩
  · apply (div_le_iff₀ hmR).2
    nlinarith only [h1']
  · apply (div_le_iff₀ hmR).2
    nlinarith only [h2']
  · apply (div_le_iff₀ (mul_pos hmR hτ)).2
    nlinarith only [h3']
  · apply (div_le_iff₀ (mul_pos hmR hτ)).2
    nlinarith only [h2']
  · nlinarith only [h4',mul_le_mul_of_nonneg_left hmBR hτ.le]

end Falconer

end OAI
