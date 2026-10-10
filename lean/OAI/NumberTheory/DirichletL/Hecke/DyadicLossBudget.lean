import OAI.NumberTheory.DirichletL.Hecke.DyadicCentralBudget

namespace OAI

noncomputable section
namespace SevenEighths.HeckeDyadic

theorem central_squared_exponents (R a e κ η ε r m : ℝ)
    (hR : 0≤R) (he : 0≤e) (hκ : 0≤κ) (_hη : 0≤η)
    (hr : r≤R) (hm : 0≤m)
    (hbudget : 12*e*(R+2)+8*κ+2*η≤ε) :
    2*((a-1/2+6*e)*r+2*κ+η)≤(2*a-1)*r+ε ∧
    2*((a-1/2)*(1-m)+6*e*(2-m)+4*κ+η)≤(2*a-1)*(1-m)+ε := by
  have hEr : e*r≤e*R := mul_le_mul_of_nonneg_left hr he
  have hEm : 0≤e*m := mul_nonneg he hm
  have hER : 0≤e*R := mul_nonneg he hR
  constructor <;> nlinarith

theorem exists_central_loss_parameters (R ε : ℝ) (hR : 0≤R) (hε : 0<ε) :
    ∃ e₀ κ η : ℝ, 0<e₀ ∧ e₀≤1/1000 ∧ 0<κ ∧ κ≤1 ∧ 0<η ∧
      ∀ e : ℝ, 0<e → e<e₀ → 12*e*(R+2)+8*κ+2*η≤ε/2 := by
  let e₀ : ℝ := min (1/1000) (ε/(96*(R+2)))
  let κ : ℝ := min (1/2) (ε/64)
  let η : ℝ := ε/16
  have hRp : 0<R+2 := by linarith
  have he₀ : 0<e₀ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hκ : 0<κ := lt_min (by norm_num) (div_pos hε (by norm_num))
  refine ⟨e₀,κ,η,he₀,min_le_left _ _,hκ,(min_le_left _ _).trans (by norm_num),
    div_pos hε (by norm_num),?_⟩
  intro e he he'
  have heb : e≤ε/(96*(R+2)) := he'.le.trans (min_le_right _ _)
  have heb' := (le_div_iff₀ (by positivity : 0<96*(R+2))).mp heb
  have hκb : κ≤ε/64 := min_le_right _ _
  dsimp only [η]
  nlinarith

theorem indexed_height_bound (i I : ℕ) (hi : i≤I) (T : ℝ) (hT : 0≤T) :
    (3+(3*i+2 : ℕ)*T)^4≤(3*(I : ℝ)+5)^4*(1+T)^4 := by
  have hi' : (i : ℝ)≤I := by exact_mod_cast hi
  have hlin : 3+(3*i+2 : ℕ)*T≤(3*(I : ℝ)+5)*(1+T) := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hi' hT,Nat.cast_nonneg (α:=ℝ) I]
  calc
    _ ≤ ((3*(I : ℝ)+5)*(1+T))^4 := pow_le_pow_left₀ (by positivity) hlin 4
    _ = _ := mul_pow _ _ _

theorem min_plain_bound (X C U δ m ε : ℝ)
    (h₁ : X≤C*U^(δ*m+ε)) (h₂ : X≤C*U^(δ*(1-m)+ε)) :
    X≤C*U^(δ*min m (1-m)+ε) := by
  rcases le_total m (1-m) with h | h
  · simpa only [min_eq_left h] using h₁
  · simpa only [min_eq_right h] using h₂

theorem squared_bound_of_central_and_error (z : ℂ) (U C E p b ε : ℝ)
    (hU : 1≤U) (hC : 0≤C) (hE : 0≤E) (hε : 0≤ε)
    (hb : 2*b≤ε)
    (hz : ‖z‖≤C*U^(p+b)+E*U^p) :
    ‖z‖^2≤(C+E)^2*U^(2*p+ε) := by
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hp₁ : U^(p+b)≤U^(p+ε/2) :=
    Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  have hp₂ : U^p≤U^(p+ε/2) :=
    Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  have hn : ‖z‖≤(C+E)*U^(p+ε/2) := by
    calc
      _ ≤ C*U^(p+b)+E*U^p := hz
      _ ≤ C*U^(p+ε/2)+E*U^(p+ε/2) := add_le_add
        (mul_le_mul_of_nonneg_left hp₁ hC) (mul_le_mul_of_nonneg_left hp₂ hE)
      _ = _ := by ring
  calc
    _ ≤ ((C+E)*U^(p+ε/2))^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = _ := by
      have hp : (U^(p+ε/2))^2=U^(2*p+ε) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hUp.le]
        congr 1
        norm_num
        ring
      rw [mul_pow,hp]

end SevenEighths.HeckeDyadic

end

end OAI
