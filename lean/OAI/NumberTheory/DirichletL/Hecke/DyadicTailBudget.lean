import OAI.NumberTheory.DirichletL.Hecke.DyadicReflectedPointwise

namespace OAI

noncomputable section
namespace SevenEighths.HeckeDyadic

theorem exists_external_tail_order (τ B p : ℝ) (hτ : 0<τ) :
    ∃ n : ℕ, ∀ Z : ℝ, 1≤Z → Z^B/(1+Z^τ)^n≤Z^p := by
  obtain ⟨n,hn⟩ := exists_nat_gt ((B-p)/τ)
  refine ⟨n,?_⟩
  intro Z hZ
  have hZp : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hn' : B≤p+τ*(n : ℝ) := by
    have h := (div_lt_iff₀ hτ).mp hn
    nlinarith
  have hden : 0<(1+Z^τ)^n := by positivity
  apply (div_le_iff₀ hden).mpr
  calc
    Z^B ≤ Z^(p+τ*(n : ℝ)) := Real.rpow_le_rpow_of_exponent_le hZ hn'
    _ = Z^p*(Z^τ)^n := by
      rw [Real.rpow_add hZp,Real.rpow_mul hZp.le,Real.rpow_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.rpow_nonneg hZp.le _) (by linarith) n)
      (Real.rpow_nonneg hZp.le _)

theorem constant_absorbed_eventually (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in Filter.atTop, C≤Z^ε := by
  exact (tendsto_rpow_atTop hε).eventually (Filter.eventually_ge_atTop C)

theorem uniform_external_tail_order (τ dmax B R : ℝ)
    (hτ : 0<τ) (_hdmax : 0≤dmax) (hB : 0≤B) (hR : 0≤R) :
    ∃ n : ℕ, ∀ Z d p : ℝ, 1≤Z → 0≤d → d≤dmax → -R≤p →
      (Z^d)^B/(1+Z^τ/2)^n≤(2 : ℝ)^n*(Z^d)^p := by
  obtain ⟨n,hn⟩ := exists_external_tail_order τ (dmax*B) (-dmax*R) hτ
  refine ⟨n,?_⟩
  intro Z d p hZ hd hd' hp
  have hZp : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hnum : (Z^d)^B≤Z^(dmax*B) := by
    rw [←Real.rpow_mul hZp.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ (mul_le_mul_of_nonneg_right hd' hB)
  have htarget : Z^(-dmax*R)≤(Z^d)^p := by
    rw [←Real.rpow_mul hZp.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    nlinarith [mul_nonneg hd (show 0≤p+R by linarith),
      mul_nonneg (show 0≤dmax-d by linarith) hR]
  have hden : ((1+Z^τ)/2)^n≤(1+Z^τ/2)^n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  calc
    _ ≤ (Z^(dmax*B))/((1+Z^τ)/2)^n :=
      div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = (2 : ℝ)^n*(Z^(dmax*B)/(1+Z^τ)^n) := by
      rw [div_pow]
      field_simp
    _ ≤ (2 : ℝ)^n*Z^(-dmax*R) := mul_le_mul_of_nonneg_left (hn Z hZ) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left htarget (by positivity)

end SevenEighths.HeckeDyadic

end

end OAI
