import OAI.NumberTheory.DirichletL.Reflection.BranchCount
import OAI.NumberTheory.DirichletL.Reflection.TruncatedSource

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve
noncomputable section

lemma retained_count_le_box (scale B : ℝ) :
    (retainedDyads scale B).card≤(retainedDyadicBox scale B).card :=
  Finset.card_filter_le _ _

lemma cutoff_ratio_cap (Z scale δ Lscale : ℝ) (hZ : 1≤Z) (hδL : 0≤δ+Lscale)
    (hscale : scale⁻¹≤Z^Lscale) :
    max 1 (16*Z^δ/scale)≤16*Z^(δ+Lscale) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  apply max_le
  · have hp : 1≤Z^(δ+Lscale) := Real.one_le_rpow hZ hδL
    linarith
  · rw [Real.rpow_add hz,div_eq_mul_inv,←mul_assoc]
    exact mul_le_mul_of_nonneg_left hscale (by positivity)

theorem retained_count_budget (ε δ Lscale : ℝ) (hε : 0<ε) (hδL : 0≤δ+Lscale) :
    ∃ C : ℝ, 0<C ∧ ∀ Z scale : ℝ, 1≤Z → scale⁻¹≤Z^Lscale →
      ((retainedDyads scale (16*Z^δ)).card:ℝ)^2≤C*Z^ε := by
  let α := ε/(1+δ+Lscale)
  have ha : 0<α := div_pos hε (by linarith)
  obtain ⟨C,hC,hcount⟩ := retainedDyadicBox_count_small_power α ha
  refine ⟨C*16^α,by positivity,?_⟩
  intro Z scale hZ hscale
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hpow : α*(δ+Lscale)≤ε := by
    have he : α*(1+δ+Lscale)=ε := by dsimp [α];field_simp [ne_of_gt (show 0<1+δ+Lscale from by linarith)]
    nlinarith
  calc
    _ ≤ ((retainedDyadicBox scale (16*Z^δ)).card:ℝ)^2 := by
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      exact_mod_cast retained_count_le_box scale (16*Z^δ)
    _ ≤ C*(max 1 (16*Z^δ/scale))^α := hcount _ _
    _ ≤ C*(16*Z^(δ+Lscale))^α := by
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (cutoff_ratio_cap Z scale δ Lscale hZ hδL hscale) ha.le) hC.le
    _ = (C*16^α)*Z^((δ+Lscale)*α) := by rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hz.le _),←Real.rpow_mul hz.le];ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)) (by positivity)

theorem surviving_count_budget (ε Lpool : ℝ) (hε : 0<ε) (hLpool : 0≤Lpool) :
    ∃ C : ℝ, 0<C ∧ ∀ {φ : Type*} [Fintype φ] (F : PrimeFamily φ),
      Pairwise (Function.onFun IsCoprime F.ideal) →
      ∀ (jF : φ→ℕ) (column : Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ) (nset bset : Finset (Ideal ActualEisensteinCubic.O))
        (Z : ℝ), 1≤Z → (Ideal.absNorm (∏ i,F.ideal i):ℝ)≤Z^Lpool →
      ((survivingFrozenBranches F jF column nset bset).card:ℝ)^2≤C*Z^ε := by
  let α := ε/(1+Lpool)
  have ha : 0<α := div_pos hε (by linarith)
  obtain ⟨C,hC,hcount⟩ := surviving_branch_count_small_power α ha
  refine ⟨C,hC,?_⟩
  intro φ _ F hF jF column nset bset Z hZ hpool
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hpow : Lpool*α≤ε := by
    have he : α*(1+Lpool)=ε := by dsimp [α];field_simp
    nlinarith
  calc
    _ ≤ C*(Ideal.absNorm (∏ i,F.ideal i):ℝ)^α := hcount F hF jF column nset bset
    _ ≤ C*(Z^Lpool)^α := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hpool ha.le) hC.le
    _ = C*Z^(Lpool*α) := by rw [←Real.rpow_mul hz.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hpow) hC.le
end
end SevenEighths.InverseReflectedPhase

end OAI
