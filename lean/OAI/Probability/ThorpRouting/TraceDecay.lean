import OAI.Probability.ThorpRouting.TraceModel

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.LowPlanes
open scoped BigOperators Classical
open Casimir Specht UnitaryFinite

attribute [local instance] hsNorm hsInner hsFinite

lemma absoluteTrace_even {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (A : V →L[ℂ] V) (u : ℕ) :
    absoluteTrace A (2 * (u : ℝ)) =
      (LinearMap.trace ℂ V ((star A * A)^u).toLinearMap).re := by
  have he : (2 : ℝ) * u = ((2*u : ℕ) : ℝ) := by simp
  unfold absoluteTrace
  rw [he, CFC.rpow_eq_pow, CFC.rpow_natCast _ _ (CFC.sqrt_nonneg _),
    pow_mul, pow_two, CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg A)]

lemma Q_square (d : ℕ) (μ : Shapes (2^d)) :
    star (Q d μ) * Q d μ = K d μ.1 (cardLabels d μ) := by
  unfold Q
  rw [physical_sweep_adjoint _ _ (cardRepresentation_unitary d μ)]
  change _ = sampleOperator (cardRepresentation d μ) (palindromePerm d)
  rw [sampleOperator_palindrome _ _ (cardRepresentation_unitary d μ)]
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint]

lemma levelScale_log (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    Real.log n ≤ levelScale n k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hratio : 1 ≤ (n : ℝ) / k := (le_div_iff₀ hkp).mpr (by simpa using (show (k : ℝ) ≤ n by exact_mod_cast hkn))
  have hp := mul_le_mul_of_nonneg_right hkR (Real.log_nonneg hratio)
  have hl := Real.log_le_sub_one_of_pos hkp
  have he : Real.log ((n : ℝ) / k) = Real.log n - Real.log k :=
    Real.log_div hn.ne' hkp.ne'
  dsimp [levelScale]
  rw [he] at hp ⊢
  nlinarith

lemma level_shape_term (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    Real.exp (-14 * levelScale n k) ≤ ((n : ℝ)^12)⁻¹ * (1/4 : ℝ)^k := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl := levelScale_log n k hk hkn
  have hj := levelScale_ge n k hkn
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    have h2 : Real.log (2 : ℝ) ≤ 1 := by
      have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at ht
      exact ht
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
    linarith
  calc
    _ ≤ Real.exp (-(12 * Real.log n + (k : ℝ) * Real.log 4)) := by
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_left hlog4 (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      linarith
    _ = _ := by
      rw [neg_add, Real.exp_add]
      congr 1
      · have he : Real.log ((n : ℝ)^12) = 12 * Real.log n := by
          norm_num [Real.log_pow]
        rw [Real.exp_neg, ←he, Real.exp_log (pow_pos hn _)]
      · rw [show -((k : ℝ) * Real.log 4) = (k : ℝ) * (-Real.log 4) by ring,
          Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
        norm_num

lemma uniform_nonconstant_decay :
    ∃ u : ℕ, 1 ≤ u ∧ ∀ v : ℕ, u ≤ v →
      ∀ (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Cell μ),
        0 < μ.card - μ.rowLen 0 →
        (Module.finrank ℂ (hilbertSpace μ) : ℝ)^2 * ‖K d μ e‖^v ≤
          Real.exp (-14 * levelScale (2^d) (μ.card - μ.rowLen 0)) := by
  obtain ⟨a, ha, hlevel⟩ := level_contraction
  obtain ⟨b, hb, hdim⟩ := HarmonicBounds.dimension_contraction
  obtain ⟨m, hm⟩ := exists_nat_ge (max (14/a) (2/b))
  have hma : 14 ≤ a * m := by
    have ht := (div_le_iff₀ ha).mp ((le_max_left _ _).trans hm)
    linarith
  have hmb : 2 ≤ b * m := by
    have ht := (div_le_iff₀ hb).mp ((le_max_right _ _).trans hm)
    linarith
  have hmp : 0 < m := by
    by_contra hn
    have hz : m = 0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero] at hma
    norm_num at hma
  refine ⟨2*m, by omega, ?_⟩
  intro v hv d μ e hk
  let D : ℝ := Module.finrank ℂ (space μ)
  let L : ℝ := levelScale (2^d) (μ.card - μ.rowLen 0)
  have hD : 0 < D := by dsimp [D]; exact_mod_cast dimension_pos μ
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg (by
    dsimp [D]; exact_mod_cast dimension_pos μ)
  have hμ : μ.card = 2^d := by
    rw [←card_cell, ←Fintype.card_congr e, card_positions]
  have hkn : μ.card - μ.rowLen 0 ≤ 2^d := by omega
  have hL : 0 ≤ L := (Nat.cast_nonneg _).trans (levelScale_ge _ _ hkn)
  have h₁ := pow_le_pow_left₀ (norm_nonneg (K d μ e)) (hlevel d μ e hk) m
  have h₂ := pow_le_pow_left₀ (norm_nonneg (K d μ e)) (hdim d μ e hk) m
  change ‖K d μ e‖^m ≤ (Real.exp (-a*L))^m at h₁
  change ‖K d μ e‖^m ≤ (Real.exp (-b*Real.log D))^m at h₂
  have hp : ‖K d μ e‖^v ≤ (Real.exp (-a*L))^m * (Real.exp (-b*Real.log D))^m := by
    apply (pow_le_pow_of_le_one (norm_nonneg _) (K_norm_le_one d μ e) hv).trans
    rw [two_mul, pow_add]
    exact mul_le_mul h₁ h₂ (pow_nonneg (norm_nonneg _) _) (by positivity)
  rw [finrank_hilbertSpace]
  change D^2 * ‖K d μ e‖^v ≤ Real.exp (-14*L)
  calc
    _ ≤ D^2 * ((Real.exp (-a*L))^m * (Real.exp (-b*Real.log D))^m) :=
      mul_le_mul_of_nonneg_left hp (sq_nonneg _)
    _ = Real.exp ((2-b*m)*Real.log D - (a*m)*L) := by
      rw [← Real.exp_log hD, ←Real.exp_nat_mul, ←Real.exp_nat_mul,
        ←Real.exp_nat_mul, ←Real.exp_add, ←Real.exp_add, Real.log_exp]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hfirst : (2-b*m)*Real.log D ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hlogD
      have hlast := mul_le_mul_of_nonneg_right hma hL
      linarith

noncomputable def tailBound (d v : ℕ) : ℝ :=
  ∑ μ : Shapes (2^d), if μ.1.card - μ.1.rowLen 0 = 0 then 0 else
    (Module.finrank ℂ (hilbertSpace μ.1) : ℝ)^2 * ‖K d μ.1 (cardLabels d μ)‖^v

lemma two_inverse_twelfth_le (x : ℝ) (hx : 2 ≤ x) :
    (x^12)⁻¹ * 2 ≤ x^(-10 : ℤ) := by
  have hxp : 0 < x := by linarith
  have hsq : 2 ≤ x^2 := by nlinarith
  rw [zpow_neg, zpow_ofNat]
  change (x^12)⁻¹ * 2 ≤ (x^10)⁻¹
  have hpow : x^12 = x^10 * x^2 := by ring
  rw [inv_mul_eq_div, inv_eq_one_div]
  apply (div_le_div_iff₀ (pow_pos hxp _) (pow_pos hxp _)).mpr
  rw [hpow]
  nlinarith [mul_le_mul_of_nonneg_left hsq (pow_nonneg hxp.le 10)]

lemma uniform_tail_bound :
    ∃ u : ℕ, 1 ≤ u ∧ ∀ d : ℕ, 1 ≤ d → ∀ v : ℕ, u ≤ v →
      tailBound d v ≤ ((2 : ℝ)^d)^(-10 : ℤ) := by
  obtain ⟨u, hu, hdec⟩ := uniform_nonconstant_decay
  refine ⟨u, hu, ?_⟩
  intro d hd v hv
  have hn : (2 : ℝ) ≤ (2 : ℝ)^d := by
    calc
      (2 : ℝ) = 2^1 := by norm_num
      _ ≤ 2^d := pow_le_pow_right₀ (by norm_num) hd
  have hterm (μ : Shapes (2^d)) :
      (if μ.1.card - μ.1.rowLen 0 = 0 then 0 else
        (Module.finrank ℂ (hilbertSpace μ.1) : ℝ)^2 * ‖K d μ.1 (cardLabels d μ)‖^v) ≤
      (((2 : ℝ)^d)^12)⁻¹ * (1/4 : ℝ)^(μ.1.card - μ.1.rowLen 0) := by
    split_ifs with hz
    · positivity
    · have hk : 0 < μ.1.card - μ.1.rowLen 0 := by omega
      have hkn : μ.1.card - μ.1.rowLen 0 ≤ 2^d := by have := μ.2; omega
      apply (hdec v hv d μ.1 (cardLabels d μ) hk).trans
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        level_shape_term (2^d) (μ.1.card - μ.1.rowLen 0) hk hkn
  calc
    tailBound d v ≤ ∑ μ : Shapes (2^d),
        (((2 : ℝ)^d)^12)⁻¹ * (1/4 : ℝ)^(μ.1.card - μ.1.rowLen 0) :=
      Finset.sum_le_sum (fun μ _ => hterm μ)
    _ = (((2 : ℝ)^d)^12)⁻¹ * ∑ μ : Shapes (2^d), (1/4 : ℝ)^(μ.1.card - μ.1.rowLen 0) :=
      (Finset.mul_sum ..).symm
    _ ≤ (((2 : ℝ)^d)^12)⁻¹ * 2 :=
      mul_le_mul_of_nonneg_left (shape_weight_sum _) (by positivity)
    _ ≤ _ := two_inverse_twelfth_le _ hn

end Thorp.LowPlanes

end ThorpNine.Harmonic

end OAI
