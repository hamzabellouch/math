import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarPolynomialScale

namespace OAI

/-! A single fixed polynomial exponent gives uniform hopping brackets for
every input size. Exponential domination selects that exponent once. -/

noncomputable section
open Filter
open scoped Topology
namespace ContinuumCoulomb

theorem exists_planar_scale_conditions_above (B : ℝ) (A : ℕ) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1) :
    ∃ k : ℕ, 0 < k ∧ B ≤ (k : ℝ) ∧ 0 ≤ (k : ℝ) * ε - ((A : ℝ) + 1) ∧
      2 ≤ (1 - ε) * ((k : ℝ) * Real.log 2) ∧
      (k : ℝ) + 3 ≤ planarHoppingLowerConstant *
        (2 : ℝ) ^ ((k : ℝ) * ε - ((A : ℝ) + 1)) ∧
      planarHoppingUpperConstant * (2 * (k : ℝ) + 1) ≤
        (2 : ℝ) ^ ((k : ℝ) * ε - ((A : ℝ) + 1)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcast : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have htbase : Tendsto (fun k : ℕ => Real.exp ((ε * Real.log 2) * (k : ℝ)) / (k : ℝ))
      atTop atTop := by
    simpa only [Function.comp_def, Real.rpow_one] using
      (tendsto_exp_mul_div_rpow_atTop 1 (ε * Real.log 2) (mul_pos hε hlog)).comp hcast
  have ht : Tendsto (fun k : ℕ => (2 : ℝ) ^ ((k : ℝ) * ε - ((A : ℝ) + 1)) / (k : ℝ))
      atTop atTop := by
    convert htbase.const_mul_atTop (Real.exp_pos (-((A : ℝ) + 1) * Real.log 2)) using 1
    funext k
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← mul_div_assoc, ← Real.exp_add]
    congr 1
    congr 1
    ring
  let bound : ℝ := max B (max 1 (max (((A : ℝ) + 1) / ε) (2 / ((1 - ε) * Real.log 2))))
  have hb : ∀ᶠ k : ℕ in atTop, bound ≤ (k : ℝ) := hcast.eventually (eventually_ge_atTop bound)
  have hr : ∀ᶠ k : ℕ in atTop,
      max (4 / planarHoppingLowerConstant) (3 * planarHoppingUpperConstant) ≤
        (2 : ℝ) ^ ((k : ℝ) * ε - ((A : ℝ) + 1)) / (k : ℝ) :=
    ht.eventually (eventually_ge_atTop _)
  obtain ⟨k, hkb, hkr⟩ := (hb.and hr).exists
  have hkbB : B ≤ (k : ℝ) := (le_max_left _ _).trans hkb
  have hkb0 : max 1 (max (((A : ℝ) + 1) / ε) (2 / ((1 - ε) * Real.log 2))) ≤ (k : ℝ) :=
    (le_max_right _ _).trans hkb
  have hk₁ : (1 : ℝ) ≤ k := (le_max_left _ _).trans hkb0
  have hkp : (0 : ℝ) < k := by linarith
  have hkA : ((A : ℝ) + 1) / ε ≤ k :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hkb0)
  have hkD : 2 / ((1 - ε) * Real.log 2) ≤ k :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hkb0)
  have hlo := (le_div_iff₀ hkp).mp ((le_max_left _ _).trans hkr)
  have hhi := (le_div_iff₀ hkp).mp ((le_max_right _ _).trans hkr)
  have hmul := mul_le_mul_of_nonneg_left hlo planarHoppingLowerConstant_positive.le
  have heq : planarHoppingLowerConstant * ((4 / planarHoppingLowerConstant) * (k : ℝ)) =
      4 * (k : ℝ) := by field_simp [planarHoppingLowerConstant_positive.ne']
  rw [heq] at hmul
  refine ⟨k, by exact_mod_cast hkp, hkbB, ?_, ?_, ?_, ?_⟩
  · exact sub_nonneg.mpr ((div_le_iff₀ hε).mp hkA)
  · have h := (div_le_iff₀ (mul_pos (sub_pos.mpr hε₁) hlog)).mp hkD
    nlinarith
  · exact (by linarith : (k : ℝ) + 3 ≤ 4 * (k : ℝ)).trans hmul
  · have hU := planarHoppingUpperConstant_positive
    nlinarith

theorem exists_planar_scale_conditions (A : ℕ) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1) :
    ∃ k : ℕ, 0 < k ∧ 0 ≤ (k : ℝ) * ε - ((A : ℝ) + 1) ∧
      2 ≤ (1 - ε) * ((k : ℝ) * Real.log 2) ∧
      (k : ℝ) + 3 ≤ planarHoppingLowerConstant *
        (2 : ℝ) ^ ((k : ℝ) * ε - ((A : ℝ) + 1)) ∧
      planarHoppingUpperConstant * (2 * (k : ℝ) + 1) ≤
        (2 : ℝ) ^ ((k : ℝ) * ε - ((A : ℝ) + 1)) := by
  obtain ⟨k, hk, _, hγ, hd, hlo, hhi⟩ := exists_planar_scale_conditions_above 0 A hε hε₁
  exact ⟨k, hk, hγ, hd, hlo, hhi⟩

/-- For every polynomial target range, a fixed power `λ=N^k` brackets that
range uniformly at the two allowed contact lengths, for all real `N≥2`. -/
theorem exists_planar_polynomial_brackets_above (B : ℝ) (A : ℕ) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1) :
    ∃ k : ℕ, 0 < k ∧ B ≤ (k : ℝ) ∧ ∀ N : ℝ, 2 ≤ N →
      2 ≤ (1 - ε) * ((k : ℝ) * Real.log N) ∧
      N ^ A ≤ N ^ k * planarHopping ((1 - ε) * ((k : ℝ) * Real.log N)) ∧
      N ^ k * planarHopping ((1 + ε) * ((k : ℝ) * Real.log N)) ≤ (N ^ A)⁻¹ := by
  obtain ⟨k, hk, hB, hγ, hd, hlo, hhi⟩ := exists_planar_scale_conditions_above B A hε hε₁
  refine ⟨k, hk, hB, fun N hN => ?_⟩
  have hNpos : 0 < N := by linarith
  have hlog : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN
  have hdN : 2 ≤ (1 - ε) * ((k : ℝ) * Real.log N) := hd.trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k)) (sub_pos.mpr hε₁).le)
  have hb := planar_polynomial_brackets hε.le hε₁.le hN hdN hγ hlo hhi
  have he : Real.exp ((k : ℝ) * Real.log N) = N ^ k := by
    rw [Real.exp_nat_mul, Real.exp_log hNpos]
  rw [he] at hb
  exact ⟨hdN, hb⟩

theorem exists_planar_polynomial_brackets (A : ℕ) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1) :
    ∃ k : ℕ, 0 < k ∧ ∀ N : ℝ, 2 ≤ N →
      2 ≤ (1 - ε) * ((k : ℝ) * Real.log N) ∧
      N ^ A ≤ N ^ k * planarHopping ((1 - ε) * ((k : ℝ) * Real.log N)) ∧
      N ^ k * planarHopping ((1 + ε) * ((k : ℝ) * Real.log N)) ≤ (N ^ A)⁻¹ := by
  obtain ⟨k, hk, _, h⟩ := exists_planar_polynomial_brackets_above 0 A hε hε₁
  exact ⟨k, hk, h⟩

end ContinuumCoulomb

end

end OAI
