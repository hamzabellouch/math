import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeMass

namespace OAI

/-! Mertens weights on the geometric bands of log(X/p) in the adaptive
double convolution. The bounds remain valid for the last band near p=2. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_mem_prime_band {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {p : ℕ} (hp : p.Prime) (hap : a < p) (hpb : (p : ℝ) ≤ b) :
    p ∈ mrtPrimeBand a b := by
  apply mem_sdiff.mpr
  constructor
  · exact mem_filter.mpr ⟨mem_Iic.mpr ((Nat.le_floor_iff hb).mpr hpb), hp⟩
  · intro h
    have hpa := (Nat.le_floor_iff ha).mp (mem_Iic.mp (mem_filter.mp h).1)
    linarith

lemma halasz_log_band_endpoints {X v : ℝ} (hX : 0 < X)
    {p : ℕ} (hp : p.Prime)
    (hlo : v ≤ Real.log (X / p)) (hhi : Real.log (X / p) < 2 * v) :
    X / Real.exp (2 * v) < p ∧ (p : ℝ) ≤ X / Real.exp v := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hxquot : 0 < X / p := div_pos hX hp0
  have hexlo : Real.exp v ≤ X / p := (Real.le_log_iff_exp_le hxquot).mp hlo
  have hexhi : X / p < Real.exp (2 * v) := (Real.log_lt_iff_lt_exp hxquot).mp hhi
  constructor
  · apply (div_lt_iff₀ (Real.exp_pos _)).mpr
    have h := (div_lt_iff₀ hp0).mp hexhi
    nlinarith
  · apply (le_div_iff₀ (Real.exp_pos _)).mpr
    have h := (le_div_iff₀ hp0).mp hexlo
    nlinarith

theorem halasz_log_band_mass {X v : ℝ} (hX : 0 < X) (hv : 0 < v)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧
      v ≤ Real.log (X / p) ∧ Real.log (X / p) < 2 * v) :
    (∑ p ∈ P, Real.log (p : ℝ) / p) ≤ v + 2 * halaszMertensConstant := by
  let a := max 1 (X / Real.exp (2 * v))
  let b := X / Real.exp v
  have hb0 : 0 < b := div_pos hX (Real.exp_pos _)
  by_cases hb : 1 ≤ b
  · have hlower : X / Real.exp (2 * v) ≤ b :=
      div_le_div_of_nonneg_left hX.le (Real.exp_pos _)
        (Real.exp_le_exp.mpr (by linarith))
    have ha : 1 ≤ a := le_max_left _ _
    have hab : a ≤ b := max_le hb hlower
    have hsub : P ⊆ mrtPrimeBand a b := by
      intro p hp
      obtain ⟨hprime, hlo, hhi⟩ := hP p hp
      obtain ⟨hpa, hpb⟩ := halasz_log_band_endpoints hX hprime hlo hhi
      exact halasz_mem_prime_band (by dsimp [a]; positivity) hb0.le hprime
        (max_lt (by exact_mod_cast hprime.one_lt) hpa) hpb
    have hsum := sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => Real.log (p : ℝ) / p)
      hsub (fun p hp _ =>
      div_nonneg (Real.log_nonneg (by exact_mod_cast (mrtPrimeBand_prime hp).one_le))
        (Nat.cast_nonneg _))
    have hlog : Real.log b - Real.log a ≤ v := by
      have hloga : Real.log (X / Real.exp (2 * v)) ≤ Real.log a :=
        Real.log_le_log (div_pos hX (Real.exp_pos _)) (le_max_right _ _)
      rw [Real.log_div hX.ne' (Real.exp_ne_zero _), Real.log_exp] at hloga
      dsimp [b]
      rw [Real.log_div hX.ne' (Real.exp_ne_zero _), Real.log_exp]
      linarith
    exact hsum.trans ((halasz_prime_band_mass_le ha hab).trans (by linarith))
  · have hempty : P = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hprime, hlo, hhi⟩ := hP p hp
      have hpb := (halasz_log_band_endpoints hX hprime hlo hhi).2
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
      linarith
    rw [hempty, sum_empty]
    exact add_nonneg hv.le (mul_nonneg (by norm_num) halaszMertensConstant_nonneg)

theorem halasz_log_band_mass_linear {X v : ℝ} (hX : 0 < X) (hv : Real.log 2 ≤ v)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧
      v ≤ Real.log (X / p) ∧ Real.log (X / p) < 2 * v) :
    (∑ p ∈ P, Real.log (p : ℝ) / p) ≤
      (1 + 2 * halaszMertensConstant / Real.log 2) * v := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (halasz_log_band_mass hX (htwo.trans_le hv) P hP).trans
  have hm := mul_le_mul_of_nonneg_left hv
    (show 0 ≤ 2 * halaszMertensConstant / Real.log 2 from
      div_nonneg (mul_nonneg (by norm_num) halaszMertensConstant_nonneg) htwo.le)
  rw [div_mul_cancel₀ _ htwo.ne'] at hm
  nlinarith

end TwoPointCorrelations

end OAI
