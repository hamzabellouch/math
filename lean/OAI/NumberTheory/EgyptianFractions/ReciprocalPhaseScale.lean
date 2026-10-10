import Mathlib

namespace OAI
noncomputable section

namespace Problem337

/-- Choose a bounded derivative order placing the reciprocal phase in the
second-derivative scale after differencing. -/
theorem reciprocal_phase_order {U Z B : ℝ} (hU : 1 < U) (_hB : 4 ≤ B)
    (hlower : U ^ (4 : ℕ) ≤ |Z|) (hupper : |Z| ≤ U ^ B) :
    ∃ k : ℕ, 4 ≤ k ∧ k ≤ Nat.ceil B + 1 ∧
      U ^ (-(3 : ℝ) / 2) ≤ |Z| * U ^ (-((k : ℝ) + 1)) ∧
      |Z| * U ^ (-((k : ℝ) + 1)) ≤ U ^ (-(1 : ℝ) / 2) := by
  have hU0 : 0 < U := by linarith
  have hlogU : 0 < Real.log U := Real.log_pos hU
  have hZ0 : 0 < |Z| := (pow_pos hU0 4).trans_le hlower
  let a : ℝ := Real.log |Z| / Real.log U
  have ha4 : 4 ≤ a := by
    apply (le_div_iff₀ hlogU).2
    have h := Real.log_le_log (pow_pos hU0 4) hlower
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have haB : a ≤ B := by
    apply (div_le_iff₀ hlogU).2
    have h := Real.log_le_log hZ0 hupper
    rwa [Real.log_rpow hU0] at h
  let k : ℕ := Nat.floor (a + 1 / 2)
  have ha0 : 0 ≤ a + 1 / 2 := by linarith
  have hklo : (k : ℝ) ≤ a + 1 / 2 := Nat.floor_le ha0
  have hkhi : a + 1 / 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hk4 : 4 ≤ k := (Nat.le_floor_iff ha0).2 (by norm_num; linarith)
  have hkB : k ≤ Nat.ceil B + 1 := by
    have hceil := Nat.le_ceil B
    have h : (k : ℝ) ≤ (Nat.ceil B : ℝ) + 1 := by linarith
    exact_mod_cast h
  have hZa : |Z| = U ^ a := by
    rw [Real.rpow_def_of_pos hU0]
    have heq : Real.log U * a = Real.log |Z| := by
      dsimp [a]
      field_simp
    rw [heq, Real.exp_log hZ0]
  refine ⟨k, hk4, hkB, ?_, ?_⟩ <;>
    rw [hZa, ← Real.rpow_add hU0]
  · exact Real.rpow_le_rpow_of_exponent_le hU.le (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_le hU.le (by linarith)

/-- The product of a bounded number of short shifts costs at most `U^(1/10)`. -/
theorem reciprocal_shift_product {U : ℝ} (hU : 1 < U) {k : ℕ} (hk : 1 ≤ k)
    (hs : List ℝ) (hlen : hs.length ≤ k)
    (hhs : ∀ h ∈ hs, 1 ≤ h ∧ h ≤ U ^ (1 / (10 * (k : ℝ)))) :
    1 ≤ hs.prod ∧ hs.prod ≤ U ^ ((1 : ℝ) / 10) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hU0 : 0 < U := by linarith
  refine ⟨List.one_le_prod (fun h hh => (hhs h hh).1), ?_⟩
  have hp : hs.prod ≤ (U ^ (1 / (10 * (k : ℝ)))) ^ hs.length := by
    have h := List.prod_map_le_prod_map₀ (s := hs) (fun x : ℝ => x)
      (fun _ => U ^ (1 / (10 * (k : ℝ))))
      (fun h hh => le_trans (by norm_num) (hhs h hh).1)
      (fun h hh => (hhs h hh).2)
    simpa [List.map_const, List.prod_replicate] using h
  rw [← Real.rpow_mul_natCast hU0.le] at hp
  apply hp.trans
  apply Real.rpow_le_rpow_of_exponent_le hU.le
  have hlenR : (hs.length : ℝ) ≤ k := by exact_mod_cast hlen
  calc
    1 / (10 * (k : ℝ)) * (hs.length : ℝ) = (hs.length : ℝ) / (10 * (k : ℝ)) := by ring
    _ ≤ 1 / 10 := (div_le_iff₀ (by positivity)).2 (by nlinarith)

/-- The derivative scale after the short shifts is uniformly a small negative power. -/
theorem reciprocal_phase_shift_scale {U Z : ℝ} (hU : 1 < U) {k : ℕ} (hk : 1 ≤ k)
    (hlower : U ^ (-(3 : ℝ) / 2) ≤ |Z| * U ^ (-((k : ℝ) + 1)))
    (hupper : |Z| * U ^ (-((k : ℝ) + 1)) ≤ U ^ (-(1 : ℝ) / 2))
    (hs : List ℝ) (hlen : hs.length ≤ k)
    (hhs : ∀ h ∈ hs, 1 ≤ h ∧ h ≤ U ^ (1 / (10 * (k : ℝ)))) :
    U ^ (-(3 : ℝ) / 2) ≤ |Z| * U ^ (-((k : ℝ) + 1)) * hs.prod ∧
    |Z| * U ^ (-((k : ℝ) + 1)) * hs.prod ≤ U ^ (-(2 : ℝ) / 5) := by
  have hU0 : 0 < U := by linarith
  obtain ⟨hplo, hphi⟩ := reciprocal_shift_product hU hk hs hlen hhs
  have hbase0 : 0 ≤ |Z| * U ^ (-((k : ℝ) + 1)) := by positivity
  constructor
  · exact hlower.trans (le_mul_of_one_le_right hbase0 hplo)
  · calc
      |Z| * U ^ (-((k : ℝ) + 1)) * hs.prod ≤
          U ^ (-(1 : ℝ) / 2) * U ^ ((1 : ℝ) / 10) :=
        mul_le_mul hupper hphi (by linarith) (by positivity)
      _ = U ^ (-(2 : ℝ) / 5) := by rw [← Real.rpow_add hU0]; norm_num

end Problem337

end

end OAI
