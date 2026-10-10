import OAI.GroupTheory.PolycyclicRecognition.Algebra.CocycleCombing
import OAI.GroupTheory.PolycyclicRecognition.Algebra.LogDistortion
import Mathlib.Algebra.Order.Floor.Semiring

namespace OAI

/-! # Sublinear cocycles on contracting root flows

An almost coboundary is sublinear on each one-parameter subgroup. Conjugating
a root vector into a fixed compact ball then gives a bound with arbitrarily
small coefficient of the logarithm of its norm.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ρ : G →* (E ≃ₗᵢ[ℝ] E)} {b : G → E}

theorem IsUnitaryCocycle.norm_inv (hb : IsUnitaryCocycle ρ b) (g : G) :
    ‖b g⁻¹‖ = ‖b g‖ := by
  have he : b g + ρ g (b g⁻¹) = 0 := by rw [← hb g g⁻¹, mul_inv_cancel, hb.map_one]
  have hi : ρ g (b g⁻¹) = -b g := by
    calc
      _ = (b g + ρ g (b g⁻¹)) - b g := by abel
      _ = -b g := by rw [he, zero_sub]
  simpa only [(ρ g).norm_map, norm_neg] using congrArg norm hi

theorem IsUnitaryCocycle.norm_conjugate_le (hb : IsUnitaryCocycle ρ b) (g x : G) :
    ‖b (g * x * g⁻¹)‖ ≤ 2 * ‖b g‖ + ‖b x‖ := by
  have h := (hb.norm_mul_le (g * x) g⁻¹).trans
    (add_le_add (hb.norm_mul_le g x) le_rfl)
  rw [hb.norm_inv] at h
  linarith

theorem IsUnitaryCocycle.sublinear_flow_of_approximation (hb : IsUnitaryCocycle ρ b)
    (d : ℝ → G) (hd0 : d 0 = 1) (hmul : ∀ s t, d (s + t) = d s * d t)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ φ : E,
      ∀ t ∈ Icc (0 : ℝ) 1, ‖b (d t) + ρ (d t) φ - φ‖ ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ t, 1 ≤ t → ‖b (d t)‖ ≤ ε * t + B := by
  let := unitaryDistribMulAction ρ
  let : IsIsometricSMul G E := ⟨fun g => (ρ g).isometry⟩
  have hb' : IsCocycle b := hb
  have hpower (s : ℝ) (n : ℕ) : d ((n : ℝ) * s) = d s ^ n := by
    induction n with
    | zero => simp [hd0]
    | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, hmul, ih, pow_succ]
  intro ε hε
  obtain ⟨φ, hφ⟩ := happrox (ε / 2) (half_pos hε)
  refine ⟨2 * ‖φ‖, by positivity, fun t ht => ?_⟩
  let n := ⌊t⌋₊ + 1
  have hn : 0 < (n : ℝ) := by dsimp [n]; positivity
  have htn : t ≤ (n : ℝ) := by simpa [n] using (Nat.lt_floor_add_one t).le
  have hnt : (n : ℝ) ≤ t + 1 := by
    simpa [n] using add_le_add_right (Nat.floor_le (by linarith : 0 ≤ t)) 1
  have hunit : t / n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith) hn.le, (div_le_one hn).mpr htn⟩
  have he : (List.replicate n (d (t / n))).prod = d t := by
    rw [List.prod_replicate, ← hpower]
    congr 1
    field_simp
  have hbound := hb'.norm_word_le_of_coboundary (d '' Icc (0 : ℝ) 1) φ
    (fun q hq => by obtain ⟨s, hs, rfl⟩ := hq; exact hφ s hs)
    (List.replicate n (d (t / n))) (fun q hq => by
      have hq' : q = d (t / n) := (List.mem_replicate.mp hq).2
      exact hq' ▸ ⟨t / n, hunit, rfl⟩)
  rw [he, List.length_replicate] at hbound
  exact hbound.trans (by nlinarith)

theorem IsUnitaryCocycle.sublinear_log_of_contracting_flow (hb : IsUnitaryCocycle ρ b)
    {V : Type*} [NormedAddCommGroup V]
    (Exp : V → G) (d : ℝ → G) (T : ℝ → V → V)
    {C : ℝ} (hC : 0 ≤ C) (k : ℕ)
    (hconj : ∀ v t, 0 ≤ t → Exp v = d t * Exp (T t v) * (d t)⁻¹)
    (hcontract : ∀ v t, 0 ≤ t → ‖T t v‖ ≤ C * (1 + t) ^ k * Real.exp (-t) * ‖v‖)
    (hlocal : ∃ M : ℝ, 0 ≤ M ∧ ∀ v, ‖v‖ ≤ 1 → ‖b (Exp v)‖ ≤ M)
    (hpath : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧
      ∀ t, 1 ≤ t → ‖b (d t)‖ ≤ ε * t + B) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧
      ∀ v, ‖b (Exp v)‖ ≤ ε * Real.log (2 + ‖v‖) + B := by
  obtain ⟨a, ha, htime⟩ := exists_logarithmic_contraction_time hC k
  obtain ⟨M, hM, hlocal⟩ := hlocal
  intro ε hε
  obtain ⟨B, hB, hpath⟩ := hpath (ε / 4) (by positivity)
  refine ⟨2 * (ε / 4) * a + 2 * B + M, by positivity, fun v => ?_⟩
  let t := 2 * Real.log (2 + ‖v‖) + a
  obtain ⟨ht, hsmall⟩ := htime ‖v‖ (norm_nonneg v)
  have hunit : ‖T t v‖ ≤ 1 := (hcontract v t (by linarith)).trans hsmall
  rw [hconj v t (by linarith)]
  have h := (hb.norm_conjugate_le (d t) (Exp (T t v))).trans
    (add_le_add (mul_le_mul_of_nonneg_left (hpath t ht) (by norm_num)) (hlocal _ hunit))
  dsimp [t] at h
  nlinarith

end PolycyclicRecognition

end

end OAI
