import OAI.GroupTheory.PolycyclicRecognition.Geometry.CocycleContractingFlow
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SwitchBounds

namespace OAI

/-! # Sublinear bounds for bounded root words

A finite family of root-coordinate logarithmic estimates is uniform on
bounded words with polynomial-exponential amplitude bounds.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G E I : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ρ : G →* (E ≃ₗᵢ[ℝ] E)} {b : G → E}

omit [Group G] [InnerProductSpace ℝ E] in
theorem sublinear_log_along_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V → E)
    (hf : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧
      ∀ v, ‖f v‖ ≤ ε * Real.log (2 + ‖v‖) + B) (v : V) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧
      ∀ t : ℝ, ‖f (t • v)‖ ≤ ε * Real.log (2 + |t|) + B := by
  intro ε hε
  obtain ⟨B, hB, hf⟩ := hf ε hε
  have hlog : 0 ≤ Real.log (2 + ‖v‖) := Real.log_nonneg (by linarith [norm_nonneg v])
  refine ⟨ε * Real.log (2 + ‖v‖) + B, by positivity, fun t => ?_⟩
  have hsize : 2 + ‖t • v‖ ≤ (2 + ‖v‖) * (2 + |t|) := by
    rw [norm_smul, Real.norm_eq_abs]
    nlinarith [norm_nonneg v, abs_nonneg t]
  have hl := Real.log_le_log (by positivity : 0 < 2 + ‖t • v‖) hsize
  rw [Real.log_mul (by positivity) (by positivity)] at hl
  have h := (hf (t • v)).trans
    (add_le_add (mul_le_mul_of_nonneg_left hl hε.le) le_rfl)
  linarith

theorem IsUnitaryCocycle.norm_word_le (hb : IsUnitaryCocycle ρ b)
    (Q : Set G) {B : ℝ} (hQ : ∀ g ∈ Q, ‖b g‖ ≤ B)
    (l : List G) (hl : ∀ g ∈ l, g ∈ Q) : ‖b l.prod‖ ≤ (l.length : ℝ) * B := by
  let := unitaryDistribMulAction ρ
  let : IsIsometricSMul G E := ⟨fun g => (ρ g).isometry⟩
  exact IsCocycle.norm_word_le hb Q hQ l hl

theorem IsUnitaryCocycle.sublinear_bounded_log_words [Fintype I]
    (hb : IsUnitaryCocycle ρ b) (root : I → ℝ → G)
    (hroot : ∀ i, ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧
      ∀ t, ‖b (root i t)‖ ≤ ε * Real.log (2 + |t|) + B)
    (k p : ℕ) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 ≤ r →
      ∀ u : List (I × ℝ), u.length ≤ k →
      (∀ z ∈ u, |z.2| ≤ C * (1 + r) ^ p * Real.exp (r * c)) →
      ‖b (u.map (fun z => root z.1 z.2)).prod‖ ≤ ε * r + B := by
  classical
  intro ε hε
  let D := (k : ℝ) * ((p : ℝ) + c + 1) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  let δ := ε / D
  have hδ : 0 < δ := div_pos hε hD
  choose B hB hbroot using fun i => hroot i δ hδ
  let M := ∑ i, B i
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => hB i)
  have hBi (i : I) : B i ≤ M := Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ i)
  have hlogC : 0 ≤ Real.log (2 + C) := Real.log_nonneg (by linarith)
  have hcoef : (k : ℝ) * δ * ((p : ℝ) + c) ≤ ε := by
    have hle : (k : ℝ) * ((p : ℝ) + c) ≤ D := by dsimp [D]; nlinarith
    calc
      _ = δ * ((k : ℝ) * ((p : ℝ) + c)) := by ring
      _ ≤ δ * D := mul_le_mul_of_nonneg_left hle hδ.le
      _ = ε := div_mul_cancel₀ _ hD.ne'
  refine ⟨(k : ℝ) * (δ * Real.log (2 + C) + M), by positivity, ?_⟩
  intro r hr u hu hamp
  let Q : Set G := {g | ∃ i t, |t| ≤ C * (1 + r) ^ p * Real.exp (r * c) ∧ root i t = g}
  have hQ : ∀ g ∈ Q, ‖b g‖ ≤ δ * (Real.log (2 + C) + ((p : ℝ) + c) * r) + M := by
    rintro g ⟨i, t, ht, rfl⟩
    have hlog := Real.log_le_log (by positivity : 0 < 2 + |t|) (add_le_add le_rfl ht)
    have hlogr : Real.log (1 + r) ≤ r := by
      linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + r)]
    have hlarge : Real.log (2 + |t|) ≤ Real.log (2 + C) + ((p : ℝ) + c) * r := by
      have h := hlog.trans (log_polynomial_exp_le hC hr hc p)
      nlinarith [mul_le_mul_of_nonneg_left hlogr (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
    exact (hbroot i t).trans (add_le_add (mul_le_mul_of_nonneg_left hlarge hδ.le) (hBi i))
  have hword := hb.norm_word_le Q hQ (u.map (fun z => root z.1 z.2)) (by
    intro g hg
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hg
    exact ⟨z.1, z.2, hamp z hz, rfl⟩)
  rw [List.length_map] at hword
  have hbound : 0 ≤ δ * (Real.log (2 + C) + ((p : ℝ) + c) * r) + M := by positivity
  calc
    ‖b (u.map (fun z => root z.1 z.2)).prod‖ ≤
        (u.length : ℝ) * (δ * (Real.log (2 + C) + ((p : ℝ) + c) * r) + M) := hword
    _ ≤ (k : ℝ) * (δ * (Real.log (2 + C) + ((p : ℝ) + c) * r) + M) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hu) hbound
    _ = ((k : ℝ) * δ * ((p : ℝ) + c)) * r +
        (k : ℝ) * (δ * Real.log (2 + C) + M) := by ring
    _ ≤ ε * r + (k : ℝ) * (δ * Real.log (2 + C) + M) :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef hr) le_rfl

end PolycyclicRecognition

end

end OAI
