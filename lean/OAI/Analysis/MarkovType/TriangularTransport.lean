import OAI.Analysis.MarkovType.TriangularBasic
import OAI.Analysis.MarkovType.FiniteMatching
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.NormNum

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

namespace TriangularSystem

variable {n : ℕ} {θ η : ℝ}

def scaleParameter (s : TriangularSystem X n θ)
    (hθ : 0 < θ) (hη : 0 ≤ η) (hηθ : η ≤ θ) :
    TriangularSystem X n η where
  vectors := s.vectors
  functionals j := (η / θ) • s.functionals j
  vectors_bound := s.vectors_bound
  functionals_bound j := by
    have hr0 : 0 ≤ η / θ := div_nonneg hη hθ.le
    have hr1 : η / θ ≤ 1 := (div_le_one hθ).mpr hηθ
    calc
      ‖(η / θ) • s.functionals j‖ = (η / θ) * ‖s.functionals j‖ := by
        rw [norm_smul (η / θ) (s.functionals j), Real.norm_eq_abs, abs_of_nonneg hr0]
      _ ≤ (η / θ) * 1 :=
        mul_le_mul_of_nonneg_left (s.functionals_bound j) hr0
      _ ≤ 1 := by simpa only [mul_one] using hr1
  pairing i j := by
    change (η / θ) * s.functionals j (s.vectors i) = _
    rw [s.pairing]
    by_cases hji : j ≤ i
    · simp only [ite_eq_left hji]
      exact div_mul_cancel₀ η (ne_of_gt hθ)
    · simp only [ite_eq_right hji, mul_zero]

def mapEquivOfBounds (s : TriangularSystem X n θ)
    (e : X ≃L[ℝ] Y) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ x, a * ‖x‖ ≤ ‖e x‖)
    (hupper : ∀ x, ‖e x‖ ≤ b * ‖x‖) :
    TriangularSystem Y n ((a / b) * θ) where
  vectors i := b⁻¹ • e (s.vectors i)
  functionals j := a • ((s.functionals j).comp e.symm.toContinuousLinearMap)
  vectors_bound i := by
    calc
      ‖b⁻¹ • e (s.vectors i)‖ = b⁻¹ * ‖e (s.vectors i)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb)]
      _ ≤ b⁻¹ * (b * ‖s.vectors i‖) :=
        mul_le_mul_of_nonneg_left (hupper _) (inv_nonneg.mpr hb.le)
      _ = ‖s.vectors i‖ := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hb), one_mul]
      _ ≤ 1 := s.vectors_bound i
  functionals_bound j := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    rw [one_mul]
    change ‖a • s.functionals j (e.symm y)‖ ≤ ‖y‖
    calc
      ‖a • s.functionals j (e.symm y)‖ = a * ‖s.functionals j (e.symm y)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      _ ≤ a * (‖s.functionals j‖ * ‖e.symm y‖) :=
        mul_le_mul_of_nonneg_left ((s.functionals j).le_opNorm _) ha.le
      _ ≤ a * (1 * ‖e.symm y‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (s.functionals_bound j) (norm_nonneg _)) ha.le
      _ = a * ‖e.symm y‖ := by rw [one_mul]
      _ ≤ ‖y‖ := by simpa only [e.apply_symm_apply] using hlower (e.symm y)
  pairing i j := by
    change a • s.functionals j (e.symm (b⁻¹ • e (s.vectors i))) = _
    rw [e.symm.map_smul, e.symm_apply_apply, (s.functionals j).map_smul, s.pairing]
    by_cases hji : j ≤ i
    · simp only [ite_eq_left hji, smul_eq_mul, div_eq_mul_inv, mul_assoc]
    · simp only [ite_eq_right hji, smul_zero]

def toDual (s : TriangularSystem X n θ) :
    TriangularSystem (StrongDual ℝ X) n θ where
  vectors i := s.functionals i.rev
  functionals j := NormedSpace.inclusionInDoubleDual ℝ X (s.vectors j.rev)
  vectors_bound i := s.functionals_bound i.rev
  functionals_bound j :=
    (NormedSpace.double_dual_bound ℝ X (s.vectors j.rev)).trans (s.vectors_bound j.rev)
  pairing i j := by
    change s.functionals i.rev (s.vectors j.rev) = if j ≤ i then θ else 0
    simpa only [Fin.rev_le_rev] using s.pairing j.rev i.rev

def ofDual (s : TriangularSystem (StrongDual ℝ X) n θ)
    {ε : ℝ} (hε : 0 < ε) : TriangularSystem X n (θ / (1 + ε)) := by
  classical
  have hmatch (j : Fin n) :
      ∃ x : X, ‖x‖ ≤ 1 + ε ∧ ∀ i, s.vectors i x = s.functionals j (s.vectors i) :=
    finite_matching_unit (s.functionals j) (s.functionals_bound j) s.vectors hε
  let x : Fin n → X := fun j => Classical.choose (hmatch j)
  have hx (j : Fin n) : ‖x j‖ ≤ 1 + ε := (Classical.choose_spec (hmatch j)).1
  have hpair (j i : Fin n) :
      s.vectors i (x j) = s.functionals j (s.vectors i) :=
    (Classical.choose_spec (hmatch j)).2 i
  have hc : 0 < 1 + ε := by linarith
  refine
    { vectors := fun i => (1 + ε)⁻¹ • x i.rev
      functionals := fun j => s.vectors j.rev
      vectors_bound := ?_
      functionals_bound := fun j => s.vectors_bound j.rev
      pairing := ?_ }
  · intro i
    calc
      ‖(1 + ε)⁻¹ • x i.rev‖ = (1 + ε)⁻¹ * ‖x i.rev‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
      _ ≤ (1 + ε)⁻¹ * (1 + ε) :=
        mul_le_mul_of_nonneg_left (hx _) (inv_nonneg.mpr hc.le)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hc)
  · intro i j

    rw [(s.vectors j.rev).map_smul, hpair, s.pairing]
    simp only [Fin.rev_le_rev]
    by_cases hji : j ≤ i
    · simp only [ite_eq_left hji, smul_eq_mul, div_eq_mul_inv, mul_comm]
    · simp only [ite_eq_right hji, smul_zero]

end TriangularSystem

theorem finiteTriangularObstruction_of_equiv_bounds
    (e : X ≃L[ℝ] Y) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b)
    (hlower : ∀ x, a * ‖x‖ ≤ ‖e x‖)
    (hupper : ∀ x, ‖e x‖ ≤ b * ‖x‖)
    (hY : FiniteTriangularObstruction Y) : FiniteTriangularObstruction X := by
  intro θ hθ hθ1
  have hr0 : 0 < a / b := div_pos ha hb
  have hr1 : a / b ≤ 1 := (div_le_one hb).mpr hab
  have hparam : (a / b) * θ < 1 :=
    lt_of_le_of_lt (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hr1 hθ.le) hθ1
  obtain ⟨n, hn, hnone⟩ := hY ((a / b) * θ) (mul_pos hr0 hθ) hparam
  refine ⟨n, hn, ?_⟩
  rintro ⟨s⟩
  exact hnone ⟨s.mapEquivOfBounds e ha hb hlower hupper⟩

theorem finiteTriangularObstruction_of_equiv
    (e : X ≃L[ℝ] Y) (hY : FiniteTriangularObstruction Y) :
    FiniteTriangularObstruction X := by
  let A : ℝ := ‖e.toContinuousLinearMap‖ + 1
  let B : ℝ := ‖e.symm.toContinuousLinearMap‖ + 1
  have hA1 : 1 ≤ A := by dsimp [A]; linarith [norm_nonneg e.toContinuousLinearMap]
  have hB1 : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg e.symm.toContinuousLinearMap]
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hiB : 0 < B⁻¹ := inv_pos.mpr hB
  have hiB1 : B⁻¹ ≤ 1 := by
    rw [← one_div]
    exact (div_le_one hB).mpr hB1
  apply finiteTriangularObstruction_of_equiv_bounds e hiB hA (hiB1.trans hA1) ?_ ?_ hY
  · intro x
    have hbase : ‖x‖ ≤ B * ‖e x‖ := by
      calc
        ‖x‖ = ‖e.symm (e x)‖ := by rw [e.symm_apply_apply]
        _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e x‖ :=
          e.symm.toContinuousLinearMap.le_opNorm (e x)
        _ ≤ B * ‖e x‖ :=
          mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (norm_nonneg _)
    calc
      B⁻¹ * ‖x‖ ≤ B⁻¹ * (B * ‖e x‖) :=
        mul_le_mul_of_nonneg_left hbase hiB.le
      _ = ‖e x‖ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hB), one_mul]
  · intro x
    exact (e.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) (norm_nonneg x))

theorem finiteTriangularObstruction_equiv_iff (e : X ≃L[ℝ] Y) :
    FiniteTriangularObstruction X ↔ FiniteTriangularObstruction Y :=
  ⟨fun hX => finiteTriangularObstruction_of_equiv e.symm hX,
    fun hY => finiteTriangularObstruction_of_equiv e hY⟩

theorem finiteTriangularObstruction_dual_iff :
    FiniteTriangularObstruction X ↔
      FiniteTriangularObstruction (StrongDual ℝ X) := by
  constructor
  · intro hX θ hθ hθ1
    have hhalf : 0 < θ / 2 := div_pos hθ (by norm_num)
    have hhalf1 : θ / 2 < 1 := by linarith
    obtain ⟨n, hn, hnone⟩ := hX (θ / 2) hhalf hhalf1
    refine ⟨n, hn, ?_⟩
    rintro ⟨s⟩
    apply hnone
    exact ⟨by simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using
      s.ofDual (by norm_num : (0 : ℝ) < 1)⟩
  · intro hD θ hθ hθ1
    obtain ⟨n, hn, hnone⟩ := hD θ hθ hθ1
    refine ⟨n, hn, ?_⟩
    rintro ⟨s⟩
    exact hnone ⟨s.toDual⟩

end MarkovSuperreflexivity

end

end OAI
