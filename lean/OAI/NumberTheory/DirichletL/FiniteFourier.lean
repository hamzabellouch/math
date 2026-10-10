import Mathlib.NumberTheory.GaussSum
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ByContra

namespace OAI

open scoped BigOperators

namespace SevenEighths.FiniteFourier

noncomputable section

variable {R : Type*} [CommRing R] [Fintype R]

def IsPrimitiveOnIdeals (χ : MulChar R ℂ) : Prop :=
  ∀ I : Ideal R, I ≠ ⊥ → ∃ u : Rˣ, (u : R) - 1 ∈ I ∧ χ (u : R) ≠ 1

theorem IsPrimitiveOnIdeals.inv {χ : MulChar R ℂ} (hχ : IsPrimitiveOnIdeals χ) :
    IsPrimitiveOnIdeals χ⁻¹ := by
  intro I hI
  obtain ⟨u, hu, hχu⟩ := hχ I hI
  refine ⟨u, hu, ?_⟩
  intro hinv
  apply hχu
  simpa only [← MulChar.star_apply', star_star, star_one] using congrArg star hinv

theorem primitiveOnIdeals_of_field {F : Type*} [Field F]
    (χ : MulChar F ℂ) (hχ : χ ≠ 1) : IsPrimitiveOnIdeals χ := by
  intro I hI
  have htop : I = ⊤ := (Ideal.eq_bot_or_top I).resolve_left hI
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hχ
  exact ⟨u, by rw [htop]; trivial, hu⟩

def transform (ψ : AddChar R ℂ) (f : R → ℂ) (a : R) : ℂ :=
  ∑ x : R, f x * ψ (a * x)

theorem transform_inversion (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (f : R → ℂ) (x : R) :
    (∑ a : R, transform ψ f a * ψ (-(a * x))) =
      (Fintype.card R : ℂ) * f x := by
  classical
  simp only [transform, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ y : R, ∑ a : R, f y * ψ (a * y) * ψ (-(a * x))) =
        ∑ y : R, f y * ∑ a : R, ψ (a * (y - x)) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = (Fintype.card R : ℂ) * f x := by
      simp only [AddChar.sum_mulShift _ hψ, sub_eq_zero]
      simp [mul_ite, mul_comm]

theorem exists_nonzero_annihilator {a : R} (ha : ¬ IsUnit a) :
    ∃ b : R, b ≠ 0 ∧ a * b = 0 := by
  by_contra! h
  apply ha
  apply IsLeftRegular.isUnit_of_finite
  apply isLeftRegular_iff_right_eq_zero_of_mul.mpr
  intro b hb
  by_contra hb0
  exact h b hb0 hb

theorem exists_unit_stabilizer (χ : MulChar R ℂ) (hχ : IsPrimitiveOnIdeals χ)
    {a : R} (ha : ¬ IsUnit a) :
    ∃ u : Rˣ, a * (u : R) = a ∧ χ (u : R) ≠ 1 := by
  obtain ⟨b, hb, hab⟩ := exists_nonzero_annihilator ha
  have hI : Ideal.span ({b} : Set R) ≠ ⊥ := by
    intro hI
    have hbI := Ideal.mem_span_singleton_self b
    rw [hI] at hbI
    exact hb hbI
  obtain ⟨u, hu, hχu⟩ := hχ _ hI
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hu
  refine ⟨u, ?_, hχu⟩
  have hzero : a * ((u : R) - 1) = 0 := by
    rw [hc, ← mul_assoc, hab, zero_mul]
  linear_combination hzero

theorem gaussSum_mulShift_nonunit_eq_zero (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ)
    {a : R} (ha : ¬ IsUnit a) :
    gaussSum χ (ψ.mulShift a) = 0 := by
  obtain ⟨u, hu, hχu⟩ := exists_unit_stabilizer χ hχ ha
  have hshift : (ψ.mulShift a).mulShift (u : R) = ψ.mulShift a := by
    ext x
    simp only [AddChar.mulShift_apply, ← mul_assoc, hu]
  have heq := gaussSum_mulShift χ (ψ.mulShift a) u
  rw [hshift] at heq
  exact eq_zero_of_mul_eq_self_left hχu heq

theorem primitive_gaussSum_mulShift (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (a : R) :
    gaussSum χ (ψ.mulShift a) = χ⁻¹ a * gaussSum χ ψ := by
  by_cases ha : IsUnit a
  · simpa only [ha.unit_spec] using gaussSum_mulShift_eq χ ψ ha.unit
  · rw [gaussSum_mulShift_nonunit_eq_zero χ hχ ψ ha,
      MulChar.map_nonunit _ ha, zero_mul]

theorem transform_primitive_character (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (a : R) :
    transform ψ χ a = χ⁻¹ a * gaussSum χ ψ := by
  exact primitive_gaussSum_mulShift χ hχ ψ a

theorem primitive_gaussSum_mul_conjugate (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * star (gaussSum χ ψ) = (Fintype.card R : ℂ) := by
  have hinv := transform_inversion ψ hψ (fun x => χ x) 1
  simp only [transform_primitive_character χ hχ, mul_one, map_one, mul_one] at hinv
  rw [star_gaussSum_eq]
  calc
    gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ =
        ∑ a : R, (χ⁻¹ a * gaussSum χ ψ) * ψ (-a) := by
      change gaussSum χ ψ * (∑ a : R, χ⁻¹ a * ψ⁻¹ a) = _
      rw [Finset.mul_sum]
      simp only [AddChar.inv_apply]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = (Fintype.card R : ℂ) := hinv

theorem primitive_gaussSum_norm_sq (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card R : ℝ) := by
  apply Complex.ofReal_inj.mp
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  simpa only [starRingEnd_apply, mul_comm, Complex.ofReal_natCast] using
    primitive_gaussSum_mul_conjugate χ hχ ψ hψ

theorem primitive_gaussSum_norm (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card R : ℝ) := by
  rw [← primitive_gaussSum_norm_sq χ hχ ψ hψ, Real.sqrt_sq (norm_nonneg _)]

theorem primitive_gaussSum_ne_zero (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ≠ 0 := by
  intro hzero
  have h := primitive_gaussSum_mul_conjugate χ hχ ψ hψ
  rw [hzero, zero_mul] at h
  exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) h.symm

theorem primitive_character_expansion (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (a : R) :
    χ a = (∑ x : R, χ⁻¹ x * ψ (a * x)) / gaussSum χ⁻¹ ψ := by
  apply (eq_div_iff (primitive_gaussSum_ne_zero χ⁻¹ hχ.inv ψ hψ)).mpr
  simpa only [inv_inv, transform] using
    (transform_primitive_character χ⁻¹ hχ.inv ψ a).symm

end

end SevenEighths.FiniteFourier

end OAI
