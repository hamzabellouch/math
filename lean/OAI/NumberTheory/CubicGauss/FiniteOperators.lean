import Mathlib

namespace OAI

/-! Finite Fourier orthogonality and row-column operator duality. -/

noncomputable section
open scoped BigOperators
open Module Complex UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment.SieveFourier
variable {R : Type*} [CommRing R] [Fintype R]

lemma finite_fourier_parseval (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (f : R → ℂ) :
    (∑ a : R, ‖∑ x : R, f x * ψ (a*x)‖^2) =
      (Fintype.card R : ℝ) * ∑ x : R, ‖f x‖^2 := by
  classical
  have hcomplex :
      (∑ a : R, (∑ x : R, f x * ψ (a*x)) * star (∑ x : R, f x * ψ (a*x))) =
        (Fintype.card R : ℂ) * ∑ x : R, f x * star (f x) := by
    simp_rw [star_sum, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    apply Eq.trans (Finset.sum_congr rfl fun x _ => Finset.sum_comm)
    have he (x y a : R) :
        f x * ψ (a*x) * star (f y * ψ (a*y)) =
          (f x * star (f y)) * ψ (a*(x-y)) := by
      rw [star_mul]
      have hc : star (ψ (a*y)) = ψ (-(a*y)) := by
        exact (ψ.map_neg_eq_conj (a*y)).symm
      rw [hc]
      rw [show f x * ψ (a*x) * (ψ (-(a*y)) * star (f y)) =
        (f x * star (f y)) * (ψ (a*x) * ψ (-(a*y))) by ring]
      rw [← ψ.map_add_eq_mul]
      congr 2
      ring
    simp_rw [he, ← Finset.mul_sum, AddChar.sum_mulShift _ hψ]
    simp only [sub_eq_zero, Nat.cast_ite, Nat.cast_zero, mul_ite, mul_zero]
    simp [Finset.mul_sum, mul_comm]
  simp only [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_sum,
    ← Complex.ofReal_natCast, ← Complex.ofReal_mul] at hcomplex
  have hre := congrArg Complex.re hcomplex
  simpa only [map_sum, Complex.mul_conj, Complex.ofReal_re, Complex.re_sum,
    Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero,
    Complex.normSq_eq_norm_sq] using hre

lemma saturated_gauss_nonunit (χ : MulChar R ℂ) (ψ : AddChar R ℂ)
    (hψ : ψ.IsPrimitive) (hG : ‖gaussSum χ ψ‖^2 = (Fintype.card R : ℝ))
    {a : R} (ha : ¬IsUnit a) : gaussSum χ (ψ.mulShift a) = 0 := by
  classical
  let d : R → ℝ := fun b => ‖gaussSum χ (ψ.mulShift b)‖^2 -
    (Fintype.card R : ℝ) * ‖χ b‖^2
  have hd (b : R) : 0 ≤ d b := by
    by_cases hb : IsUnit b
    · have he := gaussSum_mulShift_eq χ ψ hb.unit
      rw [hb.unit_spec] at he
      have hn : ‖χ⁻¹ b‖ = 1 := by
        simpa only [MulChar.coe_equivToUnitHom, hb.unit_spec] using Complex.norm_eq_one_of_mem_rootsOfUnity
          (MulChar.apply_mem_rootsOfUnity (χ := χ⁻¹) hb.unit)
      have hn' : ‖χ b‖ = 1 := by
        simpa only [MulChar.coe_equivToUnitHom, hb.unit_spec] using Complex.norm_eq_one_of_mem_rootsOfUnity
          (MulChar.apply_mem_rootsOfUnity (χ := χ) hb.unit)
      simp [d, he, hn, hn', hG]
    · simp [d, MulChar.map_nonunit _ hb]
  have hs : ∑ b : R, d b = 0 := by
    simp only [d, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hp := finite_fourier_parseval ψ hψ χ
    simpa only [gaussSum, AddChar.mulShift_apply, sub_eq_zero] using hp
  have hz : d a = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hd b)).mp hs a
    (Finset.mem_univ a)
  simpa [d, MulChar.map_nonunit _ ha] using hz

lemma saturated_gauss_mulShift (χ : MulChar R ℂ) (ψ : AddChar R ℂ)
    (hψ : ψ.IsPrimitive) (hG : ‖gaussSum χ ψ‖^2 = (Fintype.card R : ℝ)) (a : R) :
    gaussSum χ (ψ.mulShift a) = χ⁻¹ a * gaussSum χ ψ := by
  by_cases ha : IsUnit a
  · simpa [ha.unit_spec] using gaussSum_mulShift_eq χ ψ ha.unit
  · rw [saturated_gauss_nonunit χ ψ hψ hG ha, MulChar.map_nonunit _ ha, zero_mul]

end CubicFirstMoment.SieveFourier

namespace CubicFirstMoment
namespace SieveOperator

def Bound {ι θ : Type*} (H : Finset ι) (S : Finset θ) (χ : ι → θ → ℂ) (K : ℝ) : Prop :=
  ∀ u : θ → ℂ, ∑ h ∈ H, ‖∑ a ∈ S, u a * χ h a‖^2 ≤ K * ∑ a ∈ S, ‖u a‖^2

lemma sum_mul_norm_sq {ι : Type*} (s : Finset ι) (f g : ι → ℂ) :
    ‖∑ i ∈ s, f i * g i‖^2 ≤ (∑ i ∈ s, ‖f i‖^2) * ∑ i ∈ s, ‖g i‖^2 := by
  calc
    _ ≤ (∑ i ∈ s, ‖f i‖*‖g i‖)^2 := by
      apply pow_le_pow_left₀ (_root_.norm_nonneg _)
      simpa only [norm_mul] using norm_sum_le s (fun i => f i*g i)
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq s _ _

 
lemma Bound.transpose {ι θ : Type*} {H : Finset ι} {S : Finset θ}
    {χ : ι → θ → ℂ} {K : ℝ} (hK : 0 ≤ K) (h : Bound H S χ K) :
    Bound S H (fun a b => χ b a) K := by
  intro u
  let v : θ → ℂ := fun a => ∑ b ∈ H, u b * χ b a
  let E : ℝ := ∑ a ∈ S, ‖v a‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have he : (E : ℂ) = ∑ b ∈ H, u b * ∑ a ∈ S, star (v a) * χ b a := by
    change ((∑ a ∈ S, ‖v a‖^2 : ℝ) : ℂ) = _
    push_cast
    have hn (a : θ) : (‖v a‖ : ℂ)^2 = v a * star (v a) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    simp_rw [hn]
    dsimp only [v] at *
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hc := sum_mul_norm_sq H u (fun b => ∑ a ∈ S, star (v a) * χ b a)
  have hop := h (fun a => star (v a))
  simp only [norm_star] at hop
  have hc' : E^2 ≤ (∑ b ∈ H, ‖u b‖^2) * (K * E) := by
    rw [← he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE] at hc
    exact hc.trans (mul_le_mul_of_nonneg_left hop (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  change E ≤ K * ∑ b ∈ H, ‖u b‖^2
  by_cases hE0 : E = 0
  · rw [hE0]
    exact mul_nonneg hK (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · apply (mul_le_mul_iff_right₀ (lt_of_le_of_ne hE (Ne.symm hE0))).mp
    calc
      E*E = E^2 := by ring
      _ ≤ (∑ b ∈ H, ‖u b‖^2) * (K*E) := hc'
      _ = E*(K*∑ b ∈ H, ‖u b‖^2) := by ring

end SieveOperator
end CubicFirstMoment
end

end OAI
