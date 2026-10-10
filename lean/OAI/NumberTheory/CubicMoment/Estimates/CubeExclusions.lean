import OAI.NumberTheory.CubicMoment.Estimates.CubeLatticeBounds
import OAI.NumberTheory.CubicGram.CommonFactors

namespace OAI

/-! The cost of excluding prime divisors from the principal cube lattice. -/

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- The absolute sum has the same area bound as its arbitrary bounded twists. -/
theorem radial_cube_lattice_norm_sum_bound (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℝ, 0 < q →
      (∑' j : Eisenstein, if j = 0 then 0 else
        ‖radialDualProfile W (q^3*(norm j)^3)‖) ≤ K/q := by
  obtain ⟨K,hK,hbound⟩ := radial_cube_lattice_weighted_bound W hW hW'
  refine ⟨K,hK,?_⟩
  intro q hq
  let f (j : Eisenstein) := radialDualProfile W (q^3*(norm j)^3)
  let w (j : Eisenstein) : ℂ := if f j = 0 then 0 else (‖f j‖ : ℂ)/f j
  have hw : ∀ j, ‖w j‖ ≤ 1 := by
    intro j
    by_cases hj : f j = 0
    · simp [w,hj]
    · simp [w,hj]
  have he (j : Eisenstein) : w j*f j = (‖f j‖ : ℂ) := by
    by_cases hj : f j = 0
    · simp [w,hj]
    · simp [w,hj]
  have hb := hbound q hq w hw
  simp_rw [show ∀ j, radialDualProfile W (q^3*(norm j)^3) = f j from fun _ => rfl,he] at hb
  have hc : (∑' j : Eisenstein, if j = 0 then (0:ℂ) else (‖f j‖ : ℂ)) =
      (((∑' j : Eisenstein, if j = 0 then (0:ℝ) else ‖f j‖) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro j
    split_ifs <;> simp
  rw [hc,Complex.norm_real,Real.norm_of_nonneg (tsum_nonneg (by intro j; split_ifs <;> positivity))] at hb
  exact hb

lemma tsum_divisible {R : Type*} [AddCommMonoid R] [TopologicalSpace R]
    (m : Eisenstein) (hm : m ≠ 0) (f : Eisenstein → R) :
    (∑' j : Eisenstein, if m ∣ j then f j else 0) = ∑' k : Eisenstein, f (m*k) := by
  let e : Eisenstein ≃ {j : Eisenstein // m ∣ j} :=
    Equiv.ofBijective (fun k => ⟨m*k,dvd_mul_right m k⟩)
      ⟨fun a b h => mul_left_cancel₀ hm (congrArg Subtype.val h),
        fun ⟨j,hj⟩ => by obtain ⟨k,rfl⟩ := hj; exact ⟨k,rfl⟩⟩
  change (∑' j : Eisenstein, Set.indicator {j | m ∣ j} f j) = _
  rw [← tsum_subtype]
  exact (e.tsum_eq (fun j => f j.val)).symm

/-- This remains valid when the sublattice spacing exceeds the natural
radius; there is no spurious constant term for the deleted origin. -/
theorem radial_cube_multiples_bound (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℝ, 0 < q → ∀ m : Eisenstein, m ≠ 0 →
      (∑' j : Eisenstein, if m ∣ j ∧ j ≠ 0 then
        ‖radialDualProfile W (q^3*(norm j)^3)‖ else 0) ≤ K/(q*norm m) := by
  obtain ⟨K,hK,hbound⟩ := radial_cube_lattice_norm_sum_bound W hW hW'
  refine ⟨K,hK,?_⟩
  intro q hq m hm
  have he : (∑' j : Eisenstein, if m ∣ j ∧ j ≠ 0 then
      ‖radialDualProfile W (q^3*(norm j)^3)‖ else 0) =
      ∑' k : Eisenstein, if k = 0 then 0 else
        ‖radialDualProfile W ((q*norm m)^3*(norm k)^3)‖ := by
    calc
      _ = ∑' j : Eisenstein, if m ∣ j then
          (if j = 0 then 0 else ‖radialDualProfile W (q^3*(norm j)^3)‖) else 0 := by
        apply tsum_congr
        intro j
        by_cases hd : m ∣ j <;> by_cases hj : j = 0 <;> simp [hd,hj]
      _ = ∑' k : Eisenstein, if m*k = 0 then 0 else
          ‖radialDualProfile W (q^3*(norm (m*k))^3)‖ := tsum_divisible m hm _
      _ = _ := by
        apply tsum_congr
        intro k
        simp only [mul_eq_zero,hm,false_or,norm_mul_eq,mul_pow]
        congr 3
        ring
  rw [he]
  exact hbound (q*norm m) (mul_pos hq (norm_pos_of_ne_zero hm))

lemma not_coprime_prime_cover {a : Eisenstein} (ha : primary a) (hsa : Squarefree a)
    {j : Eisenstein} (hj : ¬IsCoprime a j) :
    ∃ p ∈ primaryPrimeFactors a, p ∣ j := by
  by_contra h
  apply hj
  have hall : ∀ p ∈ primaryPrimeFactors a, IsCoprime p j := by
    intro p hp
    exact (primaryPrimeFactor_spec ha hp).1.2.irreducible.coprime_iff_not_dvd.mpr
      (fun hd => h ⟨p,hp,hd⟩)
  have hh := IsCoprime.prod_left hall
  rwa [primaryPrimeFactors_prod ha hsa] at hh

end CubicFirstMoment

end

end OAI
