import OAI.NumberTheory.Jacobsthal.Estimates.ReciprocalEnvelope

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceSmallModel

theorem bin_diameter (R xi p q : ℝ) (hp : R < p ∧ p ≤ (1+xi)*R)
    (hq : R < q ∧ q ≤ (1+xi)*R) : |p-q| ≤ xi*R := by
  rw [abs_le]
  constructor <;> nlinarith

theorem reciprocal_difference_abs (C0 p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    |C0/p-C0/q| = |C0| * |p-q| / (p*q) := by
  have he : C0/p-C0/q = (-C0)*(p-q)/(p*q) := by field_simp;ring
  rw [he,abs_div,abs_mul,abs_neg,abs_of_pos (mul_pos hp hq)]

theorem fixed_m_reciprocal_diameter (R xi H C0 p q m : ℝ)
    (hR : 0 < R) (hxi1 : xi ≤ 1) (hH : 0 < H) (hC : C0 ≠ 0)
    (hp : R < p ∧ p ≤ (1+xi)*R) (hq : R < q ∧ q ≤ (1+xi)*R)
    (hmp : C0/p ≤ m ∧ m < C0/p+H) (hmq : C0/q ≤ m ∧ m < C0/q+H) :
    |p-q| ≤ 4*R^2*H/|C0| := by
  have hpp : 0 < p := hR.trans hp.1
  have hqp : 0 < q := hR.trans hq.1
  have hdiff : |C0/p-C0/q| ≤ H := by rw [abs_le];constructor <;> linarith
  rw [reciprocal_difference_abs C0 p q hpp hqp] at hdiff
  have hh := (div_le_iff₀ (mul_pos hpp hqp)).mp hdiff
  have hp2 : p ≤ 2*R := by nlinarith
  have hq2 : q ≤ 2*R := by nlinarith
  have hpq : p*q ≤ 4*R^2 := by nlinarith [mul_le_mul hp2 hq2 hqp.le (by positivity : 0 ≤ 2*R)]
  have hm := mul_le_mul_of_nonneg_left hpq hH.le
  apply (le_div_iff₀ (abs_pos.mpr hC)).mpr
  nlinarith

theorem fixed_m_prime_diameter (R xi H C0 p q m : ℝ)
    (hR : 0 < R) (_hxi : 0 < xi) (hxi1 : xi ≤ 1) (hH : 0 < H)
    (hp : R < p ∧ p ≤ (1+xi)*R) (hq : R < q ∧ q ≤ (1+xi)*R)
    (hmp : C0/p ≤ m ∧ m < C0/p+H) (hmq : C0/q ≤ m ∧ m < C0/q+H) :
    |p-q| ≤ 4*primeWidth R xi H C0 := by
  have hbin := bin_diameter R xi p q hp hq
  have hscale : |p-q| ≤ 4*R*H/totalScale R H C0 := by
    rcases le_total H (interceptScale R C0) with h | h
    · have hC : C0 ≠ 0 := by
        intro he
        rw [he,interceptScale,abs_zero,zero_div] at h
        linarith
      rw [totalScale,max_eq_right h]
      calc
        _ ≤ 4*R^2*H/|C0| := fixed_m_reciprocal_diameter R xi H C0 p q m hR hxi1 hH hC hp hq hmp hmq
        _ = _ := by dsimp [interceptScale];field_simp
    · rw [totalScale,max_eq_left h,mul_div_cancel_right₀ _ hH.ne']
      nlinarith
  rcases le_total (xi*R) (R*H/totalScale R H C0) with h | h
  · rw [primeWidth,min_eq_left h]
    nlinarith
  · rw [primeWidth,min_eq_right h]
    simpa only [mul_div_assoc,mul_assoc] using hscale

end ErdosVarianceSmallModel

end

section

namespace ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable

noncomputable def geometricFibre (P : Finset ℕ) (H C0 : ℝ) (m : ℤ) : Finset ℕ :=
  P.filter (fun p => C0/(p : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) < C0/(p : ℝ)+H)

theorem geometric_fibre_interval (P : Finset ℕ) (R xi H C0 : ℝ) (m : ℤ)
    (hR : 0 < R) (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hH : 0 < H)
    (hP : ∀ p ∈ P,R < (p : ℝ) ∧ (p : ℝ) ≤ (1+xi)*R) :
    ∃ x : ℝ,∀ p ∈ geometricFibre P H C0 m,
      x < (p : ℝ) ∧ (p : ℝ) ≤ x+5*primeWidth R xi H C0 := by
  classical
  by_cases hne : (geometricFibre P H C0 m).Nonempty
  · let p0 := (geometricFibre P H C0 m).min' hne
    have hp0 : p0 ∈ geometricFibre P H C0 m := Finset.min'_mem _ hne
    have hp0P := (Finset.mem_filter.mp hp0).1
    have hX := primeWidth_pos R xi H C0 hR hxi hH
    refine ⟨(p0 : ℝ)-primeWidth R xi H C0,?_⟩
    intro p hp
    have hpP := (Finset.mem_filter.mp hp).1
    have hmin : p0 ≤ p := Finset.min'_le _ p hp
    have hminR : (p0 : ℝ) ≤ p := by exact_mod_cast hmin
    have hd := fixed_m_prime_diameter R xi H C0 p p0 m hR hxi hxi1 hH
      (hP p hpP) (hP p0 hp0P) (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hp0).2
    have hupper := (abs_le.mp hd).2
    constructor <;> linarith
  · refine ⟨0,?_⟩
    intro p hp
    exact False.elim (hne ⟨p,hp⟩)

end ErdosVarianceSmallModel

end

end Erdos970

end OAI
