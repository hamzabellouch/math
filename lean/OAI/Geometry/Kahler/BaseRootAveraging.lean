import OAI.Geometry.Kahler.BaseDensityBandwidth

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma phaseChar_root {k : ℕ} (hk : 0 < k) :
    phaseChar (k:ℤ) (Circle.exp (2*Real.pi/k))=1 := by
  rw [phaseChar_exp]
  have hk0 : (k:ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have he : (k:ℂ)*(2*Real.pi/k:ℝ)*Complex.I=2*(Real.pi:ℂ)*Complex.I := by push_cast; field_simp
  norm_cast at *
  rw [he]
  push_cast
  exact Complex.exp_two_pi_mul_I

lemma phaseChar_root_ne_one {k : ℕ} (hk : 0 < k) {n : ℤ} (hn : n ≠ 0) (hbound : |n| < (k:ℤ)) :
    phaseChar n (Circle.exp (2*Real.pi/k)) ≠ 1 := by
  intro he
  have hec : Circle.exp ((n:ℝ)*(2*Real.pi/k))=1 := by
    apply Subtype.ext
    simpa only [Circle.coe_one,Circle.coe_exp,phaseChar_exp,Complex.ofReal_mul,Complex.ofReal_intCast,mul_assoc] using he
  obtain ⟨m,hm⟩ := Circle.exp_eq_one.mp hec
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hp := Real.pi_pos
  have hnm : (n:ℝ)=(m:ℝ)*k := by
    have hh := congrArg (fun t : ℝ => t*k) hm
    field_simp at hh
    nlinarith
  have hni : n=m*k := by exact_mod_cast hnm
  have hmn : m ≠ 0 := by intro hz; simp [hz] at hni; exact hn hni
  have hm1 : (1:ℤ) ≤ |m| := by have := abs_pos.mpr hmn; omega
  rw [hni,abs_mul,abs_of_nonneg (show (0:ℤ) ≤ k by positivity)] at hbound
  have hh := mul_le_mul_of_nonneg_right hm1 (show (0:ℤ) ≤ k by positivity)
  omega

lemma root_invariant_char_integral {k : ℕ} (hk : 0 < k) {V : Circle → ℂ}
    (hV : ∀ z, V (Circle.exp (2*Real.pi/k)*z)=V z)
    {n : ℤ} (hn : n ≠ 0) (hbound : |n| < (k:ℤ)) :
    (∫ z, V z*phaseChar n z ∂circleMeasure)=0 := by
  let w := Circle.exp (2*Real.pi/k)
  have he := integral_mul_left_eq_self (μ := circleMeasure) (fun z => V z*phaseChar n z) w
  have hf : ∀ z, V (w*z)*phaseChar n (w*z)=phaseChar n w*(V z*phaseChar n z) := by
    intro z
    rw [hV,phaseChar_mul]
    ring
  simp_rw [hf] at he
  rw [integral_const_mul] at he
  by_contra hz
  exact phaseChar_root_ne_one hk hn hbound ((mul_eq_right₀ hz).mp he)

lemma root_invariant_phaseSum {k ℓ : ℕ} (hk : 0 < k) (hl : ℓ < k)
    {V : Circle → ℂ} (hi : Integrable V circleMeasure)
    (hV : ∀ z, V (Circle.exp (2*Real.pi/k)*z)=V z)
    (s : Finset ℤ) (b : ℤ → ℂ) (hband : ∀ n ∈ s, |n| ≤ (ℓ:ℤ)) :
    (∫ z, V z*phaseSum s b z ∂circleMeasure) =
      (∫ z, V z ∂circleMeasure)*(∫ z, phaseSum s b z ∂circleMeasure) := by
  classical
  have hi' : ∀ n, Integrable (fun z => V z*phaseChar n z) circleMeasure := by
    intro n
    exact hi.mul_bdd (phaseChar_continuous n).aestronglyMeasurable
      (Eventually.of_forall (fun z => le_of_eq (phaseChar_norm n z)))
  simp only [phaseSum,Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum s (fun n _ => by simpa [mul_left_comm,mul_assoc] using (hi' n).const_mul (b n))]
  have he : ∀ n ∈ s, (∫ z, V z*(b n*phaseChar n z) ∂circleMeasure)=
      if n=0 then b n*(∫ z, V z ∂circleMeasure) else 0 := by
    intro n hn
    simp_rw [show ∀ z, V z*(b n*phaseChar n z)=b n*(V z*phaseChar n z) by intro z; ring]
    rw [integral_const_mul]
    by_cases hn0 : n=0
    · simp [hn0]
    · rw [ite_eq_right hn0,root_invariant_char_integral hk hV hn0 (lt_of_le_of_lt (hband n hn) (by exact_mod_cast hl)),mul_zero]
  rw [Finset.sum_congr rfl he]
  have hm := phaseSum_mean s b
  unfold phaseSum at hm
  rw [hm]
  by_cases hz : 0 ∈ s <;> simp [hz,mul_comm]

end PinchedHartogs.BaseConstruction

end

end OAI
