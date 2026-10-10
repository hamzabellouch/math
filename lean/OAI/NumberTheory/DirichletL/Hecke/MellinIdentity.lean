import OAI.NumberTheory.DirichletL.Continuation
import Mathlib.NumberTheory.LSeries.AbstractFuncEq

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace SevenEighths.HeckeMellinIdentity

def regularized (P : WeakFEPair ℂ) (s : ℂ) : ℂ :=
  s * (s - 1) * P.Λ₀ s - (s - 1) * P.f₀ + s * P.ε * P.g₀

theorem regularized_entire (P : WeakFEPair ℂ) : Differentiable ℂ (regularized P) := by
  unfold regularized
  have hd := P.differentiable_Λ₀
  fun_prop

theorem regularized_eq (P : WeakFEPair ℂ) (hk : P.k = 1) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) : regularized P s = s * (s-1) * P.Λ s := by
  unfold regularized WeakFEPair.Λ
  rw [hk]
  simp only [smul_eq_mul, Complex.ofReal_one]
  have h1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  ring

theorem scaled_eq (P Q : WeakFEPair ℂ) (hP : P.k = 1) (hQ : Q.k = 1)
    (A : ℝ) (hA : 0 < A)
    (hright : ∀ s : ℂ, 1 < s.re → P.Λ s = (A : ℂ)^(-s) * Q.Λ s)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    P.Λ s = (A : ℂ)^(-s) * Q.Λ s := by
  have hd : Differentiable ℂ (fun z : ℂ => (A : ℂ)^(-z) * regularized Q z) :=
    ((differentiable_id.neg).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hA.ne'))).mul (regularized_entire Q)
  have he : regularized P = fun z : ℂ => (A : ℂ)^(-z) * regularized Q z := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr (regularized_entire P)).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hd) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have hz1 : z ≠ 1 := by intro h; norm_num [h] at hz
    rw [regularized_eq P hP hz0 hz1, regularized_eq Q hQ hz0 hz1, hright z hz]
    ring
  have heq := congr_fun he s
  rw [regularized_eq P hP h0 h1, regularized_eq Q hQ h0 h1] at heq
  apply mul_left_cancel₀ (mul_ne_zero h0 (sub_ne_zero.mpr h1))
  calc
    s * (s - 1) * P.Λ s = (A : ℂ)^(-s) * (s * (s-1) * Q.Λ s) := heq
    _ = s * (s-1) * ((A : ℂ)^(-s) * Q.Λ s) := by ring

theorem eq_of_f (P Q : WeakFEPair ℂ) (hP : P.k = 1) (hQ : Q.k = 1)
    (hf : ∀ t : ℝ, 0 < t → P.f t = Q.f t) (hf₀ : P.f₀ = Q.f₀)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : P.Λ s = Q.Λ s := by
  have h := scaled_eq P Q hP hQ 1 zero_lt_one (fun z hz => by
    simp only [Complex.ofReal_one, Complex.one_cpow, one_mul]
    rw [← (P.hasMellin (by rwa [hP])).2, ← (Q.hasMellin (by rwa [hQ])).2]
    unfold mellin
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [hf t ht, hf₀]) h0 h1
  simpa only [Complex.ofReal_one, Complex.one_cpow, one_mul] using h

end SevenEighths.HeckeMellinIdentity

end

end OAI
