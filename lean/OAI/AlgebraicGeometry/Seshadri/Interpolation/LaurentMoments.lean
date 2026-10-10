import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Interpolation.TriangleJets

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
theorem sum_rows {M : Type*} [AddCommMonoid M]
    (s : Finset (ℤ × ℤ)) (f : ℤ × ℤ → M) :
    ∑ y ∈ rows s, ∑ x ∈ row s y, f (x, y) = ∑ p ∈ s, f p := by
  classical
  trans ∑ y ∈ rows s, ∑ p ∈ s with p.2 = y, f p
  · apply Finset.sum_congr rfl
    intro y _
    unfold row
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro p hp
      have h := (Finset.mem_filter.mp hp).2
      exact congrArg f (Prod.ext rfl h.symm)
    · intro p hp q hq h
      apply Prod.ext h
      exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
  · exact Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem Prod.snd hp) f

theorem laurentEval_eq_sum (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (u z : ℂ) :
    laurentEval s c u z = ∑ p ∈ s, c p * u ^ p.1 * z ^ p.2 := by
  unfold laurentEval
  simp_rw [Finset.sum_mul]
  exact sum_rows s (fun p => c p * u ^ p.1 * z ^ p.2)

def MomentJetZero {α : Type*} (s : Finset α) (c x y : α → ℂ) (m : ℕ) : Prop :=
  ∀ a b : ℕ, a + b < m → ∑ p ∈ s, c p * x p ^ a * y p ^ b = 0

theorem eulerJetZero_iff_momentJetZero (s : Finset (ℤ × ℤ))
    (c : ℤ × ℤ → ℂ) (m : ℕ) :
    EulerJetZero s c m ↔ MomentJetZero s c (fun p => (p.1 : ℂ)) (fun p => (p.2 : ℂ)) m := by
  have he (a b : ℕ) :
      (∑ y ∈ rows s, rowMoment s c a y * (y : ℂ) ^ b) =
        ∑ p ∈ s, c p * (p.1 : ℂ) ^ a * (p.2 : ℂ) ^ b := by
    simp_rw [rowMoment, Finset.sum_mul]
    exact sum_rows s (fun p => c p * (p.1 : ℂ) ^ a * (p.2 : ℂ) ^ b)
  unfold EulerJetZero MomentJetZero
  simp_rw [he]

theorem contDiffAt_zpow_ne_zero (q : ℤ) (w : ℂ) (hw : w ≠ 0) (n : WithTop ℕ∞) :
    ContDiffAt ℂ n (fun u : ℂ => u ^ q) w :=
  (analyticAt_id.zpow hw).contDiffAt

theorem laurentEval_mixed_deriv (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ)
    (u z : ℂ) (hu : u ≠ 0) (hz : z ≠ 0) (a b : ℕ) :
    iteratedDeriv b (fun v : ℂ => iteratedDeriv a (fun w : ℂ => laurentEval s c w v) u) z =
      ∑ p ∈ s, c p * (descPochhammer ℂ a).eval (p.1 : ℂ) * u ^ (p.1 - (a : ℤ)) *
        (descPochhammer ℂ b).eval (p.2 : ℂ) * z ^ (p.2 - (b : ℤ)) := by
  have hi (v : ℂ) :
      iteratedDeriv a (fun w : ℂ => laurentEval s c w v) u =
        ∑ p ∈ s, c p * (descPochhammer ℂ a).eval (p.1 : ℂ) *
          u ^ (p.1 - (a : ℤ)) * v ^ p.2 := by
    simp_rw [laurentEval_eq_sum]
    rw [iteratedDeriv_fun_sum (fun p _ =>
      (contDiffAt_const.mul (contDiffAt_zpow_ne_zero p.1 u hu a)).mul contDiffAt_const)]
    apply Finset.sum_congr rfl
    intro p _
    rw [iteratedDeriv_mul_const_field, iteratedDeriv_const_mul_field,
      iteratedDeriv_eq_iterate, iter_deriv_zpow, descPochhammer_eval_eq_prod_range]
    ring
  simp_rw [hi]
  rw [iteratedDeriv_fun_sum (fun p _ =>
    contDiffAt_const.mul (contDiffAt_zpow_ne_zero p.2 z hz b))]
  apply Finset.sum_congr rfl
  intro p _
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_zpow]
  simp_rw [descPochhammer_eval_eq_prod_range]
  ring

theorem mixedJetZero_moments (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ)
    (u z : ℂ) (hu : u ≠ 0) (hz : z ≠ 0) (m : ℕ)
    (hjet : MixedJetZero (laurentEval s c) u z m) :
    MomentJetZero s (fun p => c p * u ^ p.1 * z ^ p.2)
      (fun p => (p.1 : ℂ)) (fun p => (p.2 : ℂ)) m := by
  apply (eulerJetZero_iff_momentJetZero _ _ _).mp
  apply fallingJetZero_eulerJetZero
  intro a b hab
  have h := hjet a b hab
  rw [laurentEval_mixed_deriv s c u z hu hz] at h
  have heq : (∑ p ∈ s, c p * (descPochhammer ℂ a).eval (p.1 : ℂ) *
      u ^ (p.1 - (a : ℤ)) * (descPochhammer ℂ b).eval (p.2 : ℂ) *
        z ^ (p.2 - (b : ℤ))) * (u ^ a * z ^ b) =
      ∑ p ∈ s, (c p * u ^ p.1 * z ^ p.2) *
        (descPochhammer ℂ a).eval (p.1 : ℂ) * (descPochhammer ℂ b).eval (p.2 : ℂ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [zpow_sub₀ hu, zpow_sub₀ hz, zpow_natCast, zpow_natCast]
    field_simp
  simp_rw [Finset.sum_mul]
  rw [sum_rows s (fun p => (c p * u ^ p.1 * z ^ p.2) *
    (descPochhammer ℂ a).eval (p.1 : ℂ) * (descPochhammer ℂ b).eval (p.2 : ℂ))]
  rw [← heq, h, zero_mul]

theorem MomentJetZero.polynomial {α : Type*} (s : Finset α) (c x y : α → ℂ) (m : ℕ)
    (hjet : MomentJetZero s c x y m) (P : MvPolynomial Bool ℂ) (hP : P.totalDegree < m) :
    ∑ p ∈ s, c p * MvPolynomial.eval (Bool.rec (y p) (x p)) P = 0 := by
  classical
  simp_rw [MvPolynomial.eval_eq', Fintype.prod_bool]
  change (∑ p ∈ s, c p * ∑ d ∈ P.support, P.coeff d * (x p ^ d true * y p ^ d false)) = 0
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro d hd
  have hdeg : d true + d false < m := by
    have h := MvPolynomial.le_totalDegree hd
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_bool] at h
    exact h.trans_lt hP
  calc
    (∑ p ∈ s, c p * (P.coeff d * (x p ^ d true * y p ^ d false))) =
        P.coeff d * ∑ p ∈ s, c p * x p ^ d true * y p ^ d false := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = 0 := by rw [hjet _ _ hdeg, mul_zero]

noncomputable def affinePolynomial (a b c : ℂ) : MvPolynomial Bool ℂ :=
  MvPolynomial.C a * MvPolynomial.X true +
    MvPolynomial.C b * MvPolynomial.X false + MvPolynomial.C c

theorem affinePolynomial_degree (a b c : ℂ) : (affinePolynomial a b c).totalDegree ≤ 1 := by
  unfold affinePolynomial
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · simpa using MvPolynomial.totalDegree_mul (MvPolynomial.C a) (MvPolynomial.X true)
    · simpa using MvPolynomial.totalDegree_mul (MvPolynomial.C b) (MvPolynomial.X false)
  · simp

theorem MomentJetZero.affine {α : Type*} (s : Finset α) (c x y : α → ℂ) (m : ℕ)
    (hjet : MomentJetZero s c x y m) (A B C D E F : ℂ) :
    MomentJetZero s c (fun p => A * x p + B * y p + C)
      (fun p => D * x p + E * y p + F) m := by
  intro a b hab
  have ha : ((affinePolynomial A B C) ^ a).totalDegree ≤ a :=
    (MvPolynomial.totalDegree_pow _ _).trans (by nlinarith only [affinePolynomial_degree A B C])
  have hb : ((affinePolynomial D E F) ^ b).totalDegree ≤ b :=
    (MvPolynomial.totalDegree_pow _ _).trans (by nlinarith only [affinePolynomial_degree D E F])
  have hdeg : ((affinePolynomial A B C) ^ a * (affinePolynomial D E F) ^ b).totalDegree < m :=
    (MvPolynomial.totalDegree_mul _ _).trans_lt ((add_le_add ha hb).trans_lt hab)
  have h := hjet.polynomial s c x y m _ hdeg
  simpa [affinePolynomial, mul_assoc] using h

theorem primitiveRoot_fourier_sum (r : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r) (n : ℤ) :
    ∑ l ∈ Finset.range r, ζ ^ ((l : ℤ) * n) = if (r : ℤ) ∣ n then (r : ℂ) else 0 := by
  have hp (l : ℕ) : ζ ^ ((l : ℤ) * n) = (ζ ^ n) ^ l := by
    rw [mul_comm, zpow_mul, zpow_natCast]
  simp_rw [hp]
  by_cases hn : (r : ℤ) ∣ n
  · rw [ite_eq_left hn, (hζ.zpow_eq_one_iff_dvd n).mpr hn]
    simp
  · rw [ite_eq_right hn, geom_sum_eq (mt (hζ.zpow_eq_one_iff_dvd n).mp hn)]
    have heq : (ζ ^ n) ^ r = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm n (r : ℤ), zpow_mul,
        zpow_natCast, hζ.pow_eq_one, one_zpow]
    rw [heq]
    simp

theorem root_project_moments {α : Type*} (s : Finset α) (c x y : α → ℂ)
    (height : α → ℤ) (r m : ℕ) (hr : 0 < r) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r)
    (hjet : ∀ l < r, MomentJetZero s (fun p => c p * ζ ^ ((l : ℤ) * height p)) x y m)
    (e : ℤ) : MomentJetZero (s.filter (fun p => (r : ℤ) ∣ height p - e)) c x y m := by
  classical
  have hζ0 : ζ ≠ 0 := (hζ.isUnit hr.ne').ne_zero
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  intro a b hab
  have hz : (∑ l ∈ Finset.range r, ζ ^ (-((l : ℤ) * e)) *
      ∑ p ∈ s, (c p * ζ ^ ((l : ℤ) * height p)) * x p ^ a * y p ^ b) = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    rw [hjet l (Finset.mem_range.mp hl) a b hab, mul_zero]
  have heq : (∑ l ∈ Finset.range r, ζ ^ (-((l : ℤ) * e)) *
      ∑ p ∈ s, (c p * ζ ^ ((l : ℤ) * height p)) * x p ^ a * y p ^ b) =
      (r : ℂ) * ∑ p ∈ s.filter (fun p => (r : ℤ) ∣ height p - e), c p * x p ^ a * y p ^ b := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hs (p : α) : (∑ l ∈ Finset.range r,
        ζ ^ (-((l : ℤ) * e)) * ((c p * ζ ^ ((l : ℤ) * height p)) * x p ^ a * y p ^ b)) =
        (c p * x p ^ a * y p ^ b) *
          (if (r : ℤ) ∣ height p - e then (r : ℂ) else 0) := by
      rw [← primitiveRoot_fourier_sum r ζ hζ (height p - e), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      have hp : ζ ^ (-((l : ℤ) * e)) * ζ ^ ((l : ℤ) * height p) =
          ζ ^ ((l : ℤ) * (height p - e)) := by
        rw [← zpow_add₀ hζ0]
        congr 1
        ring
      calc
        _ = (c p * x p ^ a * y p ^ b) *
            (ζ ^ (-((l : ℤ) * e)) * ζ ^ ((l : ℤ) * height p)) := by ring
        _ = _ := by rw [hp]
    simp_rw [hs]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> simp [mul_comm]
  rw [heq] at hz
  exact (mul_eq_zero.mp hz).resolve_left hrC

theorem MomentJetZero.image {α β : Type*} [Nonempty α] [DecidableEq β]
    (s : Finset α) (c : α → ℂ) (f : α → β) (hf : Set.InjOn f s)
    (x y : β → ℂ) (m : ℕ) (hjet : MomentJetZero s c (x ∘ f) (y ∘ f) m) :
    MomentJetZero (s.image f) (c ∘ Function.invFunOn f s) x y m := by
  classical
  intro a b hab
  rw [Finset.sum_image (fun p hp q hq he => hf hp hq he)]
  convert hjet a b hab using 1
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Function.comp_apply, hf.leftInvOn_invFunOn hp]


end MaximalSeshadri.Interpolation
end

end OAI
