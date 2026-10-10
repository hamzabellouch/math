import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.IsSquare
import OAI.NumberTheory.SiegelZeros.Characters.Biquadratic

namespace OAI

namespace SiegelZeros


namespace WeightedTorusJets.W11

open QuadraticAlgebra

abbrev Biquad (d : ℚ) :=
  QuadraticAlgebra (QuadraticAlgebra ℚ d 0) ⟨2, 0⟩ 0

def flip {R : Type*} [CommRing R] (d : R) :
    QuadraticAlgebra R d 0 ≃+* QuadraticAlgebra R d 0 where
  toFun z := ⟨z.re, -z.im⟩
  invFun z := ⟨z.re, -z.im⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' z w := by ext <;> simp [add_comm]
  map_mul' z w := by ext <;> simp; ring

@[simp] theorem flip_re {R : Type*} [CommRing R] (d : R)
    (z : QuadraticAlgebra R d 0) : (flip d z).re = z.re := rfl

@[simp] theorem flip_im {R : Type*} [CommRing R] (d : R)
    (z : QuadraticAlgebra R d 0) : (flip d z).im = -z.im := rfl

def sigma (d : ℚ) : Biquad d ≃+* Biquad d where
  toFun z := ⟨flip d z.re, flip d z.im⟩
  invFun z := ⟨flip d z.re, flip d z.im⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' z w := by ext <;> simp
  map_mul' z w := by ext <;> simp

def tau (d : ℚ) : Biquad d ≃+* Biquad d :=
  flip (R := QuadraticAlgebra ℚ d 0) (⟨2, 0⟩ : QuadraticAlgebra ℚ d 0)

def a (d : ℚ) : Biquad d := ⟨⟨0, 1⟩, 0⟩
def b (d : ℚ) : Biquad d := ⟨0, 1⟩

@[simp] theorem sigma_a (d : ℚ) : sigma d (a d) = -a d := by
  ext <;> simp [sigma, flip, a]
@[simp] theorem sigma_b (d : ℚ) : sigma d (b d) = b d := by
  ext <;> simp [sigma, flip, b]
@[simp] theorem tau_a (d : ℚ) : tau d (a d) = a d := by
  ext <;> simp [tau, flip, a]
@[simp] theorem tau_b (d : ℚ) : tau d (b d) = -b d := by
  ext <;> simp [tau, flip, b]

@[simp] theorem sigma_sigma (d : ℚ) (z : Biquad d) : sigma d (sigma d z) = z := by
  ext <;> simp [sigma, flip]
@[simp] theorem tau_tau (d : ℚ) (z : Biquad d) : tau d (tau d z) = z := by
  ext <;> simp [tau, flip]
theorem sigma_tau_commute (d : ℚ) (z : Biquad d) :
    sigma d (tau d z) = tau d (sigma d z) := by
  ext <;> simp [sigma, tau, flip]

def sigmaTau (d : ℚ) : Biquad d ≃+* Biquad d := (tau d).trans (sigma d)

@[simp] theorem sigmaTau_apply (d : ℚ) (z : Biquad d) :
    sigmaTau d z = sigma d (tau d z) := rfl
@[simp] theorem sigmaTau_sigmaTau (d : ℚ) (z : Biquad d) :
    sigmaTau d (sigmaTau d z) = z := by
  simp only [sigmaTau_apply]
  rw [← sigma_tau_commute, sigma_sigma, tau_tau]

def signAction (d : ℚ) (s t : Bool) : Biquad d ≃+* Biquad d :=
  (if t then tau d else RingEquiv.refl _).trans
    (if s then sigma d else RingEquiv.refl _)

theorem signAction_comp (d : ℚ) (s t u v : Bool) (z : Biquad d) :
    signAction d s t (signAction d u v z) =
      signAction d (Bool.xor s u) (Bool.xor t v) z := by
  cases s <;> cases t <;> cases u <;> cases v <;>
    simp [signAction, sigma_tau_commute]

theorem signAction_injective (d : ℚ) :
    Function.Injective (fun st : Bool × Bool => signAction d st.1 st.2) := by
  rintro ⟨s, t⟩ ⟨u, v⟩ h
  have ha := congrArg (fun f : Biquad d ≃+* Biquad d => (f (a d)).re.im) h
  have hb := congrArg (fun f : Biquad d ≃+* Biquad d => (f (b d)).im.re) h
  cases s <;> cases t <;> cases u <;> cases v <;>
    norm_num [signAction, sigma, tau, flip, a, b] at *

def theta (d : ℚ) (n : Fin 4 → ℚ) : Biquad d :=
  ⟨⟨n 0, n 1⟩, ⟨n 2, n 3⟩⟩

@[simp] theorem sigma_theta (d : ℚ) (n : Fin 4 → ℚ) :
    sigma d (theta d n) = theta d ![n 0, -n 1, n 2, -n 3] := by
  ext <;> simp [sigma, flip, theta]
@[simp] theorem tau_theta (d : ℚ) (n : Fin 4 → ℚ) :
    tau d (theta d n) = theta d ![n 0, n 1, -n 2, -n 3] := by
  ext <;> simp [tau, flip, theta]
@[simp] theorem sigmaTau_theta (d : ℚ) (n : Fin 4 → ℚ) :
    sigmaTau d (theta d n) = theta d ![n 0, -n 1, -n 2, n 3] := by
  ext <;> simp [sigmaTau, sigma, tau, flip, theta]

theorem theta_injective (d : ℚ) : Function.Injective (theta d) := by
  intro n m h
  funext i
  fin_cases i
  · exact congrArg (fun z : Biquad d => z.re.re) h
  · exact congrArg (fun z : Biquad d => z.re.im) h
  · exact congrArg (fun z : Biquad d => z.im.re) h
  · exact congrArg (fun z : Biquad d => z.im.im) h

def evalQuadratic {R S : Type*} [CommRing R] [CommRing S]
    (d : R) (f : R →+* S) (r : S) (hr : r * r = f d) :
    QuadraticAlgebra R d 0 →+* S where
  toFun z := f z.re + f z.im * r
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by simp; ring
  map_mul' x y := by
    simp only [re_mul, im_mul, map_add, map_mul, zero_mul, add_zero]
    linear_combination -(f x.im * f y.im) * hr

def evalBiquad {K : Type*} [Field K] [Algebra ℚ K] (d : ℚ)
    (ar br : K) (ha : ar * ar = algebraMap ℚ K d) (hb : br * br = 2) :
    Biquad d →+* K :=
  evalQuadratic ⟨2, 0⟩ (evalQuadratic d (algebraMap ℚ K) ar ha) br (by
    change br * br = algebraMap ℚ K 2 + algebraMap ℚ K 0 * ar
    simpa using hb)

theorem evalBiquad_theta {K : Type*} [Field K] [Algebra ℚ K] (d : ℚ)
    (ar br : K) (ha : ar * ar = algebraMap ℚ K d) (hb : br * br = 2)
    (n : Fin 4 → ℚ) :
    evalBiquad d ar br ha hb (theta d n) =
      algebraMap ℚ K (n 0) + algebraMap ℚ K (n 1) * ar +
      algebraMap ℚ K (n 2) * br + algebraMap ℚ K (n 3) * (ar * br) := by
  change algebraMap ℚ K (n 0) + algebraMap ℚ K (n 1) * ar +
    (algebraMap ℚ K (n 2) + algebraMap ℚ K (n 3) * ar) * br = _
  ring

theorem evalBiquad_injective {K : Type*} [Field K] [Algebra ℚ K] (d : ℚ)
    (ar br : K) (ha : ar * ar = algebraMap ℚ K d) (hb : br * br = 2)
    (hli : LinearIndependent ℚ ![1, ar, br, ar * br]) :
    Function.Injective (evalBiquad d ar br ha hb) := by
  intro x y hxy
  let n : Fin 4 → ℚ := ![x.re.re - y.re.re, x.re.im - y.re.im,
    x.im.re - y.im.re, x.im.im - y.im.im]
  have heval : evalBiquad d ar br ha hb (theta d n) = 0 := by
    have hsub : theta d n = x - y := by ext <;> rfl
    rw [hsub, map_sub, hxy, sub_self]
  have hsum : ∑ i : Fin 4, n i • (![1, ar, br, ar * br] : Fin 4 → K) i = 0 := by
    rw [evalBiquad_theta] at heval
    simpa [Fin.sum_univ_succ, Algebra.smul_def, add_assoc] using heval
  have hn := Fintype.linearIndependent_iff.mp hli n hsum
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · exact sub_eq_zero.mp (hn 0)
    · exact sub_eq_zero.mp (hn 1)
  · apply QuadraticAlgebra.ext
    · exact sub_eq_zero.mp (hn 2)
    · exact sub_eq_zero.mp (hn 3)

end WeightedTorusJets.W11



namespace W10

variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]

omit [Algebra ℚ K] in
theorem square_root_not_rational (a : K) (d : ℚ) (ha : a ^ 2 = (d : K))
    (hd : ∀ x : ℚ, x ^ 2 ≠ d) (r : ℚ) : a ≠ (r : K) := by
  intro h
  apply hd r
  rw [h] at ha
  exact_mod_cast ha

omit [Algebra ℚ K] in
theorem quadratic_coefficients_eq_zero (a : K) (d : ℚ)
    (ha : a ^ 2 = (d : K)) (hd : ∀ x : ℚ, x ^ 2 ≠ d)
    (r s : ℚ) (h : (r : K) + (s : K) * a = 0) : r = 0 ∧ s = 0 := by
  by_cases hs : s = 0
  · subst s
    simpa using h
  · exfalso
    apply square_root_not_rational a d ha hd (-r / s)
    rw [Rat.cast_div, Rat.cast_neg]
    apply (eq_div_iff (Rat.cast_ne_zero.mpr hs)).mpr
    linear_combination h

omit [Algebra ℚ K] in
theorem second_root_not_linear (a b : K) (d e : ℚ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = (e : K))
    (hd : ∀ x : ℚ, x ^ 2 ≠ d) (he : ∀ x : ℚ, x ^ 2 ≠ e)
    (hde : ∀ x : ℚ, x ^ 2 ≠ d * e) (r s : ℚ) :
    b ≠ (r : K) + (s : K) * a := by
  intro h
  rw [h] at hb
  have hrel : ((r ^ 2 + s ^ 2 * d - e : ℚ) : K) +
      ((2 * r * s : ℚ) : K) * a = 0 := by
    push_cast
    linear_combination hb - (s : K) ^ 2 * ha
  obtain ⟨h0, h1⟩ := quadratic_coefficients_eq_zero a d ha hd
    (r ^ 2 + s ^ 2 * d - e) (2 * r * s) hrel
  have hrs : r * s = 0 := by linarith
  rcases mul_eq_zero.mp hrs with hr | hs
  · apply hde (s * d)
    have hed : s ^ 2 * d = e := by simpa [hr, sub_eq_zero] using h0
    calc
      (s * d) ^ 2 = d * (s ^ 2 * d) := by ring
      _ = d * e := by rw [hed]
  · apply he r
    simpa [hs, sub_eq_zero] using h0

theorem quadratic_norm_eq_zero (d : ℚ) (hd : ∀ x : ℚ, x ^ 2 ≠ d)
    (t u : ℚ) (h : t ^ 2 - u ^ 2 * d = 0) : t = 0 ∧ u = 0 := by
  by_cases hu : u = 0
  · subst u
    constructor
    · nlinarith
    · rfl
  · exfalso
    apply hd (t / u)
    apply (div_pow t u 2).trans
    apply (div_eq_iff (pow_ne_zero 2 hu)).mpr
    linear_combination h

omit [Algebra ℚ K] in
theorem biquadratic_coefficients_eq_zero
    (a b : K) (d e : ℚ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = (e : K))
    (hd : ∀ x : ℚ, x ^ 2 ≠ d) (he : ∀ x : ℚ, x ^ 2 ≠ e)
    (hde : ∀ x : ℚ, x ^ 2 ≠ d * e) (r s t u : ℚ)
    (h : (r : K) + (s : K) * a + (t : K) * b + (u : K) * (a * b) = 0) :
    r = 0 ∧ s = 0 ∧ t = 0 ∧ u = 0 := by
  by_cases hn : t ^ 2 - u ^ 2 * d = 0
  · obtain ⟨ht, hu⟩ := quadratic_norm_eq_zero d hd t u hn
    obtain ⟨hr, hs⟩ := quadratic_coefficients_eq_zero a d ha hd r s
      (by simpa [ht, hu] using h)
    exact ⟨hr, hs, ht, hu⟩
  · exfalso
    have hnK : ((t ^ 2 - u ^ 2 * d : ℚ) : K) ≠ 0 := Rat.cast_ne_zero.mpr hn
    apply second_root_not_linear a b d e ha hb hd he hde
      ((s * u * d - r * t) / (t ^ 2 - u ^ 2 * d))
      ((r * u - s * t) / (t ^ 2 - u ^ 2 * d))
    push_cast at hnK ⊢
    apply (mul_right_cancel₀ hnK)
    field_simp
    linear_combination ((t : K) - (u : K) * a) * h +
      ((u : K) ^ 2 * b + (s : K) * (u : K)) * ha

theorem generators_linearIndependent_of_squares
    (a b : K) (d e : ℚ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = (e : K))
    (hd : ∀ x : ℚ, x ^ 2 ≠ d) (he : ∀ x : ℚ, x ^ 2 ≠ e)
    (hde : ∀ x : ℚ, x ^ 2 ≠ d * e) :
    LinearIndependent ℚ (generators a b) := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg
  have hsum : (g 0 : K) + (g 1 : K) * a + (g 2 : K) * b +
      (g 3 : K) * (a * b) = 0 := by
    simpa [generators, Fin.sum_univ_succ, Algebra.smul_def,
      add_assoc] using hg
  obtain ⟨h0, h1, h2, h3⟩ := biquadratic_coefficients_eq_zero a b d e
    ha hb hd he hde (g 0) (g 1) (g 2) (g 3) hsum
  intro i
  fin_cases i <;> assumption

theorem rational_sq_ne_two (x : ℚ) : x ^ 2 ≠ 2 := by
  intro h
  have hns : ¬ IsSquare (2 : ℚ) := by norm_num
  apply hns
  exact ⟨x, by simpa [pow_two] using h.symm⟩

theorem generators_linearIndependent_sqrt_two
    (a b : K) (d : ℚ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hd : ∀ x : ℚ, x ^ 2 ≠ d) (h2d : ∀ x : ℚ, x ^ 2 ≠ 2 * d) :
    LinearIndependent ℚ (generators a b) := by
  apply generators_linearIndependent_of_squares a b d 2 ha (by simpa using hb)
    hd rational_sq_ne_two
  simpa [mul_comm] using h2d

theorem rational_sq_ne_of_negative (d : ℚ) (hd : d < 0) (x : ℚ) : x ^ 2 ≠ d := by
  intro h
  have := sq_nonneg x
  linarith

theorem generators_linearIndependent_of_negative_radicand
    (a b : K) (d : ℚ) (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) (hd : d < 0) :
    LinearIndependent ℚ (generators a b) := by
  apply generators_linearIndependent_sqrt_two a b d ha hb
    (rational_sq_ne_of_negative d hd)
  exact rational_sq_ne_of_negative (2 * d) (by linarith)

end W10



namespace WeightedTorusJets.W11

variable {K : Type*} [Field K] [Algebra ℚ K]

def evalAlg (d : ℚ) (ar br : K)
    (ha : ar * ar = algebraMap ℚ K d) (hb : br * br = 2) : Biquad d →ₐ[ℚ] K :=
  { evalBiquad d ar br ha hb with
    commutes' := fun r => by
      change algebraMap ℚ K r + algebraMap ℚ K 0 * ar +
        (algebraMap ℚ K 0 + algebraMap ℚ K 0 * ar) * br = algebraMap ℚ K r
      simp }

@[simp] theorem evalAlg_a (d : ℚ) (ar br : K)
    (ha : ar * ar = algebraMap ℚ K d) (hb : br * br = 2) :
    evalAlg d ar br ha hb (a d) = ar := by
  simp [evalAlg, evalBiquad, evalQuadratic, a]

@[simp] theorem evalAlg_b (d : ℚ) (ar br : K)
    (ha : ar * ar = algebraMap ℚ K d) (hb : br * br = 2) :
    evalAlg d ar br ha hb (b d) = br := by
  simp [evalAlg, evalBiquad, evalQuadratic, b,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem evalAlg_mem_adjoin (d : ℚ) (ar br : K)
    (ha : ar * ar = algebraMap ℚ K d) (hb : br * br = 2) (z : Biquad d) :
    evalAlg d ar br ha hb z ∈ Algebra.adjoin ℚ ({ar, br} : Set K) := by
  let S := Algebra.adjoin ℚ ({ar, br} : Set K)
  have har : ar ∈ S := Algebra.subset_adjoin (by simp)
  have hbr : br ∈ S := Algebra.subset_adjoin (by simp)
  change algebraMap ℚ K z.re.re + algebraMap ℚ K z.re.im * ar +
    (algebraMap ℚ K z.im.re + algebraMap ℚ K z.im.im * ar) * br ∈ S
  exact S.add_mem (S.add_mem (S.algebraMap_mem _) (S.mul_mem (S.algebraMap_mem _) har))
    (S.mul_mem (S.add_mem (S.algebraMap_mem _) (S.mul_mem (S.algebraMap_mem _) har)) hbr)

theorem evalAlg_range (d : ℚ) (ar br : K)
    (ha : ar * ar = algebraMap ℚ K d) (hb : br * br = 2) :
    (evalAlg d ar br ha hb).range = Algebra.adjoin ℚ ({ar, br} : Set K) := by
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    exact evalAlg_mem_adjoin d ar br ha hb z
  · apply Algebra.adjoin_le
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hxa | hx
    · rw [hxa]
      exact ⟨a d, evalAlg_a d ar br ha hb⟩
    · rw [Set.mem_singleton_iff.mp hx]
      exact ⟨b d, evalAlg_b d ar br ha hb⟩

noncomputable def adjoinEquiv (d : ℚ) (ar br : K)
    (ha : ar * ar = algebraMap ℚ K d) (hb : br * br = 2)
    (hli : LinearIndependent ℚ ![1, ar, br, ar * br]) :
    Biquad d ≃ₐ[ℚ] Algebra.adjoin ℚ ({ar, br} : Set K) :=
  (AlgEquiv.ofInjective (evalAlg d ar br ha hb)
    (evalBiquad_injective d ar br ha hb hli)).trans
      (Subalgebra.equivOfEq _ _ (evalAlg_range d ar br ha hb))

@[simp] theorem adjoinEquiv_apply (d : ℚ) (ar br : K)
    (ha : ar * ar = algebraMap ℚ K d) (hb : br * br = 2)
    (hli : LinearIndependent ℚ ![1, ar, br, ar * br]) (z : Biquad d) :
    ↑(adjoinEquiv d ar br ha hb hli z) = evalAlg d ar br ha hb z := rfl

def sigmaAlg (d : ℚ) : Biquad d ≃ₐ[ℚ] Biquad d :=
  { sigma d with
    commutes' := fun r => by
      change sigma d ⟨⟨r, 0⟩, 0⟩ = ⟨⟨r, 0⟩, 0⟩
      ext <;> simp [sigma, flip] }

def tauAlg (d : ℚ) : Biquad d ≃ₐ[ℚ] Biquad d :=
  { tau d with
    commutes' := fun r => by
      change tau d ⟨⟨r, 0⟩, 0⟩ = ⟨⟨r, 0⟩, 0⟩
      ext <;> simp [tau, flip] }

noncomputable def adjoinSigma (d : ℚ) (ar br : K)
    (ha : ar * ar = algebraMap ℚ K d) (hb : br * br = 2)
    (hli : LinearIndependent ℚ ![1, ar, br, ar * br]) :
    Algebra.adjoin ℚ ({ar, br} : Set K) ≃ₐ[ℚ] Algebra.adjoin ℚ ({ar, br} : Set K) :=
  let e := adjoinEquiv d ar br ha hb hli
  (e.symm.trans (sigmaAlg d)).trans e

noncomputable def adjoinTau (d : ℚ) (ar br : K)
    (ha : ar * ar = algebraMap ℚ K d) (hb : br * br = 2)
    (hli : LinearIndependent ℚ ![1, ar, br, ar * br]) :
    Algebra.adjoin ℚ ({ar, br} : Set K) ≃ₐ[ℚ] Algebra.adjoin ℚ ({ar, br} : Set K) :=
  let e := adjoinEquiv d ar br ha hb hli
  (e.symm.trans (tauAlg d)).trans e

@[simp] theorem adjoinSigma_on_model (d : ℚ) (ar br : K)
    (ha : ar * ar = algebraMap ℚ K d) (hb : br * br = 2)
    (hli : LinearIndependent ℚ ![1, ar, br, ar * br]) (z : Biquad d) :
    adjoinSigma d ar br ha hb hli (adjoinEquiv d ar br ha hb hli z) =
      adjoinEquiv d ar br ha hb hli (sigma d z) := by
  simp [adjoinSigma, sigmaAlg]

@[simp] theorem adjoinTau_on_model (d : ℚ) (ar br : K)
    (ha : ar * ar = algebraMap ℚ K d) (hb : br * br = 2)
    (hli : LinearIndependent ℚ ![1, ar, br, ar * br]) (z : Biquad d) :
    adjoinTau d ar br ha hb hli (adjoinEquiv d ar br ha hb hli z) =
      adjoinEquiv d ar br ha hb hli (tau d z) := by
  simp [adjoinTau, tauAlg]

theorem adjoinSigma_a (d : ℚ) (ar br : K)
    (ha : ar * ar = algebraMap ℚ K d) (hb : br * br = 2)
    (hli : LinearIndependent ℚ ![1, ar, br, ar * br]) :
    ((adjoinSigma d ar br ha hb hli
      (adjoinEquiv d ar br ha hb hli (a d)) : Algebra.adjoin ℚ ({ar, br} : Set K)) : K) =
      -ar := by
  rw [adjoinSigma_on_model, sigma_a, map_neg]
  simp

theorem adjoinSigma_b (d : ℚ) (ar br : K)
    (ha : ar * ar = algebraMap ℚ K d) (hb : br * br = 2)
    (hli : LinearIndependent ℚ ![1, ar, br, ar * br]) :
    ((adjoinSigma d ar br ha hb hli
      (adjoinEquiv d ar br ha hb hli (b d)) : Algebra.adjoin ℚ ({ar, br} : Set K)) : K) =
      br := by
  rw [adjoinSigma_on_model, sigma_b]
  simp

@[simp] theorem adjoinSigma_involutive (d : ℚ) (ar br : K)
    (ha : ar * ar = algebraMap ℚ K d) (hb : br * br = 2)
    (hli : LinearIndependent ℚ ![1, ar, br, ar * br])
    (z : Algebra.adjoin ℚ ({ar, br} : Set K)) :
    adjoinSigma d ar br ha hb hli (adjoinSigma d ar br ha hb hli z) = z := by
  obtain ⟨x, rfl⟩ := (adjoinEquiv d ar br ha hb hli).surjective z
  simp

@[simp] theorem adjoinTau_involutive (d : ℚ) (ar br : K)
    (ha : ar * ar = algebraMap ℚ K d) (hb : br * br = 2)
    (hli : LinearIndependent ℚ ![1, ar, br, ar * br])
    (z : Algebra.adjoin ℚ ({ar, br} : Set K)) :
    adjoinTau d ar br ha hb hli (adjoinTau d ar br ha hb hli z) = z := by
  obtain ⟨x, rfl⟩ := (adjoinEquiv d ar br ha hb hli).surjective z
  simp

theorem adjoinSigma_adjoinTau_commute (d : ℚ) (ar br : K)
    (ha : ar * ar = algebraMap ℚ K d) (hb : br * br = 2)
    (hli : LinearIndependent ℚ ![1, ar, br, ar * br])
    (z : Algebra.adjoin ℚ ({ar, br} : Set K)) :
    adjoinSigma d ar br ha hb hli (adjoinTau d ar br ha hb hli z) =
      adjoinTau d ar br ha hb hli (adjoinSigma d ar br ha hb hli z) := by
  obtain ⟨x, rfl⟩ := (adjoinEquiv d ar br ha hb hli).surjective z
  simp [sigma_tau_commute]

noncomputable def adjoinEquivOfNonsquares [CharZero K] (d : ℚ) (ar br : K)
    (ha : ar * ar = algebraMap ℚ K d) (hb : br * br = 2)
    (hd : ∀ x : ℚ, x ^ 2 ≠ d) (h2d : ∀ x : ℚ, x ^ 2 ≠ 2 * d) :
    Biquad d ≃ₐ[ℚ] Algebra.adjoin ℚ ({ar, br} : Set K) :=
  adjoinEquiv d ar br ha hb (by
    apply SiegelZeros.W10.generators_linearIndependent_sqrt_two ar br d
      (by simpa [pow_two] using ha) (by simpa [pow_two] using hb) hd h2d)

end WeightedTorusJets.W11


end SiegelZeros

end OAI
