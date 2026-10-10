import Mathlib

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open scoped BigOperators

@[reducible] def Cube : ℕ → Type
  | 0 => Unit
  | n+1 => Bool × Cube n

instance cubeFintype : (n : ℕ) → Fintype (Cube n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => by
      letI := cubeFintype n
      exact inferInstanceAs (Fintype (Bool × Cube n))

instance cubeNonempty : (n : ℕ) → Nonempty (Cube n)
  | 0 => inferInstanceAs (Nonempty Unit)
  | n+1 => @instNonemptyProd Bool (Cube n) _ (cubeNonempty n)

noncomputable def mean {n : ℕ} (f : Cube n → ℝ) : ℝ := 𝔼 x, f x

lemma mean_zero (f : Cube 0 → ℝ) : mean f = f () := by
  change (𝔼 x : Unit, f x) = f ()
  simp [Finset.expect_eq_sum_div_card]

lemma mean_succ {n : ℕ} (f : Cube (n+1) → ℝ) :
    mean f = (mean (fun x => f (false,x)) + mean (fun x => f (true,x))) / 2 := by
  change (𝔼 x : Bool × Cube n, f x) = _
  rw [show (Finset.univ : Finset (Bool × Cube n)) = Finset.univ ×ˢ Finset.univ from rfl,
    Finset.expect_product]
  simp [Finset.expect_eq_sum_div_card, mean, add_comm]

lemma mean_add {n : ℕ} (f g : Cube n → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g := Finset.expect_add_distrib _ _ _

lemma mean_sub {n : ℕ} (f g : Cube n → ℝ) :
    mean (fun x => f x - g x) = mean f - mean g := Finset.expect_sub_distrib _ _ _

lemma mean_mul {n : ℕ} (a : ℝ) (f : Cube n → ℝ) :
    mean (fun x => a * f x) = a * mean f := (Finset.mul_expect _ _ _).symm

lemma mean_nonneg {n : ℕ} {f : Cube n → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean f :=
  Finset.expect_nonneg (fun x _ => hf x)

lemma mean_mono {n : ℕ} {f g : Cube n → ℝ} (h : ∀ x, f x ≤ g x) : mean f ≤ mean g :=
  Finset.expect_le_expect (fun x _ => h x)

lemma mean_cauchy {n : ℕ} (f g : Cube n → ℝ) :
    (mean (fun x => f x * g x))^2 ≤ mean (fun x => f x^2) * mean (fun x => g x^2) :=
  Finset.expect_mul_sq_le_sq_mul_sq _ _ _

noncomputable def evenPart {n : ℕ} (f : Cube (n+1) → ℝ) (x : Cube n) :=
  (f (false,x) + f (true,x)) / 2

noncomputable def oddPart {n : ℕ} (f : Cube (n+1) → ℝ) (x : Cube n) :=
  (f (false,x) - f (true,x)) / 2

noncomputable def noise (ρ : ℝ) : {n : ℕ} → (Cube n → ℝ) → Cube n → ℝ
  | 0, f, x => f x
  | _+1, f, (b,x) => noise ρ (evenPart f) x + (if b then -ρ else ρ) * noise ρ (oddPart f) x

lemma mean_square_split {n : ℕ} (f : Cube (n+1) → ℝ) :
    mean (fun x => f x^2) = mean (fun x => evenPart f x^2) + mean (fun x => oddPart f x^2) := by
  rw [mean_succ, ← mean_add]
  rw [← mean_add, div_eq_mul_inv, mul_comm _ (2⁻¹), ← mean_mul]
  congr 1
  funext x
  dsimp [evenPart, oddPart]
  ring

lemma mean_noise_fourth {n : ℕ} (ρ : ℝ) (f : Cube (n+1) → ℝ) :
    mean (fun x => noise ρ f x ^ 4) =
      mean (fun x => noise ρ (evenPart f) x ^ 4) +
      6 * ρ^2 * mean (fun x => (noise ρ (evenPart f) x)^2 * (noise ρ (oddPart f) x)^2) +
      ρ^4 * mean (fun x => noise ρ (oddPart f) x ^ 4) := by
  rw [mean_succ, ← mean_add, div_eq_mul_inv, mul_comm _ (2⁻¹), ← mean_mul, ← mean_mul, ← mean_add,
    ← mean_mul, ← mean_add]
  congr 1
  funext x
  dsimp [noise]
  ring

theorem hypercontractive_two_four {n : ℕ} (f : Cube n → ℝ) :
    mean (fun x => noise (1/2) f x ^ 4) ≤ (mean (fun x => f x^2))^2 := by
  induction n with
  | zero =>
    simp only [mean_zero, noise]
    nlinarith
  | succ n ih =>
    let a := evenPart f
    let b := oddPart f
    let A := mean (fun x => a x^2)
    let B := mean (fun x => b x^2)
    let C := mean (fun x => noise (1/2) a x^4)
    let D := mean (fun x => noise (1/2) b x^4)
    let E := mean (fun x => (noise (1/2) a x)^2 * (noise (1/2) b x)^2)
    have hA : 0 ≤ A := mean_nonneg (fun x => sq_nonneg _)
    have hB : 0 ≤ B := mean_nonneg (fun x => sq_nonneg _)
    have hC : 0 ≤ C := mean_nonneg (fun x => by positivity)
    have hD : 0 ≤ D := mean_nonneg (fun x => by positivity)
    have hE : 0 ≤ E := mean_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have hCA : C ≤ A^2 := ih a
    have hDB : D ≤ B^2 := ih b
    have hEC : E^2 ≤ C*D := by
      have hc := mean_cauchy (fun x => (noise (1/2) a x)^2) (fun x => (noise (1/2) b x)^2)
      have hpow (x : ℝ) : (x^2)^2 = x^4 := by ring
      simp only [hpow] at hc
      exact hc
    have hmul : C*D ≤ A^2*B^2 := mul_le_mul hCA hDB hD (sq_nonneg A)
    have hEAB : E ≤ A*B := by
      nlinarith [hEC.trans hmul, mul_nonneg hA hB]
    rw [mean_noise_fourth, mean_square_split]
    change C + 6*(1/2:ℝ)^2*E + (1/2:ℝ)^4*D ≤ (A+B)^2
    nlinarith [mul_nonneg hA hB]

lemma evenPart_noise {n : ℕ} (ρ : ℝ) (f : Cube (n+1) → ℝ) :
    evenPart (noise ρ f) = noise ρ (evenPart f) := by
  funext x
  dsimp [evenPart, noise]
  ring

lemma oddPart_noise {n : ℕ} (ρ : ℝ) (f : Cube (n+1) → ℝ) :
    oddPart (noise ρ f) = fun x => ρ * noise ρ (oddPart f) x := by
  funext x
  dsimp [oddPart, noise]
  ring

lemma mean_product_split {n : ℕ} (f g : Cube (n+1) → ℝ) :
    mean (fun x => f x * g x) =
      mean (fun x => evenPart f x * evenPart g x) +
      mean (fun x => oddPart f x * oddPart g x) := by
  rw [mean_succ, ← mean_add, div_eq_mul_inv, mul_comm _ (2⁻¹), ← mean_mul,
    ← mean_add]
  congr 1
  funext x
  dsimp [evenPart, oddPart]
  ring

lemma noise_selfadjoint {n : ℕ} (ρ : ℝ) (f g : Cube n → ℝ) :
    mean (fun x => f x * noise ρ g x) = mean (fun x => noise ρ f x * g x) := by
  induction n with
  | zero => simp only [mean_zero, noise]
  | succ n ih =>
    rw [mean_product_split, mean_product_split, evenPart_noise, oddPart_noise,
      evenPart_noise, oddPart_noise, ih]
    have h₁ : mean (fun x => oddPart f x * (ρ * noise ρ (oddPart g) x)) =
        ρ * mean (fun x => oddPart f x * noise ρ (oddPart g) x) := by
      rw [← mean_mul]
      congr 1; funext x; ring
    have h₂ : mean (fun x => ρ * noise ρ (oddPart f) x * oddPart g x) =
        ρ * mean (fun x => noise ρ (oddPart f) x * oddPart g x) := by
      rw [← mean_mul]
      congr 1; funext x; ring
    rw [h₁, h₂, ih]

lemma mean_holder_four {n : ℕ} (g h : Cube n → ℝ) :
    (mean (fun x => g x * h x))^4 ≤
      (mean (fun x => |g x|))^2 * mean (fun x => g x^2) * mean (fun x => h x^4) := by
  let G := mean (fun x => |g x|)
  let U := mean (fun x => |g x| * |h x|)
  let V := mean (fun x => |g x| * h x^2)
  have hG : 0 ≤ G := mean_nonneg (fun x => abs_nonneg _)
  have hU : 0 ≤ U := mean_nonneg (fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hV : 0 ≤ V := mean_nonneg (fun x => mul_nonneg (abs_nonneg _) (sq_nonneg _))
  have huv : U^2 ≤ G*V := by
    have hc := mean_cauchy (fun x => Real.sqrt |g x|) (fun x => Real.sqrt |g x| * |h x|)
    have he₁ : (fun x => Real.sqrt |g x| * (Real.sqrt |g x| * |h x|)) =
        (fun x => |g x| * |h x|) := by
      funext x
      rw [← mul_assoc, Real.mul_self_sqrt (abs_nonneg _)]
    have he₂ : (fun x => (Real.sqrt |g x|)^2) = (fun x => |g x|) := by
      funext x; exact Real.sq_sqrt (abs_nonneg _)
    have he₃ : (fun x => (Real.sqrt |g x| * |h x|)^2) = (fun x => |g x| * h x^2) := by
      funext x
      rw [mul_pow, Real.sq_sqrt (abs_nonneg _), sq_abs]
    simpa only [he₁, he₂, he₃] using hc
  have hv : V^2 ≤ mean (fun x => g x^2) * mean (fun x => h x^4) := by
    have hc := mean_cauchy (fun x => |g x|) (fun x => h x^2)
    have hpow (x : ℝ) : (x^2)^2 = x^4 := by ring
    simp only [sq_abs, hpow] at hc
    exact hc
  have habs : |mean (fun x => g x * h x)| ≤ U := by
    have hh := Finset.abs_expect_le Finset.univ (fun x => g x*h x)
    simp only [abs_mul] at hh
    exact hh
  have hs : (mean (fun x => g x * h x))^2 ≤ U^2 := by
    have ha := abs_nonneg (mean (fun x => g x*h x))
    nlinarith [sq_abs (mean (fun x => g x*h x))]
  have hsq : (mean (fun x => g x * h x))^4 ≤ (G*V)^2 := by
    nlinarith [hs.trans huv, sq_nonneg (mean (fun x => g x*h x))]
  have hm := mul_le_mul_of_nonneg_left hv (sq_nonneg G)
  nlinarith

theorem noise_small_l1 {n : ℕ} (g : Cube n → ℝ) (hg : ∀ x, |g x| ≤ 1) :
    (mean (fun x => noise (1/2) g x^2))^2 ≤ (mean (fun x => |g x|))^3 := by
  let u := noise (1/2) g
  let A := mean (fun x => u x^2)
  let I := mean (fun x => |g x|)
  have hA : 0 ≤ A := mean_nonneg (fun x => sq_nonneg _)
  have hI : 0 ≤ I := mean_nonneg (fun x => abs_nonneg _)
  have hgs : mean (fun x => g x^2) ≤ I := by
    apply mean_mono
    intro x
    nlinarith [hg x, abs_nonneg (g x), sq_abs (g x)]
  have he : mean (fun x => g x * noise (1/2) u x) = A := by
    rw [noise_selfadjoint]
    congr 1; funext x; simp only [u, pow_two]
  have h := mean_holder_four g (noise (1/2) u)
  rw [he] at h
  have hh := hypercontractive_two_four u
  have hp : 0 ≤ I^2 * mean (fun x => g x^2) :=
    mul_nonneg (sq_nonneg _) (mean_nonneg (fun x => sq_nonneg _))
  have h₂ := mul_le_mul_of_nonneg_left hh hp
  have h₃ := mul_le_mul_of_nonneg_left hgs (sq_nonneg I)
  have h₄ := mul_le_mul_of_nonneg_right h₃ (sq_nonneg A)
  change A^2 ≤ I^3
  change _ ≤ _ * A^2 at h₂
  nlinarith [h.trans h₂]

end LargeIndependentSets.BooleanJunta

end OAI
