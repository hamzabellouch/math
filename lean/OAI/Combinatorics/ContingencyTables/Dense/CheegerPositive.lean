import OAI.Combinatorics.ContingencyTables.Dense.CheegerCoarea

namespace OAI

/-! # Cheeger energy bound for functions supported on half the mass -/
namespace ContingencyTables.CheegerProof
open CommonBasesFPRAS
open scoped BigOperators Classical
noncomputable section

private lemma weighted_cauchy {ι : Type*} [Fintype ι]
    (w a b : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i*a i*b i)^2 ≤ (∑ i, w i*(a i)^2)*(∑ i, w i*(b i)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (w i)*a i) (fun i => Real.sqrt (w i)*b i)
  have hmul (i : ι) : (Real.sqrt (w i)*a i)*(Real.sqrt (w i)*b i) = w i*a i*b i := by
    calc
      _ = (Real.sqrt (w i))^2*a i*b i := by ring
      _ = _ := by rw [Real.sq_sqrt (hw i)]
  have hsq (f : ι → ℝ) (i : ι) : (Real.sqrt (w i)*f i)^2 = w i*(f i)^2 := by
    rw [mul_pow,Real.sq_sqrt (hw i)]
  simpa only [hmul,hsq] using h

variable {X : Type*} [Fintype X] (C : FiniteChain X)

lemma sum_pair_squares (g : X → ℝ) :
    (∑ x, ∑ y, C.π x*C.P x y*((g x)^2+(g y)^2)) = 2*(∑ x, C.π x*(g x)^2) := by
  simp_rw [mul_add,Finset.sum_add_distrib]
  have hleft : (∑ x, ∑ y, C.π x*C.P x y*(g x)^2) = ∑ x, C.π x*(g x)^2 := by
    simp_rw [← Finset.sum_mul,← Finset.mul_sum,C.stochastic,mul_one]
  have hright : (∑ x, ∑ y, C.π x*C.P x y*(g y)^2) = ∑ y, C.π y*(g y)^2 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul,C.stationary]
  rw [hleft,hright]
  ring

lemma sum_pair_add_square_le (g : X → ℝ) :
    (∑ x, ∑ y, C.π x*C.P x y*(g x+g y)^2) ≤ 4*(∑ x, C.π x*(g x)^2) := by
  calc
    _ ≤ ∑ x, ∑ y, 2*(C.π x*C.P x y*((g x)^2+(g y)^2)) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      have hQ := mul_nonneg (C.positive x).le (C.nonnegative x y)
      have hsq : (g x+g y)^2 ≤ 2*((g x)^2+(g y)^2) := by nlinarith [sq_nonneg (g x-g y)]
      nlinarith [mul_le_mul_of_nonneg_left hsq hQ]
    _ = _ := by simp_rw [← Finset.mul_sum]; rw [sum_pair_squares]; ring

theorem positive_energy (κ : ℝ) (hk : 0 < κ)
    (hcut : ∀ S : Finset X, κ*min (mass C S) (mass C Sᶜ) ≤ cut C S)
    (g : X → ℝ) (hg : ∀ x, 0 ≤ g x)
    (hsmall : mass C (Finset.univ.filter fun x => 0 < g x) ≤ 1/2) :
    κ^2*(∑ x, C.π x*(g x)^2) ≤ 2*C.energy g := by
  let N := ∑ x, C.π x*(g x)^2
  let W := ∑ x, ∑ y, C.π x*C.P x y*|(g x)^2-(g y)^2|
  have hE : 0 ≤ C.energy g := C.energy_nonneg g
  have hN : 0 ≤ N := Finset.sum_nonneg fun x _ => mul_nonneg (C.positive x).le (sq_nonneg _)
  have hW : 0 ≤ W := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (mul_nonneg (C.positive x).le (C.nonnegative x y)) (abs_nonneg _)
  have hsquare : mass C (Finset.univ.filter fun x => 0 < (g x)^2) ≤ 1/2 := by
    apply le_trans (mass_mono C ?_) hsmall
    intro x hx
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hx ⊢
    nlinarith [hg x]
  have hc : 2*κ*N ≤ W := coarea C κ hcut (fun x => (g x)^2) (fun _ => sq_nonneg _) hsquare
  have hsqW : (2*κ*N)^2 ≤ W^2 := (sq_le_sq₀ (by positivity) hW).mpr hc
  have ha (x y : X) : |(g x)^2-(g y)^2| = |g x-g y| * (g x+g y) := by
    rw [show (g x)^2-(g y)^2 = (g x-g y)*(g x+g y) by ring,
      abs_mul,abs_of_nonneg (add_nonneg (hg x) (hg y))]
  have hcs := weighted_cauchy
    (fun z : X×X => C.π z.1*C.P z.1 z.2)
    (fun z => |g z.1-g z.2|) (fun z => g z.1+g z.2)
    (fun z => mul_nonneg (C.positive _).le (C.nonnegative _ _))
  simp only [Fintype.sum_prod_type,sq_abs] at hcs
  have he : (∑ x, ∑ y, C.π x*C.P x y*(g x-g y)^2) = 2*C.energy g := by
    rw [C.energy_eq]; ring
  have hW' : W = ∑ x, ∑ y, C.π x*C.P x y*|g x-g y| * (g x+g y) := by
    dsimp [W]
    simp_rw [ha,mul_assoc]
  rw [← hW',he] at hcs
  have hb := sum_pair_add_square_le C g
  have hall : (2*κ*N)^2 ≤ (2*C.energy g)*(4*N) :=
    (hsqW.trans hcs).trans (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2*C.energy g))
  rcases hN.eq_or_lt with hz | hp
  · change κ^2*N ≤ _
    rw [← hz,mul_zero]
    positivity
  · change κ^2*N ≤ _
    have h : 4*N*(κ^2*N) ≤ 4*N*(2*C.energy g) := by nlinarith [hall]
    exact (mul_le_mul_iff_right₀ (by positivity : 0 < 4*N)).mp h

end
end ContingencyTables.CheegerProof

end OAI
