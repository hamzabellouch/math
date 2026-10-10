import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.GeometricProduct
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OneOrZero

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter

namespace OrdinaryCorrelations.PretentiousEuler
open Finset Completion NonpretentiousEuler

def coefficientHom (z : ℕ → ℂ) : ℕ →* ℂ where
  toFun n := complete z n / (n : ℂ)
  map_one' := by simp
  map_mul' m n := by
    simp only [complete_mul, Nat.cast_mul]
    exact _root_.div_mul_div_comm .. |>.symm

lemma coefficient_prime_norm {z : ℕ → ℂ} (hz : OneBounded z) {p : ℕ} (hp : Nat.Prime p) :
    ‖coefficientHom z p‖ < 1 := by
  change ‖complete z p / (p:ℂ)‖ < 1
  rw [complete_prime z hp, norm_div, Complex.norm_natCast]
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  apply (div_lt_one hp0).mpr
  exact (hz p).trans_lt (by exact_mod_cast hp.one_lt)

lemma complete_twist (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ∀ n : ℕ, complete (twist f χ t) n = twist (complete f) χ t n := by
  have hm (m n : ℕ) : twist (complete f) χ t (m*n) =
      twist (complete f) χ t m * twist (complete f) χ t n := by
    by_cases hm : m = 0
    · simp [hm,twist]
    by_cases hn : n = 0
    · simp [hn,twist]
    have he : Complex.exp (((t * Real.log ((m*n:ℕ):ℝ)):ℝ) * Complex.I) =
        Complex.exp (((t * Real.log (m:ℝ)):ℝ) * Complex.I) *
        Complex.exp (((t * Real.log (n:ℝ)):ℝ) * Complex.I) := by
      rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hm) (by exact_mod_cast hn),mul_add,
        Complex.ofReal_add,add_mul,Complex.exp_add]
    simp only [twist,complete_mul]
    rw [he]
    simp only [Nat.cast_mul,map_mul,star_mul]
    ring
  refine Nat.recOnMul (by simp [twist]) ?_ ?_ ?_
  · simp [twist]
  · intro p hp
    simp [complete_prime _ hp,twist]
  · intro m n ih1 ih2
    rw [complete_mul,ih1,ih2,hm]

def smoothSeries (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (N : ℕ) : ℂ :=
  ∑' n : Nat.factoredNumbers (Icc 2 N),
    complete f n * star (χ (n : ZMod q) *
      Complex.exp (((t * Real.log (n:ℕ):ℝ):ℝ) * Complex.I)) / (n:ℕ)

lemma smoothSeries_summable {f : ℕ → ℂ} (hf : OneBounded f) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) (N : ℕ) :
    Summable (fun n : Nat.factoredNumbers (Icc 2 N) =>
      ‖complete f n * star (χ (n : ZMod q) *
        Complex.exp (((t * Real.log (n:ℕ):ℝ):ℝ) * Complex.I)) / (n:ℕ)‖) := by
  have hh := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := coefficientHom (twist f χ t))
    (fun {_} hp => coefficient_prime_norm (twist_norm_le hf χ t) hp) (Icc 2 N)).1
  simpa only [coefficientHom,MonoidHom.coe_mk,OneHom.coe_mk,complete_twist,twist] using hh

lemma normalized_smoothSeries_eq (f : ℕ → ℂ) (hf : OneBounded f) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) (N : ℕ) :
    (∏ p ∈ (Icc 2 N).filter Nat.Prime, (1-(p:ℂ)⁻¹)) * smoothSeries f χ t N =
      geometricProduct f χ t N := by
  have hh := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := coefficientHom (twist f χ t))
    (fun {_} hp => coefficient_prime_norm (twist_norm_le hf χ t) hp) (Icc 2 N)).2.tsum_eq
  have hs : smoothSeries f χ t N = ∏ p ∈ (Icc 2 N).filter Nat.Prime,
      (1 - twist f χ t p / (p:ℂ))⁻¹ := by
    calc
      _ = ∑' n : Nat.factoredNumbers (Icc 2 N), coefficientHom (twist f χ t) n := by
        apply tsum_congr
        intro n
        simp only [coefficientHom,MonoidHom.coe_mk,OneHom.coe_mk,complete_twist,twist]
      _ = _ := hh.trans (by
        apply prod_congr rfl
        intro p hp
        simp [coefficientHom,complete_prime _ (mem_filter.mp hp).2])
  rw [hs, ←prod_mul_distrib]
  apply prod_congr rfl
  intro p hp
  simp only [factor,Complex.ofReal_inv,Complex.ofReal_natCast]
  congr 2
  ring

theorem eventual_normalized_smoothSeries_small {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (q : ℕ) (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ Set.Icc (-(N:ℝ)) (N:ℝ),
      ‖(∏ p ∈ (Icc 2 N).filter Nat.Prime, (1-(p:ℂ)⁻¹)) * smoothSeries f χ t N‖ ≤ ε := by
  simpa only [normalized_smoothSeries_eq f hf χ] using
    eventual_uniform_geometric hf hNP q hq χ hε

end OrdinaryCorrelations.PretentiousEuler

end

end OAI
