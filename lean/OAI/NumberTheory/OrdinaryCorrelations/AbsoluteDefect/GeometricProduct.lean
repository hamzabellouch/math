import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OneBounded
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Factor
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.NormOneAddLeExp

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter

namespace OrdinaryCorrelations.PretentiousEuler
open Finset NonpretentiousEuler

def geometricProduct (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (N : ℕ) : ℂ :=
  ∏ p ∈ (Icc 2 N).filter Nat.Prime, factor (p:ℝ)⁻¹ (twist f χ t p)

theorem geometricProduct_norm_le {f : ℕ → ℂ} (hf : OneBounded f) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ‖geometricProduct f χ t N‖ ≤ Real.exp (1-distanceSq f χ t N) := by
  let P := (Icc 2 N).filter Nat.Prime
  have hr (p : ℕ) (hp : p ∈ P) : (p:ℝ)⁻¹ ≤ 1/2 := by
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
    simpa using inv_anti₀ (by norm_num : (0:ℝ) < 2) hp2
  have hid : (∑ p ∈ P, (p:ℝ)⁻¹*(1-(twist f χ t p).re)) = distanceSq f χ t N := by
    simp only [distanceSq,Nat.floor_natCast]
    apply sum_congr rfl
    intro p hp
    change (p:ℝ)⁻¹*(1-(twist f χ t p).re) = (1-(twist f χ t p).re)/(p:ℝ)
    ring
  refine (product_norm_le P (fun p => (p:ℝ)⁻¹) (twist f χ t)
    (fun p hp => inv_nonneg.mpr (Nat.cast_nonneg p)) hr (fun p hp => twist_norm_le hf χ t p)).trans ?_
  rw [hid]
  apply Real.exp_le_exp.mpr
  have hs := prime_inv_sq_sum_le hN
  change _ ≤ 1 at hs
  linarith

lemma eventual_distanceSq_lower {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (q : ℕ) (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ Set.Icc (-(N:ℝ)) (N:ℝ), B ≤ distanceSq f χ t N := by
  have hmin := (hNP q hq χ).eventually (eventually_ge_atTop (max 1 B))
  filter_upwards [hmin] with N hN
  intro t ht
  have hbdd : BddBelow ((fun t : ℝ => distance f χ t N) '' Set.Icc (-(N:ℝ)) (N:ℝ)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t,ht,rfl⟩
    exact Real.sqrt_nonneg _
  have hh := hN.trans (csInf_le hbdd (Set.mem_image_of_mem _ ht))
  have hd1 : 1 ≤ distance f χ t N := (le_max_left _ _).trans hh
  have hdB : B ≤ distance f χ t N := (le_max_right _ _).trans hh
  have hs : distance f χ t N ^2 = distanceSq f χ t N := Real.sq_sqrt (distanceSq_nonneg hf χ t N)
  nlinarith

theorem eventual_uniform_geometric {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (q : ℕ) (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ Set.Icc (-(N:ℝ)) (N:ℝ), ‖geometricProduct f χ t N‖ ≤ ε := by
  filter_upwards [eventual_distanceSq_lower hf hNP q hq χ (1-Real.log ε),
    eventually_ge_atTop (1:ℕ)] with N hN hN1
  intro t ht
  calc
    _ ≤ Real.exp (1-distanceSq f χ t N) := geometricProduct_norm_le hf χ t hN1
    _ ≤ Real.exp (Real.log ε) := Real.exp_le_exp.mpr (by linarith [hN t ht])
    _ = ε := Real.exp_log hε

end OrdinaryCorrelations.PretentiousEuler

end

end OAI
