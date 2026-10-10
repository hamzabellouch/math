import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateMass

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.DiagonalEstimate
open Ostmann.Preliminaries Ostmann.Construction
attribute [local instance] Classical.propDecidable

private theorem weighted_pair_square_le {p q D a b : ℝ}
    (hp : 0≤p) (hq : 0≤q) (hpD : p≤D) (hqD : q≤D) :
    2*(p*q*a*b)≤D*(p*a^2+q*b^2) := by
  have h1 := mul_nonneg (mul_nonneg hp hq) (sq_nonneg (a-b))
  have h2 := mul_nonneg (mul_nonneg hp (sub_nonneg.mpr hqD)) (sq_nonneg a)
  have h3 := mul_nonneg (mul_nonneg hq (sub_nonneg.mpr hpD)) (sq_nonneg b)
  nlinarith

theorem matched_norm_sum_le {α : Type*} [Fintype α] (μ : FinitePrior α)
    (e : Equiv.Perm α) (W : α→ℂ) (D : ℝ) (hD : 0≤D)
    (hcap : ∀x,W x≠0 → μ.mass x≤D) :
    (∑x,μ.mass x*μ.mass (e x)*‖W x‖*‖W (e x)‖) ≤
      D*μ.mean (fun x => ‖W x‖^2) := by
  have hp (x : α) : 2*(μ.mass x*μ.mass (e x)*‖W x‖*‖W (e x)‖)≤
      D*(μ.mass x*‖W x‖^2+μ.mass (e x)*‖W (e x)‖^2) := by
    by_cases hx : W x=0
    · simp only [hx,norm_zero,mul_zero,zero_mul,zero_pow,ne_eq,OfNat.ofNat_ne_zero,
        not_false_eq_true,zero_add]
      exact mul_nonneg hD (mul_nonneg (μ.mass_nonneg _) (sq_nonneg _))
    by_cases hy : W (e x)=0
    · simp only [hy,norm_zero,mul_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,
        not_false_eq_true,add_zero]
      exact mul_nonneg hD (mul_nonneg (μ.mass_nonneg _) (sq_nonneg _))
    exact weighted_pair_square_le (μ.mass_nonneg _) (μ.mass_nonneg _) (hcap _ hx) (hcap _ hy)
  have hs := Finset.sum_le_sum (fun x (_ : x∈Finset.univ) => hp x)
  have he : (∑x,μ.mass (e x)*‖W (e x)‖^2)=(∑x,μ.mass x*‖W x‖^2) :=
    Equiv.sum_comp e (fun x => μ.mass x*‖W x‖^2)
  rw [←Finset.mul_sum,←Finset.mul_sum,Finset.sum_add_distrib,he] at hs
  change _≤D*(∑x,μ.mass x*‖W x‖^2)
  linarith

def tuplePermutation {I β : Type*} (e : Equiv.Perm I) : Equiv.Perm (I→β) where
  toFun f := f ∘ e
  invFun f := f ∘ e.symm
  left_inv f := by funext i; simp
  right_inv f := by funext i; simp

theorem harmonic_matched_norm_sum_le {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ}
    (E : I → Finset (PrimeUpTo N)) (hE : ∀i,0<primeShellMass (E i))
    (e : Equiv.Perm I) (Wf : (I→PrimeUpTo N)→ℂ) (T Δ W : ℝ)
    (hrange : ∀f,(productPrior (fun i => primeShellPrior (E i) (hE i))).mass f≠0 →
      Wf f≠0 → Real.exp (T+Δ-W)≤((∏i,(f i).val : ℕ):ℝ)) :
    let μ := productPrior (fun i => primeShellPrior (E i) (hE i))
    (∑f,μ.mass f*μ.mass (f ∘ e)*‖Wf f‖*‖Wf (f ∘ e)‖) ≤
      (copiedNormalization E*Real.exp (-T-Δ+W))*μ.mean (fun f => ‖Wf f‖^2) := by
  exact matched_norm_sum_le _ (tuplePermutation e) Wf _
    (mul_nonneg (copiedNormalization_nonneg E hE) (Real.exp_pos _).le)
    (by
      intro f hf
      by_cases hm : (productPrior (fun i => primeShellPrior (E i) (hE i))).mass f=0
      · rw [hm]
        exact mul_nonneg (copiedNormalization_nonneg E hE) (Real.exp_pos _).le
      exact tuple_mass_le_exp_window E hE f T Δ W (hrange f hm hf))

theorem harmonic_matching_family_norm_sum_le {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ}
    (E : I → Finset (PrimeUpTo N)) (hE : ∀i,0<primeShellMass (E i))
    (A : Finset (Equiv.Perm I)) (Wf : (I→PrimeUpTo N)→ℂ) (T Δ W : ℝ)
    (hrange : ∀f,(productPrior (fun i => primeShellPrior (E i) (hE i))).mass f≠0 →
      Wf f≠0 → Real.exp (T+Δ-W)≤((∏i,(f i).val : ℕ):ℝ)) :
    let μ := productPrior (fun i => primeShellPrior (E i) (hE i))
    (∑e∈A,∑f,μ.mass f*μ.mass (f ∘ e)*‖Wf f‖*‖Wf (f ∘ e)‖) ≤
      (A.card:ℝ)*(copiedNormalization E*Real.exp (-T-Δ+W))*
        μ.mean (fun f => ‖Wf f‖^2) := by
  dsimp only
  calc
    _≤∑_e∈A,(copiedNormalization E*Real.exp (-T-Δ+W))*
        (productPrior (fun i => primeShellPrior (E i) (hE i))).mean (fun f => ‖Wf f‖^2) :=
      Finset.sum_le_sum fun e he => harmonic_matched_norm_sum_le E hE e Wf T Δ W hrange
    _=_ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

end Ostmann.Characters.DiagonalEstimate

end

end OAI
