import OAI.NumberTheory.CubicMoment.Estimates.PrimeIdealEulerExclusion
import OAI.NumberTheory.CubicMoment.Estimates.IdealDirichletInverse

namespace OAI

/-! Exact finite Euler factors for the complete ideal Dirichlet series.
These retain the ramified factors lost in primitive reduction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeIdealRestriction_norm_le (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (ν : EisensteinIdealExponent) :
    ‖primeIdealRestriction S χ ν‖ ≤ 1 := by
  unfold primeIdealRestriction
  split_ifs
  · exact hχ ν
  · simp

lemma primeIdealRestriction_add (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν κ, χ (ν+κ)=χ ν*χ κ)
    (ν κ : EisensteinIdealExponent) :
    primeIdealRestriction S χ (ν+κ)=primeIdealRestriction S χ ν*primeIdealRestriction S χ κ := by
  have hz : (∀ p ∈ S, (ν+κ) p=0) ↔ (∀ p ∈ S, ν p=0) ∧ (∀ p ∈ S, κ p=0) := by
    simp only [Finsupp.add_apply,Nat.add_eq_zero_iff,forall_and]
  unfold primeIdealRestriction
  simp only [hz,hχ]
  split_ifs <;> simp_all

lemma primeIdealRestriction_insert (S : Finset EisensteinIdealPrime) (p : EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) :
    primeIdealRestriction (insert p S) χ = primeIdealRestriction {p} (primeIdealRestriction S χ) := by
  funext ν
  simp only [primeIdealRestriction,Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,
    forall_eq]
  split_ifs <;> simp_all

lemma idealDirichlet_single_exclusion (p : EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {s : ℂ} (hs : 1 < s.re) :
    normDirichletSeries (primeIdealRestriction {p} χ) idealExponentNorm s =
      (1-χ (Finsupp.single p 1)*(idealExponentNorm (Finsupp.single p 1):ℂ)^(-s))*
        normDirichletSeries χ idealExponentNorm s := by
  let δ : EisensteinIdealExponent := Finsupp.single p 1
  let f (ν : EisensteinIdealExponent) := χ ν*(idealExponentNorm ν:ℂ)^(-s)
  let g (ν : EisensteinIdealExponent) := if δ ≤ ν then f ν else 0
  have hf : Summable f := (idealDirichlet_norm_summable χ hχ hs).of_norm
  have hg : Summable g := by
    convert hf.indicator {ν | δ ≤ ν} using 1
    ext ν
    by_cases hν : δ ≤ ν <;> simp [g,Set.indicator,hν]
  have hi : Function.Injective (fun ν : EisensteinIdealExponent => δ+ν) :=
    fun _ _ h => add_left_cancel h
  have hshift : (∑' ν, g ν)=f δ*(∑' ν, f ν) := by
    have hsup : Function.support g ⊆ Set.range (fun ν => δ+ν) := by
      intro ν hν
      have hd : δ ≤ ν := by
        by_contra hn
        exact hν (by simp [g,hn])
      exact ⟨ν-δ,add_tsub_cancel_of_le hd⟩
    rw [←hi.tsum_eq hsup]
    simp only [g,le_add_of_nonneg_right zero_le,ite_true]
    simp_rw [show ∀ ν, f (δ+ν)=f δ*f ν from fun ν => idealDirichlet_weight_add χ hadd s δ ν]
    exact tsum_mul_left
  have he (ν : EisensteinIdealExponent) :
      primeIdealRestriction {p} χ ν*(idealExponentNorm ν:ℂ)^(-s)=f ν-g ν := by
    have hd : δ ≤ ν ↔ 0 < ν p := by
      simp only [δ,Finsupp.single_le_iff,Nat.one_le_iff_ne_zero,Nat.pos_iff_ne_zero]
    simp only [primeIdealRestriction,Finset.mem_singleton,forall_eq]
    by_cases hp : ν p=0
    · simp [f,g,hd,hp]
    · simp [f,g,hd,hp,Nat.pos_of_ne_zero hp]
  unfold normDirichletSeries
  simp_rw [he]
  rw [hf.tsum_sub hg,hshift]
  dsimp only [f,δ]
  ring

def idealEulerFactor (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (s : ℂ) : ℂ :=
  ∏ p ∈ S, (1-χ (Finsupp.single p 1)*(idealExponentNorm (Finsupp.single p 1):ℂ)^(-s))

theorem idealDirichlet_euler_exclusion (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {s : ℂ} (hs : 1 < s.re) :
    normDirichletSeries (primeIdealRestriction S χ) idealExponentNorm s =
      idealEulerFactor S χ s*normDirichletSeries χ idealExponentNorm s := by
  induction S using Finset.induction_on with
  | empty => simp [primeIdealRestriction,idealEulerFactor,normDirichletSeries]
  | @insert p S hp ih =>
      rw [primeIdealRestriction_insert,idealDirichlet_single_exclusion p _
        (primeIdealRestriction_norm_le S χ hχ) (primeIdealRestriction_add S χ hadd) hs,ih,
        primeIdealRestriction_single,ite_eq_right hp]
      simp only [idealEulerFactor,Finset.prod_insert hp]
      ring

end CubicFirstMoment

end

end OAI
