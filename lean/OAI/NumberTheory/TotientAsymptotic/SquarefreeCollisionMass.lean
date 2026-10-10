import OAI.NumberTheory.TotientAsymptotic.FiniteSieveMass
import Mathlib.Data.Nat.Squarefree

namespace OAI

/-! A finite Euler-product bound for the squarefree interval factors in Ford's sieve. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma squarefree_primeFactors_card {n : ℕ} (hn : Squarefree n) :
    n.primeFactors.card=n.primeFactorsList.length :=
  List.toFinset_card_of_nodup hn.nodup_primeFactorsList

lemma squarefree_reciprocal_moment (S Q : Finset ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hQ : ∀ n ∈ Q,Squarefree n ∧ n.primeFactors ⊆ S) :
    (∑ n ∈ Q,c^n.primeFactors.card/(n:ℝ)) ≤
      Real.exp (c*(∑ p ∈ S,(p:ℝ)⁻¹)) := by
  classical
  have hi : ∀ n ∈ Q,∀ m ∈ Q,n.primeFactors=m.primeFactors → n=m := by
    intro n hn m hm he
    rw [← Nat.prod_primeFactors_of_squarefree (hQ n hn).1,
      ← Nat.prod_primeFactors_of_squarefree (hQ m hm).1,he]
  have hsub : Q.image Nat.primeFactors ⊆ S.powerset := by
    intro T hT
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_powerset.mpr (hQ n hn).2
  have he (n : ℕ) (hn : n ∈ Q) : c^n.primeFactors.card/(n:ℝ)=
      ∏ p ∈ n.primeFactors,c/(p:ℝ) := by
    rw [Finset.prod_div_distrib,Finset.prod_const,← Nat.cast_prod,
      Nat.prod_primeFactors_of_squarefree (hQ n hn).1]
  calc
    _ = ∑ n ∈ Q,∏ p ∈ n.primeFactors,c/(p:ℝ) := Finset.sum_congr rfl he
    _ = ∑ T ∈ Q.image Nat.primeFactors,∏ p ∈ T,c/(p:ℝ) :=
      by rw [Finset.sum_image hi]
    _ ≤ ∑ T ∈ S.powerset,∏ p ∈ T,c/(p:ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun T _ _ =>
        Finset.prod_nonneg (fun p _ => div_nonneg hc (Nat.cast_nonneg p)))
    _ = ∏ p ∈ S,(1+c/(p:ℝ)) := by rw [← Finset.prod_one_add]
    _ ≤ ∏ p ∈ S,Real.exp (c/(p:ℝ)) := by
      apply Finset.prod_le_prod₀
      · intro p _
        positivity
      · intro p _
        have hh := Real.add_one_le_exp (c/(p:ℝ))
        linarith
    _ = _ := by
      rw [← Real.exp_sum,Finset.mul_sum]
      congr 1

/-- The elementary tilt giving Ford's `(e*i)^I` interval bound. -/
lemma squarefree_collision_mass (S Q : Finset ℕ) {c I H : ℝ} (hc : 1 ≤ c)
    (hQ : ∀ n ∈ Q,Squarefree n ∧ n.primeFactors ⊆ S ∧
      (n.primeFactors.card:ℝ) ≤ I)
    (hH : (∑ p ∈ S,(p:ℝ)⁻¹) ≤ H) (hIH : c*H ≤ I) :
    (∑ n ∈ Q,c^(2*n.primeFactors.card)/(n:ℝ)) ≤
      Real.exp (I*(Real.log c+1)) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hmoment := squarefree_reciprocal_moment S Q hc0.le
    (fun n hn => ⟨(hQ n hn).1,(hQ n hn).2.1⟩)
  have ht : (∑ n ∈ Q,c^(2*n.primeFactors.card)/(n:ℝ)) ≤
      c^I*(∑ n ∈ Q,c^n.primeFactors.card/(n:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hh := Real.rpow_le_rpow_of_exponent_le hc (hQ n hn).2.2
    rw [Real.rpow_natCast] at hh
    have hm := mul_le_mul_of_nonneg_right hh (show 0 ≤ c^n.primeFactors.card/(n:ℝ) by positivity)
    convert hm using 1
    rw [two_mul,pow_add]
    ring
  calc
    _ ≤ c^I*(∑ n ∈ Q,c^n.primeFactors.card/(n:ℝ)) := ht
    _ ≤ c^I*Real.exp (c*(∑ p ∈ S,(p:ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_left hmoment (Real.rpow_nonneg hc0.le I)
    _ ≤ c^I*Real.exp I := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hc0.le I)
      exact Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left hH hc0.le).trans hIH)
    _ = _ := by
      rw [Real.rpow_def_of_pos hc0,← Real.exp_add]
      congr 1
      ring

end TotientAsymptotic

end

end OAI
