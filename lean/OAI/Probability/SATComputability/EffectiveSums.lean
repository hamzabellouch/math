import OAI.Probability.SATComputability.EffectiveLog

namespace OAI

namespace PeriodicLattice.CertifiedReal

open Encodable Filter
open scoped Topology BigOperators
local instance effectiveSumsRatPrimcodable : Primcodable ℚ := RecursiveArithmetic.ratPrimcodable

variable {A : Type*} [Primcodable A]

theorem Effective.sum_range {f : A → ℕ → ℝ}
    (hf : Effective (fun p : A × ℕ => f p.1 p.2))
    {m : A → ℕ} (hm : Computable m) :
    Effective (fun a => ∑ i ∈ Finset.range (m a), f a i) := by
  obtain ⟨q, hq, herror⟩ := hf
  apply of_enclosures
    (q := fun an => ∑ i ∈ Finset.range (m an.1), q ((an.1,i),an.2))
    (e := fun an => (m an.1 : ℚ)*qerror an.2)
  · apply computable_sum (hm.comp Computable.fst)
    unfold Computable₂
    fun_prop
  · fun_prop
  · intro a n
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, cast_qerror]
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i ∈ Finset.range (m a), |f a i - (q ((a,i),n) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range (m a), error n :=
        Finset.sum_le_sum (fun i _ => herror (a,i) n)
      _ = _ := by simp
  · intro a
    simpa only [Rat.cast_mul, Rat.cast_natCast, cast_qerror, mul_zero] using
      error_tendsto.const_mul (m a : ℝ)

theorem effective_limit {f : A → ℝ} {g : A → ℕ → ℝ}
    (hg : Effective (fun p : A × ℕ => g p.1 p.2))
    (tail : A × ℕ → ℚ) (htail : Computable tail)
    (hbound : ∀ a n, |f a - g a n| ≤ (tail (a,n) : ℝ))
    (hzero : ∀ a, Tendsto (fun n => (tail (a,n) : ℝ)) atTop (nhds 0)) :
    Effective f := by
  obtain ⟨q, hq, he⟩ := hg
  apply of_enclosures (q := fun an => q ((an.1,an.2),an.2))
    (e := fun an => tail an + qerror an.2)
  · fun_prop
  · fun_prop
  · intro a n
    simp only [Rat.cast_add, cast_qerror]
    exact (abs_sub_le _ _ _).trans (add_le_add (hbound a n) (he (a,n) n))
  · intro a
    simpa only [Rat.cast_add, cast_qerror, add_zero] using (hzero a).add error_tendsto

end PeriodicLattice.CertifiedReal

end OAI
