import OAI.NumberTheory.TotientAsymptotic.PrimeBoxGeometry
import Mathlib.Data.List.Sort

namespace OAI

/-! Exact recovery of an ordered prime tuple from its product. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma prime_coordinates_strictAnti {n : ℕ} {p : Fin n → ℕ}
    (hp : ∀ i,(p i).Prime) (hcoord : StrictAnti (primePrefixCoord p)) : StrictAnti p := by
  intro i j hij
  by_contra! hh
  have hip : (0:ℝ) < p i := by exact_mod_cast (hp i).pos
  have hi1 : (1:ℝ) < p i := by exact_mod_cast (hp i).one_lt
  have hlog := Real.log_le_log hip (show (p i:ℝ) ≤ p j by exact_mod_cast hh)
  have hloglog := Real.log_le_log (Real.log_pos hi1) hlog
  have hstrict := hcoord hij
  change Real.log (Real.log (p j:ℝ)) < Real.log (Real.log (p i:ℝ)) at hstrict
  exact (not_lt_of_ge hloglog) hstrict

lemma ordered_prime_product_injective {n : ℕ} {p q : Fin n → ℕ}
    (hp : ∀ i,(p i).Prime) (hq : ∀ i,(q i).Prime)
    (hpo : StrictAnti p) (hqo : StrictAnti q)
    (he : ∏ i,p i = ∏ i,q i) : p=q := by
  have hpl : ∀ a ∈ List.ofFn p,a.Prime := by
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact hp i
  have hql : ∀ a ∈ List.ofFn q,a.Prime := by
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact hq i
  have hpp := Nat.primeFactorsList_unique (List.prod_ofFn (f:=p)) hpl
  have hqp := Nat.primeFactorsList_unique (List.prod_ofFn (f:=q)) hql
  rw [he] at hpp
  have hperm := hpp.trans hqp.symm
  have hsortedp : (List.ofFn p).Pairwise (fun a b => b ≤ a) :=
    List.pairwise_ofFn.mpr (fun _ _ hij => (hpo hij).le)
  have hsortedq : (List.ofFn q).Pairwise (fun a b => b ≤ a) :=
    List.pairwise_ofFn.mpr (fun _ _ hij => (hqo hij).le)
  exact List.ofFn_inj.mp (List.Perm.eq_of_pairwise
    (fun _ _ _ _ h₁ h₂ => Nat.le_antisymm h₂ h₁) hsortedp hsortedq hperm)

end TotientAsymptotic

end

end OAI
