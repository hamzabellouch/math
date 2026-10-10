import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSamplerExecution

namespace OAI

/-! # Retaining the accepted scalar draws as fixed-size arrays

The prime-width arguments are stored integers. These routines copy only
accepted values and retain the bounded rejection sampler's actual work.
-/

noncomputable section
namespace LowSpaceSubsetSum.ScalarSamplerArrays

open scoped BigOperators

def factors (p : (ℕ × ℕ) × ℕ) : Vector ℕ 3 := #v[p.1.1, p.1.2, p.2]

def nested (n a b c : ℕ) (s : (triplePrimeCoupling n a b c).Seed) :
    Option (Vector ℕ 3) × ℕ :=
  let out := (SamplerExecution.triplePrime n a b c).run s
  (out.value.map (fun p => factors p.val), out.reads + out.tests + 7)

theorem nested_value (n a b c : ℕ) (s : (triplePrimeCoupling n a b c).Seed) :
    (nested n a b c s).1 =
      ((triplePrimeCoupling n a b c).bounded s).map (fun p => factors p.val) := by
  exact congrArg (Option.map (fun p => factors p.val))
    ((SamplerExecution.triplePrime n a b c).value_eq s)

theorem nested_work {n a b c : ℕ} (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n)
    (s : (triplePrimeCoupling n a b c).Seed) :
    (nested n a b c s).2 ≤ 3 * n ^ 3 + 3 * SamplerExecution.primeTestBudget n + 7 := by
  have h := SamplerExecution.triplePrime_bounded ha hb hc s
  change _ + _ + 7 ≤ _
  omega

def moduli (p : Vector ℕ 3) : Vector ℕ 3 × ℕ :=
  (#v[p[0] * p[1] * p[2], p[0] * p[1], p[0]], 3)

theorem moduli_value {n : ℕ} (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (p : R.PrimeSpace z) (j : Fin 3) :
    (moduli (factors p.val)).1[j.val] = prefixModulus p.val j := by
  fin_cases j <;> rfl

def extra {ell : ℕ} (hell : 4 ≤ ell) (n : ℕ) (s : (primeCoupling hell n).Seed) :
    Option ℕ × ℕ :=
  let out := (SamplerExecution.prime hell n).run s
  (out.value.map Subtype.val, out.reads + out.tests + 1)

theorem extra_value {ell : ℕ} (hell : 4 ≤ ell) (n : ℕ) (s : (primeCoupling hell n).Seed) :
    (extra hell n s).1 = ((primeCoupling hell n).bounded s).map Subtype.val := by
  exact congrArg (Option.map Subtype.val) ((SamplerExecution.prime hell n).value_eq s)

theorem extra_work {n ell : ℕ} (hell : 4 ≤ ell) (he : ell ≤ n)
    (s : (primeCoupling hell n).Seed) :
    (extra hell n s).2 ≤ n ^ 3 + SamplerExecution.primeTestBudget n + 1 := by
  have h := SamplerExecution.prime_bounded hell n s
  have ht : n ^ 3 * 2 ^ ((ell + 1) / 2) ≤ SamplerExecution.primeTestBudget n :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
  change _ + _ + 1 ≤ _
  omega

def residueCoupling (n p0 pL pR : ℕ) [NeZero p0] [NeZero pL] [NeZero pR] :=
  (finCoupling n p0).prod ((finCoupling n pL).prod (finCoupling n pR))

def residueExecution (n p0 pL pR : ℕ) [NeZero p0] [NeZero pL] [NeZero pR] :
    SamplerExecution.Execution (residueCoupling n p0 pL pR) :=
  SamplerExecution.prod (SamplerExecution.fin n p0)
    (SamplerExecution.prod (SamplerExecution.fin n pL) (SamplerExecution.fin n pR))

def residueValues {p0 pL pR : ℕ} (r : Fin p0 × (Fin pL × Fin pR)) : Vector ℕ 3 :=
  #v[r.1.val, r.2.1.val, r.2.2.val]

def residues (n p0 pL pR : ℕ) [NeZero p0] [NeZero pL] [NeZero pR]
    (s : (residueCoupling n p0 pL pR).Seed) : Option (Vector ℕ 3) × ℕ :=
  let out := (residueExecution n p0 pL pR).run s
  (out.value.map residueValues, out.reads + out.tests + 7)

theorem residues_value (n p0 pL pR : ℕ) [NeZero p0] [NeZero pL] [NeZero pR]
    (s : (residueCoupling n p0 pL pR).Seed) :
    (residues n p0 pL pR s).1 = ((residueCoupling n p0 pL pR).bounded s).map residueValues := by
  exact congrArg (Option.map residueValues) ((residueExecution n p0 pL pR).value_eq s)

theorem residues_work (n p0 pL pR : ℕ) [NeZero p0] [NeZero pL] [NeZero pR]
    (s : (residueCoupling n p0 pL pR).Seed) : (residues n p0 pL pR s).2 ≤ 3 * n ^ 3 + 7 := by
  have h := SamplerExecution.prod_bounded _ _ (SamplerExecution.fin_bounded n p0)
    (SamplerExecution.prod_bounded _ _ (SamplerExecution.fin_bounded n pL)
      (SamplerExecution.fin_bounded n pR)) s
  obtain ⟨hr, ht⟩ := h
  change ((residueExecution n p0 pL pR).run s).reads ≤ n ^ 3 + (n ^ 3 + n ^ 3) at hr
  change ((residueExecution n p0 pL pR).run s).tests ≤ 0 + (0 + 0) at ht
  change _ + _ + 7 ≤ _
  omega

end LowSpaceSubsetSum.ScalarSamplerArrays

end

end OAI
