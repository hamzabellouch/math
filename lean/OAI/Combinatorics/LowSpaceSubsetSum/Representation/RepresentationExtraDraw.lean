import OAI.Combinatorics.LowSpaceSubsetSum.Counting.ScalarSamplerArrays

namespace OAI

/-! # The extra prime drawn at the stored fourth width -/

noncomputable section
namespace LowSpaceSubsetSum.RepresentationExtraDraw

variable {n : ℕ}

def transport {ell ell' : ℕ} {h : 4 ≤ ell} {h' : 4 ≤ ell'}
    (he : ell = ell') (s : (primeCoupling h' n).Seed) : (primeCoupling h n).Seed := by
  subst ell'
  exact s

def draw (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) (hn : 100 ≤ n)
    (ell : ℕ) (he : ell = R.extraPrimeParameter z) (s : (R.extraPrimeCoupling z hn).Seed) :
    Option ℕ × ℕ :=
  ScalarSamplerArrays.extra (he.symm ▸ (R.extraPrimeParameter_range z hn).1) n
    (transport he s)

theorem value (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) (hn : 100 ≤ n)
    (ell : ℕ) (he : ell = R.extraPrimeParameter z) (s : (R.extraPrimeCoupling z hn).Seed) :
    (draw R z hn ell he s).1 = ((R.extraPrimeCoupling z hn).bounded s).map Subtype.val := by
  subst ell
  exact ScalarSamplerArrays.extra_value _ _ s

theorem work (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) (hn : 100 ≤ n)
    (ell : ℕ) (he : ell = R.extraPrimeParameter z) (s : (R.extraPrimeCoupling z hn).Seed) :
    (draw R z hn ell he s).2 ≤ n ^ 3 + SamplerExecution.primeTestBudget n + 1 := by
  subst ell
  exact ScalarSamplerArrays.extra_work _ (R.extraPrimeParameter_range z hn).2 s

end LowSpaceSubsetSum.RepresentationExtraDraw

end

end OAI
