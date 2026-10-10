import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrimeSystem

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.FiniteIntegration OrdinaryCorrelations.SignedTrace
open Finset Classical
variable {S : PrimeSystem} {h ℓ : ℕ}

def vertexWeight (S : PrimeSystem) (r : S.Residues) (b : ℤ) : ℝ :=
  ∏ p : S.Index, (S.beta p)⁻¹ ^
    (if r p + (b : ZMod (p : ℕ)) = 0 then (1 : ℕ) else 0)

lemma vertexWeight_inv (S : PrimeSystem) (r : S.Residues) (b : ℤ) :
    (S.vertexWeight r b)⁻¹ = ∏ p : S.Index, S.beta p ^
      (if r p + (b : ZMod (p : ℕ)) = 0 then (1 : ℕ) else 0) := by
  simp only [vertexWeight, prod_inv_distrib, inv_pow, inv_inv]

def edgeWeight (S : PrimeSystem) (w : ClosedLine h ℓ) {T : ℝ}
    (cut : S.Cutoffs T) (r : S.Residues) (i : Fin ℓ) : ℝ :=
  (cut.value (w.label i) (S.shiftCore (S.restrictCore r) (w.offset i.castSucc)) *
    cut.value (w.label i) (S.shiftCore (S.restrictCore r) (w.offset i.succ))) *
      ∏ p, S.occurrenceFactor w p i (r p)

def chronologicalKernel (S : PrimeSystem) (w : ClosedLine h ℓ) {T : ℝ}
    (cut : S.Cutoffs T) (r : S.Residues) : ℝ :=
  ∏ i : Fin ℓ, S.edgeWeight w cut r i / S.vertexWeight r (w.offset i.castSucc)

lemma chronologicalKernel_eq (S : PrimeSystem) (w : ClosedLine h ℓ) {T : ℝ}
    (cut : S.Cutoffs T) (r : S.Residues) :
    S.chronologicalKernel w cut r = S.kernel w cut r := by
  simp only [chronologicalKernel, edgeWeight, div_eq_mul_inv, vertexWeight_inv,
    kernel, cutoffProduct, primeFactor]
  trans (∏ i : Fin ℓ,
    (cut.value (w.label i) (S.shiftCore (S.restrictCore r) (w.offset i.castSucc)) *
      cut.value (w.label i) (S.shiftCore (S.restrictCore r) (w.offset i.succ))) *
      (∏ p : S.Index, S.occurrenceFactor w p i (r p) *
        S.beta p ^ (if r p + (w.offset i.castSucc : ZMod (p : ℕ)) = 0 then 1 else 0)))
  · apply prod_congr rfl
    intro i _
    rw [prod_mul_distrib]
    ring
  · rw [prod_mul_distrib, prod_comm]

lemma center_primeFactor_eq (S : PrimeSystem) (w : ClosedLine h ℓ) (p : S.Index)
    (hp : ¬S.IsCore p) (r : ZMod (p : ℕ)) :
    S.primeFactor w p r = centerPrimeFactor w.departures w.label r := by
  simp only [primeFactor, occurrenceFactor, hp, ite_false, beta, amplitude,
    add_eq_zero_iff_eq_neg, centerPrimeFactor, activeResidue, ClosedLine.departures,
    activity, betaZ]
  rfl

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
