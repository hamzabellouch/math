import OAI.Analysis.MutuallyUnbiased.Matrix.Square
import OAI.Analysis.MutuallyUnbiased.Moments.Moments

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

def qCross : Charge := ![2, 0, 0, -2, 0, 0]
def qSame : Charge := ![2, -2, 0, 0, 0, 0]
def pairW : Charge := ![-3, -2, 0, 1, 2, 2]
def pairA : Fin 4 → Charge :=
  ![![-1, -1, 0, 0, 1, 1], ![-2, 0, 0, 0, 1, 1],
    ![-1, -1, 0, 1, 0, 1], ![-1, -1, 0, 1, 1, 0]]
def pairCoefficient : Fin 4 → ℂ := ![2, 1, 1, 1]

def pairL (H : CMatrix) : ℂ :=
  -g H pairW + ∑ j, pairCoefficient j * g H (pairA j) * g H (pairW - pairA j)

def PairCertificateIdentity (H : CMatrix) (q : Charge) : Prop :=
  3 * pairAverage H (fun K => Complex.normSq (pairL K)) +
    pairAverage H (fun K => Complex.normSq (g K alpha * g K q)) = 0

theorem pair_product_zero_of_certificate {H : CMatrix} {q : Charge}
    (h : PairCertificateIdentity H q) (π : Equiv.Perm Coord) :
    g (fun i j => H (π i) j) alpha * g (fun i j => H (π i) j) q = 0 := by
  have hL := pairAverage_nonneg H (fun K => Complex.normSq (pairL K))
    (fun K => Complex.normSq_nonneg _)
  have hg := pairAverage_nonneg H (fun K => Complex.normSq (g K alpha * g K q))
    (fun K => Complex.normSq_nonneg _)
  have hz : pairAverage H (fun K => Complex.normSq (g K alpha * g K q)) = 0 := by
    unfold PairCertificateIdentity at h
    linarith
  have ht := (pairAverage_zero_terms H (fun K => Complex.normSq (g K alpha * g K q))
    (fun K => Complex.normSq_nonneg _) hz π).1
  exact Complex.normSq_eq_zero.mp ht

end MUB6

end

end OAI
