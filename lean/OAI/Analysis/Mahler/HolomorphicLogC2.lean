import OAI.Analysis.Mahler.LogNormSquare
import OAI.Analysis.Mahler.HolomorphicRegularity
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

open Set Filter Metric
open scoped Topology
namespace SymmetricMahler
noncomputable section
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [Fintype J]

theorem uniform_C2_log_sumNormSq_of_holomorphic [FiniteDimensional ℂ E] [FiniteDimensional ℝ E]
    {I : Type*} {l : Filter I} {K U : Set E} {f : I → J → E → ℂ} {g : J → E → ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hg : ∀ j, DifferentiableOn ℂ (g j) U)
    (hf : ∀ᶠ i in l, ∀ j, DifferentiableOn ℂ (f i j) U)
    (hp : ∀ x ∈ K, 0 < ∑ j, Complex.normSq (g j x))
    (h0 : ∀ j, TendstoUniformlyOn (fun i => f i j) (g j) l K)
    (h1 : ∀ j, TendstoUniformlyOn (fun i => fderiv ℂ (f i j)) (fderiv ℂ (g j)) l K)
    (h2 : ∀ j, TendstoUniformlyOn (fun i => fderiv ℂ (fderiv ℂ (f i j)))
      (fderiv ℂ (fderiv ℂ (g j))) l K) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ i in l, ∀ x ∈ K, c ≤ ∑ j, Complex.normSq (f i j x)) ∧
    TendstoUniformlyOn (fun i x => Real.log (∑ j, Complex.normSq (f i j x)))
      (fun x => Real.log (∑ j, Complex.normSq (g j x))) l K ∧
    TendstoUniformlyOn
      (fun i => fderiv ℝ (fun x => Real.log (∑ j, Complex.normSq (f i j x))))
      (fderiv ℝ (fun x => Real.log (∑ j, Complex.normSq (g j x)))) l K ∧
    TendstoUniformlyOn
      (fun i => fderiv ℝ (fderiv ℝ (fun x => Real.log (∑ j, Complex.normSq (f i j x)))))
      (fderiv ℝ (fderiv ℝ (fun x => Real.log (∑ j, Complex.normSq (g j x))))) l K := by
  apply uniform_C2_log_sumNormSq hK hU hKU
    (fun j => Mahler.contDiffOn_nat_of_differentiableOn_open hU 2 (hg j))
    (hf.mono (fun i hi j => Mahler.contDiffOn_nat_of_differentiableOn_open hU 2 (hi j)))
    hp h0 h1 h2

/-- A fixed closed annulus containing the unit sphere in its interior. -/
def logCompactAnnulus (n : ℕ) : Set (EuclideanSpace ℂ (Fin n)) :=
  closedBall 0 2 \ ball 0 (1/2)

lemma isCompact_logCompactAnnulus (n : ℕ) : IsCompact (logCompactAnnulus n) :=
  (isCompact_closedBall _ _).diff isOpen_ball

lemma logCompactAnnulus_subset_ball (n : ℕ) :
    logCompactAnnulus n ⊆ ball 0 4 :=
  sdiff_subset.trans (closedBall_subset_ball (by norm_num : (2 : ℝ) < 4))

lemma logCompactAnnulus_ne_zero {n : ℕ} {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ logCompactAnnulus n) : z ≠ 0 := by
  intro he
  exact hz.2 (he ▸ mem_ball_self (by norm_num : (0 : ℝ) < 1/2))

end
end SymmetricMahler

end OAI
