import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.WeightedMoments
import OAI.Probability.SKBarriers.Gaussian.PolynomialGap
import OAI.Probability.SKBarriers.Replicas.ReplicaCoordinates
import OAI.Probability.SKBarriers.Replicas.PairContinuumPressure

namespace OAI

section

noncomputable section
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def pairMismatchSet (n : ℕ) (β : ℝ) (α : ℝ → ℝ) (e : ℝ) : Finset (ReplicaConfig n 2) := by
  classical
  exact Finset.univ.filter (fun s => 0≤overlap (s 0) (s 1) ∧
    e≤|overlap (s 0) (s 1)-scalarCDFOverlap β α (overlap (s 0) (s 1))|)

theorem pairMismatch_pressure_gap {n : ℕ} (hn : 0<n) (β : ℝ)
    (α : StieltjesFunction ℝ) (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hα1 : α 1=1)
    (hmin : scalarCDFParisi β α=finiteParisiInf β)
    {e : ℝ} (he : 0≤e) {s : ReplicaConfig n 2} (hs : s∈pairMismatchSet n β α e) :
    matrixConstrainedPressure n 2 β (replicaGram s)≤2*finiteParisiInf β-e^2/2 := by
  classical
  obtain ⟨hs0,hse⟩ := (Finset.mem_filter.mp hs).2
  have hq : overlap (s 0) (s 1)∈Icc (0:ℝ) 1 := ⟨hs0,(abs_le.mp (abs_overlap_le_one _ _)).2⟩
  have hfeas := replicaGram_feasible s
  rw [replicaGram_pair_overlap hn] at hfeas ⊢
  have H := pairConstrainedPressure_continuum hn β α hα hα1 hq hfeas
  rw [hmin] at H
  have he2 := pow_le_pow_left₀ he hse 2
  rw [sq_abs] at he2
  nlinarith only [H,he2]

theorem eventual_pairMismatch_polynomial_bound {β A a t ε : ℝ} (hβ : 0<β)
    (hA : 0<A) (ha : 0≤a) (ha48 : a<1/48) (ht : t<1-4*a) (hε : 0<ε)
    (α : StieltjesFunction ℝ) (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hα1 : α 1=1)
    (hmin : scalarCDFParisi β α=finiteParisiInf β) :
    ∀ᶠ n : ℕ in atTop,
      (∫ J,replicaGibbsMass β J (pairMismatchSet n β α (A*(n:ℝ)^(-a))) ∂disorderLaw n)≤
        ε*Real.exp (-(n:ℝ)^t) := by
  have H := eventual_replicaGibbsMass_polynomial_gap (c:=A^2/2) (a:=2*a) (t:=t) hβ
    2 1 (by decide) (by positivity) (by positivity) (by linarith) (by linarith) hε
  filter_upwards [H,eventually_gt_atTop (0:ℕ)] with n hn hn0
  apply hn (Fin (n+1)) (by simp) pairReplicaCode (fun s t h => pairReplicaCode_gram hn0 h)
  intro s hs
  have HP := pairMismatch_pressure_gap hn0 β α hα hα1 hmin (by positivity : 0≤A*(n:ℝ)^(-a)) hs
  have hp : (0:ℝ)<n := by exact_mod_cast hn0
  have he : (A*(n:ℝ)^(-a))^2/2=A^2/2*(n:ℝ)^(-(2*a)) := by
    rw [mul_pow,← Real.rpow_natCast ((n:ℝ)^(-a)) 2,← Real.rpow_mul hp.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (-a)*2= -(2*a) by ring]
    ring
  simpa only [Nat.cast_ofNat,he] using HP

end SK.Analytic

end
end

end OAI
