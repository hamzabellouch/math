import OAI.Probability.BenjaminiSchramm.GhostPivotalProbability
import OAI.Probability.BenjaminiSchramm.GhostMomentBound
import OAI.Probability.BenjaminiSchramm.GhostTiltedTransport

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] [Countable E] in
lemma criticalModel_finiteGhostConnection (x : V) (m : Set V) :
    finiteGhostConnection G x id m =
      {ω | ∃ y ∈ m, ((criticalModel G).openGraph ω).Reachable x y} := by
  ext ω
  simp only [finiteGhostConnection, Set.mem_ofPred_eq, criticalModel_openGraph]
  exact exists_congr fun y => and_congr_right fun _ => conn_iff_reachable G ω x y

omit [Countable V] [Countable E] in
lemma ghostAvoid_finite_sum (h : ℝ) (w : V → ℝ≥0) (S : Finset V) :
    ghostAvoid h (∑ y ∈ S, (w y : ℝ≥0∞)) =
      ENNReal.ofReal (Real.exp (-h * ∑ y ∈ S, (w y : ℝ))) := by
  have hfin : (∑ y ∈ S, (w y : ℝ≥0∞)) ≠ ⊤ :=
    (ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.coe_lt_top).ne
  rw [ghostAvoid,ite_eq_right hfin,ENNReal.toReal_sum (fun _ _ => ENNReal.coe_ne_top)]
  simp only [ENNReal.coe_toReal]

omit [Countable V] [Countable E] in
lemma exp_avoidance_sq (h : ℝ) (w : V → ℝ≥0) (S : Finset V) :
    ENNReal.ofReal (Real.exp (-h * ∑ y ∈ S, (w y : ℝ))) ^ 2 =
      ghostAvoid (2*h) (∑ y ∈ S, (w y : ℝ≥0∞)) := by
  rw [ghostAvoid_finite_sum, pow_two, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add]
  congr 2
  ring

theorem averaged_ghostBridge_quarter_weight_le
    (hc : (criticalModel G).fullGraph.Connected) (hl : LocallyFinite G)
    (p : unitInterval) (hp : (p : ℝ) < 1)
    (hfin : ∀ v, ∀ᵐ ω ∂law p, (cluster G ω v).Finite)
    (K : ℝ) (hbound : ∀ x h, 0 ≤ h →
      (criticalModel G).quarterGhostMagnetization p x h ≤ K * h ^ (3/4 : ℝ))
    (S : Finset V) (x : V) (e : E) (u v : V) (hends : G e = s(u,v))
    (hu : u ∈ S) (hv : v ∉ S) (h : ℝ≥0) :
    (∫⁻ m, ∫⁻ n, law p {ω | GhostBridgePivotal G ω m n x e u v ∧
      cluster G (ω \ {e}) x = (S : Set V)}
      ∂ghostFieldLaw h ((criticalModel G).quarterGhostWeight x)
      ∂ghostFieldLaw h ((criticalModel G).quarterGhostWeight x)) ≤
      (ENNReal.ofReal (p : ℝ) / ENNReal.ofReal (1 - (p : ℝ))) *
        law p {ω | cluster G ω x = (S : Set V)} *
        ghostAvoid (2*(h : ℝ)) (∑ y ∈ S, ((criticalModel G).quarterGhostWeight x y : ℝ≥0∞)) *
        (ENNReal.ofReal (K^2 * (h : ℝ)^(3/2 : ℝ)) *
          (criticalModel G).stabilizerWeight x v ^ (3/8 : ℝ)) := by
  let H := criticalModel G
  have hf : ∀ᵐ ω ∂H.law p, (H.cluster ω v).Finite := by
    rw [show H.law p = (law p : Measure (Set E)) from rfl]
    simpa only [H,criticalModel_cluster] using hfin v
  have haverage : (∫⁻ m, law p (finiteGhostConnection G v id m)
      ∂ghostFieldLaw h (H.quarterGhostWeight x)) =
        ENNReal.ofReal (H.quarterGhostMagnetization p v (h * H.quarterGhostWeight x v)) := by
    simp_rw [criticalModel_finiteGhostConnection G]
    exact H.quarterGhostConnection_change_base hc hl p x v h hf
  have hsquare : ENNReal.ofReal (H.quarterGhostMagnetization p v
        (h * H.quarterGhostWeight x v)) ^ 2 ≤
      ENNReal.ofReal (K^2 * (h : ℝ)^(3/2 : ℝ)) * H.stabilizerWeight x v ^ (3/8 : ℝ) := by
    have hnonneg : 0 ≤ H.quarterGhostMagnetization p v (h * H.quarterGhostWeight x v) :=
      integral_nonneg fun _ => ghostKernel_nonneg (by positivity) ENNReal.toReal_nonneg
    rw [← ENNReal.ofReal_pow hnonneg]
    have hb := ENNReal.ofReal_le_ofReal (H.rebased_quarterGhost_square_bound hbound x v h.2)
    rw [ENNReal.ofReal_mul (mul_nonneg (sq_nonneg K) (Real.rpow_nonneg h.2 _)),
      ENNReal.ofReal_toReal
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (H.stabilizerWeight_ne_top x v))] at hb
    exact hb
  have hb := averaged_ghostBridge_fixed_cluster_le G p hp S x e u v hends hu hv h
    (H.quarterGhostWeight x)
  rw [exp_avoidance_sq, haverage] at hb
  exact hb.trans (mul_le_mul' le_rfl hsquare)

end Percolation.BenjaminiSchramm

end

end OAI
