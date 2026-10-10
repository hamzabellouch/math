import OAI.Probability.BenjaminiSchramm.GhostPivotalSum

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def averagedQuarterBridge (p : unitInterval) (x : V) (h : ℝ≥0)
    (e : E) (u v : V) (S : Finset V) : ℝ≥0∞ :=
  ∫⁻ m, ∫⁻ n, law p {ω | GhostBridgePivotal G ω m n x e u v ∧
    cluster G (ω \ {e}) x = (S : Set V)}
    ∂ghostFieldLaw h ((criticalModel G).quarterGhostWeight x)
    ∂ghostFieldLaw h ((criticalModel G).quarterGhostWeight x)

theorem averagedQuarterBridge_oriented_le
    (hc : (criticalModel G).fullGraph.Connected) (hl : LocallyFinite G)
    (p : unitInterval) (hp : (p : ℝ) < 1)
    (hfin : ∀ v, ∀ᵐ ω ∂law p, (cluster G ω v).Finite)
    (K : ℝ) (hbound : ∀ x h, 0 ≤ h →
      (criticalModel G).quarterGhostMagnetization p x h ≤ K*h^(3/4 : ℝ))
    (S : Finset V) (x : V) (e : E) (u v : V) (h : ℝ≥0) :
    averagedQuarterBridge G p x h e u v S ≤
      ((ENNReal.ofReal (p : ℝ)/ENNReal.ofReal (1-(p : ℝ))) *
        law p {ω | cluster G ω x = (S : Set V)} *
        ghostAvoid (2*(h : ℝ)) (∑ y ∈ S, ((criticalModel G).quarterGhostWeight x y : ℝ≥0∞)) *
        ENNReal.ofReal (K^2*(h : ℝ)^(3/2 : ℝ))) *
      (if G e = s(u,v) ∧ u ∈ (S : Set V) ∧ v ∉ (S : Set V) then
        (criticalModel G).stabilizerWeight x v ^ (3/8 : ℝ) else 0) := by
  by_cases hor : G e = s(u,v) ∧ u ∈ (S : Set V) ∧ v ∉ (S : Set V)
  · rw [ite_eq_left hor]
    exact (averaged_ghostBridge_quarter_weight_le G hc hl p hp hfin K hbound S x e u v
      hor.1 hor.2.1 hor.2.2 h).trans_eq (by simp only [mul_assoc])
  · rw [ite_eq_right hor,mul_zero]
    have hempty (m n : Set V) : {ω | GhostBridgePivotal G ω m n x e u v ∧
        cluster G (ω \ {e}) x = (S : Set V)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨hpiv,hcl⟩
      apply hor
      refine ⟨hpiv.2.1,?_,?_⟩
      · have hu : u ∈ cluster G (ω \ {e}) x := hpiv.2.2.1
        rw [hcl] at hu
        exact hu
      · intro hv
        have hv' : v ∈ cluster G (ω \ {e}) x := by rw [hcl]; exact hv
        exact hpiv.2.2.2.1 hv'
    simp only [averagedQuarterBridge,hempty,measure_empty,lintegral_zero,le_refl]

theorem averagedQuarterBridge_cluster_sum_le
    (hc : (criticalModel G).fullGraph.Connected) (hl : LocallyFinite G)
    (p : unitInterval) (hp : (p : ℝ) < 1)
    (hfin : ∀ v, ∀ᵐ ω ∂law p, (cluster G ω v).Finite)
    (K : ℝ) (hbound : ∀ x h, 0 ≤ h →
      (criticalModel G).quarterGhostMagnetization p x h ≤ K*h^(3/4 : ℝ))
    (S : Finset V) (x : V) (h : ℝ≥0) :
    (∑' e, ∑' u, ∑' v, averagedQuarterBridge G p x h e u v S) ≤
      ((ENNReal.ofReal (p : ℝ)/ENNReal.ofReal (1-(p : ℝ))) *
        law p {ω | cluster G ω x = (S : Set V)} *
        ghostAvoid (2*(h : ℝ)) (∑ y ∈ S, ((criticalModel G).quarterGhostWeight x y : ℝ≥0∞)) *
        ENNReal.ofReal (K^2*(h : ℝ)^(3/2 : ℝ))) *
      (2 * ∑' e, if e ∈ (criticalModel G).incidentEdges (S : Set V) then
        (criticalModel G).ghostBondWeight x e else 0) := by
  let C := (ENNReal.ofReal (p : ℝ)/ENNReal.ofReal (1-(p : ℝ))) *
    law p {ω | cluster G ω x = (S : Set V)} *
    ghostAvoid (2*(h : ℝ)) (∑ y ∈ S, ((criticalModel G).quarterGhostWeight x y : ℝ≥0∞)) *
    ENNReal.ofReal (K^2*(h : ℝ)^(3/2 : ℝ))
  calc
    _ ≤ ∑' e, ∑' u, ∑' v, C * (if G e = s(u,v) ∧ u ∈ (S : Set V) ∧ v ∉ (S : Set V) then
        (criticalModel G).stabilizerWeight x v ^ (3/8 : ℝ) else 0) := by
      apply ENNReal.tsum_le_tsum
      intro e
      apply ENNReal.tsum_le_tsum
      intro u
      exact ENNReal.tsum_le_tsum fun v =>
        averagedQuarterBridge_oriented_le G hc hl p hp hfin K hbound S x e u v h
    _ = C * ∑' e, ∑' u, ∑' v, if G e = s(u,v) ∧ u ∈ (S : Set V) ∧ v ∉ (S : Set V) then
        (criticalModel G).stabilizerWeight x v ^ (3/8 : ℝ) else 0 := by
      simp_rw [ENNReal.tsum_mul_left]
    _ ≤ C * ∑' e, if e ∈ (criticalModel G).incidentEdges (S : Set V) then
        2*(criticalModel G).ghostBondWeight x e else 0 := by
      apply mul_le_mul' le_rfl
      apply ENNReal.tsum_le_tsum
      intro e
      have he := oriented_pivotal_weight_le G (S : Set V) e
        (fun v => (criticalModel G).stabilizerWeight x v ^ (3/8 : ℝ))
      convert he using 1
      · apply tsum_congr
        intro u
        apply tsum_congr
        intro v
        by_cases hor : G e = s(u,v) ∧ u ∈ (S : Set V) ∧ v ∉ (S : Set V)
        · simp only [ite_eq_left hor]
        · simp only [ite_eq_right hor]
      · rfl
    _ = _ := by
      congr 1
      rw [←ENNReal.tsum_mul_left]
      apply tsum_congr
      intro e
      split_ifs <;> simp

theorem averagedQuarterBridge_sum_le_boundary
    (hc : (criticalModel G).fullGraph.Connected) (hl : LocallyFinite G)
    (p : unitInterval) (hp : (p : ℝ) < 1)
    (hfin : ∀ v, ∀ᵐ ω ∂law p, (cluster G ω v).Finite)
    (K : ℝ) (hbound : ∀ x h, 0 ≤ h →
      (criticalModel G).quarterGhostMagnetization p x h ≤ K*h^(3/4 : ℝ))
    (x : V) (h : ℝ≥0) :
    (∑' e, ∑' u, ∑' v, ∑' S, averagedQuarterBridge G p x h e u v S) ≤
      (2*(ENNReal.ofReal (p : ℝ)/ENNReal.ofReal (1-(p : ℝ)))*
        ENNReal.ofReal (K^2*(h : ℝ)^(3/2 : ℝ))) *
      ∫⁻ ω, ghostAvoid (2*(h : ℝ)) ((criticalModel G).quarterTiltedMass ω x) *
        (∑' e, if e ∈ (criticalModel G).incidentEdges (cluster G ω x) then
          (criticalModel G).ghostBondWeight x e else 0) ∂law p := by
  let H := criticalModel G
  let R := ENNReal.ofReal (p : ℝ)/ENNReal.ofReal (1-(p : ℝ))
  let Q := ENNReal.ofReal (K^2*(h : ℝ)^(3/2 : ℝ))
  let F := fun S : Set V => ghostAvoid (2*(h : ℝ))
    (∑' y, if y ∈ S then (H.quarterGhostWeight x y : ℝ≥0∞) else 0) *
      (∑' e, if e ∈ H.incidentEdges S then H.ghostBondWeight x e else 0)
  have hF (S : Finset V) : F (S : Set V) =
      ghostAvoid (2*(h : ℝ)) (∑ y ∈ S, (H.quarterGhostWeight x y : ℝ≥0∞)) *
        (∑' e, if e ∈ H.incidentEdges (S : Set V) then H.ghostBondWeight x e else 0) := by
    dsimp only [F]
    apply congrArg (fun m => ghostAvoid (2*(h : ℝ)) m *
      (∑' e, if e ∈ H.incidentEdges (S : Set V) then H.ghostBondWeight x e else 0))
    calc
      _ = ∑' y, if y ∈ S then (H.quarterGhostWeight x y : ℝ≥0∞) else 0 := by
        apply tsum_congr
        intro y
        by_cases hy : y ∈ S
        · simp only [Finset.mem_coe,ite_eq_left hy]
        · simp only [Finset.mem_coe,ite_eq_right hy]
      _ = ∑ y ∈ S, (H.quarterGhostWeight x y : ℝ≥0∞) := by
        rw [tsum_eq_sum (s := S) (fun y hy => ite_eq_right hy)]
        apply Finset.sum_congr rfl
        intro y hy
        exact ite_eq_left hy
  have hI : (∫⁻ ω, F (cluster G ω x) ∂law p) =
      ∫⁻ ω, ghostAvoid (2*(h : ℝ)) (H.quarterTiltedMass ω x) *
        (∑' e, if e ∈ H.incidentEdges (cluster G ω x) then H.ghostBondWeight x e else 0) ∂law p := by
    apply lintegral_congr
    intro ω
    dsimp only [F]
    congr 2
    unfold CriticalPercolation.BondGraph.quarterTiltedMass
    apply tsum_congr
    intro y
    rw [H.coe_quarterGhostWeight]
    congr 1
    rw [show H.openGraph ω = openSimpleGraph G ω from criticalModel_openGraph G ω]
    exact propext (conn_iff_reachable G ω x y)
  calc
    _ = ∑' e, ∑' u, ∑' S, ∑' v, averagedQuarterBridge G p x h e u v S :=
      tsum_congr fun e => tsum_congr fun u => ENNReal.tsum_comm
    _ = ∑' e, ∑' S, ∑' u, ∑' v, averagedQuarterBridge G p x h e u v S :=
      tsum_congr fun e => ENNReal.tsum_comm
    _ = ∑' S, ∑' e, ∑' u, ∑' v, averagedQuarterBridge G p x h e u v S := ENNReal.tsum_comm
    _ ≤ ∑' S : Finset V, (2*R*Q) * (law p {ω | cluster G ω x = (S : Set V)} * F (S : Set V)) := by
      apply ENNReal.tsum_le_tsum
      intro S
      exact (averagedQuarterBridge_cluster_sum_le G hc hl p hp hfin K hbound S x h).trans_eq (by rw [hF]; dsimp [R,Q,H]; ac_rfl)
    _ = (2*R*Q) * ∫⁻ ω, F (cluster G ω x) ∂law p := by
      rw [ENNReal.tsum_mul_left]
      congr 1
      have hf : ∀ᵐ ω ∂(criticalModel G).law p, ((criticalModel G).cluster ω x).Finite := by
        change ∀ᵐ ω ∂law p, ((criticalModel G).cluster ω x).Finite
        simpa only [criticalModel_cluster] using hfin x
      have hh := ((criticalModel G).lintegral_eq_sum_finite_clusters p x hf F).symm
      change (∑' S : Finset V, law p {ω | (criticalModel G).cluster ω x = (S : Set V)}*F (S : Set V)) =
        ∫⁻ ω, F ((criticalModel G).cluster ω x) ∂law p at hh
      simpa only [criticalModel_cluster] using hh
    _ = _ := by rw [hI]

end Percolation.BenjaminiSchramm

end

end OAI
