import OAI.Probability.BenjaminiSchramm.GhostPivotalBoundary
import OAI.Probability.BenjaminiSchramm.RootGhostSums

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem quarter_twoGhost_le_square_add_boundary
    (hinj : Function.Injective G)
    (hc : (criticalModel G).fullGraph.Connected) (hl : LocallyFinite G)
    (p : unitInterval) (hp : (p : ℝ) < 1)
    (hfin : ∀ v, ∀ᵐ ω ∂law p, (cluster G ω v).Finite)
    (K : ℝ) (hbound : ∀ x h, 0 ≤ h →
      (criticalModel G).quarterGhostMagnetization p x h ≤ K*h^(3/4 : ℝ))
    (x : V) (h : ℝ≥0) :
    ENNReal.ofReal (∫ ω, ghostKernel h ((criticalModel G).quarterTiltedMass ω x).toReal ^ 2 ∂law p) ≤
      ENNReal.ofReal ((criticalModel G).quarterGhostMagnetization p x h)^2 +
      (2*(ENNReal.ofReal (p : ℝ)/ENNReal.ofReal (1-(p : ℝ)))*
        ENNReal.ofReal (K^2*(h : ℝ)^(3/2 : ℝ))) *
      ∫⁻ ω, ghostAvoid (2*(h : ℝ)) ((criticalModel G).quarterTiltedMass ω x) *
        (∑' e, if e ∈ (criticalModel G).incidentEdges (cluster G ω x) then
          (criticalModel G).ghostBondWeight x e else 0) ∂law p := by
  let H := criticalModel G
  have hf : ∀ᵐ ω ∂H.law p, (H.cluster ω x).Finite := by
    change ∀ᵐ ω ∂law p, (H.cluster ω x).Finite
    simpa only [H,criticalModel_cluster] using hfin x
  have hb := averaged_twoGhost_le_fan_add_pivotal_sum G hinj p x (hfin x)
    (ghostFieldLaw h (H.quarterGhostWeight x))
  have htwo := H.quarterTwoGhostConnection_average p x h hf
  have hone := H.quarterGhostConnection_average p x h hf
  change (∫⁻ m, ∫⁻ n, law p
      ({ω | ∃ y ∈ m, (H.openGraph ω).Reachable x y} ∩
        {ω | ∃ y ∈ n, (H.openGraph ω).Reachable x y})
      ∂ghostFieldLaw h (H.quarterGhostWeight x) ∂ghostFieldLaw h (H.quarterGhostWeight x)) =
    ENNReal.ofReal (∫ ω, ghostKernel h (H.quarterTiltedMass ω x).toReal^2 ∂law p) at htwo
  change (∫⁻ m, law p {ω | ∃ y ∈ m, (H.openGraph ω).Reachable x y}
      ∂ghostFieldLaw h (H.quarterGhostWeight x)) = ENNReal.ofReal (H.quarterGhostMagnetization p x h) at hone
  simp_rw [criticalModel_finiteGhostConnection G] at hb
  rw [htwo,hone] at hb
  exact hb.trans (add_le_add le_rfl
    (averagedQuarterBridge_sum_le_boundary G hc hl p hp hfin K hbound x h))

theorem root_twoGhost_bound
    (hinj : Function.Injective G)
    (hc : (criticalModel G).fullGraph.Connected) (hl : LocallyFinite G)
    (hq : (criticalModel G).QuasiTransitive)
    (p : unitInterval) (hp : (p : ℝ) < 1)
    (hfin : ∀ v, ∀ᵐ ω ∂law p, (cluster G ω v).Finite)
    (K : ℝ) (hbound : ∀ x h, 0 ≤ h →
      (criticalModel G).quarterGhostMagnetization p x h ≤ K*h^(3/4 : ℝ))
    (D B : ℕ) (hD : ∀ v, ((criticalModel G).incidentEdges {v}).ncard ≤ D)
    (hB : ∀ v, ((criticalModel G).vertexBall v 1).ncard ≤ B) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ h : ℝ≥0, 0 < h →
      (∑ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
        ∫ ω, ghostKernel h ((criticalModel G).quarterTiltedMass ω x).toReal ^ 2 ∂law p) ≤
      (∑ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
        (criticalModel G).quarterGhostMagnetization p x h)^2 +
      A*(h : ℝ)^(3/2 : ℝ) *
        (∑ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
          (criticalModel G).quarterGhostDerivative p x (2*h)) := by
  let H := criticalModel G
  let O := (H.orbitRepresentatives hq).roots
  let R := ENNReal.ofReal (p : ℝ)/ENNReal.ofReal (1-(p : ℝ))
  let J : ℝ≥0∞ := (2*R*ENNReal.ofReal (K^2)) * ((D : ℝ≥0∞)*(2*(B : ℝ≥0∞)^(3/8 : ℝ))) * 2
  have hR : R ≠ ⊤ := by
    dsimp [R]
    apply ENNReal.div_ne_top ENNReal.ofReal_ne_top
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hp)).ne'
  have hJ : J ≠ ⊤ := by
    dsimp [J]
    finiteness
  refine ⟨J.toReal,ENNReal.toReal_nonneg,?_⟩
  intro h hh
  have hh0 : (0 : ℝ) < h := hh
  have h2 : (0 : ℝ) < 2*h := by positivity
  let M := ∑ x ∈ O, H.quarterGhostMagnetization p x h
  let Derv := ∑ x ∈ O, H.quarterGhostDerivative p x (2*h)
  have hM (x : V) : 0 ≤ H.quarterGhostMagnetization p x h :=
    integral_nonneg fun _ => ghostKernel_nonneg h.2 ENNReal.toReal_nonneg
  have hDerv (x : V) : 0 ≤ H.quarterGhostDerivative p x (2*h) :=
    integral_nonneg fun _ => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
  have hpow : ENNReal.ofReal (K^2*(h : ℝ)^(3/2 : ℝ)) =
      ENNReal.ofReal (K^2) * ENNReal.ofReal ((h : ℝ)^(3/2 : ℝ)) :=
    ENNReal.ofReal_mul (sq_nonneg K)
  have htransport := H.expected_ghost_boundary_weight_le hc hl hq p (by positivity : (0 : ℝ) ≤ 2*h)
    D B hD hB
  have hderiv : (∑ x ∈ O, ∫⁻ ω, ghostAvoid (2*(h : ℝ)) (H.quarterTiltedMass ω x)*H.quarterTiltedMass ω x ∂H.law p) =
      ENNReal.ofReal Derv := by
    simp_rw [H.lintegral_ghostAvoid_mass_eq_derivative p _ h2]
    exact (ENNReal.ofReal_sum_of_nonneg (fun x _ => hDerv x)).symm
  have hsq : (∑ x ∈ O, ENNReal.ofReal (H.quarterGhostMagnetization p x h)^2) ≤ ENNReal.ofReal (M^2) := by
    simp_rw [←ENNReal.ofReal_pow (hM _)]
    rw [←ENNReal.ofReal_sum_of_nonneg (fun x _ => sq_nonneg (H.quarterGhostMagnetization p x h))]
    exact ENNReal.ofReal_le_ofReal (Finset.sum_sq_le_sq_sum_of_nonneg (fun x _ => hM x))
  have hfinal : (∑ x ∈ O, ENNReal.ofReal (∫ ω, ghostKernel h (H.quarterTiltedMass ω x).toReal^2 ∂law p)) ≤
      ENNReal.ofReal (M^2) + J*ENNReal.ofReal ((h : ℝ)^(3/2 : ℝ))*ENNReal.ofReal Derv := by
    calc
      _ ≤ (∑ x ∈ O, ENNReal.ofReal (H.quarterGhostMagnetization p x h)^2) +
          (2*R*ENNReal.ofReal (K^2*(h : ℝ)^(3/2 : ℝ))) *
            ∑ x ∈ O, ∫⁻ ω, ghostAvoid (2*(h : ℝ)) (H.quarterTiltedMass ω x)*
              (∑' e, if e ∈ H.incidentEdges (cluster G ω x) then H.ghostBondWeight x e else 0) ∂law p := by
        rw [Finset.mul_sum,←Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun x _ => quarter_twoGhost_le_square_add_boundary G hinj hc hl p hp hfin K hbound x h
      _ ≤ ENNReal.ofReal (M^2) + (2*R*ENNReal.ofReal (K^2*(h : ℝ)^(3/2 : ℝ))) *
          (((D : ℝ≥0∞)*(2*(B : ℝ≥0∞)^(3/8 : ℝ)))*(2*ENNReal.ofReal Derv)) := by
        apply add_le_add hsq
        apply mul_le_mul' le_rfl
        have htrans := htransport
        change (∑ x ∈ O, ∫⁻ ω, ghostAvoid (2*(h:ℝ)) (H.quarterTiltedMass ω x)*
            (∑' e, if e ∈ H.incidentEdges (H.cluster ω x) then H.ghostBondWeight x e else 0) ∂law p) ≤ _ at htrans
        rw [hderiv] at htrans
        simpa only [H,criticalModel_cluster] using htrans
      _ = _ := by rw [hpow]; dsimp [J]; ac_rfl
  have hreal := ENNReal.toReal_mono (by finiteness) hfinal
  rw [ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top),ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_ofReal (sq_nonneg M),ENNReal.toReal_mul,ENNReal.toReal_mul] at hreal
  have hpnonneg : 0 ≤ (h : ℝ)^(3/2 : ℝ) := Real.rpow_nonneg h.2 _
  have hdnonneg : 0 ≤ Derv := Finset.sum_nonneg (fun x _ => hDerv x)
  rw [ENNReal.toReal_ofReal hpnonneg,ENNReal.toReal_ofReal hdnonneg] at hreal
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun _ => sq_nonneg _))] using hreal

end Percolation.BenjaminiSchramm

end

end OAI
