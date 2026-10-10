import OAI.Geometry.IsometricImmersion.Energy.DirectedDefectCost

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def directedFluxCostConstant (D M lambda S MI X : ℝ) : ℝ :=
  6*X*D*Real.exp (lambda*S+MI)*(M+1)

theorem ellipticWeightC1_energy_nonneg
    {b c glow : ℝ} {chi K G1 u : Coord → ℝ} {p : Coord}
    (hc : 0 < c) (hg : 0 < glow) (hG1 : glow ≤ G1 p) (hp : p 1 ≤ b) :
    0 ≤ ellipticEnergy (fun q => G1 q*K q) (ellipticWeightC1 b c chi K) u p := by
  apply ellipticEnergy_nonneg _ _ _ p (ellipticWeightC1_nonneg _ _ _ _ _)
  intro hv
  have hplt : p 1 < b := by
    by_contra h
    have heq : p 1 = b := le_antisymm hp (le_of_not_gt h)
    rw [ellipticWeightC1_zero heq.ge] at hv
    exact (lt_irrefl (0 : ℝ)) hv
  have hvraw : 0 < ellipticWeight b c chi K p := by
    simpa only [ellipticWeightC1_eq hp] using hv
  have hk := ellipticWeight_pos_implies_curvature hc hplt hvraw
  have hKpos : 0 < K p := (mul_pos (by positivity : 0 < c/2) (sub_pos.mpr hplt)).trans hk
  exact mul_pos (hg.trans_le hG1) hKpos

theorem directedCostConstants_nonneg {D M lambda S MI X c2 : ℝ}
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hlambda : 0 ≤ lambda) (hX : 0 ≤ X) (hc2 : 0 ≤ c2) :
    0 ≤ directedFluxCostConstant D M lambda S MI X ∧
    0 ≤ directedDefectCostConstant D M lambda S MI c2 := by
  have hN := (directedWeightJetBudget_bounds hD hM hlambda).1
  constructor
  · unfold directedFluxCostConstant
    positivity
  · unfold directedDefectCostConstant directedQuadraticCostConstant
    positivity

end SmoothLocal.Weighted

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Model

theorem actual_cap_directed_costs_le_elliptic
    {g0 eta : MetricField} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
    {L R A0 b kappa c1 c2 D glow lambda epsilon S MI M : ℝ}
    {G1 B C I u : Coord → ℝ} {p : Coord}
    (hL : -2 < L) (hR : R < 2) (hA0 : -2 < A0)
    (hk : 0 < kappa) (hc1 : 0 < c1) (hc2 : 0 ≤ c2) (hg : 0 < glow)
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hlambda : 0 ≤ lambda)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hbackground : ∀ q ∈ U, gaussianCurvature g0 q = modelCurvature kappa q)
    (hsupport : tsupport eta ⊆ patchBox) (hpU : capChart Y p ∈ U)
    (hdisp : |capFlowHeight Y p-p 1| ≤ (1 : ℝ)/50)
    (hbelow : p 1 ≤ b) (hdD : edgeDistance b p ≤ D)
    (ht : |p 0| ≤ 2) (hs : |p 1| ≤ S) (hIv : |I p| ≤ MI)
    (hId : DifferentiableAt ℝ I p) (hIi : ∀ i : Fin 2, |coordPartial i I p| ≤ M)
    (hG1 : glow ≤ G1 p)
    (hAd : DifferentiableAt ℝ (fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q) p)
    (hAv : |G1 p*capPullback Y (gaussianCurvature (g0+eta)) p| ≤ M)
    (hAi : ∀ i : Fin 2,
      |coordPartial i (fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q) p| ≤ M)
    (hBv : |B p| ≤ M) (hCv : |C p| ≤ M)
    (hcoercive : capPullback Y (gaussianCurvature (g0+eta)) p ≤ c1*edgeDistance b p →
      c2*directedWeight b lambda I p*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2) ≤
        multiplierQuadratic (fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q) B C
          (directedM b lambda I) (directedN b lambda epsilon I) u p) :
    let A := fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q
    let chi := capSpatialCutoff L R A0
    let c := capOverlapThreshold kappa c1 D
    let X := capSpatialDerivativeConstant L R A0
    |directedCutoffError A chi I u b lambda epsilon p| +
      directedCoercivityDefect A B C chi I u b lambda epsilon c2 p ≤
      (directedFluxCostConstant D M lambda S MI X + directedDefectCostConstant D M lambda S MI c2)*
        (D+1/(glow*c))*
          ellipticEnergy A (ellipticWeightC1 b c (capOuterSpatialCutoff L R A0)
            (capPullback Y (gaussianCurvature (g0+eta)))) u p := by
  let A := fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q
  let K := capPullback Y (gaussianCurvature (g0+eta))
  let chi := capSpatialCutoff L R A0
  let c := capOverlapThreshold kappa c1 D
  let X := capSpatialDerivativeConstant L R A0
  let E := ellipticEnergy A (ellipticWeightC1 b c (capOuterSpatialCutoff L R A0) K) u p
  let CE := D+1/(glow*c)
  let CF := directedFluxCostConstant D M lambda S MI X
  let CD := directedDefectCostConstant D M lambda S MI c2
  change |directedCutoffError A chi I u b lambda epsilon p| +
    directedCoercivityDefect A B C chi I u b lambda epsilon c2 p ≤ (CF+CD)*CE*E
  have hc : 0 < c := capOverlapThreshold_pos hk hc1 hD
  have hX : 0 ≤ X := (abs_nonneg _).trans (capSpatialCutoff_partial_uniform hL hR hA0 p 0)
  have hEnonneg : 0 ≤ E := ellipticWeightC1_energy_nonneg hc hg hG1 hbelow
  have hCE : 0 ≤ CE := by dsimp only [CE]; positivity
  have hconst := directedCostConstants_nonneg (S := S) (MI := MI) hD hM hlambda hX hc2
  have hCF : 0 ≤ CF := hconst.1
  have hCD : 0 ≤ CD := hconst.2
  have hd : 0 ≤ edgeDistance b p := sub_nonneg.mpr hbelow
  have hfluxcost : |directedCutoffError A chi I u b lambda epsilon p| ≤ CF*weightedGradient b u p :=
    directedCutoffError_abs_le_seven hlambda heps heps1 ht hd hdD hs hIv hAv
      (capSpatialCutoff_partial_uniform hL hR hA0 p)
  have hdefcost : directedCoercivityDefect A B C chi I u b lambda epsilon c2 p ≤ CD*weightedGradient b u p :=
    directedCoercivityDefect_le_seven hAd hId hlambda hM hc2 heps heps1 ht hd hdD hs hIv hIi
      hAv hBv hCv hAi (capSpatialCutoff_range L R A0 p)
  by_cases hedge : p 1 < b
  · have hdpos : 0 < edgeDistance b p := sub_pos.mpr hedge
    have hflux : |directedCutoffError A chi I u b lambda epsilon p| ≤ CF*CE*E := by
      by_cases hz : directedCutoffError A chi I u b lambda epsilon p = 0
      · rw [hz, abs_zero]
        positivity
      · have hder : ∃ i : Fin 2, coordPartial i chi p ≠ 0 := by
          by_contra h
          have hh : ∀ i : Fin 2, coordPartial i chi p = 0 := by
            intro i
            by_contra hi
            exact h ⟨i,hi⟩
          exact hz (multiplierCutoffError_zero A chi (directedM b lambda I)
            (directedN b lambda epsilon I) u p (hh 0) (hh 1))
        obtain ⟨i,hi⟩ := hder
        have hgrad : weightedGradient b u p ≤ CE*E :=
          capOuterElliptic_gradient_on_actual_cutoff_support hL hR hA0 hk hc1 hD hg
            hbackground hsupport hpU hdisp hdpos hdD hG1 hi
        exact hfluxcost.trans (by
          have hh := mul_le_mul_of_nonneg_left hgrad hCF
          convert hh using 1
          ring)
    have hdef : directedCoercivityDefect A B C chi I u b lambda epsilon c2 p ≤ CD*CE*E := by
      by_cases hz : directedCoercivityDefect A B C chi I u b lambda epsilon c2 p = 0
      · rw [hz]
        positivity
      · have hgrad : weightedGradient b u p ≤ CE*E :=
          capOuterElliptic_gradient_on_defect hL hR hA0 hk hc1 hD hg hdpos hdD hG1 hcoercive hz
        exact hdefcost.trans (by
          have hh := mul_le_mul_of_nonneg_left hgrad hCD
          convert hh using 1
          ring)
    have hh := add_le_add hflux hdef
    convert hh using 1
    ring
  · have heq : p 1 = b := le_antisymm hbelow (le_of_not_gt hedge)
    rw [directedCutoffError_edge_zero A chi I u b lambda epsilon p heq,
      directedCoercivityDefect_edge_zero A B C chi I u b lambda epsilon c2 p hAd hId heq,
      abs_zero, zero_add]
    positivity

end SmoothLocal.Flow

end

end OAI
