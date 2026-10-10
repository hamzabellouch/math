import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.GaugeOrthogonal
import OAI.Geometry.TamingCompatibility.DifferentialForms.Regular
import OAI.Geometry.TamingCompatibility.Hodge.HodgeCompactExtension

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.UniformJets
open Metric Set
open scoped ContDiff
variable {P V W₁ W₂ W₃ : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W₁] [NormedSpace ℝ W₁]
  [NormedAddCommGroup W₂] [NormedSpace ℝ W₂]
  [NormedAddCommGroup W₃] [NormedSpace ℝ W₃]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [NormedSpace ℝ W₃] in
lemma compact_normal_bounds (F : P × V → W₁) (G : P × V → W₂) (H : P × V → W₃)
    (K : Set P) (hK : IsCompact K) (O : Set (P × V)) (hO : IsOpen O)
    (hKO : K ×ˢ {(0 : V)} ⊆ O)
    (hF : ∀ x ∈ O, ContDiffAt ℝ ∞ F x) (hG : ∀ x ∈ O, ContDiffAt ℝ ∞ G x)
    (hH : ∀ x ∈ O, ContinuousAt H x)
    (hF0 : ∀ p ∈ K, dpos F (p,0) = 0) (hG0 : ∀ p ∈ K, G (p,0) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧ K ×ˢ closedBall (0 : V) r ⊆ O ∧
      ∀ p ∈ K, ∀ z : V, ‖z‖ ≤ r →
        ‖F (p,z)-F (p,0)‖ ≤ C*‖z‖^2 ∧ ‖G (p,z)‖ ≤ C*‖z‖ ∧ ‖H (p,z)‖ ≤ C := by
  obtain ⟨Ca,hCa,ra,hra,hsuba,hba⟩ := local_quadratic_bound F K hK O hO hKO hF hF0
  obtain ⟨Cb,hCb,rb,hrb,hsubb,hbb⟩ := local_linear_bound G K hK O hO hKO hG
  let r := min ra rb
  have hr : 0 < r := lt_min hra hrb
  have hsub : K ×ˢ closedBall (0 : V) r ⊆ O := fun x hx =>
    hsuba ⟨hx.1, closedBall_subset_closedBall (min_le_left ra rb) hx.2⟩
  have hcont : ContinuousOn H (K ×ˢ closedBall (0 : V) r) :=
    fun x hx => (hH x (hsub hx)).continuousWithinAt
  obtain ⟨Cc,hbc⟩ := (hK.prod (isCompact_closedBall (0 : V) r)).exists_bound_of_continuousOn hcont
  refine ⟨Ca+Cb+max Cc 0,by positivity,r,hr,hsub,fun p hp z hz => ⟨?_,?_,?_⟩⟩
  · exact ((hba p hp z (hz.trans (min_le_left ra rb))).1).trans
      (mul_le_mul_of_nonneg_right (by linarith [le_max_right Cc 0] : Ca ≤ Ca+Cb+max Cc 0) (sq_nonneg _))
  · have hh : ‖G (p,z)‖ ≤ Cb*‖z‖ := by
      simpa [hG0 p hp] using hbb p hp z (hz.trans (min_le_right ra rb))
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith [le_max_right Cc 0] : Cb ≤ Ca+Cb+max Cc 0)
      (norm_nonneg _))
  · exact (hbc (p,z) ⟨hp,by simpa using hz⟩).trans (by linarith [le_max_left Cc 0])

end TamingCompatibility.GeometricHilbert.UniformJets

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local irreducible] normalFirst

lemma gaugedFirst_center (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {q : Space} (hactual : ActualData J α ht p D q g B) (j : Fin 4) :
    gaugedFirst J α ht p D g B j (q,0) = 0 := by
  have hjets := hactual.jets J α hs ht p D q g B hg hB
  unfold gaugedFirst normalGauge
  exact transformedFirst_zero (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4)) EuclideanEnergy.e
    (fun i k => by simp [EuclideanEnergy.e])
    (fun i k z => normalPrincipal g B i k (q,z))
    (fun i z => normalFirst J α ht p D g B i (q,z))
    (fun i k => (hjets.2.2.2.2.2.1 i k).2.1) j

lemma normalGauge_unitary (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {q : Space} (hactual : ActualData J α ht p D q g B) (z : Space) :
    normalGauge J α ht p D g B (q,z) ∈ unitary (W →L[ℝ] W) := by
  obtain ⟨ha,hb,hρ,hρone,hρzero,hpr,hskew⟩ := hactual.jets J α hs ht p D q g B hg hB
  unfold normalGauge
  apply OrthogonalJets.gauge_unitary
  intro v
  apply halfJet_skew
  intro j
  have he : normalFirst J α ht p D g B j (q,0) =
      actualSquareFirst EuclideanEnergy.e (pulledA J α ht p D g B q)
        (pulledB J α ht p D g B q) (fun z => volumeDensity (normalMetric g B (q,z))) j 0 := by
    unfold normalFirst normalDensity
    rw [firstMatrix_eq]
  rw [he]
  exact hskew j

lemma compact_actual_coefficients (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (K : Set Space) (hK : IsCompact K) (hactual : ∀ q ∈ K, ActualData J α ht p D q g B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧
      K ×ˢ Metric.closedBall (0 : Space) r ⊆ gaugedDomain J α ht p D g B ∧
      ∀ q ∈ K, ∀ z : Space, ‖z‖ ≤ r →
        (∀ i j, |normalPrincipal g B i j (q,z) - (if i=j then 1 else 0)| ≤ C*‖z‖^2) ∧
        (∀ j, ‖gaugedFirst J α ht p D g B j (q,z)‖ ≤ C*‖z‖) ∧
        ‖gaugedZero J α ht p D g B (q,z)‖ ≤ C := by
  let F : Space × Space → Fin 4 → Fin 4 → ℝ := fun x i j => normalPrincipal g B i j x
  let G : Space × Space → Fin 4 → W →L[ℝ] W := fun x j => gaugedFirst J α ht p D g B j x
  let H := gaugedZero J α ht p D g B
  let O := gaugedDomain J α ht p D g B
  have hKO : K ×ˢ {(0 : Space)} ⊆ O := by
    rintro ⟨q,z⟩ ⟨hq,hz⟩
    have hz' : z = 0 := hz
    subst z
    exact (hactual q hq).center J α ht p D g B
  have hF : ∀ x ∈ O, ContDiffAt ℝ ∞ F x := by
    intro x hx
    exact contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j =>
      normalPrincipal_smooth g B hg hB hx.1.2 i j
  have hG : ∀ x ∈ O, ContDiffAt ℝ ∞ G x := fun x hx => contDiffAt_pi.mpr
    (gaugedFirst_smooth J α ht p D g B hs hg hB hx)
  have hH : ∀ x ∈ O, ContinuousAt H x := fun x hx =>
    (gaugedZero_smooth J α ht p D g B hs hg hB hx).continuousAt
  have hF0 (q : Space) (hq : q ∈ K) : dpos F (q,0) = 0 := by
    have hjets := (hactual q hq).jets J α hs ht p D q g B hg hB
    rw [dpos_eq_at F q 0 ((hF (q,0) (hKO ⟨hq,rfl⟩)).differentiableAt (by simp))]
    have hsmooth (i j : Fin 4) : ContDiffAt ℝ ∞ (fun z => normalPrincipal g B i j (q,z)) 0 :=
      (hjets.2.2.2.2.2.1 i j).1
    change fderiv ℝ (fun z i j => normalPrincipal g B i j (q,z)) 0 = 0
    rw [fderiv_pi (fun i => (contDiffAt_pi.mpr (hsmooth i)).differentiableAt (by simp))]
    ext v i j
    simp only [ContinuousLinearMap.pi_apply,zero_apply,Pi.zero_apply]
    rw [fderiv_pi (fun j => (hsmooth i j).differentiableAt (by simp))]
    simp only [ContinuousLinearMap.pi_apply]
    exact congrArg (fun L : Space →L[ℝ] ℝ => L v) (hjets.2.2.2.2.2.1 i j).2.2
  have hG0 (q : Space) (hq : q ∈ K) : G (q,0) = 0 := by
    funext j
    exact gaugedFirst_center J α ht p D g B hs hg hB (hactual q hq) j
  obtain ⟨C,hC,r,hr,hsub,hbounds⟩ := compact_normal_bounds F G H K hK O
    (gaugedDomain_open J α ht p D g B hg hB) hKO hF hG hH hF0 hG0
  refine ⟨C,hC,r,hr,hsub,fun q hq z hz => ⟨fun i j => ?_,fun j => ?_,(hbounds q hq z hz).2.2⟩⟩
  · have hjets := (hactual q hq).jets J α hs ht p D q g B hg hB
    have hnorm := (norm_le_pi_norm ((F (q,z)-F (q,0)) i) j).trans
      (norm_le_pi_norm (F (q,z)-F (q,0)) i)
    have he : F (q,0) i j = if i=j then 1 else 0 := (hjets.2.2.2.2.2.1 i j).2.1
    simpa only [Pi.sub_apply,Real.norm_eq_abs,he] using hnorm.trans (hbounds q hq z hz).1
  · exact (norm_le_pi_norm (G (q,z)) j).trans (hbounds q hq z hz).2.1

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

lemma pulledA_scalar_at (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ y v w, g y v w = g y w v) {q z : Space}
    (hx : (q,z) ∈ regularSet J α ht p D g B)
    (hgact : g (normalMap g B q z) = (coordinateMetric J α ht p (normalMap g B q z)).bilinear)
    (i j : Fin 4) :
    (pulledA J α ht p D g B q i z).adjoint ∘L pulledA J α ht p D g B q j z +
      (pulledA J α ht p D g B q j z).adjoint ∘L pulledA J α ht p D g B q i z =
      (2*normalPrincipal g B i j (q,z)) • ContinuousLinearMap.id ℝ W := by
  obtain ⟨L,hL⟩ := hx.2
  have hm : normalMetric g B (q,z) =
      MetricDensity.pullMetric (coordinateMetric J α ht p (normalMap g B q z)).bilinear
        L.toContinuousLinearMap := by
    rw [normalMetric_eq_pullback g B hg hB hsym]
    change MetricDensity.pullMetric (g (normalMap g B q z))
      (fderiv ℝ (normalMap g B q) z) = _
    rw [normalMap_fderiv g B hg hB hsym,←hL,hgact]
  have hp := pulled_principal (coordinateMetric J α ht p (normalMap g B q z))
    (fun k => D.frame k (normalMap g B q z)) (D.frame_gram _ hx.1) L i j
  have ha (k : Fin 4) : pulledA J α ht p D g B q k z =
      pullCoefficient (HodgeFrozenEnergy.coefficient (fun l => D.frame l (normalMap g B q z)))
        L.symm.toContinuousLinearMap k := by
    simp only [pulledA,←hL,ContinuousLinearMap.inverse_equiv]
    rfl
  rw [ha i,ha j,hp]
  simp only [normalPrincipal,hm]

attribute [local irreducible] pulledA pulledB normalFirst normalZero normalDensity
  normalPrincipal normalGauge gaugedFirst gaugedZero

lemma actual_normal_residual_bound (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ y v w, g y v w = g y w v) {q z : Space}
    (hactual : ActualData J α ht p D q g B)
    (hz : (q,z) ∈ normalDomain J α ht p D g B)
    (hgact : g (normalMap g B q z) = (coordinateMetric J α ht p (normalMap g B q z)).bilinear)
    {C : ℝ} (hC : 0 ≤ C)
    (hzcoeff : (∀ i j, |normalPrincipal g B i j (q,z) - (if i=j then 1 else 0)| ≤ C*‖z‖^2) ∧
      (∀ j, ‖gaugedFirst J α ht p D g B j (q,z)‖ ≤ C*‖z‖) ∧
      ‖gaugedZero J α ht p D g B (q,z)‖ ≤ C)
    {t : ℝ} (htpos : 0 < t) (u : W) :
      ‖deriv (fun s => normalGauge J α ht p D g B (q,z) (NormalHeatResidual.modelSection s u z)) t +
        weightedAdjoint EuclideanEnergy.e (pulledA J α ht p D g B q)
          (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y))
          (differential EuclideanEnergy.e (pulledA J α ht p D g B q)
            (pulledB J α ht p D g B q)
            (fun y => normalGauge J α ht p D g B (q,y) (NormalHeatResidual.modelSection t u y))) z‖ ≤
        ((2304*C+64*C+4*C)*FlatHeat.heat (2*t) z)*‖u‖ := by
  have hpa := pulledA_joint J α ht p D g B hg hB hz.1
  have hpb := pulledB_joint J α hs ht p D g B hg hB hz.1
  have hpρ := normalDensity_smooth g B hg hB hz.2
  have hU : ContDiff ℝ ∞ (fun y => normalGauge J α ht p D g B (q,y)) := by
    unfold normalGauge
    exact OrthogonalJets.gauge_contDiff (V := Space) (W := W)
      (halfJet (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4))
        (fun j => normalFirst J α ht p D g B j (q,0)))
  have hu : ∀ y, normalGauge J α ht p D g B (q,y) ∈ unitary (W →L[ℝ] W) :=
    normalGauge_unitary J α ht p D g B hs hg hB hactual
  have horth (y : Space) : (normalGauge J α ht p D g B (q,y)).adjoint ∘L
      normalGauge J α ht p D g B (q,y) = ContinuousLinearMap.id ℝ W := by
    simpa only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.mul_def,ContinuousLinearMap.one_def]
      using (Unitary.star_mul_self_of_mem (hu y))
  have hρpos : normalDensity g B (q,z) ≠ 0 := by
    unfold normalDensity
    exact ne_of_gt (volumeDensity_pos hz.2)
  have hres := NormalHeatResidual.actual_residual (pulledA J α ht p D g B q)
    (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y))
    (fun i j y => normalPrincipal g B i j (q,y))
    (fun y => normalGauge J α ht p D g B (q,y)) hU horth
    (fun i => ((hpa i).comp z (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp))
    ((hpb.comp z (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp))
    ((hpρ.comp z (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp))
    hρpos
    (pulledA_scalar_at J α ht p D g B hg hB hsym hz.1 hgact) htpos u
  have hee : (EuclideanSpace.basisFun (Fin 4) ℝ : Fin 4 → Space) = EuclideanEnergy.e := by
    funext i
    simp [EuclideanEnergy.e]
  rw [hee] at hres
  simp only [gaugeFirst_eq,gaugeZero_eq] at hres
  have hf (y : Space) (j : Fin 4) : transformedFirst
      (fun i j y => normalPrincipal g B i j (q,y))
      (firstMatrix EuclideanEnergy.e (pulledA J α ht p D g B q)
        (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y)))
      (fun y => normalGauge J α ht p D g B (q,y)) EuclideanEnergy.e j y =
      gaugedFirst J α ht p D g B j (q,y) := by
    unfold gaugedFirst normalFirst
    rfl
  have hc : transformedZero
      (fun i j y => normalPrincipal g B i j (q,y))
      (firstMatrix EuclideanEnergy.e (pulledA J α ht p D g B q)
        (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y)))
      (zeroMatrix EuclideanEnergy.e (pulledA J α ht p D g B q)
        (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y)))
      (fun y => normalGauge J α ht p D g B (q,y)) EuclideanEnergy.e =
      (fun y => gaugedZero J α ht p D g B (q,y)) := by
    unfold gaugedZero normalFirst normalZero
    rfl
  simp only [hf,hc] at hres
  have hbound := NormalHeatResidual.residual_bound
    (fun y i j => normalPrincipal g B i j (q,y))
    (fun y j => gaugedFirst J α ht p D g B j (q,y))
    (fun y => gaugedZero J α ht p D g B (q,y)) htpos hC hC z
    hzcoeff.1 hzcoeff.2.1 hzcoeff.2.2
  have hh : ‖NormalHeatResidual.residual
      (fun y i j => normalPrincipal g B i j (q,y))
      (fun y j => gaugedFirst J α ht p D g B j (q,y))
      (fun y => gaugedZero J α ht p D g B (q,y)) t z u‖ ≤
      ((2304*C+64*C+4*C)*FlatHeat.heat (2*t) z)*‖u‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg u))
  have hn := ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.star_mem (hu z))
    (deriv (fun s => normalGauge J α ht p D g B (q,z) (NormalHeatResidual.modelSection s u z)) t +
      weightedAdjoint EuclideanEnergy.e (pulledA J α ht p D g B q)
        (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y))
        (differential EuclideanEnergy.e (pulledA J α ht p D g B q)
          (pulledB J α ht p D g B q)
          (fun y => normalGauge J α ht p D g B (q,y) (NormalHeatResidual.modelSection t u y))) z)
  rw [ContinuousLinearMap.star_eq_adjoint] at hn
  rw [←hn,hres]
  exact hh

lemma compact_actual_residual (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (O : Set Space) (hO : IsOpen O) (hOD : O ⊆ D.domain)
    (hgact : ∀ y ∈ O, g y = (coordinateMetric J α ht p y).bilinear)
    (hBact : ∀ y ∈ O, B y = frameMap (fun i => D.frame i y))
    (hsym : ∀ y v w, g y v w = g y w v)
    (K : Set Space) (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧ ∀ q ∈ K, ∀ t : ℝ, 0 < t →
      ∀ z : Space, ‖z‖ ≤ r → ∀ u : W,
        ‖deriv (fun s => normalGauge J α ht p D g B (q,z) (NormalHeatResidual.modelSection s u z)) t +
          weightedAdjoint EuclideanEnergy.e (pulledA J α ht p D g B q)
            (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y))
            (differential EuclideanEnergy.e (pulledA J α ht p D g B q)
              (pulledB J α ht p D g B q)
              (fun y => normalGauge J α ht p D g B (q,y) (NormalHeatResidual.modelSection t u y))) z‖ ≤
          (C*FlatHeat.heat (2*t) z)*‖u‖ := by
  have hactual (q : Space) (hq : q ∈ K) : ActualData J α ht p D q g B :=
    ⟨O,hO,hKO hq,hOD,hgact,hBact,hsym⟩
  obtain ⟨C,hC,s,hspos,hsub,hcoeff⟩ := compact_actual_coefficients J α ht p D g B hs hg hB K hK hactual
  let Ω := gaugedDomain J α ht p D g B ∩ (fun x : Space × Space => normalMap g B x.1 x.2) ⁻¹' O
  have hΩ : IsOpen Ω := (gaugedDomain_open J α ht p D g B hg hB).inter
    (hO.preimage (normalMap_joint g B hg hB).continuous)
  have hKΩ : K ×ˢ {(0 : Space)} ⊆ Ω := by
    rintro ⟨q,z⟩ ⟨hq,hz⟩
    have hz' : z = 0 := hz
    subst z
    exact ⟨(hactual q hq).center J α ht p D g B,by simpa using hKO hq⟩
  obtain ⟨a,ha,hasub⟩ := compact_tube K hK Ω hΩ hKΩ
  refine ⟨2304*C+64*C+4*C,by positivity,min s a,lt_min hspos ha,fun q hq t htpos z hz u => ?_⟩
  have hzΩ : (q,z) ∈ Ω := hasub ⟨hq,by simpa using hz.trans (min_le_right s a)⟩
  have hzcoeff := hcoeff q hq z (hz.trans (min_le_left s a))
  exact actual_normal_residual_bound J α ht p D g B hs hg hB hsym (hactual q hq)
    hzΩ.1.1 (hgact _ hzΩ.2) hC hzcoeff htpos u

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
