import Mathlib
import OAI.Geometry.TamingCompatibility.Concentration.HodgeCompactResidual
import OAI.Geometry.TamingCompatibility.Hodge.HodgeCutoffFamilies

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.CutoffFamilies
open OperatorCalculus NormalHeatResidual UniformJets FlatHeat Filter Set Metric
open scoped Topology ContDiff
variable {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma compact_cutoff_residual (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (c : P × V → W →L[ℝ] W)
    (K : Set P) (hK : IsCompact K) {r : ℝ} (hr : 0 ≤ r)
    (ha : ∀ x ∈ K ×ˢ closedBall (0 : V) r, ∀ i j, ContDiffAt ℝ ∞ (a i j) x)
    (hb : ∀ x ∈ K ×ˢ closedBall (0 : V) r, ∀ j, ContDiffAt ℝ ∞ (b j) x)
    (hc : ∀ x ∈ K ×ˢ closedBall (0 : V) r, ContDiffAt ℝ ∞ c x)
    (ha0 : ∀ q ∈ K, ∀ i j, a i j (q,0) = euclideanPrincipal i j)
    (hda0 : ∀ q ∈ K, ∀ i j, fderiv ℝ (fun z => a i j (q,z)) 0 = 0)
    (hb0 : ∀ q ∈ K, ∀ j, b j (q,0) = 0)
    (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ =ᶠ[𝓝 (0 : V)] 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ z : V, ‖z‖ ≤ r → ∀ t : ℝ, 0 < t → ∀ u : W,
      ‖deriv (fun s => χ z • modelSection s u z) t +
        secondOrder (EuclideanSpace.basisFun (Fin 4) ℝ) (fun i j y => a i j (q,y))
          (fun j y => b j (q,y)) (fun y => c (q,y)) (fun y => χ y • modelSection t u y) z‖ ≤
        (C*heat (2*t) z)*‖u‖ := by
  have hp (q : P) (hq : q ∈ K) : (q,0) ∈ K ×ˢ closedBall (0 : V) r := ⟨hq,by simpa using hr⟩
  have hF0 (q : P) (hq : q ∈ K) : dpos (principal a χ) (q,0) = 0 :=
    principal_dpos_zero a χ hχ hχ0 q (ha _ (hp q hq)) (hda0 q hq)
  have hG0 (q : P) (hq : q ∈ K) : first a b χ (q,0) = 0 := by
    rw [first_center a b χ hχ0 q]
    funext j
    exact hb0 q hq j
  obtain ⟨C,hC,hbounds⟩ := normal_bounds_on_tube (principal a χ) (first a b χ) (zero a b c χ)
    K hK hr (fun x hx => principal_smooth a χ hχ (ha x hx))
    (fun x hx => first_smooth a b χ hχ (ha x hx) (hb x hx))
    (fun x hx => (zero_smooth a b c χ hχ (ha x hx) (hb x hx) (hc x hx)).continuousAt) hF0 hG0
  refine ⟨2304*C+64*C+4*C,by positivity,fun q hq z hz t ht u => ?_⟩
  rw [cutoff_gaussian_residual _ _ _ χ hχ ht z u]
  have hba (i j : Fin 4) : |principal a χ (q,z) i j - euclideanPrincipal i j| ≤ C*‖z‖^2 := by
    have hp0 : principal a χ (q,0) i j = euclideanPrincipal i j := by
      rw [principal_center a χ hχ0 q]
      exact ha0 q hq i j
    have hn := ((norm_le_pi_norm ((principal a χ (q,z)-principal a χ (q,0)) i) j).trans
      (norm_le_pi_norm (principal a χ (q,z)-principal a χ (q,0)) i)).trans (hbounds q hq z hz).1
    simpa only [Pi.sub_apply,Real.norm_eq_abs,hp0] using hn
  have hbb (j : Fin 4) : ‖first a b χ (q,z) j‖ ≤ C*‖z‖ :=
    (norm_le_pi_norm (first a b χ (q,z)) j).trans (hbounds q hq z hz).2.1
  have hh := residual_bound (fun y => principal a χ (q,y)) (fun y => first a b χ (q,y))
    (fun y => zero a b c χ (q,y)) ht hC hC z hba hbb (hbounds q hq z hz).2.2
  exact (ContinuousLinearMap.le_opNorm _ u).trans (mul_le_mul_of_nonneg_right hh (norm_nonneg u))

end TamingCompatibility.GeometricHilbert.CutoffFamilies

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalHeatResidual
open OperatorCalculus FlatHeat
open scoped ContDiff
variable {W Q : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma actual_cutoff_residual (a : Fin 4 → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (ρ : V → ℝ) (g : Fin 4 → Fin 4 → V → ℝ) (U : V → W →L[ℝ] W)
    (hU : ContDiff ℝ ∞ U) (horth : ∀ z, (U z).adjoint ∘L U z = ContinuousLinearMap.id ℝ W)
    (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ)
    {z : V} (ha : ∀ i, DifferentiableAt ℝ (a i) z) (hb : DifferentiableAt ℝ b z)
    (hρ : DifferentiableAt ℝ ρ z) (hρz : ρ z ≠ 0)
    (hp : ∀ i j, (a i z).adjoint ∘L a j z + (a j z).adjoint ∘L a i z =
      (2*g i j z) • ContinuousLinearMap.id ℝ W) {t : ℝ} (ht : 0 < t) (u : W) :
    (U z).adjoint (deriv (fun s => U z (χ z • modelSection s u z)) t +
      weightedAdjoint (EuclideanSpace.basisFun (Fin 4) ℝ) a b ρ
        (differential (EuclideanSpace.basisFun (Fin 4) ℝ) a b
          (fun y => U y (χ y • modelSection t u y))) z) =
      deriv (fun s => χ z • modelSection s u z) t +
        secondOrder (EuclideanSpace.basisFun (Fin 4) ℝ) g
          (gaugeFirst (EuclideanSpace.basisFun (Fin 4) ℝ) g
            (firstMatrix (EuclideanSpace.basisFun (Fin 4) ℝ) a b ρ) U)
          (gaugeZero (EuclideanSpace.basisFun (Fin 4) ℝ) g
            (firstMatrix (EuclideanSpace.basisFun (Fin 4) ℝ) a b ρ)
            (zeroMatrix (EuclideanSpace.basisFun (Fin 4) ℝ) a b ρ) U)
          (fun y => χ y • modelSection t u y) z := by
  have hU2 : ContDiff ℝ 2 U := hU.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hm0 : ContDiff ℝ ∞ (fun y : V => χ y • modelSection t u y) :=
    hχ.smul ((heat_contDiff t).smul contDiff_const)
  have hm : ContDiff ℝ 2 (fun y => χ y • modelSection t u y) :=
    hm0.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hd := ((heat_hasDerivAt_time ht z).smul_const u).const_smul (χ z)
  have htime : deriv (fun s => U z (χ z • modelSection s u z)) t =
      U z (deriv (fun s => χ z • modelSection s u z) t) :=
    ((U z).hasFDerivAt.comp_hasDerivAt t hd).deriv.trans (congrArg (U z) hd.deriv.symm)
  have hcancel (v : W) : (U z).adjoint (U z v) = v :=
    congrArg (fun C : W →L[ℝ] W => C v) (horth z)
  rw [map_add,htime,hcancel]
  congr 1
  exact gauge_formal_square _ a b ρ g U _ hU2 hm ha hb hρ hρz hp (horth z)

end TamingCompatibility.GeometricHilbert.NormalHeatResidual

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

attribute [local irreducible] pulledA pulledB normalFirst normalZero normalDensity
  normalPrincipal normalGauge gaugedFirst gaugedZero

lemma actual_cutoff_square_norm (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ y v w, g y v w = g y w v) {q z : Space}
    (hactual : ActualData J α ht p D q g B)
    (hz : (q,z) ∈ normalDomain J α ht p D g B)
    (hgact : g (normalMap g B q z) = (coordinateMetric J α ht p (normalMap g B q z)).bilinear)
    (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) {t : ℝ} (htpos : 0 < t) (u : W) :
      ‖deriv (fun s => normalGauge J α ht p D g B (q,z) (χ z • NormalHeatResidual.modelSection s u z)) t +
        weightedAdjoint EuclideanEnergy.e (pulledA J α ht p D g B q)
          (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y))
          (differential EuclideanEnergy.e (pulledA J α ht p D g B q)
            (pulledB J α ht p D g B q)
            (fun y => normalGauge J α ht p D g B (q,y) (χ y • NormalHeatResidual.modelSection t u y))) z‖ =
      ‖deriv (fun s => χ z • NormalHeatResidual.modelSection s u z) t +
        secondOrder EuclideanEnergy.e (fun i j y => normalPrincipal g B i j (q,y))
          (fun j y => gaugedFirst J α ht p D g B j (q,y))
          (fun y => gaugedZero J α ht p D g B (q,y))
          (fun y => χ y • NormalHeatResidual.modelSection t u y) z‖ := by
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
  have hres := NormalHeatResidual.actual_cutoff_residual (pulledA J α ht p D g B q)
    (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y))
    (fun i j y => normalPrincipal g B i j (q,y))
    (fun y => normalGauge J α ht p D g B (q,y)) hU horth χ hχ
    (fun i => ((hpa i).comp z (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp))
    ((hpb.comp z (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp))
    ((hpρ.comp z (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp))
    hρpos (pulledA_scalar_at J α ht p D g B hg hB hsym hz.1 hgact) htpos u
  have hee : (EuclideanSpace.basisFun (Fin 4) ℝ : Fin 4 → Space) = EuclideanEnergy.e := by
    funext i
    simp [EuclideanEnergy.e]
  rw [hee] at hres
  have hf : gaugeFirst EuclideanEnergy.e (fun i j y => normalPrincipal g B i j (q,y))
      (firstMatrix EuclideanEnergy.e (pulledA J α ht p D g B q)
        (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y)))
      (fun y => normalGauge J α ht p D g B (q,y)) =
        (fun j y => gaugedFirst J α ht p D g B j (q,y)) := by
    unfold gaugedFirst normalFirst
    rfl
  have hc : gaugeZero EuclideanEnergy.e (fun i j y => normalPrincipal g B i j (q,y))
      (firstMatrix EuclideanEnergy.e (pulledA J α ht p D g B q)
        (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y)))
      (zeroMatrix EuclideanEnergy.e (pulledA J α ht p D g B q)
        (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y)))
      (fun y => normalGauge J α ht p D g B (q,y)) =
        (fun y => gaugedZero J α ht p D g B (q,y)) := by
    unfold gaugedZero normalFirst normalZero
    rfl
  rw [hf,hc] at hres
  have hn := ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.star_mem (hu z))
    (deriv (fun s => normalGauge J α ht p D g B (q,z) (χ z • NormalHeatResidual.modelSection s u z)) t +
      weightedAdjoint EuclideanEnergy.e (pulledA J α ht p D g B q)
        (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y))
        (differential EuclideanEnergy.e (pulledA J α ht p D g B q)
          (pulledB J α ht p D g B q)
          (fun y => normalGauge J α ht p D g B (q,y) (χ y • NormalHeatResidual.modelSection t u y))) z)
  rw [ContinuousLinearMap.star_eq_adjoint,hres] at hn
  exact hn.symm

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
