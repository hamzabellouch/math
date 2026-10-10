import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeCutoffBounds
import OAI.Geometry.TamingCompatibility.Hodge.HodgeParametrixGaussian

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalHeatResidual
open OperatorCalculus FlatHeat Filter Set
open scoped Topology ContDiff RealInnerProductSpace
variable {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma residual_family_smooth (a : P × V → Principal) (b : P × V → First (W := W))
    (c : P × V → W →L[ℝ] W) {x : P × V} {t : ℝ} (ht : t ≠ 0)
    (ha : ContDiffAt ℝ ∞ a x) (hb : ContDiffAt ℝ ∞ b x) (hc : ContDiffAt ℝ ∞ c x) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (P × V) =>
      residual (fun z => a (v.2.1,z)) (fun z => b (v.2.1,z))
        (fun z => c (v.2.1,z)) v.1 v.2.2) (t,x) := by
  have hh : ContDiffAt ℝ ∞ (fun v : ℝ × (P × V) => heat v.1 v.2.2) (t,x) :=
    (heat_joint_contDiffAt (x := (t,x.2)) ht).comp (t,x) (contDiffAt_fst.prodMk contDiffAt_snd.snd)
  have hi (u : V) : ContDiffAt ℝ ∞ (fun v : ℝ × (P × V) => ⟪v.2.2,u⟫) (t,x) :=
    contDiffAt_snd.snd.inner ℝ contDiffAt_const
  have hd : ContDiffAt ℝ ∞ (fun v : ℝ × (P × V) => (2*v.1)⁻¹) (t,x) :=
    (contDiffAt_const.mul contDiffAt_fst).inv (mul_ne_zero (by norm_num) ht)
  have hd2 : ContDiffAt ℝ ∞ (fun v : ℝ × (P × V) => (4*v.1^2)⁻¹) (t,x) :=
    (contDiffAt_const.mul (contDiffAt_fst.pow 2)).inv (mul_ne_zero (by norm_num) (pow_ne_zero 2 ht))
  unfold residual
  simp_rw [heat_hessian,heat_fderiv,div_eq_mul_inv]
  apply ContDiffAt.add
  · apply ContDiffAt.add
    · apply ContDiffAt.sum
      intro i _
      apply ContDiffAt.sum
      intro j _
      have hk : ContDiffAt ℝ ∞ (fun v : ℝ × (P × V) =>
          (euclideanPrincipal i j - a v.2 i j) * (heat v.1 v.2.2 *
            (⟪v.2.2,EuclideanSpace.basisFun (Fin 4) ℝ i⟫ *
              ⟪v.2.2,EuclideanSpace.basisFun (Fin 4) ℝ j⟫ * (4*v.1^2)⁻¹ -
                ⟪EuclideanSpace.basisFun (Fin 4) ℝ i,EuclideanSpace.basisFun (Fin 4) ℝ j⟫ *
                  (2*v.1)⁻¹))) (t,x) :=
        (contDiffAt_const.sub ((contDiffAt_pi.mp (contDiffAt_pi.mp ha i) j).comp (t,x) contDiffAt_snd)).mul
          (hh.mul ((((hi (EuclideanSpace.basisFun (Fin 4) ℝ i)).mul
            (hi (EuclideanSpace.basisFun (Fin 4) ℝ j))).mul hd2).sub (contDiffAt_const.mul hd)))
      exact hk.smul (contDiffAt_const (c := ContinuousLinearMap.id ℝ W))
    · apply ContDiffAt.sum
      intro i _
      exact ((hh.neg.mul hd).mul (hi (EuclideanSpace.basisFun (Fin 4) ℝ i))).smul ((contDiffAt_pi.mp hb i).comp (t,x) contDiffAt_snd)
  · exact hh.smul (hc.comp (t,x) contDiffAt_snd)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in

lemma cutoff_residual_eq_zero (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (c : P × V → W →L[ℝ] W)
    (χ : V → ℝ) {z : V} (hz : z ∉ tsupport χ) (q : P) (t : ℝ) :
    residual (fun y => CutoffFamilies.principal a χ (q,y))
      (fun y => CutoffFamilies.first a b χ (q,y))
      (fun y => CutoffFamilies.zero a b c χ (q,y)) t z = 0 := by
  have he : χ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp hz
  have hd : fderiv ℝ χ z = 0 := by simpa using he.fderiv_eq (𝕜 := ℝ)
  have hdd (v : V) : fderiv ℝ (fun y => fderiv ℝ χ y v) z = 0 := by
    have he' : (fun y => fderiv ℝ χ y v) =ᶠ[𝓝 z] 0 := by
      filter_upwards [he.fderiv (𝕜 := ℝ)] with y hy
      simpa using congrArg (fun C : V →L[ℝ] ℝ => C v) hy
    simpa using he'.fderiv_eq (𝕜 := ℝ)
  simp [residual,CutoffFamilies.principal,CutoffFamilies.first,CutoffFamilies.zero,
    cutoffPrincipal,cutoffFirst,cutoffZero,he.eq_of_nhds,hd,hdd]

lemma compact_cutoff_matrix (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (c : P × V → W →L[ℝ] W)
    (K : Set P) (hK : IsCompact K) {r : ℝ} (hr : 0 ≤ r)
    (ha : ∀ x ∈ K ×ˢ Metric.closedBall (0 : V) r, ∀ i j, ContDiffAt ℝ ∞ (a i j) x)
    (hb : ∀ x ∈ K ×ˢ Metric.closedBall (0 : V) r, ∀ j, ContDiffAt ℝ ∞ (b j) x)
    (hc : ∀ x ∈ K ×ˢ Metric.closedBall (0 : V) r, ContDiffAt ℝ ∞ c x)
    (ha0 : ∀ q ∈ K, ∀ i j, a i j (q,0) = euclideanPrincipal i j)
    (hda0 : ∀ q ∈ K, ∀ i j, fderiv ℝ (fun z => a i j (q,z)) 0 = 0)
    (hb0 : ∀ q ∈ K, ∀ j, b j (q,0) = 0)
    (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ =ᶠ[𝓝 (0 : V)] 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ z : V, ‖z‖ ≤ r → ∀ t : ℝ, 0 < t →
      ‖residual (fun y => CutoffFamilies.principal a χ (q,y))
        (fun y => CutoffFamilies.first a b χ (q,y))
        (fun y => CutoffFamilies.zero a b c χ (q,y)) t z‖ ≤ C*heat (2*t) z := by
  obtain ⟨C,hC,hb⟩ := CutoffFamilies.compact_cutoff_residual a b c K hK hr ha hb hc ha0 hda0 hb0 χ hχ hχ0
  refine ⟨C,hC,fun q hq z hz t ht => ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (heat_nonneg _ _))
  intro u
  have hh := hb q hq z hz t ht u
  rw [cutoff_gaussian_residual _ _ _ χ hχ ht] at hh
  exact hh

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
local instance residualFamilyMetricTensorNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance residualFamilyMetricTensorNormedSpace :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local irreducible] pulledA pulledB normalFirst normalZero normalDensity
  normalGauge normalPrincipal gaugedFirst gaugedZero

def residualCoordinate (ψ χ : Space → ℝ) (t : ℝ) (x : Space × Space) : W →L[ℝ] W :=
  ψ x.1 • ((normalGauge J α ht p D g B x) ∘L
    NormalHeatResidual.residual
      (fun z => CutoffFamilies.principal (normalPrincipal g B) χ (x.1,z))
      (fun z => CutoffFamilies.first (normalPrincipal g B) (gaugedFirst J α ht p D g B) χ (x.1,z))
      (fun z => CutoffFamilies.zero (normalPrincipal g B) (gaugedFirst J α ht p D g B)
        (gaugedZero J α ht p D g B) χ (x.1,z)) t x.2)

def residualPatch (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)
    (ψ χ : Space → ℝ) (t : ℝ) : Space × Space → W →L[ℝ] W :=
  KernelExtension.push (geometricNormalChart g B hg hB q₀ Bq hBq)
    (residualCoordinate J α ht p D g B ψ χ t)

lemma residualCoordinate_support (ψ χ : Space → ℝ) (t : ℝ) :
    Function.support (residualCoordinate J α ht p D g B ψ χ t) ⊆
      Function.support ψ ×ˢ tsupport χ := by
  classical
  intro x hx
  constructor
  · intro h
    apply hx
    simp only [residualCoordinate,h,zero_smul]
  · by_contra hz
    apply hx
    rw [residualCoordinate,NormalHeatResidual.cutoff_residual_eq_zero _ _ _ χ hz]
    simp

lemma residualCoordinate_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (ψ χ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    {t : ℝ} (htpos : 0 < t) {x : Space × Space} (hx : x ∈ gaugedDomain J α ht p D g B) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) =>
      residualCoordinate J α ht p D g B ψ χ v.1 v.2) (t,x) := by
  have ha := fun i j => normalPrincipal_smooth g B hg hB hx.1.2 i j
  have hb := fun j => gaugedFirst_smooth J α ht p D g B hs hg hB hx j
  have hc := gaugedZero_smooth J α ht p D g B hs hg hB hx
  exact (hψ.contDiffAt.comp (t,x) contDiffAt_snd.fst).smul
    (((normalGauge_smooth J α ht p D g B hs hg hB hx.2).comp (t,x) contDiffAt_snd).clm_comp
      (NormalHeatResidual.residual_family_smooth _ _ _ (ne_of_gt htpos)
        (CutoffFamilies.principal_smooth _ χ hχ ha)
        (CutoffFamilies.first_smooth _ _ χ hχ ha hb)
        (CutoffFamilies.zero_smooth _ _ _ χ hχ ha hb hc)))

lemma residualMatrix_gaussian (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (χ : Space → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ =ᶠ[𝓝 (0 : Space)] 1)
    (K : Set Space) (hK : IsCompact K)
    (hactual : ∀ q ∈ K, ActualData J α ht p D q g B)
    {r : ℝ} (hr : 0 ≤ r)
    (hsub : K ×ˢ Metric.closedBall (0 : Space) r ⊆ gaugedDomain J α ht p D g B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ z : Space, ‖z‖ ≤ r → ∀ t : ℝ, 0 < t →
      ‖NormalHeatResidual.residual
        (fun y => CutoffFamilies.principal (normalPrincipal g B) χ (q,y))
        (fun y => CutoffFamilies.first (normalPrincipal g B) (gaugedFirst J α ht p D g B) χ (q,y))
        (fun y => CutoffFamilies.zero (normalPrincipal g B) (gaugedFirst J α ht p D g B)
          (gaugedZero J α ht p D g B) χ (q,y)) t z‖ ≤ C*FlatHeat.heat (2*t) z := by
  classical
  have hp (q : Space) (hq : q ∈ K) := (hactual q hq).jets J α hs ht p D q g B hg hB
  obtain ⟨C,hC,hb⟩ := NormalHeatResidual.compact_cutoff_matrix
    (normalPrincipal g B) (gaugedFirst J α ht p D g B) (gaugedZero J α ht p D g B)
    K hK hr
    (fun x hx => normalPrincipal_smooth g B hg hB (hsub hx).1.2)
    (fun x hx => gaugedFirst_smooth J α ht p D g B hs hg hB (hsub hx))
    (fun x hx => gaugedZero_smooth J α ht p D g B hs hg hB (hsub hx))
    (fun q hq i j => by
      simpa only [normalPrincipal,NormalHeatResidual.euclideanPrincipal] using ((hp q hq).2.2.2.2.2.1 i j).2.1)
    (fun q hq i j => by
      simpa only [normalPrincipal] using ((hp q hq).2.2.2.2.2.1 i j).2.2)
    (fun q hq j => gaugedFirst_center J α ht p D g B hs hg hB (hactual q hq) j) χ hχ hχ0
  exact ⟨C,hC,hb⟩

lemma norm_smul_comp_le {s K : ℝ} (hs : 0 ≤ s ∧ s ≤ 1) (U R : W →L[ℝ] W)
    (hU : ‖U‖ ≤ 1) (hR : ‖R‖ ≤ K) : ‖s • (U ∘L R)‖ ≤ K := by
  have hK : 0 ≤ K := (norm_nonneg _).trans hR
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs.1]
  calc
    _ ≤ s * (‖U‖ * ‖R‖) := mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) hs.1
    _ ≤ s * (1*K) := mul_le_mul_of_nonneg_left (mul_le_mul hU hR (norm_nonneg _) zero_le_one) hs.1
    _ ≤ K := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hs.2 hK

lemma residualCoordinate_gaussian (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (ψ χ : Space → ℝ) (hψ : ∀ q, 0 ≤ ψ q ∧ ψ q ≤ 1)
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ =ᶠ[𝓝 (0 : Space)] 1)
    (K : Set Space) (hK : IsCompact K) (hψK : Function.support ψ ⊆ K)
    (hactual : ∀ q ∈ K, ActualData J α ht p D q g B)
    {r : ℝ} (hr : 0 ≤ r) (hχr : tsupport χ ⊆ Metric.closedBall (0 : Space) r)
    (hsub : K ×ˢ Metric.closedBall (0 : Space) r ⊆ gaugedDomain J α ht p D g B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ q z : Space,
      ‖residualCoordinate J α ht p D g B ψ χ t (q,z)‖ ≤ C*FlatHeat.heat (2*t) z := by

  classical
  obtain ⟨C,hC,hb⟩ := residualMatrix_gaussian J α ht p D g B hs hg hB χ hχ hχ0
    K hK hactual hr hsub
  refine ⟨C,hC,fun t htpos q z => ?_⟩
  by_cases he : residualCoordinate J α ht p D g B ψ χ t (q,z) = 0
  · simpa only [he,norm_zero] using mul_nonneg hC (FlatHeat.heat_nonneg (2*t) z)
  have hh := residualCoordinate_support J α ht p D g B ψ χ t he
  have hqK := hψK hh.1
  have hzr : ‖z‖ ≤ r := by simpa using hχr hh.2
  exact norm_smul_comp_le (hψ q) _ _
    (normalGauge_norm_le J α ht p D g B hg hB hs (hactual q hqK) z)
    (hb q hqK z hzr t htpos)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
