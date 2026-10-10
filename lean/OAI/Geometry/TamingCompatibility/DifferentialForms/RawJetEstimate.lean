import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.InteriorEstimateApply
import OAI.Geometry.TamingCompatibility.DifferentialForms.ClosedLiftData
import OAI.Geometry.TamingCompatibility.DifferentialForms.JetOperator

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def coordinateTwoJet (u : 𝓢(Space,C 2)) (x : Space) : ℝ :=
  ‖u x‖ + ∑ i : Fin 4, ‖(∂_{EuclideanEnergy.e i} u) x‖ +
    ∑ i : Fin 4, ∑ j : Fin 4, ‖(∂_{EuclideanEnergy.e j} (∂_{EuclideanEnergy.e i} u)) x‖

lemma coordinateTwoJet_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : 𝓢(Space,ComplexMatrix.C 2)) (x : Space),
    coordinateTwoJet u x ≤ C * ‖schwartzToH (5:ℝ) u‖ := by
  have hd : Module.finrank ℝ Space < 2*((5:ℝ)-1-1) := by norm_num [Space]
  exact schwartz_two_jet_bound EuclideanEnergy.e 5 hd

lemma raw_two_jet_estimate (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hq : q ∈ U) :
    ∃ W V : Set Space, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ W ∧
      ∀ (χ : 𝓢(Space,ℂ)), HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ V →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (f a : antiPre A J α hs ht) (g : 𝓢(Space,EuclideanEnergy.Pair)),
        (∀ z ∈ W, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z) →
        (∀ v : antiEnergy A J α hs ht,
          ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht a),weakDelta A J α hs ht v⟫ =
            ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) →
        ∀ x : Space, coordinateTwoJet (localizedRawSchwartz A J α hs ht D hD p τ χ a) x ≤
          K * (‖antiToEnergy A J α hs ht a‖ +
            ‖schwartzToH (3:ℝ) (SchwartzMap.postcompCLM (embed 2) g)‖) := by
  obtain ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,hest⟩ :=
    raw_schwartz_estimate A J α hs ht D hD p τ hU hUD hτ q hq
  refine ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,fun χ hc hχV => ?_⟩
  obtain ⟨K,hK,hbound⟩ := hest 3 χ hc hχV
  obtain ⟨C,hC,hjet⟩ := coordinateTwoJet_bound
  refine ⟨C*K,mul_nonneg hC hK,fun f a g hg heq x => ?_⟩
  have hb := hbound f a g hg heq
  have h5 : ((3:ℕ):ℝ)+2 = 5 := by norm_num
  rw [h5] at hb
  simp only [Nat.cast_ofNat] at hb
  dsimp only [Space,EuclideanEnergy.V,ScalarPair.F,ComplexMatrix.C] at hb hjet ⊢
  have hj := hjet (localizedRawSchwartz A J α hs ht D hD p τ χ a) x
  have hm := mul_le_mul_of_nonneg_left hb hC
  have hf := hj.trans hm
  simpa only [mul_assoc] using hf

end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator GeometricAdjoint Set Filter ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

def deltaComplexA (i : Fin 4) (z : Space) : C 2 →L[ℝ] MetricForms.Form Space 1 :=
  (deltaA J α ht p D i z).comp (retract 2)
def deltaComplexB (z : Space) : C 2 →L[ℝ] MetricForms.Form Space 1 :=
  (deltaB J α ht p D z).comp (retract 2)

include hs in
lemma deltaComplexA_smooth (i : Fin 4) : ContDiffOn ℝ ∞ (deltaComplexA J α ht p D i) D.domain :=
  (deltaA_smooth J α hs ht p D i).clm_comp contDiffOn_const
include hs in
lemma deltaComplexB_smooth : ContDiffOn ℝ ∞ (deltaComplexB J α ht p D) D.domain :=
  (deltaB_smooth J α hs ht p D).clm_comp contDiffOn_const

include hs in
lemma delta_local_representation {a : TwoForm X} (ha : IsSmooth a)
    (hanti : antiInvariantPart J a = a) {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ D.domain)
    (u : 𝓢(Space,C 2)) (hrep : ∀ z ∈ U, rawPair J α ht p D a z = retract 2 (u z))
    {z : Space} (hz : z ∈ U) :
    ManifoldForms.pullback (codifferential J α ht a) (extChartAt Model p).symm z =
      JetOperator.firstOrder (deltaComplexA J α ht p D) (deltaComplexB J α ht p D) u z := by
  have he : rawPair J α ht p D a =ᶠ[𝓝 z] fun y => retract 2 (u y) :=
    Filter.mem_of_superset (hU.mem_nhds hz) hrep
  have hfd : fderiv ℝ (rawPair J α ht p D a) z =
      (retract 2).comp (fderiv ℝ (u : Space → C 2) z) := by
    rw [he.fderiv_eq]
    exact ((retract 2).hasFDerivAt.comp z u.differentiableAt.hasFDerivAt).fderiv
  rw [delta_coefficient_expansion J α hs ht p D ha hanti (hUD hz),hfd,hrep z hz]
  simp only [JetOperator.firstOrder,deltaComplexA,deltaComplexB,ContinuousLinearMap.comp_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]

include hs in
lemma ddstar_local_jet {a : TwoForm X} (ha : IsSmooth a)
    (hanti : antiInvariantPart J a = a) {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ D.domain)
    (u : 𝓢(Space,C 2)) (hrep : ∀ z ∈ U, rawPair J α ht p D a z = retract 2 (u z))
    {z : Space} (hz : z ∈ U) :
    ManifoldForms.pullback (exteriorDerivative (codifferential J α ht a))
      (extChartAt Model p).symm z =
        JetOperator.exteriorJet (deltaComplexA J α ht p D) (deltaComplexB J α ht p D) z
          (JetOperator.value u z) := by
  have he : ManifoldForms.pullback (codifferential J α ht a) (extChartAt Model p).symm =ᶠ[𝓝 z]
      JetOperator.firstOrder (deltaComplexA J α ht p D) (deltaComplexB J α ht p D) u := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact delta_local_representation J α hs ht p D ha hanti hU hUD u hrep hy
  rw [pullback_exteriorDerivative _ (codifferential_smooth J α hs ht ha)
    (isOpen_extChartAt_target p) (contMDiffOn_extChartAt_symm p) (D.domain_subset (hUD hz)),
    extDerivWithin_eq_of_mem (isOpen_extChartAt_target p) (D.domain_subset (hUD hz)),he.extDeriv_eq]
  symm
  apply JetOperator.exteriorJet_spec
  · intro i
    exact ((deltaComplexA_smooth J α hs ht p D i).differentiableOn (by simp) z (hUD hz)).differentiableAt
      (D.domain_open.mem_nhds (hUD hz))
  · exact ((deltaComplexB_smooth J α hs ht p D).differentiableOn (by simp) z (hUD hz)).differentiableAt
      (D.domain_open.mem_nhds (hUD hz))

end TamingCompatibility.GeometricChart

end
end

section
noncomputable section
namespace TamingCompatibility.JetOperator
open EuclideanEnergy ContinuousAlternatingMap Set LineDeriv
open scoped SchwartzMap ContDiff LineDeriv
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma schwartz_direction_basis (v : V) (u : 𝓢(V,F)) :
    ∂_{v} u = ∑ i : Fin 4, (v i) • ∂_{e i} u := by
  have he : v = ∑ i : Fin 4, v i • e i := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,e] using
      ((EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr v).symm
  conv_lhs => rw [he]
  simp only [lineDerivOp_left_sum,lineDerivOp_left_smul]

def directionOne (v : V) : Jet F →L[ℝ] F := ∑ i : Fin 4, (v i) • projOne i

def directionTwo (v w : V) : Jet F →L[ℝ] F :=
  ∑ i : Fin 4, ∑ j : Fin 4, (v i * w j) • projTwo i j

lemma directionOne_value (v : V) (u : 𝓢(V,F)) (x : V) :
    directionOne v (value u x) = (∂_{v} u) x := by
  rw [schwartz_direction_basis]
  simp only [directionOne,value,projOne,_root_.sum_apply,_root_.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']

lemma directionTwo_value (v w : V) (u : 𝓢(V,F)) (x : V) :
    directionTwo v w (value u x) = (∂_{w} (∂_{v} u)) x := by
  rw [schwartz_direction_basis v u]
  simp only [lineDerivOp_sum,lineDerivOp_smul]
  simp_rw [schwartz_direction_basis w]
  simp only [Finset.smul_sum,smul_smul,directionTwo,value,projTwo,
    _root_.sum_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,ContinuousLinearMap.coe_snd']

def linearTransport (L : V ≃L[ℝ] V) : Jet F →L[ℝ] Jet F :=
  projZero.prod ((ContinuousLinearMap.pi (fun i : Fin 4 => directionOne (L (e i)))).prod
    (ContinuousLinearMap.pi (fun i : Fin 4 =>
      ContinuousLinearMap.pi (fun j : Fin 4 => directionTwo (L (e i)) (L (e j))))))

lemma linearTransport_value (L : V ≃L[ℝ] V) (u : 𝓢(V,F)) (x : V) :
    linearTransport L (value u (L x)) =
      value (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ L u) x := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext i
      change directionOne (L (e i)) (value u (L x)) = _
      rw [directionOne_value]
      simp only [value,SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply]
    · funext i j
      change directionTwo (L (e i)) (L (e j)) (value u (L x)) = _
      rw [directionTwo_value]
      simp only [value,SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply]

lemma value_recover_linear (L : V ≃L[ℝ] V) (u : 𝓢(V,F)) (x : V) :
    value u x = linearTransport L
      (value (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ L.symm u) (L x)) := by
  rw [linearTransport_value]
  congr 1
  ext y
  simp

lemma linear_output_scaled_bound {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : Jet F →L[ℝ] G) (L : V ≃L[ℝ] V) (u : 𝓢(V,F)) (z : V)
    {r M : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (h : let U := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ L.symm u
      r*‖U (L z)‖ + r^2*∑ i, ‖(∂_{e i} U) (L z)‖ +
        r^3*∑ i, ∑ j, ‖(∂_{e j} (∂_{e i} U)) (L z)‖ ≤ M) :
    r^3*‖T (value u z)‖ ≤ ‖T.comp (linearTransport L)‖*M := by
  let U := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ L.symm u
  have h13 : r^3 ≤ r := by nlinarith [sq_nonneg r, mul_le_mul_of_nonneg_left hr1 (sq_nonneg r)]
  have h23 : r^3 ≤ r^2 := by nlinarith [mul_le_mul_of_nonneg_left hr1 (sq_nonneg r)]
  have hn : r^3*‖value U (L z)‖ ≤ M := by
    apply (mul_le_mul_of_nonneg_left (value_norm U (L z)) (by positivity : 0 ≤ r^3)).trans
    have ha := mul_le_mul_of_nonneg_right h13 (norm_nonneg (U (L z)))
    have hb := mul_le_mul_of_nonneg_right h23
      (show 0 ≤ ∑ i : Fin 4, ‖(∂_{e i} U) (L z)‖ from Finset.sum_nonneg (fun i _ => norm_nonneg ((∂_{e i} U) (L z))))
    dsimp only at h
    change r*‖U (L z)‖ + r^2*∑ i, ‖(∂_{e i} U) (L z)‖ +
        r^3*∑ i, ∑ j, ‖(∂_{e j} (∂_{e i} U)) (L z)‖ ≤ M at h
    nlinarith only [ha,hb,h]
  rw [value_recover_linear L u z]
  change r^3*‖(T.comp (linearTransport L)) (value U (L z))‖ ≤ _
  calc
    _ ≤ r^3*(‖T.comp (linearTransport L)‖*‖value U (L z)‖) :=
      mul_le_mul_of_nonneg_left ((T.comp (linearTransport L)).le_opNorm _) (by positivity)
    _ = ‖T.comp (linearTransport L)‖*(r^3*‖value U (L z)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
end TamingCompatibility.JetOperator

end
end

end
end
end

end OAI
