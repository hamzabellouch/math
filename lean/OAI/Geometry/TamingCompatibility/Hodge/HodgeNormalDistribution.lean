import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.AntiEnergyWeak
import OAI.Geometry.TamingCompatibility.Charts.LocalFormalAdjoint
import OAI.Geometry.TamingCompatibility.Hodge.HodgeNormalEnergy

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume LocalFormalAdjoint
open Set Filter MeasureTheory LineDeriv
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)

lemma firstOrder_local (a : Fin 4 → 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q))
    (b : 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q)) (s : 𝓢(Space,HodgeNormalSymbol.W))
    (f : Space → HodgeNormalSymbol.W) {z : Space} (he : (s : Space → _) =ᶠ[𝓝 z] f)
    (ha : ∀ i, a i z = normalA J α ht p D i z) (hb : b z = normalB J α ht p D z) :
    firstOrder EuclideanEnergy.e a b s z = normalOperator J α ht p D f z := by
  simp only [firstOrder,_root_.add_apply,_root_.sum_apply,ContinuousLinearMap.comp_apply,
    multiply_apply,lineDerivOpCLM_apply,SchwartzMap.lineDerivOp_apply_eq_fderiv,
    ha,hb,he.fderiv_eq,he.eq_of_nhds,normalOperator]

lemma firstOrder_zero_off (a : Fin 4 → 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q))
    (b : 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q)) (q : 𝓢(Space,HodgeNormalSymbol.W))
    {z : Space} (hz : z ∉ tsupport q) : firstOrder EuclideanEnergy.e a b q z = 0 := by
  have hd (i : Fin 4) : (∂_{EuclideanEnergy.e i} q : 𝓢(Space,HodgeNormalSymbol.W)) z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hz (SchwartzMap.tsupport_lineDerivOp_subset _ _ h))
  simp only [firstOrder,_root_.add_apply,_root_.sum_apply,ContinuousLinearMap.comp_apply,
    multiply_apply,lineDerivOpCLM_apply,hd,image_eq_zero_of_notMem_tsupport hz,map_zero,
    Finset.sum_const_zero,add_zero]

variable [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X)
include hs in
lemma chart_energy_local {u : TwoForm X} (hu : IsSmooth u)
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ D.domain)
    (a : Fin 4 → 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q))
    (b : 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q)) (ρ : 𝓢(Space,ℝ))
    (ha : ∀ z ∈ U, ∀ i, a i z = normalA J α ht p D i z)
    (hb : ∀ z ∈ U, b z = normalB J α ht p D z)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p z)
    (s q : 𝓢(Space,HodgeNormalSymbol.W))
    (hsU : ∀ z ∈ U, s z = rawVector J α ht p D u z)
    (hqc : HasCompactSupport (q : Space → _)) (hqU : tsupport q ⊆ U) :
    (∫ z, ρ z * ⟪firstOrder EuclideanEnergy.e a b s z,firstOrder EuclideanEnergy.e a b q z⟫) =
      ∫ x, energyPairing J α ht u (manifoldTest J α ht p D q) x ∂geometricVolume A J α := by
  rw [normal_energy_integral J α ht hs p D A hu (q.smooth ⊤) hqc (hqU.trans hUD)]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ tsupport q
  · have hzU := hqU hz
    have he : (s : Space → _) =ᶠ[𝓝 z] rawVector J α ht p D u := by
      filter_upwards [hU.mem_nhds hzU] with y hy
      exact hsU y hy
    rw [firstOrder_local J α ht p D a b s _ he (ha z hzU) (hb z hzU),
      firstOrder_local J α ht p D a b q q Filter.EventuallyEq.rfl (ha z hzU) (hb z hzU),hρ z hzU]
  · rw [firstOrder_zero_off a b q hz,normalOperator_zero_off J α ht p D q hz]
    simp
end TamingCompatibility.HodgeChart

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def hodgeDelta : PreL2 A J α hs ht true →ₗ[ℝ] PreL2 A J α hs ht false where
  toFun a := ⟨codifferential J α ht a.val,GeometricAdjoint.codifferential_smooth J α hs ht a.property⟩
  map_add' a b := by
    apply Subtype.ext
    change codifferential J α ht (a.val+b.val) =
      codifferential J α ht a.val + codifferential J α ht b.val
    rw [codifferential,hodgeStar_add,
      exteriorDerivative_add (starTwo_smooth J α hs ht a.property) (starTwo_smooth J α hs ht b.property),
      starThree_add,neg_add]
    rfl
  map_smul' c a := by
    apply Subtype.ext
    change codifferential J α ht (c • a.val) = c • codifferential J α ht a.val
    rw [codifferential,hodgeStar_smul,exteriorDerivative_smul,starThree_smul]
    exact (smul_neg c _).symm

abbrev HodgeDerivativePair := WithLp 2 (L2 A J α hs ht false × L2 A J α hs ht false)
abbrev HodgeGraphSpace := WithLp 2 (L2 A J α hs ht true × HodgeDerivativePair A J α hs ht)

def hodgeGraph : PreL2 A J α hs ht true →ₗ[ℝ] HodgeGraphSpace A J α hs ht :=
  (WithLp.linearEquiv 2 ℝ _).symm.toLinearMap.comp <|
    (smoothL2 A J α hs ht true).toLinearMap.prod
      ((WithLp.linearEquiv 2 ℝ _).symm.toLinearMap.comp <|
        ((smoothL2 A J α hs ht false).toLinearMap.comp (hodgeDelta A J α hs ht)).prod
          ((smoothL2 A J α hs ht false).toLinearMap.comp
            ((hodgeDelta A J α hs ht).comp (preStar A J α hs ht).toLinearMap)))

def hodgeEnergy : Submodule ℝ (HodgeGraphSpace A J α hs ht) :=
  (LinearMap.range (hodgeGraph A J α hs ht)).topologicalClosure

instance hodgeEnergy_complete : CompleteSpace (hodgeEnergy A J α hs ht) :=
  ((LinearMap.range (hodgeGraph A J α hs ht)).isClosed_topologicalClosure).completeSpace_coe

lemma hodgeGraph_weak (a : PreL2 A J α hs ht true) (b : PreL2 A J α hs ht false) :
    ⟪testDerivative A J α hs ht b,(hodgeGraph A J α hs ht a).fst⟫ =
      ⟪smoothL2 A J α hs ht false b,(hodgeGraph A J α hs ht a).snd.fst⟫ := by
  let db : PreL2 A J α hs ht true := ⟨exteriorDerivative b.val,b.property.exteriorDerivative⟩
  have h := GeometricAdjoint.formal_adjoint A J α hs ht b.property a.property
  have he : l2Pairing A J α ht db a = l2Pairing A J α ht b (hodgeDelta A J α hs ht a) := h
  exact ((smoothL2 A J α hs ht true).inner_map_map db a).trans
    ((preL2_inner A J α hs ht true db a).trans (he.trans
      (((smoothL2 A J α hs ht false).inner_map_map b (hodgeDelta A J α hs ht a)).trans
        (preL2_inner A J α hs ht false b (hodgeDelta A J α hs ht a))).symm))

lemma hodgeGraph_weak_star (a : PreL2 A J α hs ht true) (b : PreL2 A J α hs ht false) :
    ⟪l2Star A J α hs ht (testDerivative A J α hs ht b),(hodgeGraph A J α hs ht a).fst⟫ =
      ⟪smoothL2 A J α hs ht false b,(hodgeGraph A J α hs ht a).snd.snd⟫ := by
  rw [l2Star_self_adjoint]
  change ⟪testDerivative A J α hs ht b,l2Star A J α hs ht (smoothL2 A J α hs ht true a)⟫ = _
  rw [l2Star_smooth]
  exact hodgeGraph_weak A J α hs ht (preStar A J α hs ht a) b

lemma hodgeEnergy_weak (u : hodgeEnergy A J α hs ht) (b : PreL2 A J α hs ht false) :
    ⟪testDerivative A J α hs ht b,u.val.fst⟫ =
      ⟪smoothL2 A J α hs ht false b,u.val.snd.fst⟫ := by
  have hc : _root_.IsClosed {v : HodgeGraphSpace A J α hs ht |
      ⟪testDerivative A J α hs ht b,v.fst⟫ = ⟪smoothL2 A J α hs ht false b,v.snd.fst⟫} :=
    isClosed_eq (continuous_const.inner (WithLp.fstL 2 ℝ _ _).continuous)
      (continuous_const.inner ((WithLp.fstL 2 ℝ _ _).continuous.comp (WithLp.sndL 2 ℝ _ _).continuous))
  exact (closure_minimal (by rintro _ ⟨a,rfl⟩; exact hodgeGraph_weak A J α hs ht a b) hc) u.property

lemma hodgeEnergy_weak_star (u : hodgeEnergy A J α hs ht) (b : PreL2 A J α hs ht false) :
    ⟪l2Star A J α hs ht (testDerivative A J α hs ht b),u.val.fst⟫ =
      ⟪smoothL2 A J α hs ht false b,u.val.snd.snd⟫ := by
  have hc : _root_.IsClosed {v : HodgeGraphSpace A J α hs ht |
      ⟪l2Star A J α hs ht (testDerivative A J α hs ht b),v.fst⟫ = ⟪smoothL2 A J α hs ht false b,v.snd.snd⟫} :=
    isClosed_eq (continuous_const.inner (WithLp.fstL 2 ℝ _ _).continuous)
      (continuous_const.inner ((WithLp.sndL 2 ℝ _ _).continuous.comp (WithLp.sndL 2 ℝ _ _).continuous))
  exact (closure_minimal (by rintro _ ⟨a,rfl⟩; exact hodgeGraph_weak_star A J α hs ht a b) hc) u.property

def hodgeInclusion : hodgeEnergy A J α hs ht →L[ℝ] L2 A J α hs ht true :=
  (WithLp.fstL 2 ℝ _ _) ∘L (hodgeEnergy A J α hs ht).subtypeL

def hodgeWeakDerivative : hodgeEnergy A J α hs ht →L[ℝ] HodgeDerivativePair A J α hs ht :=
  (WithLp.sndL 2 ℝ _ _) ∘L (hodgeEnergy A J α hs ht).subtypeL

lemma hodgeInclusion_injective : Function.Injective (hodgeInclusion A J α hs ht) := by
  suffices hz : ∀ u : hodgeEnergy A J α hs ht, hodgeInclusion A J α hs ht u = 0 → u = 0 by
    intro u v huv
    exact sub_eq_zero.mp (hz (u-v) (by rw [map_sub,sub_eq_zero.mpr huv]))
  intro u hu
  change u.val.fst = 0 at hu
  have hz (w : L2 A J α hs ht false)
      (hw : ∀ b : PreL2 A J α hs ht false, ⟪smoothL2 A J α hs ht false b,w⟫ = 0) : w = 0 := by
    have hall : ∀ v : L2 A J α hs ht false, ⟪v,w⟫ = 0 := fun v =>
      (smoothL2_dense A J α hs ht false).induction_on v
        (isClosed_eq (continuous_id.inner continuous_const) continuous_const) hw
    exact inner_self_eq_zero.mp (hall w)
  have h1 := hz u.val.snd.fst (fun b => by rw [← hodgeEnergy_weak A J α hs ht u b,hu,inner_zero_right])
  have h2 := hz u.val.snd.snd (fun b => by rw [← hodgeEnergy_weak_star A J α hs ht u b,hu,inner_zero_right])
  apply Subtype.ext
  apply (WithLp.linearEquiv 2 ℝ _).injective
  apply Prod.ext hu
  apply (WithLp.linearEquiv 2 ℝ _).injective
  exact Prod.ext h1 h2

def hodgeSmooth : PreL2 A J α hs ht true →ₗ[ℝ] hodgeEnergy A J α hs ht :=
  (hodgeGraph A J α hs ht).codRestrict _ (fun a => subset_closure ⟨a,rfl⟩)

@[simp] lemma hodgeInclusion_smooth (a : PreL2 A J α hs ht true) :
    hodgeInclusion A J α hs ht (hodgeSmooth A J α hs ht a) = smoothL2 A J α hs ht true a := rfl

lemma hodgeInclusion_dense : DenseRange (hodgeInclusion A J α hs ht) :=
  (smoothL2_dense A J α hs ht true).mono (by rintro _ ⟨a,rfl⟩; exact ⟨hodgeSmooth A J α hs ht a,rfl⟩)
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
