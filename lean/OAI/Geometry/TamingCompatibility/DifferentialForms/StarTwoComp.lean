import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.ChartMetric
import OAI.Geometry.TamingCompatibility.DifferentialForms.UnitaryVectors

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.MetricHodge
open ContinuousAlternatingMap MetricForms MetricModel
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D]

lemma starTwo_comp (g : Metric E) (h : Metric D) (L : E ≃L[ℝ] D)
    (hL : ∀ u v, h.bilinear (L u) (L v) = g.bilinear u v)
    (hdim : Module.finrank ℝ E = 4) (J : E →L[ℝ] E) (K : D →L[ℝ] D)
    (hJ : ∀ u, L (J u) = K (L u)) (F α : MetricForms.Form D 2) :
    starTwo g J (F.compContinuousLinearMap L.toContinuousLinearMap) (α.compContinuousLinearMap L.toContinuousLinearMap) =
      (starTwo h K F α).compContinuousLinearMap L.toContinuousLinearMap := by
  unfold starTwo
  rw [pairing_two_comp g h L hL hdim]
  ext v
  change _ - α (fun i => L (J (v i))) = _ - α (fun i => K (L (v i)))
  simp only [hJ]
  rfl

lemma starThree_comp (g : Metric E) (h : Metric D) (L : E ≃L[ℝ] D)
    (hL : ∀ u v, h.bilinear (L u) (L v) = g.bilinear u v)
    (hdim : Module.finrank ℝ E = 4) (F : MetricForms.Form D 2) (α : MetricForms.Form D 3) :
    starThree g (F.compContinuousLinearMap L.toContinuousLinearMap) (α.compContinuousLinearMap L.toContinuousLinearMap) =
      (starThree h F α).compContinuousLinearMap L.toContinuousLinearMap := by
  ext v
  have hv : v = ![v 0] := by ext i; fin_cases i; rfl
  rw [hv,starThree_apply]
  have hc : ((starThree h F α).compContinuousLinearMap L.toContinuousLinearMap) ![v 0] =
      starThree h F α ![L (v 0)] := by rfl
  rw [hc,starThree_apply,volumeSquare_comp]
  have he : ((ExteriorForms.volumeSquare F).compContinuousLinearMap L.toContinuousLinearMap).curryLeft (v 0) =
      ((ExteriorForms.volumeSquare F).curryLeft (L (v 0))).compContinuousLinearMap L.toContinuousLinearMap := by
    ext w
    change ExteriorForms.volumeSquare F (fun i => L (Matrix.vecCons (v 0) w i)) =
      ExteriorForms.volumeSquare F (Matrix.vecCons (L (v 0)) (fun i => L (w i)))
    congr 1
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [he,pairing_three_comp g h L hL hdim]

variable (g : Metric E) (J : E →L[ℝ] E)
  (hJ : ∀ u, J (J u) = -u)
  (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
  (hdim : Module.finrank ℝ E = 4) (F : MetricForms.Form E 2)
  (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)

include hJ horth hdim hF
lemma starTwo_self_adjoint (α β : MetricForms.Form E 2) :
    pairing g (starTwo g J F α) β = pairing g α (starTwo g J F β) := by
  change FormMetric.pairing (formEquiv g 2 (starTwo g J F α)) (formEquiv g 2 β) =
    FormMetric.pairing (formEquiv g 2 α) (formEquiv g 2 (starTwo g J F β))
  rw [formEquiv_starTwo g J horth,formEquiv_starTwo g J horth]
  exact HermitianHodge.star_self_adjoint (isometry g J horth) hJ
    ((finrank_model g).trans hdim) (formEquiv g 2 F) hF _ _

lemma starTwo_antiInvariant (α : MetricForms.Form E 2) :
    starTwo g J F ((1/2 : ℝ) • (α - α.compContinuousLinearMap J)) =
      (1/2 : ℝ) • (α - α.compContinuousLinearMap J) := by
  apply (formEquiv g 2).injective
  rw [formEquiv_starTwo g J horth]
  have he : formEquiv g 2 ((1/2 : ℝ) • (α - α.compContinuousLinearMap J)) =
      GeometricSymbol.antiInvariant (isometry g J horth).toContinuousLinearMap (formEquiv g 2 α) := by
    ext v
    rfl
  rw [he]
  exact HermitianHodge.star_antiInvariant (isometry g J horth) hJ
    ((finrank_model g).trans hdim) (formEquiv g 2 F) hF _
end TamingCompatibility.MetricHodge

namespace TamingCompatibility.ManifoldHodge
open Bundle ContinuousAlternatingMap ManifoldVolume
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

local instance (x : X) : NormedAddCommGroup (TangentSpace Model x) :=
  inferInstanceAs (NormedAddCommGroup Space)
local instance (x : X) : NormedSpace ℝ (TangentSpace Model x) :=
  inferInstanceAs (NormedSpace ℝ Space)
local instance (x : X) : FiniteDimensional ℝ (TangentSpace Model x) :=
  inferInstanceAs (FiniteDimensional ℝ Space)

def tangentMetric (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (x : X) :
    MetricModel.Metric (TangentSpace Model x) where
  bilinear := associatedBilinear J (invariantPart J α) x
  symm := (invariantPart_isInvariant J α).associatedBilinear_symm x
  positive := (tames_invariantPart ht).associatedBilinear_pos x

def starTwo (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (β : TwoForm X) : TwoForm X :=
  fun x => MetricHodge.starTwo (tangentMetric J α ht x) (J.endomorphism x) (invariantPart J α x) (β x)

def starThree (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (β : ManifoldForms.Form X 3) : ManifoldForms.Form X 1 :=
  fun x => MetricHodge.starThree (tangentMetric J α ht x) (invariantPart J α x) (β x)

lemma starTwo_square (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (β : TwoForm X) :
    starTwo J α ht (starTwo J α ht β) = β := by
  funext x
  exact MetricHodge.starTwo_square (tangentMetric J α ht x) (J.endomorphism x) (J.square x)
    ((invariantPart_isInvariant J α).associatedBilinear_hermitian x)
    (by change Module.finrank ℝ Space = 4; simp [Space]) (invariantPart J α x)
    (fun u v => (associatedBilinear_invariantPart_fundamental J α x u v).symm) (β x)

lemma starTwo_antiInvariant (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (β : TwoForm X) :
    starTwo J α ht (antiInvariantPart J β) = antiInvariantPart J β := by
  funext x
  exact MetricHodge.starTwo_antiInvariant (tangentMetric J α ht x) (J.endomorphism x) (J.square x)
    ((invariantPart_isInvariant J α).associatedBilinear_hermitian x)
    (by change Module.finrank ℝ Space = 4; simp [Space]) (invariantPart J α x)
    (fun u v => (associatedBilinear_invariantPart_fundamental J α x u v).symm) (β x)

lemma starThree_eq_zero (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (β : ManifoldForms.Form X 3) : starThree J α ht β = 0 ↔ β = 0 := by
  constructor
  · intro h
    funext x
    exact (MetricHodge.starThree_eq_zero (tangentMetric J α ht x) (J.endomorphism x) (J.square x)
      ((invariantPart_isInvariant J α).associatedBilinear_hermitian x)
      (by change Module.finrank ℝ Space = 4; simp [Space]) (invariantPart J α x)
      (fun u v => (associatedBilinear_invariantPart_fundamental J α x u v).symm) (β x)).mp (congrFun h x)
  · intro h
    subst β
    funext x
    exact MetricHodge.starThree_zero _ _

def inverseChartEquiv (p : X) (z : Space) (hz : z ∈ (extChartAt Model p).target) :
    Space ≃L[ℝ] TangentSpace Model ((extChartAt Model p).symm z) :=
  ((trivializationAt Space (TangentSpace Model) p).continuousLinearEquivAt ℝ
    ((extChartAt Model p).symm z) (by
      simpa only [TangentBundle.trivializationAt_baseSet,extChartAt_source] using
        (extChartAt Model p).map_target hz)).symm

lemma inverseChartEquiv_coe (p : X) (z : Space) (hz : z ∈ (extChartAt Model p).target) :
    (inverseChartEquiv p z hz).toContinuousLinearMap = mfderiv Model Model (extChartAt Model p).symm z := by
  rw [inverseChart_derivative p hz]
  exact Trivialization.symm_continuousLinearEquivAt_eq' _ _

def flatMetric : MetricModel.Metric Space where
  bilinear := innerSL ℝ
  symm := fun u v => real_inner_comm v u
  positive := fun _ h => real_inner_self_pos.mpr h

def coordinateMetric (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) (z : Space) : MetricModel.Metric Space := by
  classical
  exact if hz : z ∈ (extChartAt Model p).target then
    ⟨chartMetric J α p z, chartMetric_symm J α p hz, chartMetric_pos J α ht p hz⟩
  else flatMetric

lemma coordinateMetric_bilinear (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    (coordinateMetric J α ht p z).bilinear = chartMetric J α p z := by
  simp only [coordinateMetric,dite_eq_left hz]

lemma coordinateMetric_pullback (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) (u v : Space) :
    (tangentMetric J α ht ((extChartAt Model p).symm z)).bilinear
      (inverseChartEquiv p z hz u) (inverseChartEquiv p z hz v) =
        (coordinateMetric J α ht p z).bilinear u v := by
  rw [coordinateMetric_bilinear J α ht p hz,chartMetric_derivative J α p hz]
  change associatedBilinear J (invariantPart J α) _
    ((inverseChartEquiv p z hz).toContinuousLinearMap u) ((inverseChartEquiv p z hz).toContinuousLinearMap v) = _
  rw [inverseChartEquiv_coe]
  rfl

def coordinateJ (J : AlmostComplexStructure X) (p : X) (z : Space) : Space →L[ℝ] Space :=
  SmoothAlmostComplex.coord
    (⟨J.endomorphism,J.square,J.smooth⟩ : SmoothAlmostComplex.AlmostComplexStructure X)
    (trivializationAt Space (TangentSpace Model) p) ((extChartAt Model p).symm z)

lemma coordinateJ_conjugate (J : AlmostComplexStructure X) (p : X) {z : Space}
    (hz : z ∈ (extChartAt Model p).target) (u : Space) :
    coordinateJ J p z u = (inverseChartEquiv p z hz).symm
      (J.endomorphism ((extChartAt Model p).symm z) (inverseChartEquiv p z hz u)) := by
  let te := trivializationAt Space (TangentSpace Model) p
  have hy : (extChartAt Model p).symm z ∈ te.baseSet := by
    simpa only [te,TangentBundle.trivializationAt_baseSet,extChartAt_source] using
      (extChartAt Model p).map_target hz
  change te.continuousLinearMapAt ℝ _ (J.endomorphism _ (te.symmL ℝ _ u)) = _
  simp only [inverseChartEquiv,ContinuousLinearEquiv.symm_symm,
    Trivialization.coe_continuousLinearEquivAt_eq,Trivialization.symm_continuousLinearEquivAt_eq]
  rfl

lemma coordinateJ_intertwine (J : AlmostComplexStructure X) (p : X) {z : Space}
    (hz : z ∈ (extChartAt Model p).target) (u : Space) :
    inverseChartEquiv p z hz (coordinateJ J p z u) =
      J.endomorphism ((extChartAt Model p).symm z) (inverseChartEquiv p z hz u) := by
  rw [coordinateJ_conjugate J p hz,ContinuousLinearEquiv.apply_symm_apply]

lemma coordinateJ_square (J : AlmostComplexStructure X) (p : X) {z : Space}
    (hz : z ∈ (extChartAt Model p).target) (u : Space) : coordinateJ J p z (coordinateJ J p z u) = -u := by
  apply (inverseChartEquiv p z hz).injective
  rw [coordinateJ_intertwine J p hz,coordinateJ_intertwine J p hz,J.square,map_neg]

lemma coordinateMetric_hermitian (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) (u v : Space) :
    (coordinateMetric J α ht p z).bilinear (coordinateJ J p z u) (coordinateJ J p z v) =
      (coordinateMetric J α ht p z).bilinear u v := by
  rw [← coordinateMetric_pullback J α ht p hz,← coordinateMetric_pullback J α ht p hz,
    coordinateJ_intertwine J p hz,coordinateJ_intertwine J p hz]
  exact (invariantPart_isInvariant J α).associatedBilinear_hermitian _ _ _

lemma pullback_starTwo (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (β : TwoForm X) (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    ManifoldForms.pullback (starTwo J α ht β) (extChartAt Model p).symm z =
      MetricHodge.starTwo (coordinateMetric J α ht p z) (coordinateJ J p z)
        (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm z)
        (ManifoldForms.pullback β (extChartAt Model p).symm z) := by
  have he := MetricHodge.starTwo_comp (coordinateMetric J α ht p z)
    (tangentMetric J α ht ((extChartAt Model p).symm z)) (inverseChartEquiv p z hz)
    (coordinateMetric_pullback J α ht p hz) (by simp [Space])
    (coordinateJ J p z) (J.endomorphism ((extChartAt Model p).symm z))
    (coordinateJ_intertwine J p hz) (invariantPart J α ((extChartAt Model p).symm z))
    (β ((extChartAt Model p).symm z))
  rw [inverseChartEquiv_coe] at he
  exact he.symm

lemma pullback_starThree (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (β : ManifoldForms.Form X 3) (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    ManifoldForms.pullback (starThree J α ht β) (extChartAt Model p).symm z =
      MetricHodge.starThree (coordinateMetric J α ht p z)
        (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm z)
        (ManifoldForms.pullback β (extChartAt Model p).symm z) := by
  have he := MetricHodge.starThree_comp (coordinateMetric J α ht p z)
    (tangentMetric J α ht ((extChartAt Model p).symm z)) (inverseChartEquiv p z hz)
    (coordinateMetric_pullback J α ht p hz) (by simp [Space])
    (invariantPart J α ((extChartAt Model p).symm z)) (β ((extChartAt Model p).symm z))
  rw [inverseChartEquiv_coe] at he
  exact he.symm

lemma coordinateMetric_smooth (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (p : X) :
    ContDiffOn ℝ ∞ (fun z => (coordinateMetric J α ht p z).bilinear) (extChartAt Model p).target := by
  apply ((hs.invariantPart J).metricCoords J p).congr
  intro z hz
  exact coordinateMetric_bilinear J α ht p hz

lemma coordinateJ_smooth (J : AlmostComplexStructure X) (p : X) :
    ContDiffOn ℝ ∞ (coordinateJ J p) (extChartAt Model p).target :=
  SmoothAlmostComplex.contDiffOn_coord_chart ⟨J.endomorphism,J.square,J.smooth⟩ p

lemma starTwo_smooth (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) {β : TwoForm X} (hβ : IsSmooth β) :
    IsSmooth (starTwo J α ht β) := by
  apply ManifoldForms.smooth_of_charts
  intro p
  apply (SmoothHodge.starTwo_contDiffOn (coordinateMetric J α ht p) (coordinateJ J p)
    (by simp [Space]) (isOpen_extChartAt_target p) (coordinateMetric_smooth J α hs ht p)
    (coordinateJ_smooth J p) (fun z hz => coordinateJ_square J p hz)
    (fun z hz => coordinateMetric_hermitian J α ht p hz)
    (ManifoldForms.smooth_chart _ (hs.invariantPart J) p)
    (ManifoldForms.smooth_chart β hβ p)).congr
  intro z hz
  exact pullback_starTwo J α ht β p hz

lemma starThree_smooth (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) {β : ManifoldForms.Form X 3}
    (hβ : ManifoldForms.Smooth β) : ManifoldForms.Smooth (starThree J α ht β) := by
  apply ManifoldForms.smooth_of_charts
  intro p
  apply (SmoothHodge.starThree_contDiffOn (coordinateMetric J α ht p) (coordinateJ J p)
    (by simp [Space]) (isOpen_extChartAt_target p) (coordinateMetric_smooth J α hs ht p)
    (coordinateJ_smooth J p) (fun z hz => coordinateJ_square J p hz)
    (fun z hz => coordinateMetric_hermitian J α ht p hz)
    (ManifoldForms.smooth_chart _ (hs.invariantPart J) p)
    (ManifoldForms.smooth_chart β hβ p)).congr
  intro z hz
  exact pullback_starThree J α ht β p hz

def codifferential (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (β : TwoForm X) : ManifoldForms.Form X 1 :=
  -starThree J α ht (ManifoldForms.exteriorDerivative (starTwo J α ht β))

lemma coclosed_selfdual_closed (J : AlmostComplexStructure X) (α : TwoForm X)
    (ht : Tames α J) {β : TwoForm X} (hβ : IsSmooth β)
    (hself : starTwo J α ht β = β) (hc : codifferential J α ht β = 0) : IsClosed β := by
  change -(starThree J α ht (ManifoldForms.exteriorDerivative (starTwo J α ht β))) = 0 at hc
  rw [hself, neg_eq_zero,starThree_eq_zero J α ht] at hc
  exact (ManifoldForms.closed_iff_exteriorDerivative_eq_zero hβ).mpr hc

lemma coclosed_antiInvariant_closed (J : AlmostComplexStructure X) (α : TwoForm X)
    (ht : Tames α J) {β : TwoForm X} (hβ : IsSmooth β)
    (hanti : antiInvariantPart J β = β) (hc : codifferential J α ht β = 0) : IsClosed β := by
  apply coclosed_selfdual_closed J α ht hβ _ hc
  rw [← hanti]
  exact starTwo_antiInvariant J α ht β

end TamingCompatibility.ManifoldHodge

end

end OAI
