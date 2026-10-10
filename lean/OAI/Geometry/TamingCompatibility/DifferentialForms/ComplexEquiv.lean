import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.Wedge

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
namespace TamingCompatibility.MetricForms
open MetricModel ContinuousAlternatingMap
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma pairing_sub_left (g : Metric E) {k : ℕ} (a b c : Form E k) :
    pairing g (a-b) c = pairing g a c - pairing g b c := by
  change FormMetric.pairing (MetricHodge.formEquiv g k (a-b)) (MetricHodge.formEquiv g k c) = _
  rw [_root_.map_sub]
  simp only [FormMetric.pairing,_root_.map_sub,inner_sub_left]
  rfl
lemma pairing_smul_left (g : Metric E) {k : ℕ} (t : ℝ) (a b : Form E k) :
    pairing g (t • a) b = t * pairing g a b := by
  change FormMetric.pairing (MetricHodge.formEquiv g k (t • a)) (MetricHodge.formEquiv g k b) = _
  rw [_root_.map_smul]
  exact FormMetric.pairing_smul_left _ _ _
lemma pairing_sub_right (g : Metric E) {k : ℕ} (a b c : Form E k) :
    pairing g a (b-c) = pairing g a b - pairing g a c := by
  rw [pairing_symm,pairing_sub_left,pairing_symm g b a,pairing_symm g c a]
lemma pairing_smul_right (g : Metric E) {k : ℕ} (t : ℝ) (a b : Form E k) :
    pairing g a (t • b) = t * pairing g a b := by
  rw [pairing_symm,pairing_smul_left,pairing_symm g b a]

def complexEquiv (J : E →L[ℝ] E) (hJ : ∀ u, J (J u) = -u) : E ≃L[ℝ] E where
  toLinearEquiv := {
    toLinearMap := J.toLinearMap
    invFun := fun u => -(J u)
    left_inv := fun u => by change -J (J u) = u; rw [hJ,neg_neg]
    right_inv := fun u => by change J (-J u) = u; rw [map_neg,hJ,neg_neg] }
  continuous_toFun := J.continuous
  continuous_invFun := J.continuous.neg
omit [FiniteDimensional ℝ E] in
lemma complexEquiv_coe (J : E →L[ℝ] E) (hJ : ∀ u, J (J u) = -u) :
    (complexEquiv J hJ).toContinuousLinearMap = J := rfl
end TamingCompatibility.MetricForms

namespace TamingCompatibility.GeometricAdjoint
open Bundle ManifoldForms ManifoldHodge ManifoldVolume ManifoldLocalization MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
lemma pairing_jAction (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (a b : TwoForm X) (x : X) : pairing J α ht (jAction J a) (jAction J b) x = pairing J α ht a b x := by
  let g := pointMetric J α ht x
  let a' : MetricForms.Form Space 2 := a x
  let b' : MetricForms.Form Space 2 := b x
  have he := MetricForms.pairing_two_comp g g (MetricForms.complexEquiv (J.endomorphism x) (J.square x))
    ((invariantPart_isInvariant J α).associatedBilinear_hermitian x) (by simp [Space]) a' b'
  exact he
lemma pairing_jAction_self_adjoint (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (a b : TwoForm X) (x : X) : pairing J α ht (jAction J a) b x = pairing J α ht a (jAction J b) x := by
  have he := pairing_jAction J α ht a (jAction J b) x
  rwa [jAction_involutive J b] at he
lemma pairing_antiInvariantPart (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (a b : TwoForm X) (x : X) :
    pairing J α ht (antiInvariantPart J a) b x = pairing J α ht a (antiInvariantPart J b) x := by
  let g := pointMetric J α ht x
  let a' : MetricForms.Form Space 2 := a x
  let b' : MetricForms.Form Space 2 := b x
  let Ja : MetricForms.Form Space 2 := jAction J a x
  let Jb : MetricForms.Form Space 2 := jAction J b x
  change MetricForms.pairing g ((1/2:ℝ) • (a'-Ja)) b' =
    MetricForms.pairing g a' ((1/2:ℝ) • (b'-Jb))
  rw [MetricForms.pairing_smul_left,MetricForms.pairing_smul_right,
    MetricForms.pairing_sub_left,MetricForms.pairing_sub_right]
  have he := pairing_jAction_self_adjoint J α ht a b x
  change MetricForms.pairing g Ja b' = MetricForms.pairing g a' Jb at he
  rw [he]

def rdd (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (a : TwoForm X) : TwoForm X := antiInvariantPart J (exteriorDerivative (codifferential J α ht a))
lemma rdd_smooth (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
    (ht : Tames α J) {a : TwoForm X} (ha : IsSmooth a) : IsSmooth (rdd J α ht a) :=
  IsSmooth.antiInvariantPart (Smooth.exteriorDerivative (codifferential_smooth J α hs ht ha)) J

variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X)

theorem rdd_green (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
    (ht : Tames α J) {a b : TwoForm X} (ha : IsSmooth a) (hb : IsSmooth b)
    (hRb : antiInvariantPart J b = b) :
    (∫ x, pairing J α ht (rdd J α ht a) b x ∂geometricVolume A J α) =
      ∫ x, pairing J α ht (codifferential J α ht a) (codifferential J α ht b) x
        ∂geometricVolume A J α := by
  have he : pairing J α ht (rdd J α ht a) b =
      pairing J α ht (exteriorDerivative (codifferential J α ht a)) b := by
    funext x
    rw [rdd,pairing_antiInvariantPart,hRb]
  rw [he]
  exact formal_adjoint A J α hs ht (codifferential_smooth J α hs ht ha) hb

theorem rdd_nonnegative (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
    (ht : Tames α J) {a : TwoForm X} (ha : IsSmooth a) (hRa : antiInvariantPart J a = a) :
    0 ≤ ∫ x, pairing J α ht (rdd J α ht a) a x ∂geometricVolume A J α := by
  rw [rdd_green A J α hs ht ha ha hRa]
  exact integral_nonneg (fun x => MetricForms.pairing_self_nonneg (pointMetric J α ht x) _)

theorem rdd_symmetric (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
    (ht : Tames α J) {a b : TwoForm X} (ha : IsSmooth a) (hb : IsSmooth b)
    (hRa : antiInvariantPart J a = a) (hRb : antiInvariantPart J b = b) :
    (∫ x, pairing J α ht (rdd J α ht a) b x ∂geometricVolume A J α) =
      ∫ x, pairing J α ht a (rdd J α ht b) x ∂geometricVolume A J α := by
  rw [rdd_green A J α hs ht ha hb hRb]
  have he := rdd_green A J α hs ht hb ha hRa
  convert he.symm using 1 <;> apply integral_congr_ae <;>
    exact Filter.Eventually.of_forall (fun x => MetricForms.pairing_symm (pointMetric J α ht x) _ _)
end TamingCompatibility.GeometricAdjoint

namespace TamingCompatibility.MetricForms
open ContinuousAlternatingMap MetricModel
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D]
lemma pairing_one_eq_sum (g : Metric E) (hdim : Module.finrank ℝ E = 4)
    (b : Fin 4 → E) (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
    (α β : Form E 1) : pairing g α β = ∑ i, α ![b i] * β ![b i] := by
  rw [pairing,FormMetric.pairing_one (basisOfFrame g hdim b hb)]
  simp only [basisOfFrame_apply,compContinuousLinearMap_apply]
  rfl
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] in
lemma comp_one (α : Form D 1) (L : E →L[ℝ] D) (u : E) :
    (α.compContinuousLinearMap L) ![u] = α ![L u] := by
  change α (fun i => L (![u] i)) = _
  congr 1
  ext i
  fin_cases i
  rfl
lemma pairing_one_comp (g : Metric E) (h : Metric D) (L : E ≃L[ℝ] D)
    (hL : ∀ u v, h.bilinear (L u) (L v) = g.bilinear u v)
    (hdim : Module.finrank ℝ E = 4) (α β : Form D 1) :
    pairing g (α.compContinuousLinearMap L) (β.compContinuousLinearMap L) = pairing h α β := by
  let b : OrthonormalBasis (Fin 4) ℝ (MetricModel.Model g) :=
    (stdOrthonormalBasis ℝ (MetricModel.Model g)).reindex (finCongr ((finrank_model g).trans hdim))
  rw [pairing,pairing,FormMetric.pairing_one b,
    FormMetric.pairing_one (b.map (isometryEquiv g h L hL))]
  simp only [comp_one,OrthonormalBasis.map_apply]
  rfl
end TamingCompatibility.MetricForms

namespace TamingCompatibility.SmoothMetric
open MetricModel MetricForms FormSmooth
open scoped ContDiff
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
lemma contDiffOn_pairing_one_frame (g : D → Metric E) (hdim : Module.finrank ℝ E = 4)
    {U : Set D} (b : Fin 4 → D → E) (hbs : ∀ i, ContDiffOn ℝ ∞ (b i) U)
    (hb : ∀ x ∈ U, ∀ i j, (g x).bilinear (b i x) (b j x) = if i = j then 1 else 0)
    {α β : D → Form E 1} (hα : ContDiffOn ℝ ∞ α U) (hβ : ContDiffOn ℝ ∞ β U) :
    ContDiffOn ℝ ∞ (fun x => pairing (g x) (α x) (β x)) U := by
  have hs : ContDiffOn ℝ ∞ (fun x => ∑ i : Fin 4, α x ![b i x] * β x ![b i x]) U := by
    apply ContDiffOn.sum
    intro i hi
    have he (x : D) : ![b i x] = (fun _ : Fin 1 => b i x) := by ext j; fin_cases j; rfl
    simp_rw [he]
    exact (contDiffOn_apply hα (fun _ => hbs i)).mul (contDiffOn_apply hβ (fun _ => hbs i))
  exact hs.congr (fun x hx => pairing_one_eq_sum (g x) hdim (fun i => b i x) (hb x hx) _ _)
lemma contDiffOn_pairing_one (g : D → Metric E) (J : D → E →L[ℝ] E)
    (hdim : Module.finrank ℝ E = 4) {U : Set D} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U) (hJ : ContDiffOn ℝ ∞ J U)
    (hJs : ∀ x ∈ U, ∀ u, J x (J x u) = -u)
    (hgJ : ∀ x ∈ U, ∀ u v, (g x).bilinear (J x u) (J x v) = (g x).bilinear u v)
    {α β : D → Form E 1} (hα : ContDiffOn ℝ ∞ α U) (hβ : ContDiffOn ℝ ∞ β U) :
    ContDiffOn ℝ ∞ (fun x => pairing (g x) (α x) (β x)) U := by
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  obtain ⟨V,hV,hxV,hVU,b,hbs,hb⟩ := exists_orthonormalFrame_near g J hdim hU hg hJ hJs hgJ hx
  exact ⟨V,hV,hxV,(contDiffOn_pairing_one_frame g hdim b hbs hb
    (hα.mono hVU) (hβ.mono hVU)).mono Set.inter_subset_right⟩
end TamingCompatibility.SmoothMetric

end

end OAI
