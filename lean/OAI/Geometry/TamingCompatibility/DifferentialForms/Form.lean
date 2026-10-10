import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.Star

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
open scoped BigOperators
open RealInnerProductSpace ContinuousAlternatingMap
open MetricModel
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D]

abbrev Form (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) :=
  E [⋀^Fin k]→L[ℝ] ℝ

def pairing (g : Metric E) {k : ℕ} (α β : Form E k) : ℝ :=
  FormMetric.pairing (α.compContinuousLinearMap (equiv g).toContinuousLinearMap)
    (β.compContinuousLinearMap (equiv g).toContinuousLinearMap)

lemma pairing_symm (g : Metric E) {k : ℕ} (α β : Form E k) :
    pairing g α β = pairing g β α := FormMetric.pairing_symm _ _

lemma pairing_self_nonneg (g : Metric E) {k : ℕ} (α : Form E k) :
    0 ≤ pairing g α α := FormMetric.pairing_self_nonneg _

lemma pairing_self_eq_zero (g : Metric E) {k : ℕ} (α : Form E k) :
    pairing g α α = 0 ↔ α = 0 := by
  rw [pairing, FormMetric.pairing_self_eq_zero]
  constructor
  · intro h
    ext v
    have hv := congrArg (fun a : Form (MetricModel.Model g) k => a (fun i => (equiv g).symm (v i))) h
    simpa only [compContinuousLinearMap_apply, Function.comp_def,
      ContinuousAlternatingMap.coe_zero, Pi.zero_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply] using hv
  · intro h
    ext v
    simp only [h, compContinuousLinearMap_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]

def basisOfFrame (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0) :
    OrthonormalBasis (Fin 4) ℝ (MetricModel.Model g) := by
  let v : Fin 4 → MetricModel.Model g := fun i => ofOriginal g (b i)
  have hv : Orthonormal ℝ v := orthonormal_iff_ite.mpr hb
  exact OrthonormalBasis.mk hv
    (hv.linearIndependent.span_eq_top_of_card_eq_finrank (by
      rw [finrank_model, hdim]; rfl)).ge

@[simp] lemma basisOfFrame_apply (g : Metric E) (hdim : Module.finrank ℝ E = 4)
    (b : Fin 4 → E) (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
    (i : Fin 4) : basisOfFrame g hdim b hb i = ofOriginal g (b i) := by
  simp only [basisOfFrame, OrthonormalBasis.coe_mk]

lemma pairing_two_eq_sum (g : Metric E) (hdim : Module.finrank ℝ E = 4)
    (b : Fin 4 → E) (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
    (α β : Form E 2) :
    pairing g α β = ∑ i, α ![b (FormMetric.pairLeft i), b (FormMetric.pairRight i)] *
      β ![b (FormMetric.pairLeft i), b (FormMetric.pairRight i)] := by
  rw [pairing, FormMetric.pairing_eq_sum (basisOfFrame g hdim b hb)]
  simp only [basisOfFrame_apply, compContinuousLinearMap_apply]
  rfl

lemma pairing_three_eq_sum (g : Metric E) (hdim : Module.finrank ℝ E = 4)
    (b : Fin 4 → E) (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
    (α β : Form E 3) :
    pairing g α β = ∑ i, α (fun j => b (FormMetric.tripleIndices i j)) *
      β (fun j => b (FormMetric.tripleIndices i j)) := by
  rw [pairing, FormMetric.pairing_three (basisOfFrame g hdim b hb)]
  simp only [basisOfFrame_apply, compContinuousLinearMap_apply]
  rfl

def isometryEquiv (g : Metric E) (h : Metric D) (L : E ≃L[ℝ] D)
    (hL : ∀ u v, h.bilinear (L u) (L v) = g.bilinear u v) :
    MetricModel.Model g ≃ₗᵢ[ℝ] MetricModel.Model h :=
  (((equiv g).trans L).trans (equiv h).symm).toLinearEquiv.isometryOfInner hL

@[simp] lemma isometryEquiv_apply (g : Metric E) (h : Metric D) (L : E ≃L[ℝ] D)
    (hL : ∀ u v, h.bilinear (L u) (L v) = g.bilinear u v) (u : MetricModel.Model g) :
    isometryEquiv g h L hL u = L u := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] in
lemma comp_two (α : Form D 2) (L : E →L[ℝ] D) (u v : E) :
    (α.compContinuousLinearMap L) ![u,v] = α ![L u,L v] := by
  change α (fun i => L (![u,v] i)) = _
  congr 1
  ext i
  fin_cases i <;> rfl

lemma pairing_two_comp (g : Metric E) (h : Metric D) (L : E ≃L[ℝ] D)
    (hL : ∀ u v, h.bilinear (L u) (L v) = g.bilinear u v)
    (hdim : Module.finrank ℝ E = 4) (α β : Form D 2) :
    pairing g (α.compContinuousLinearMap L) (β.compContinuousLinearMap L) =
      pairing h α β := by
  let b : OrthonormalBasis (Fin 4) ℝ (MetricModel.Model g) :=
    (stdOrthonormalBasis ℝ (MetricModel.Model g)).reindex (finCongr ((finrank_model g).trans hdim))
  rw [pairing, pairing, FormMetric.pairing_eq_sum b,
    FormMetric.pairing_eq_sum (b.map (isometryEquiv g h L hL))]
  simp only [comp_two, OrthonormalBasis.map_apply]
  rfl

lemma pairing_three_comp (g : Metric E) (h : Metric D) (L : E ≃L[ℝ] D)
    (hL : ∀ u v, h.bilinear (L u) (L v) = g.bilinear u v)
    (hdim : Module.finrank ℝ E = 4) (α β : Form D 3) :
    pairing g (α.compContinuousLinearMap L) (β.compContinuousLinearMap L) =
      pairing h α β := by
  let b : OrthonormalBasis (Fin 4) ℝ (MetricModel.Model g) :=
    (stdOrthonormalBasis ℝ (MetricModel.Model g)).reindex (finCongr ((finrank_model g).trans hdim))
  rw [pairing, pairing, FormMetric.pairing_three b,
    FormMetric.pairing_three (b.map (isometryEquiv g h L hL))]
  rfl

end TamingCompatibility.MetricForms

namespace TamingCompatibility.HermitianHodge
open RealInnerProductSpace FormMetric GeometricSymbol UnitaryBasis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma pairing_coords (b : OrthonormalBasis (Fin 4) ℝ E)
    (α β : GeometricSymbol.TwoForm E) : pairing α β = ⟪coords b α, coords b β⟫ := by
  rw [pairing_eq_sum b]
  simp [coords, pairLeft, pairRight, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_succ]
  ring

def star (J : E →L[ℝ] E) (F α : GeometricSymbol.TwoForm E) : GeometricSymbol.TwoForm E :=
  pairing α F • F - α.compContinuousLinearMap J

omit [FiniteDimensional ℝ E] in
lemma coords_sub (b : OrthonormalBasis (Fin 4) ℝ E) (α β : GeometricSymbol.TwoForm E) :
    coords b (α - β) = coords b α - coords b β := by
  ext i
  fin_cases i <;> rfl

lemma unitary_star_formula (a : UnitaryFrame.W) :
    (a 0 + a 5) • UnitaryFrame.fundamental - UnitaryFrame.jAction a =
      UnitaryFrame.star a := by
  ext i
  fin_cases i <;>
    simp [UnitaryFrame.star, UnitaryFrame.fundamental, UnitaryFrame.jAction]

section UnitaryFrame
variable (b : OrthonormalBasis (Fin 4) ℝ E) (J : E →L[ℝ] E)
  (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
  (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)

include h0 h1 h2 h3 in
omit [FiniteDimensional ℝ E] in
lemma coords_jAction (α : GeometricSymbol.TwoForm E) :
    coords b (α.compContinuousLinearMap J) = UnitaryFrame.jAction (coords b α) := by
  have hc (u v : E) : (α.compContinuousLinearMap J) ![u,v] = α ![J u,J v] := by
    change α (fun i => J (![u,v] i)) = _
    congr 1
    ext i
    fin_cases i <;> rfl
  have h10 := GeometricSymbol.eval_swap α (b 0) (b 1)
  have h32 := GeometricSymbol.eval_swap α (b 2) (b 3)
  ext i
  fin_cases i <;>
    simp [coords, UnitaryFrame.jAction, hc,
      h0, h1, h2, h3, GeometricSymbol.eval_neg_left, GeometricSymbol.eval_neg_right, h10, h32]

variable (F : GeometricSymbol.TwoForm E) (hF : ∀ u v, F ![u,v] = ⟪J u,v⟫)

include h0 h1 h2 hF in
omit [FiniteDimensional ℝ E] in
lemma coords_fundamental : coords b F = UnitaryFrame.fundamental := by
  have hb := orthonormal_iff_ite.mp b.orthonormal
  ext i
  fin_cases i <;> simp [coords, UnitaryFrame.fundamental, hF, h0, h1, h2, hb]

include h0 h1 h2 hF in
lemma pairing_fundamental (α : GeometricSymbol.TwoForm E) : pairing α F = coords b α 0 + coords b α 5 := by
  rw [pairing_coords b α F, coords_fundamental b J h0 h1 h2 F hF]
  simp [UnitaryFrame.fundamental, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_succ]

include h0 h1 h2 h3 hF in
lemma coords_star (α : GeometricSymbol.TwoForm E) : coords b (star J F α) = UnitaryFrame.star (coords b α) := by
  rw [star, coords_sub, coords_smul, coords_fundamental b J h0 h1 h2 F hF,
    coords_jAction b J h0 h1 h2 h3 α, pairing_fundamental b J h0 h1 h2 F hF]
  exact unitary_star_formula _

end UnitaryFrame

variable (J : E →ₗᵢ[ℝ] E) (hJ : ∀ u, J (J u) = -u)
  (hdim : Module.finrank ℝ E = 4) (F : GeometricSymbol.TwoForm E)
  (hF : ∀ u v, F ![u,v] = ⟪J u,v⟫)

include hJ hdim hF

lemma star_square (α : GeometricSymbol.TwoForm E) : star J.toContinuousLinearMap F (star J.toContinuousLinearMap F α) = α := by
  obtain ⟨b,h0,h1,h2,h3⟩ := exists_unitary_basis J hJ hdim
  apply coords_injective b
  rw [coords_star b _ h0 h1 h2 h3 F hF, coords_star b _ h0 h1 h2 h3 F hF,
    UnitaryFrame.star_square]

lemma star_self_adjoint (α β : GeometricSymbol.TwoForm E) :
    pairing (star J.toContinuousLinearMap F α) β = pairing α (star J.toContinuousLinearMap F β) := by
  obtain ⟨b,h0,h1,h2,h3⟩ := exists_unitary_basis J hJ hdim
  rw [pairing_coords b, pairing_coords b, coords_star b _ h0 h1 h2 h3 F hF,
    coords_star b _ h0 h1 h2 h3 F hF, UnitaryFrame.star_self_adjoint]

lemma star_isometry (α β : GeometricSymbol.TwoForm E) :
    pairing (star J.toContinuousLinearMap F α) (star J.toContinuousLinearMap F β) = pairing α β := by
  rw [star_self_adjoint J hJ hdim F hF, star_square J hJ hdim F hF]

lemma star_antiInvariant (α : GeometricSymbol.TwoForm E) :
    star J.toContinuousLinearMap F (antiInvariant J.toContinuousLinearMap α) =
      antiInvariant J.toContinuousLinearMap α := by
  obtain ⟨b,h0,h1,h2,h3⟩ := exists_unitary_basis J hJ hdim
  apply coords_injective b
  rw [coords_star b _ h0 h1 h2 h3 F hF, coords_antiInvariant b _ h0 h1 h2 h3,
    UnitaryFrame.star_antiInvariantPart]

lemma star_fundamental : star J.toContinuousLinearMap F F = F := by
  obtain ⟨b,h0,h1,h2,h3⟩ := exists_unitary_basis J hJ hdim
  apply coords_injective b
  rw [coords_star b _ h0 h1 h2 h3 F hF, coords_fundamental b J.toContinuousLinearMap h0 h1 h2 F hF,
    UnitaryFrame.star_fundamental]

lemma fundamental_sq : pairing F F = 2 := by
  obtain ⟨b,h0,h1,h2,h3⟩ := exists_unitary_basis J hJ hdim
  rw [pairing_coords b, coords_fundamental b J.toContinuousLinearMap h0 h1 h2 F hF,
    real_inner_self_eq_norm_sq, UnitaryFrame.fundamental_norm_sq]

end TamingCompatibility.HermitianHodge

end

end OAI
