import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.FormEquiv
import OAI.Geometry.TamingCompatibility.DifferentialForms.TopForms

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
namespace TamingCompatibility.FormMetric
open RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def singleFamily (b : OrthonormalBasis (Fin 4) ℝ E) (i : Fin 4) : ⋀[ℝ]^1 E :=
  exteriorPower.ιMulti ℝ 1 ![b i]

lemma singleFamily_orthonormal (b : OrthonormalBasis (Fin 4) ℝ E) : Orthonormal ℝ (singleFamily b) := by
  rw [orthonormal_iff_ite]
  intro i j
  simpa [singleFamily,exteriorPower.inner_ιMulti_ιMulti,Matrix.det_fin_one] using
    orthonormal_iff_ite.mp b.orthonormal i j

def singleBasis (b : OrthonormalBasis (Fin 4) ℝ E) : OrthonormalBasis (Fin 4) ℝ (⋀[ℝ]^1 E) :=
  OrthonormalBasis.mk (singleFamily_orthonormal b)
    ((singleFamily_orthonormal b).linearIndependent.span_eq_top_of_card_eq_finrank (by
      rw [exteriorPower.finrank_eq,Module.finrank_eq_card_basis b.toBasis]
      norm_num)).ge

lemma singleBasis_repr (b : OrthonormalBasis (Fin 4) ℝ E) (a : E [⋀^Fin 1]→L[ℝ] ℝ) (i : Fin 4) :
    (singleBasis b).repr (sharp a) i = a ![b i] := by
  rw [OrthonormalBasis.repr_apply_apply,real_inner_comm]
  simp only [singleBasis,OrthonormalBasis.coe_mk,singleFamily]
  exact sharp_inner _ _

lemma pairing_one (b : OrthonormalBasis (Fin 4) ℝ E) (a c : E [⋀^Fin 1]→L[ℝ] ℝ) :
    pairing a c = ∑ i, a ![b i] * c ![b i] := by
  have h := (singleBasis b).repr.inner_map_map (sharp a) (sharp c)
  rw [pairing,← h]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,singleBasis_repr]
  congr 1
  ext i
  exact mul_comm _ _
end TamingCompatibility.FormMetric

namespace TamingCompatibility.WedgePairing
open RealInnerProductSpace ContinuousAlternatingMap ExteriorForms FormMetric GeometricSymbol
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma top_ext (b : Module.Basis (Fin 4) ℝ E) {a c : Form (E := E) 4} (h : a b = c b) : a = c := by
  ext v
  rw [TopForms.eval_eq_det_mul b a v,TopForms.eval_eq_det_mul b c v,h]

omit [FiniteDimensional ℝ E] in
lemma wedgeTwo_on_frame (b : OrthonormalBasis (Fin 4) ℝ E) (a c : Form (E := E) 2) :
    wedgeTwo a c b = ⟪coords b a,UnitaryFrame.star (coords b c)⟫ := by
  have he : (b : Fin 4 → E) = ![b 0,b 1,b 2,b 3] := by ext i; fin_cases i <;> rfl
  rw [he,wedgeTwo_apply]
  simp [coords,UnitaryFrame.star,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_succ]
  ring

section Frame
variable (b : OrthonormalBasis (Fin 4) ℝ E) (J : E →L[ℝ] E)
  (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
  (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
  (F : Form (E := E) 2) (hF : ∀ u v, F ![u,v] = ⟪J u,v⟫)
include h0 h1 h2 h3 hF

omit [FiniteDimensional ℝ E] in
lemma volume_on_frame : volumeSquare F b = 1 := by
  have h := HodgeThree.volume_on_frame b J h0 h1 h2 h3 F hF 0 0
  have he : Matrix.vecCons (b 0) (fun l => b (FormMetric.tripleIndices 0 l)) = (b : Fin 4 → E) := by
    ext i
    fin_cases i <;> rfl
  change volumeSquare F (Matrix.vecCons (b 0) (fun l => b (FormMetric.tripleIndices 0 l))) = _ at h
  simpa only [he,ite_true,Fin.val_zero,pow_zero] using h

lemma wedgeTwo_star (a c : Form (E := E) 2) :
    wedgeTwo a (HermitianHodge.star J F c) = FormMetric.pairing a c • volumeSquare F := by
  apply top_ext b.toBasis
  change wedgeTwo a (HermitianHodge.star J F c) b = (FormMetric.pairing a c • volumeSquare F) b
  rw [wedgeTwo_on_frame,HermitianHodge.coords_star b J h0 h1 h2 h3 F hF,
    UnitaryFrame.star_square,ContinuousAlternatingMap.smul_apply,
    volume_on_frame b J h0 h1 h2 h3 F hF]
  rw [smul_eq_mul,mul_one,HermitianHodge.pairing_coords b]

lemma wedgeOne_three (a : Form (E := E) 1) (c : Form (E := E) 3) :
    wedgeOne (oneLinear a) c = -FormMetric.pairing a (HodgeThree.star F c) • volumeSquare F := by
  apply top_ext b.toBasis
  change wedgeOne (oneLinear a) c b = (-FormMetric.pairing a (HodgeThree.star F c) • volumeSquare F) b
  rw [ContinuousAlternatingMap.smul_apply,volume_on_frame b J h0 h1 h2 h3 F hF,smul_eq_mul,mul_one,
    pairing_one b]
  simp_rw [HodgeThree.star_on_frame b J h0 h1 h2 h3 F hF]
  have he : (b : Fin 4 → E) = ![b 0,b 1,b 2,b 3] := by ext i; fin_cases i <;> rfl
  nth_rw 1 [he]
  rw [wedgeOne_apply_four]
  have h₀ : (fun l => b (FormMetric.tripleIndices 0 l)) = ![b 1,b 2,b 3] := by ext i; fin_cases i <;> rfl
  have h₁ : (fun l => b (FormMetric.tripleIndices 1 l)) = ![b 0,b 2,b 3] := by ext i; fin_cases i <;> rfl
  have h₂ : (fun l => b (FormMetric.tripleIndices 2 l)) = ![b 0,b 1,b 3] := by ext i; fin_cases i <;> rfl
  have h₃ : (fun l => b (FormMetric.tripleIndices 3 l)) = ![b 0,b 1,b 2] := by ext i; fin_cases i <;> rfl
  simp [oneLinear_apply,Fin.sum_univ_succ,h₀,h₁,h₂,h₃]
  ring
end Frame

lemma wedgeTwo_star_intrinsic (J : E →ₗᵢ[ℝ] E) (hJ : ∀ u, J (J u) = -u)
    (hdim : Module.finrank ℝ E = 4) (F : Form (E := E) 2) (hF : ∀ u v, F ![u,v] = ⟪J u,v⟫)
    (a c : Form (E := E) 2) :
    wedgeTwo a (HermitianHodge.star J.toContinuousLinearMap F c) = FormMetric.pairing a c • volumeSquare F := by
  obtain ⟨b,h0,h1,h2,h3⟩ := UnitaryBasis.exists_unitary_basis J hJ hdim
  exact wedgeTwo_star b J.toContinuousLinearMap h0 h1 h2 h3 F hF a c

lemma wedgeOne_three_intrinsic (J : E →ₗᵢ[ℝ] E) (hJ : ∀ u, J (J u) = -u)
    (hdim : Module.finrank ℝ E = 4) (F : Form (E := E) 2) (hF : ∀ u v, F ![u,v] = ⟪J u,v⟫)
    (a : Form (E := E) 1) (c : Form (E := E) 3) :
    wedgeOne (oneLinear a) c = -FormMetric.pairing a (HodgeThree.star F c) • volumeSquare F := by
  obtain ⟨b,h0,h1,h2,h3⟩ := UnitaryBasis.exists_unitary_basis J hJ hdim
  exact wedgeOne_three b J.toContinuousLinearMap h0 h1 h2 h3 F hF a c

end TamingCompatibility.WedgePairing

namespace TamingCompatibility.MetricWedgePairing
open ContinuousAlternatingMap ExteriorForms MetricHodge MetricModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma formEquiv_volume (g : Metric E) (F : ExteriorForms.Form (E := E) 2) :
    formEquiv g 4 (volumeSquare F) = volumeSquare (formEquiv g 2 F) := by
  exact (MetricHodge.volumeSquare_comp F (equiv g).toContinuousLinearMap).symm

lemma formEquiv_wedgeTwo (g : Metric E) (a b : ExteriorForms.Form (E := E) 2) :
    formEquiv g 4 (wedgeTwo a b) = wedgeTwo (formEquiv g 2 a) (formEquiv g 2 b) := by
  simp only [wedgeTwo,_root_.map_sub,formEquiv_volume,_root_.map_add]

lemma formEquiv_wedgeOne {degree : ℕ} (g : Metric E) (a : ExteriorForms.Form (E := E) 1) (b : ExteriorForms.Form (E := E) degree) :
    formEquiv g (degree+1) (wedgeOne (oneLinear a) b) = wedgeOne (oneLinear (formEquiv g 1 a)) (formEquiv g degree b) := by
  exact (wedgeOne_comp (oneLinear a) b (equiv g).toContinuousLinearMap).trans
    (congrArg (fun L => wedgeOne L (formEquiv g degree b)) (oneLinear_comp a (equiv g).toContinuousLinearMap).symm)

variable (g : Metric E) (J : E →L[ℝ] E) (hJ : ∀ u, J (J u) = -u)
  (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
  (hdim : Module.finrank ℝ E = 4) (F : ExteriorForms.Form (E := E) 2)
  (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)
include hJ horth hdim hF

lemma wedgeTwo_star (a b : ExteriorForms.Form (E := E) 2) :
    wedgeTwo a (starTwo g J F b) = MetricForms.pairing g a b • volumeSquare F := by
  apply (formEquiv g 4).injective
  rw [formEquiv_wedgeTwo,formEquiv_starTwo g J horth,_root_.map_smul,formEquiv_volume]
  exact WedgePairing.wedgeTwo_star_intrinsic (isometry g J horth) hJ
    ((finrank_model g).trans hdim) (formEquiv g 2 F) hF _ _

lemma wedgeOne_three (a : ExteriorForms.Form (E := E) 1) (b : ExteriorForms.Form (E := E) 3) :
    wedgeOne (oneLinear a) b = -MetricForms.pairing g a (starThree g F b) • volumeSquare F := by
  apply (formEquiv g 4).injective
  rw [formEquiv_wedgeOne,_root_.map_smul,formEquiv_volume]
  have he : formEquiv g 1 (starThree g F b) = HodgeThree.star (formEquiv g 2 F) (formEquiv g 3 b) :=
    (formEquiv g 1).apply_symm_apply _
  change wedgeOne (oneLinear (formEquiv g 1 a)) (formEquiv g 3 b) =
    -FormMetric.pairing (formEquiv g 1 a) (formEquiv g 1 (starThree g F b)) • volumeSquare (formEquiv g 2 F)
  rw [he]
  exact WedgePairing.wedgeOne_three_intrinsic (isometry g J horth) hJ
    ((finrank_model g).trans hdim) (formEquiv g 2 F) hF _ _

end TamingCompatibility.MetricWedgePairing

end

end OAI
