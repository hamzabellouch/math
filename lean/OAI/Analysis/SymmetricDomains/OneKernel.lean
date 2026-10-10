import Mathlib
import OAI.Analysis.SymmetricDomains.EulerSpectrum

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061.Biholomorph.WeightedLieModel
variable {r k : ℕ} {G : Type*} [LieRing G] [LieAlgebra ℝ G]
    (M : WeightedLieModel r k G)

attribute [local instance] complexificationRatLieAlgebra

def jet := analyticSecondJetCoordinates M.field M.point M.analytic (modelBasis r k)
def firstJet := fieldFirstJet M.field M.point M.analytic

theorem euler_jet (X : ℂ ⊗[ℝ] G) (j : SecondJetIndex (ModelIndex r k)) :
    M.jet (M.center ⁅M.E,X⁆) j=secondJetWeight modelEulerWeight j*M.jet (M.center X) j :=
  LieFieldJets.conjugated_diagonal M.field M.point M.analytic M.lie (modelBasis r k)
    M.center M.E (flatWeightedEuler r k) M.centered_euler_germ modelEulerWeight
    (flatWeightedEuler_basis r k) X j

theorem rotation_jet (X : ℂ ⊗[ℝ] G) (j : SecondJetIndex (ModelIndex r k)) :
    M.jet (M.center ⁅M.H,X⁆) j=secondJetWeight modelRotationWeight j*M.jet (M.center X) j :=
  LieFieldJets.conjugated_diagonal M.field M.point M.analytic M.lie (modelBasis r k)
    M.center M.H (flatTangentialInfinitesimal r k) M.centered_rotation_germ modelRotationWeight
    (flatTangentialInfinitesimal_basis r k) X j

theorem eigen_jet_zero {X : ℂ ⊗[ℝ] G} {μ : ℂ} (hX : ⁅M.E,X⁆=μ • X)
    (j : SecondJetIndex (ModelIndex r k)) (hj : secondJetWeight modelEulerWeight j≠μ) :
    M.jet (M.center X) j=0 := by
  have he := M.euler_jet X j
  simp only [hX,map_smul,Pi.smul_apply,smul_eq_mul] at he
  have hh : (secondJetWeight modelEulerWeight j-μ)*M.jet (M.center X) j=0 := by
    rw [sub_mul,←he,sub_self]
  exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hj)

theorem centered_value_zero {X : ℂ ⊗[ℝ] G} {μ : ℂ} (hX : ⁅M.E,X⁆=μ • X)
    (hμ : μ=0 ∨ μ=1/2 ∨ μ=1) : M.field (M.center X) M.point=0 := by
  apply (modelBasis r k).ext_elem
  intro i
  have hh := M.eigen_jet_zero hX (.inl i) (by
    rcases hμ with rfl|rfl|rfl <;> cases i <;> norm_num [secondJetWeight,modelEulerWeight])
  simpa [jet,analyticSecondJetCoordinates] using hh

theorem centered_firstJet_one_zero {X : ℂ ⊗[ℝ] G} (hX : ⁅M.E,X⁆=(1 : ℂ) • X) :
    M.firstJet (M.center X)=0 := by
  apply ContinuousLinearMap.coe_injective
  apply (modelBasis r k).ext
  intro j
  apply (modelBasis r k).ext_elem
  intro i
  have hh := M.eigen_jet_zero hX (.inr (.inl (i,j))) (by
    cases i <;> cases j <;> norm_num [secondJetWeight,modelEulerWeight])
  simpa [jet,analyticSecondJetCoordinates,firstJet] using hh

theorem centered_half_rotation_firstJet {X : ℂ ⊗[ℝ] G} (hX : ⁅M.E,X⁆=(1/2 : ℂ) • X) :
    M.firstJet (M.center ⁅M.H,X⁆)= -Complex.I • M.firstJet (M.center X) := by
  apply ContinuousLinearMap.coe_injective
  apply (modelBasis r k).ext
  intro j
  apply (modelBasis r k).ext_elem
  intro i
  have hh := M.rotation_jet X (.inr (.inl (i,j)))
  change (modelBasis r k).repr ((M.firstJet (M.center ⁅M.H,X⁆)) (modelBasis r k j)) i=
    secondJetWeight modelRotationWeight (.inr (.inl (i,j)))*
      (modelBasis r k).repr ((M.firstJet (M.center X)) (modelBasis r k j)) i at hh
  change (modelBasis r k).repr ((M.firstJet (M.center ⁅M.H,X⁆)) (modelBasis r k j)) i=
    (modelBasis r k).repr ((-Complex.I • M.firstJet (M.center X)) (modelBasis r k j)) i
  simp only [smul_apply,map_smul,Finsupp.smul_apply,smul_eq_mul]
  rw [hh]
  by_cases hw : secondJetWeight modelEulerWeight (.inr (.inl (i,j)))=(1/2 : ℂ)
  · have hv : secondJetWeight modelRotationWeight (.inr (.inl (i,j)))= -Complex.I := by
      cases i <;> cases j <;> norm_num [secondJetWeight,modelEulerWeight] at hw
      simp [secondJetWeight,modelRotationWeight]
    rw [hv]
  · have hz := M.eigen_jet_zero hX (.inr (.inl (i,j))) hw
    change (modelBasis r k).repr ((M.firstJet (M.center X)) (modelBasis r k j)) i=0 at hz
    rw [hz,mul_zero,mul_zero]

theorem centered_rotation_value (X : ℂ ⊗[ℝ] G) :
    M.field (M.center ⁅M.H,X⁆) M.point= -flatTangentialInfinitesimal r k (M.field (M.center X) M.point) := by
  rw [M.center.map_lie,M.center_rotation]
  have he := LieFieldJets.centered_bracket M.field M.point M.lie M.H
    (flatTangentialInfinitesimal r k) (by simpa only [M.center_rotation] using M.centered_rotation_germ)
    (M.center X)
  rw [he.eq_of_nhds,lieBracket_centeredLinear_zeroJet]

theorem ofReal_eigen {X : G} {μ : ℝ} (hX : ⁅M.euler,X⁆=μ • X) :
    ⁅M.E,Complexification.ofReal X⁆=(μ : ℂ) • Complexification.ofReal X := by
  rw [←Complexification.ofReal_lie,hX,map_smul]
  exact (IsScalarTower.algebraMap_smul ℂ μ (Complexification.ofReal X)).symm

theorem center_of_commutes {X : ℂ ⊗[ℝ] G} (hX : ⁅M.T,X⁆=0) : M.center X=X :=
  LieAlgebra.innerExp_fixed _ _ _ _ hX

theorem real_zero_of_zero_jet (X : G)
    (h0 : M.field (Complexification.ofReal X) M.point=0)
    (h1 : M.firstJet (Complexification.ofReal X)=0) : X=0 := by
  apply M.isotropy_real X 0 h0
  · simp
  · change M.firstJet (Complexification.ofReal 0)=Complex.I • M.firstJet (Complexification.ofReal X)
    simp only [map_zero,h1,smul_zero]

theorem half_real_kernel {X : G} (hX : ⁅M.euler,X⁆=(1/2 : ℝ) • X)
    (hTX : ⁅M.translation,X⁆=0) : X=0 := by
  let Z := Complexification.ofReal X
  have hZ : ⁅M.E,Z⁆=(1/2 : ℂ) • Z := by simpa [Z] using M.ofReal_eigen hX
  have hcZ : M.center Z=Z := M.center_of_commutes (by rw [←Complexification.ofReal_lie,hTX,map_zero])
  have hz0 : M.field Z M.point=0 := by
    simpa only [hcZ] using M.centered_value_zero hZ (Or.inr (Or.inl rfl))
  have hcB : M.center ⁅M.H,Z⁆=⁅M.H,Z⁆ := by rw [M.center.map_lie,M.center_rotation,hcZ]
  have hb0 : M.field ⁅M.H,Z⁆ M.point=0 := by
    simpa only [hcB,hcZ,hz0,map_zero,neg_zero] using M.centered_rotation_value Z
  have hb1 : M.firstJet ⁅M.H,Z⁆= -Complex.I • M.firstJet Z := by
    simpa only [hcB,hcZ] using M.centered_half_rotation_firstJet hZ
  apply M.isotropy_real X (-⁅M.rotation,X⁆) hz0
  · rw [map_neg,Complexification.ofReal_lie,map_neg]
    change -M.field ⁅M.H,Z⁆ M.point=0
    rw [hb0,neg_zero]
  · change M.firstJet (Complexification.ofReal (-⁅M.rotation,X⁆))=Complex.I • M.firstJet Z
    rw [map_neg,Complexification.ofReal_lie,map_neg,hb1,neg_smul,neg_neg]

theorem half_kernel {X : ℂ ⊗[ℝ] G} (hX : ⁅M.E,X⁆=(1/2 : ℂ) • X)
    (hTX : ⁅M.T,X⁆=0) : X=0 := by
  have hr : Complexification.realPart X=0 := M.half_real_kernel
    (Complexification.realPart_eigen M.euler (1/2) (by simpa using hX))
    (by simpa only [T,Complexification.realPart_lie_ofReal,map_zero] using congrArg Complexification.realPart hTX)
  have hi : Complexification.imagPart X=0 := M.half_real_kernel
    (Complexification.imagPart_eigen M.euler (1/2) (by simpa using hX))
    (by simpa only [T,Complexification.imagPart_lie_ofReal,map_zero] using congrArg Complexification.imagPart hTX)
  rw [Complexification.normalForm X,hr,hi,map_zero,smul_zero,add_zero]

theorem bracket_translation_eigen {X : ℂ ⊗[ℝ] G} {μ : ℂ}
    (hX : ⁅M.E,X⁆=μ • X) : ⁅M.E,⁅M.T,X⁆⁆=(μ-1) • ⁅M.T,X⁆ := by
  have het : ⁅M.E,M.T⁆= -M.T := by rw [←lie_skew M.E M.T,M.translation_euler]
  rw [leibniz_lie,het,hX,neg_lie,LieAlgebra.lie_smul μ M.T X,sub_smul,one_smul]
  abel

theorem one_real_kernel {X : G} (hX : ⁅M.euler,X⁆=(1 : ℝ) • X)
    (hTX : ⁅M.translation,⁅M.translation,X⁆⁆=0) : X=0 := by
  let Z := Complexification.ofReal X
  let Y := ⁅M.translation,X⁆
  have hZ : ⁅M.E,Z⁆=(1 : ℂ) • Z := by simpa [Z] using M.ofReal_eigen hX
  have hTZ : ⁅M.T,Z⁆=Complexification.ofReal Y := (Complexification.ofReal_lie _ _).symm
  have hTTZ : ⁅M.T,⁅M.T,Z⁆⁆=0 := by rw [hTZ,←Complexification.ofReal_lie,hTX,map_zero]
  have hcZ : M.center Z=Z-Complex.I • Complexification.ofReal Y := by
    rw [center,LieAlgebra.innerExp_apply_of_square_zero _ _ _ _ hTTZ,hTZ]
    simp [sub_eq_add_neg]
  have hcY : M.center (Complexification.ofReal Y)=Complexification.ofReal Y :=
    M.center_of_commutes (by rw [←Complexification.ofReal_lie,hTX,map_zero])
  have hY : ⁅M.E,Complexification.ofReal Y⁆=(0 : ℂ) • Complexification.ofReal Y := by
    simpa only [hTZ,sub_self] using M.bracket_translation_eigen hZ
  have hy0 : M.field (Complexification.ofReal Y) M.point=0 := by
    simpa only [hcY] using M.centered_value_zero hY (Or.inl rfl)
  have hz0 : M.field Z M.point=0 := by
    have hh := M.centered_value_zero hZ (Or.inr (Or.inr rfl))
    simpa only [hcZ,map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,hy0,smul_zero,sub_zero] using hh
  have hz1 : M.firstJet Z=Complex.I • M.firstJet (Complexification.ofReal Y) := by
    have hh := M.centered_firstJet_one_zero hZ
    rw [hcZ,map_sub,map_smul] at hh
    exact sub_eq_zero.mp hh
  have hy : Y=0 := M.isotropy_real Y X hy0 hz0 hz1
  apply M.real_zero_of_zero_jet X hz0
  rw [hz1,hy,map_zero,map_zero,smul_zero]

theorem one_kernel {X : ℂ ⊗[ℝ] G} (hX : ⁅M.E,X⁆=(1 : ℂ) • X)
    (hTX : ⁅M.T,⁅M.T,X⁆⁆=0) : X=0 := by
  have hr : Complexification.realPart X=0 := M.one_real_kernel
    (Complexification.realPart_eigen M.euler 1 (by simpa using hX))
    (by simpa only [T,Complexification.realPart_lie_ofReal,map_zero] using congrArg Complexification.realPart hTX)
  have hi : Complexification.imagPart X=0 := M.one_real_kernel
    (Complexification.imagPart_eigen M.euler 1 (by simpa using hX))
    (by simpa only [T,Complexification.imagPart_lie_ofReal,map_zero] using congrArg Complexification.imagPart hTX)
  rw [Complexification.normalForm X,hr,hi,map_zero,smul_zero,add_zero]

end Release061.Biholomorph.WeightedLieModel

open scoped TensorProduct

end

end OAI
