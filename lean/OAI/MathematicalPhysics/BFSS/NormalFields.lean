import Mathlib
import OAI.MathematicalPhysics.BFSS.CovariantFields

namespace OAI

/-! Normal linear fields, Clifford kinetic symbols and potential identities. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory Matrix Finset Set Filter Topology
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] coreToL2 charge bracketPart normalSlice gaugeAction
local instance normalFieldsFermionNormedAddCommGroup :
    NormedAddCommGroup (Fermion N →L[ℝ] Fermion N) := inferInstance
local instance normalFieldsFermionNormedSpace :
    NormedSpace ℝ (Fermion N →L[ℝ] Fermion N) := inferInstance
local instance normalFieldsLinearNormedAddCommGroup :
    NormedAddCommGroup (Boson N →L[ℝ] (Fermion N →L[ℝ] Fermion N)) := inferInstance
local instance normalFieldsLinearNormedSpace :
    NormedSpace ℝ (Boson N →L[ℝ] (Fermion N →L[ℝ] Fermion N)) := inferInstance

def normalLinearField (q : Boson N) (α : SpinIndex) :
    Boson N →L[ℝ] (Fermion N →L[ℝ] Fermion N) :=
  fderiv ℝ (M.deformedRealField 1 1 α) q

lemma normalLinearField_apply (q z : Boson N) (α : SpinIndex) :
    M.normalLinearField q α z =
      M.bracketBilinear α q z + M.bracketBilinear α z q + M.massLinear α z := by
  simp only [normalLinearField,M.deformedRealField_fderiv,one_smul]

lemma normalLinearField_difference (q z : Boson N) (α : SpinIndex) :
    M.normalLinearField q α z = M.deformedRealField 1 1 α (q+z) -
      M.deformedRealField 1 1 α q - M.deformedRealField 1 0 α z := by
  simp only [M.normalLinearField_apply,M.deformedRealField_polarized,map_add,
    IsAddApply.add_apply,one_smul,zero_smul,add_zero]
  abel

lemma normalLinearField_selfAdjoint (q z : Boson N) (α : SpinIndex) :
    IsSelfAdjoint (M.normalLinearField q α z) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  have h₁ := M.deformedRealField_selfAdjoint 1 1 α (q+z)
  have h₂ := M.deformedRealField_selfAdjoint 1 1 α q
  have h₃ := M.deformedRealField_selfAdjoint 1 0 α z
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at h₁ h₂ h₃
  rw [M.normalLinearField_difference]
  change inner ℝ ((M.deformedRealField 1 1 α (q+z)) u - (M.deformedRealField 1 1 α q) u -
    (M.deformedRealField 1 0 α z) u) v = inner ℝ u
    ((M.deformedRealField 1 1 α (q+z)) v - (M.deformedRealField 1 1 α q) v -
    (M.deformedRealField 1 0 α z) v)
  simp only [inner_sub_left,inner_sub_right]
  exact congrArg₂ (·-·) (congrArg₂ (·-·) (h₁ u v) (h₂ u v)) (h₃ u v)

lemma normalLinearField_anticommutator (q z : Boson N) (p : SpaceIndex × ColorIndex N) :
    (∑ α : SpinIndex, (M.kineticSkewSymbol α p * M.normalLinearField q α z +
      M.normalLinearField q α z * M.kineticSkewSymbol α p)) = 0 := by
  simp only [M.normalLinearField_difference,mul_sub,sub_mul]
  have hr (a b c d e f : Fermion N →L[ℝ] Fermion N) :
      (a-b-c)+(d-e-f) = (a+d)-(b+e)-(c+f) := by abel
  simp only [hr,Finset.sum_sub_distrib,M.deformedRealField_anticommutator,
    sub_self]

lemma deformedRealField_zero (q : Boson N) (hq : q ∈ M.massiveZeros) (α : SpinIndex) :
    M.deformedRealField 1 1 α q = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have he := M.deformed_potential_average 1 1 q u
  have hq0 : M.deformedBosonicPotential 1 1 q = 0 := hq
  rw [hq0,zero_mul] at he
  change (1/16 : ℝ)*∑ β : SpinIndex, ‖M.deformedRealField 1 1 β q u‖^2 = 0 at he
  have hsum : (∑ β : SpinIndex, ‖M.deformedRealField 1 1 β q u‖^2) = 0 :=
    (mul_eq_zero.mp he).resolve_left (by norm_num)
  have hz : ‖M.deformedRealField 1 1 α q u‖^2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun β (_ : β ∈ (Finset.univ : Finset SpinIndex)) =>
      sq_nonneg ‖M.deformedRealField 1 1 β q u‖)).mp hsum α (Finset.mem_univ α)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

lemma normalLinearField_scaled (q z : Boson N) (hq : q ∈ M.massiveZeros)
    (h : ℝ) (hh : h ≠ 0) (α : SpinIndex) :
    M.deformedRealField h 1 α (h⁻¹ • q+z) =
      M.normalLinearField q α z + h • M.bracketBilinear α z z := by
  have he : M.deformedRealField h 1 α (h⁻¹ • q+z) =
      h⁻¹ • M.deformedRealField 1 1 α q +
        M.normalLinearField q α z + h • M.bracketBilinear α z z := by
    simp only [M.deformedRealField_polarized,M.normalLinearField_apply,map_add,map_smul,
      IsAddApply.add_apply,IsSMulApply.smul_apply,
      smul_add,smul_smul,←mul_assoc,mul_inv_cancel₀ hh,one_smul]
    module
  rw [he,M.deformedRealField_zero q hq α,smul_zero,zero_add]

lemma normalLinearField_potential_average (q z : Boson N) (hq : q ∈ M.massiveZeros)
    (u : Fermion N) :
    (1/16 : ℝ)*∑ α : SpinIndex, ‖M.normalLinearField q α z u‖^2 =
      M.normalQuadratic q z * ‖u‖^2 := by
  let h : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hh (n : ℕ) : 0 < h n := one_div_pos.mpr (by positivity)
  have ht : Tendsto h atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have he (n : ℕ) :
      (1/16 : ℝ)*∑ α : SpinIndex, ‖(M.normalLinearField q α z + h n • M.bracketBilinear α z z) u‖^2 =
        M.normalEffectivePotential q (h n) z * ‖u‖^2 := by
    have hn := M.deformed_potential_average (h n) 1 ((h n)⁻¹ • q+z) u
    change (1/16 : ℝ)*∑ α : SpinIndex, ‖M.deformedRealField (h n) 1 α ((h n)⁻¹ • q+z) u‖^2 = _ at hn
    simp only [M.normalLinearField_scaled q z hq (h n) (hh n).ne'] at hn
    rw [M.normalEffectivePotential_eq q hq (hh n) z] at hn
    exact hn
  have hleft : Tendsto (fun n => (1/16 : ℝ)*∑ α : SpinIndex,
      ‖(M.normalLinearField q α z + h n • M.bracketBilinear α z z) u‖^2) atTop
      (𝓝 ((1/16 : ℝ)*∑ α : SpinIndex, ‖M.normalLinearField q α z u‖^2)) := by
    apply Tendsto.const_mul
    apply tendsto_finsetSum
    intro α _
    have hc : Continuous (fun t : ℝ => ‖(M.normalLinearField q α z + t • M.bracketBilinear α z z) u‖^2) :=
      ((continuous_const.add (continuous_id.smul continuous_const)).clm_apply continuous_const).norm.pow 2
    simpa only [zero_smul,add_zero,Function.comp_def] using hc.continuousAt.tendsto.comp ht
  have hright : Tendsto (fun n => M.normalEffectivePotential q (h n) z * ‖u‖^2) atTop
      (𝓝 (M.normalQuadratic q z * ‖u‖^2)) := by
    have hc := (M.normalEffectivePotential_continuous q).tendsto (0,z)
    simpa only [M.normalEffectivePotential_zero,Function.comp_apply] using
      (hc.comp (ht.prodMk_nhds tendsto_const_nhds)).mul_const (‖u‖^2)
  exact tendsto_nhds_unique hleft (hright.congr (fun n => (he n).symm))
end
end BFSSQuantum.AlgebraData
namespace BFSSSliceAnalytic
noncomputable section
open Finset
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma contraction_projection (S : Submodule ℝ E) [S.HasOrthogonalProjection]
    (e : OrthonormalBasis ι ℝ E) (b : OrthonormalBasis κ ℝ S)
    (K : E →ₗ[ℝ] (F →L[ℝ] F)) (D : E →ₗ[ℝ] F)
    (hD : ∀ x, D (S.starProjection x) = D x) :
    (∑ j, K (b j) (D (b j))) = ∑ i, K (e i) (D (e i)) := by
  have hx (j : κ) : K (b j) = ∑ i, (inner ℝ (e i) (b j : E)) • K (e i) := by
    simpa only [map_sum,map_smul] using congrArg K (e.sum_repr' (b j : E)).symm
  simp_rw [hx,_root_.sum_apply,_root_.smul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [←map_smul,←map_sum]
  congr 1
  have hp : (∑ j, (inner ℝ (e i) (b j : E)) • (b j : E)) = S.starProjection (e i) := by
    have he := congrArg (fun x : S => (x : E)) (b.orthogonalProjectionOnto_apply_eq_sum (e i))
    simpa only [Submodule.coe_sum,Submodule.coe_smul_of_tower,real_inner_comm,Submodule.starProjection_apply] using he.symm
  rw [hp,hD]
end
end BFSSSliceAnalytic

namespace BFSSQuantum.AlgebraData
noncomputable section
open Finset MeasureTheory
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] normalSlice gaugeAction coreToL2
local instance : NormedAddCommGroup (Fermion N →L[ℝ] Fermion N) := inferInstance
local instance : NormedSpace ℝ (Fermion N →L[ℝ] Fermion N) := inferInstance

lemma normalLinearField_eq_zero (q z : Boson N) (hq : q ∈ M.massiveZeros)
    (hz : M.normalQuadratic q z = 0) (α : SpinIndex) : M.normalLinearField q α z = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have he := M.normalLinearField_potential_average q z hq u
  rw [hz,zero_mul] at he
  have hsum : (∑ β : SpinIndex, ‖M.normalLinearField q β z u‖^2) = 0 :=
    (mul_eq_zero.mp he).resolve_left (by norm_num)
  have hv : ‖M.normalLinearField q α z u‖^2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun β (_ : β ∈ (Finset.univ : Finset SpinIndex)) =>
      sq_nonneg ‖M.normalLinearField q β z u‖)).mp hsum α (Finset.mem_univ α)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hv)

lemma normalLinearField_projection (q z : Boson N) (hq : q ∈ M.massiveZeros)
    (α : SpinIndex) : M.normalLinearField q α ((M.normalSlice q).starProjection z) =
      M.normalLinearField q α z := by
  have ht : z-(M.normalSlice q).starProjection z ∈ LinearMap.range (M.gaugeTangent q) := by
    have hh := (M.normalSlice q).sub_starProjection_mem_orthogonal z
    simpa only [normalSlice,Submodule.orthogonal_orthogonal] using hh
  have hz : M.normalQuadratic q 0 = 0 := by
    simpa only [zero_smul,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_mul] using M.normalQuadratic_smul q 0 0
  have he := M.normalQuadratic_sub_tangent q (z-(M.normalSlice q).starProjection z)
    (z-(M.normalSlice q).starProjection z) hq ht
  rw [sub_self,hz] at he
  have hL := M.normalLinearField_eq_zero q _ hq he.symm α
  rw [map_sub,sub_eq_zero] at hL
  exact hL.symm

lemma kineticSkewLinear_skew (α : SpinIndex) (ξ : Boson N) (u v : Fermion N) :
    inner ℝ (M.kineticSkewLinear α ξ u) v = -inner ℝ u (M.kineticSkewLinear α ξ v) := by
  have hh : inner ℂ (M.principalSymbolLinear α ξ u) v =
      inner ℂ u (M.principalSymbolLinear α ξ v) :=
    (M.cliffordLinear_selfAdjoint (M.principalCoefficients (Pi.single α 1) ξ)).isSymmetric u v
  have hc : inner ℂ ((-Complex.I) • M.principalSymbolLinear α ξ u) v =
      -inner ℂ u ((-Complex.I) • M.principalSymbolLinear α ξ v) := by
    rw [inner_smul_left,inner_smul_right,hh]
    simp
  simpa [kineticSkewLinear,PiLp.inner_apply,real_inner_eq_re_inner,map_sum] using congrArg Complex.re hc

lemma normalLinearField_anticommutator_linear (q z ξ : Boson N) :
    (∑ α : SpinIndex, (M.kineticSkewLinear α ξ * M.normalLinearField q α z +
      M.normalLinearField q α z * M.kineticSkewLinear α ξ)) = 0 := by
  let e := EuclideanSpace.basisFun (SpaceIndex × ColorIndex N) ℝ
  have hx (α : SpinIndex) : M.kineticSkewLinear α ξ =
      ∑ p, (ξ p) • M.kineticSkewSymbol α p := by
    simpa only [map_sum,map_smul,e,EuclideanSpace.basisFun_apply,EuclideanSpace.inner_single_left,
      M.kineticSkewLinear_basis,map_one,one_mul] using congrArg (M.kineticSkewLinear α) (e.sum_repr' ξ).symm
  have hl (r : ℝ) (A B : Fermion N →L[ℝ] Fermion N) :
      (r • A)*B+B*(r • A) = r • (A*B+B*A) := by
    ext u
    simp only [IsAddApply.add_apply,mul_apply_eq_comp,
      IsSMulApply.smul_apply,map_smul,smul_add]
  simp only [hx,Finset.sum_mul,Finset.mul_sum,←Finset.sum_add_distrib,hl]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro p _
  rw [←Finset.smul_sum,M.normalLinearField_anticommutator,smul_zero]

abbrev NormalIndex (q : Boson N) := Fin (Module.finrank ℝ (M.normalSlice q))

def normalBasisVector (q : Boson N) (i : M.NormalIndex q) : Boson N :=
  (stdOrthonormalBasis ℝ (M.normalSlice q) i : M.normalSlice q)

def normalKineticSymbol (q : Boson N) (α : SpinIndex) (i : M.NormalIndex q) :
    Fermion N →L[ℝ] Fermion N :=
  (M.principalSymbolLinear α (M.normalBasisVector q i)).restrictScalars ℝ

def normalKineticSkewSymbol (q : Boson N) (α : SpinIndex) (i : M.NormalIndex q) :
    Fermion N →L[ℝ] Fermion N := M.kineticSkewLinear α (M.normalBasisVector q i)

lemma normalKineticSymbol_selfAdjoint (q : Boson N) (α : SpinIndex) (i : M.NormalIndex q) :
    IsSelfAdjoint (M.normalKineticSymbol q α i) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  have h := (M.cliffordLinear_selfAdjoint
    (M.principalCoefficients (Pi.single α 1) (M.normalBasisVector q i))).isSymmetric u v
  simpa [normalKineticSymbol,principalSymbolLinear,principalSymbol,PiLp.inner_apply,
    real_inner_eq_re_inner,map_sum] using congrArg Complex.re h

lemma normalKineticSymbol_CAR (q : Boson N) (α : SpinIndex) (i j : M.NormalIndex q) :
    M.normalKineticSymbol q α i * M.normalKineticSymbol q α j +
      M.normalKineticSymbol q α j * M.normalKineticSymbol q α i = (if i=j then 1 else 0) := by
  have hi : inner ℝ (M.normalBasisVector q i) (M.normalBasisVector q j) =
      if i=j then 1 else 0 := by
    exact (stdOrthonormalBasis ℝ (M.normalSlice q)).inner_eq_ite i j
  have h := M.principalSymbol_basis_mixed α (M.normalBasisVector q i) (M.normalBasisVector q j)
  rw [hi] at h
  ext u : 1
  have hu := congrArg (fun A : Fermion N →L[ℂ] Fermion N => A u) h
  split_ifs with hij
  · simpa [normalKineticSymbol,principalSymbolLinear,hij] using hu
  · simpa [normalKineticSymbol,principalSymbolLinear,hij] using hu

lemma normalFermion_contraction (q : Boson N) (hq : q ∈ M.massiveZeros) (u : Fermion N) :
    (1/16 : ℝ) • (∑ α : SpinIndex, ∑ i : M.NormalIndex q,
      M.normalKineticSkewSymbol q α i (M.normalLinearField q α (M.normalBasisVector q i) u)) =
      M.deformedFermionField 1 1 q u := by
  have he (α : SpinIndex) := BFSSSliceAnalytic.contraction_projection
    (M.normalSlice q) (EuclideanSpace.basisFun (SpaceIndex × ColorIndex N) ℝ)
    (stdOrthonormalBasis ℝ (M.normalSlice q)) (M.kineticSkewLinear α)
    ((ContinuousLinearMap.apply ℝ (Fermion N) u).toLinearMap.comp (M.normalLinearField q α).toLinearMap)
    (fun x => congrArg (fun A : Fermion N →L[ℝ] Fermion N => A u) (M.normalLinearField_projection q x hq α))
  change (1/16 : ℝ) • _ = _
  simp only [LinearMap.comp_apply,ContinuousLinearMap.coe_coe,ContinuousLinearMap.apply_apply,
    EuclideanSpace.basisFun_apply,M.kineticSkewLinear_basis] at he
  simp only [normalKineticSkewSymbol,normalBasisVector,he]
  simp only [deformedFermionField,MixedEnergy.remainderField,IsSMulApply.smul_apply,
    _root_.sum_apply,mul_apply_eq_comp,normalLinearField]
end
end BFSSQuantum.AlgebraData

end OAI
