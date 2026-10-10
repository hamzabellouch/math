import Mathlib
import OAI.MathematicalPhysics.BFSS.GaugeOrbits

namespace OAI

/-! Uniform scaling limits of normal bosonic and fermionic potentials. -/

namespace BFSSSliceAnalytic
open Set Filter Topology
lemma continuous_parameter_uniformOn {E F : Type*} [UniformSpace E] [UniformSpace F]
    (f : ℝ → E → F) (hf : Continuous (Function.uncurry f))
    (K : Set E) (hK : IsCompact K) :
    TendstoUniformlyOn f (f 0) (nhds 0) K := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  exact Continuous.tendstoUniformly (fun h (z : K) => f h z)
    (hf.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) 0
end BFSSSliceAnalytic
namespace BFSSQuantum.AlgebraData
noncomputable section
open Finset Set Filter Topology
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] coreToL2 charge bracketPart normalSlice gaugeAction

def normalEffectivePotential (q : Boson N) (h : ℝ) (z : Boson N) : ℝ :=
    (‖M.cyclicLinearization q z 0 1 2 + h • M.colorLie (spatialColor z 0) (spatialColor z 1)‖^2 +
     ‖M.cyclicLinearization q z 1 2 0 + h • M.colorLie (spatialColor z 1) (spatialColor z 2)‖^2 +
     ‖M.cyclicLinearization q z 2 0 1 + h • M.colorLie (spatialColor z 2) (spatialColor z 0)‖^2 +
     (∑ i : SpaceIndex, ∑ j : SpaceIndex, if i < j ∧ 3 ≤ j.val then
       ‖M.bracketLinearization q z i j + h • M.colorLie (spatialColor z i) (spatialColor z j)‖^2 else 0) +
     (∑ d : SpaceIndex, if 3 ≤ d.val then ‖spatialColor z d‖^2 else 0))/2

lemma normalEffectivePotential_zero (q z : Boson N) :
    M.normalEffectivePotential q 0 z = M.normalQuadratic q z := by
  simp only [normalEffectivePotential,normalQuadratic,zero_smul,add_zero]

lemma normalEffectivePotential_continuous (q : Boson N) :
    Continuous (fun p : ℝ × Boson N => M.normalEffectivePotential q p.1 p.2) := by
  have hc (i j k : SpaceIndex) : Continuous (fun p : ℝ × Boson N =>
      ‖M.cyclicLinearization q p.2 i j k + p.1 • M.colorLie (spatialColor p.2 i) (spatialColor p.2 j)‖^2) := by
    simp_rw [←M.cyclicLinearizationMap_apply]
    exact (((M.cyclicLinearizationMap q i j k).continuous_of_finiteDimensional.comp continuous_snd).add
      (continuous_fst.smul ((M.spatialBracket_continuous i j).comp continuous_snd))).norm.pow 2
  have hb : Continuous (fun p : ℝ × Boson N => ∑ i : SpaceIndex, ∑ j : SpaceIndex,
      if i < j ∧ 3 ≤ j.val then
        ‖M.bracketLinearization q p.2 i j + p.1 • M.colorLie (spatialColor p.2 i) (spatialColor p.2 j)‖^2 else 0) := by
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by
      split_ifs
      · simp_rw [←M.bracketLinearizationMap_apply]
        exact (((M.bracketLinearizationMap q i j).continuous_of_finiteDimensional.comp continuous_snd).add
          (continuous_fst.smul ((M.spatialBracket_continuous i j).comp continuous_snd))).norm.pow 2
      · exact continuous_const
  have hs : Continuous (fun p : ℝ × Boson N => ∑ d : SpaceIndex,
      if 3 ≤ d.val then ‖spatialColor p.2 d‖^2 else 0) := by
    exact continuous_finsetSum _ fun d _ => by
      split_ifs
      · exact (((spatialColorMap d).continuous_of_finiteDimensional.comp continuous_snd).norm.pow 2)
      · exact continuous_const
  exact (((((hc 0 1 2).add (hc 1 2 0)).add (hc 2 0 1)).add hb).add hs).div_const 2

lemma potential_scaled_taylor (q z : Boson N) (hq : q ∈ M.massiveZeros) (h : ℝ) :
    M.deformedBosonicPotential 1 1 (q+h • z) = h^2 * M.normalEffectivePotential q h z := by
  rw [M.potential_taylor_squares q _ hq]
  have hc (i j k : SpaceIndex) :
      M.cyclicLinearization q (h • z) i j k + M.colorLie (spatialColor (h • z) i) (spatialColor (h • z) j) =
      h • (M.cyclicLinearization q z i j k + h • M.colorLie (spatialColor z i) (spatialColor z j)) := by
    simp only [←M.cyclicLinearizationMap_apply,map_smul,spatialColor_smul,
      M.colorLie_smul_left,M.colorLie_smul_right,smul_add]
  have hb (i j : SpaceIndex) :
      M.bracketLinearization q (h • z) i j + M.colorLie (spatialColor (h • z) i) (spatialColor (h • z) j) =
      h • (M.bracketLinearization q z i j + h • M.colorLie (spatialColor z i) (spatialColor z j)) := by
    simp only [←M.bracketLinearizationMap_apply,map_smul,spatialColor_smul,
      M.colorLie_smul_left,M.colorLie_smul_right,smul_add]
  simp_rw [hc,hb]
  simp only [spatialColor_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  have hif (P : Prop) [Decidable P] (a : ℝ) :
      (if P then h^2*a else 0) = h^2 * (if P then a else 0) := by split_ifs <;> simp
  simp_rw [hif]
  simp only [←Finset.mul_sum,normalEffectivePotential]
  ring

lemma normalEffectivePotential_eq (q : Boson N) (hq : q ∈ M.massiveZeros)
    {h : ℝ} (hh : 0 < h) (z : Boson N) :
    M.deformedBosonicPotential h 1 (h⁻¹ • q+z) = M.normalEffectivePotential q h z := by
  rw [M.deformedBosonicPotential_scaling h 1 hh (by norm_num)]
  simp only [div_one,one_pow,smul_add,smul_smul,mul_inv_cancel₀ hh.ne',one_smul]
  rw [M.potential_scaled_taylor q z hq h]
  field_simp

theorem normalPotential_uniform_limit (q : Boson N) (hq : q ∈ M.massiveZeros)
    (K : Set (Boson N)) (hK : IsCompact K) :
    TendstoUniformlyOn (fun h z => M.deformedBosonicPotential h 1 (h⁻¹ • q+z))
      (M.normalQuadratic q) (nhdsWithin 0 (Ioi 0)) K := by
  have hu := BFSSSliceAnalytic.continuous_parameter_uniformOn (M.normalEffectivePotential q)
    (M.normalEffectivePotential_continuous q) K hK
  have h0 : M.normalEffectivePotential q 0 = M.normalQuadratic q :=
    funext (M.normalEffectivePotential_zero q)
  rw [h0] at hu
  have hw : TendstoUniformlyOn (M.normalEffectivePotential q) (M.normalQuadratic q)
      (nhdsWithin 0 (Ioi 0)) K :=
    fun u hu' => (hu u hu').filter_mono nhdsWithin_le_nhds
  apply hw.congr
  filter_upwards [self_mem_nhdsWithin] with h hh
  intro z _
  exact (M.normalEffectivePotential_eq q hq hh z).symm
end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
open Finset Set Filter Topology
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] coreToL2 charge bracketPart normalSlice gaugeAction

lemma deformedRealField_fderiv (h m : ℝ) (α : SpinIndex) (x v : Boson N) :
    fderiv ℝ (M.deformedRealField h m α) x v =
      h • (M.bracketBilinear α x v + M.bracketBilinear α v x) + m • M.massLinear α v := by
  have he : M.deformedRealField h m α = fun y =>
      h • M.bracketBilinear α y y + m • M.massLinear α y :=
    funext (M.deformedRealField_polarized h m α)
  rw [he]
  exact BilinearGrowth.derivative_quadratic_linear _ _ _ _ _ _

lemma deformedFermionField_normal_affine (q z : Boson N) {h : ℝ} (hh : h ≠ 0) :
    M.deformedFermionField h 1 (h⁻¹ • q+z) =
      M.deformedFermionField 1 1 q + h • M.deformedFermionField 1 0 z := by
  have he (α : SpinIndex) (v : Boson N) :
      fderiv ℝ (M.deformedRealField h 1 α) (h⁻¹ • q+z) v =
        fderiv ℝ (M.deformedRealField 1 1 α) q v +
          h • fderiv ℝ (M.deformedRealField 1 0 α) z v := by
    simp only [M.deformedRealField_fderiv,map_add,map_smul,
      add_apply,smul_apply,
      smul_add,smul_smul,mul_inv_cancel₀ hh,one_smul]
    module
  simp only [deformedFermionField,MixedEnergy.remainderField,he,
    mul_add,mul_smul_comm,Finset.sum_add_distrib,←Finset.smul_sum,smul_add,smul_smul]
  module

lemma deformedFermionField_continuous (h m : ℝ) : Continuous (M.deformedFermionField h m) := by
  unfold deformedFermionField MixedEnergy.remainderField
  apply Continuous.smul (M := ℝ) (X := Fermion N →L[ℝ] Fermion N) continuous_const
  apply continuous_finsetSum
  intro α _
  apply continuous_finsetSum
  intro p _
  simp only [M.deformedRealField_fderiv]
  have hB : Continuous (fun x : Boson N => M.bracketBilinear α x (EuclideanSpace.single p 1)) :=
    (M.bracketBilinear α).continuous.clm_apply continuous_const
  have hB' : Continuous (fun x : Boson N => M.bracketBilinear α (EuclideanSpace.single p 1) x) :=
    (M.bracketBilinear α (EuclideanSpace.single p 1)).continuous
  exact continuous_const.mul (((hB.add hB').const_smul h).add continuous_const)

theorem normalFermion_uniform_limit (q : Boson N) (K : Set (Boson N)) (hK : IsCompact K) :
    TendstoUniformlyOn (fun h z => M.deformedFermionField h 1 (h⁻¹ • q+z))
      (fun _ => M.deformedFermionField 1 1 q) (nhdsWithin 0 (Ioi 0)) K := by
  let F := fun (h : ℝ) (z : Boson N) => M.deformedFermionField 1 1 q + h • M.deformedFermionField 1 0 z
  have hF : Continuous (Function.uncurry F) :=
    continuous_const.add (continuous_fst.smul ((M.deformedFermionField_continuous 1 0).comp continuous_snd))
  have hu := BFSSSliceAnalytic.continuous_parameter_uniformOn F hF K hK
  have h0 : F 0 = fun _ => M.deformedFermionField 1 1 q := by
    funext z
    change M.deformedFermionField 1 1 q + (0 : ℝ) • M.deformedFermionField 1 0 z = _
    module
  rw [h0] at hu
  have hw : TendstoUniformlyOn F (fun _ => M.deformedFermionField 1 1 q)
      (nhdsWithin 0 (Ioi 0)) K :=
    fun u hu' => (hu u hu').filter_mono nhdsWithin_le_nhds
  apply hw.congr
  filter_upwards [self_mem_nhdsWithin] with h hh
  intro z _
  exact (M.deformedFermionField_normal_affine q z (ne_of_gt hh)).symm
end
end BFSSQuantum.AlgebraData

end OAI
