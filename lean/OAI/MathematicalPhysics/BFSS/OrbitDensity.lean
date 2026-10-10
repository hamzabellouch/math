import Mathlib
import OAI.MathematicalPhysics.BFSS.SliceDensity

namespace OAI

/-! Stabilizer-invariant normal density and orbit measures. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory Set TopologicalSpace
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : AlgebraData N)
local instance stabilizerMeasurable (q : Boson N) : MeasurableSpace (M.gaugeStabilizer q) := borel _
local instance stabilizerBorel (q : Boson N) : BorelSpace (M.gaugeStabilizer q) := ⟨rfl⟩

def stabilizerNormalIsometry (q : Boson N) (U : M.gaugeStabilizer q) :
    M.normalSlice q ≃ₗᵢ[ℝ] M.normalSlice q where
  toFun z := ⟨M.gaugeAction U z,M.stabilizer_preserves_normalSlice q z z.prop U U.prop⟩
  invFun z := ⟨M.gaugeAction (U⁻¹ : M.gaugeStabilizer q) z,
    M.stabilizer_preserves_normalSlice q z z.prop (U⁻¹ : M.gaugeStabilizer q) (U⁻¹).prop⟩
  left_inv z := Subtype.ext (M.gaugeAction_inv U z)
  right_inv z := Subtype.ext (by
    change M.gaugeAction (U : unitary (ColorMatrix N))
      (M.gaugeAction (U : unitary (ColorMatrix N))⁻¹ z) = z
    simpa only [inv_inv] using M.gaugeAction_inv (U : unitary (ColorMatrix N))⁻¹ z)
  map_add' z w := Subtype.ext (M.gaugeAction_add U z w)
  map_smul' c z := Subtype.ext (M.gaugeAction_smul U c z)
  norm_map' z := M.gaugeAction_norm U z

lemma stabilizerNormalIsometry_one (q : Boson N) (z : M.normalSlice q) :
    M.stabilizerNormalIsometry q 1 z = z := Subtype.ext (M.gaugeAction_one z)

lemma stabilizerNormalIsometry_mul (q : Boson N) (U V : M.gaugeStabilizer q) (z : M.normalSlice q) :
    M.stabilizerNormalIsometry q (U*V) z =
      M.stabilizerNormalIsometry q U (M.stabilizerNormalIsometry q V z) :=
  Subtype.ext (M.gaugeAction_mul U V z)

attribute [local irreducible] gaugeAction

lemma stabilizerNormalIsometry_continuous (q : Boson N) :
    Continuous (fun p : M.gaugeStabilizer q × M.normalSlice q => M.stabilizerNormalIsometry q p.1 p.2) := by
  apply Continuous.subtype_mk
  have hc : Continuous (fun p : M.gaugeStabilizer q × M.normalSlice q =>
      ((p.1 : unitary (ColorMatrix N)),(p.2 : Boson N))) :=
    (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  change Continuous (fun p : M.gaugeStabilizer q × M.normalSlice q =>
    M.gaugeAction (p.1 : unitary (ColorMatrix N)) (p.2 : Boson N))
  exact M.gaugeAction_continuous.comp hc

def stabilizerPositiveCompact (hN : 2 ≤ N) (q : Boson N) : PositiveCompacts (M.gaugeStabilizer q) where
  carrier := univ
  isCompact' := by
    let := isCompact_iff_compactSpace.mp (M.gaugeStabilizer_isCompact hN q)
    exact isCompact_univ
  interior_nonempty' := by simp

def stabilizerHaar (hN : 2 ≤ N) (q : Boson N) : Measure (M.gaugeStabilizer q) :=
  Measure.haarMeasure (M.stabilizerPositiveCompact hN q)

instance stabilizerHaar_isHaar (hN : 2 ≤ N) (q : Boson N) :
    (M.stabilizerHaar hN q).IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure _

instance stabilizerHaar_isProbability (hN : 2 ≤ N) (q : Boson N) :
    IsProbabilityMeasure (M.stabilizerHaar hN q) where
  measure_univ := Measure.haarMeasure_self

def normalInvariantDensity (hN : 2 ≤ N) (q : Boson N) (J : M.normalSlice q → ℝ)
    (z : M.normalSlice q) : ℝ :=
  ∫ U, J (M.stabilizerNormalIsometry q U⁻¹ z) ∂M.stabilizerHaar hN q

lemma normalInvariantDensity_zero (hN : 2 ≤ N) (q : Boson N) (J : M.normalSlice q → ℝ) :
    M.normalInvariantDensity hN q J 0 = J 0 := by
  simp [normalInvariantDensity]

lemma normalInvariantDensity_nonneg (hN : 2 ≤ N) (q : Boson N) (J : M.normalSlice q → ℝ)
    (hJ : ∀ z, 0 ≤ J z) (z : M.normalSlice q) :
    0 ≤ M.normalInvariantDensity hN q J z := integral_nonneg (fun _ => hJ _)

lemma normalInvariantDensity_continuous (hN : 2 ≤ N) (q : Boson N) (J : M.normalSlice q → ℝ)
    (hJ : Continuous J) : Continuous (M.normalInvariantDensity hN q J) := by
  change Continuous (fun z => ∫ U, J (M.stabilizerNormalIsometry q U⁻¹ z) ∂M.stabilizerHaar hN q)
  let := isCompact_iff_compactSpace.mp (M.gaugeStabilizer_isCompact hN q)
  have hc : Continuous (fun p : M.normalSlice q × M.gaugeStabilizer q => (p.2⁻¹,p.1)) :=
    continuous_snd.inv.prodMk continuous_fst
  have ha := (M.stabilizerNormalIsometry_continuous q).comp hc
  have hi := continuous_parametric_integral_of_continuous (μ := M.stabilizerHaar hN q)
    (f := fun z U => J (M.stabilizerNormalIsometry q U⁻¹ z)) (hJ.comp ha) isCompact_univ
  simpa only [Measure.restrict_univ] using hi

lemma normalInvariantDensity_invariant (hN : 2 ≤ N) (q : Boson N) (J : M.normalSlice q → ℝ)
    (U : M.gaugeStabilizer q) (z : M.normalSlice q) :
    M.normalInvariantDensity hN q J (M.stabilizerNormalIsometry q U z) =
      M.normalInvariantDensity hN q J z := by
  have he := integral_mul_left_eq_self (μ := M.stabilizerHaar hN q)
    (fun V => J (M.stabilizerNormalIsometry q V⁻¹ z)) U⁻¹
  simp only [_root_.mul_inv_rev,inv_inv,M.stabilizerNormalIsometry_mul] at he
  exact he

end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : AlgebraData N)
local instance normalHaarMeasurable (q : Boson N) : MeasurableSpace (M.gaugeStabilizer q) := borel _
local instance normalHaarBorel (q : Boson N) : BorelSpace (M.gaugeStabilizer q) := ⟨rfl⟩

theorem normalInvariantDensity_integral (hN : 2 ≤ N) (q : Boson N)
    (b F : M.normalSlice q → ℝ)
    (hb : Continuous b) (hF : Continuous F) (hFc : HasCompactSupport F)
    (hFi : ∀ U : M.gaugeStabilizer q, ∀ x, F (M.stabilizerNormalIsometry q U x) = F x) :
    (∫ x, M.normalInvariantDensity hN q b x * F x) = ∫ x, b x * F x := by
  let : CompactSpace (M.gaugeStabilizer q) :=
    isCompact_iff_compactSpace.mp (M.gaugeStabilizer_isCompact hN q)
  let g : M.gaugeStabilizer q → M.normalSlice q → ℝ :=
    fun U x => b (M.stabilizerNormalIsometry q U⁻¹ x) * F x
  have hact : Continuous (fun p : M.gaugeStabilizer q × M.normalSlice q => (p.1⁻¹,p.2)) :=
    continuous_fst.inv.prodMk continuous_snd
  have hga := (M.stabilizerNormalIsometry_continuous q).comp hact
  have hgb := hb.comp hga
  have hF' : Continuous (fun p : M.gaugeStabilizer q × M.normalSlice q => F p.2) :=
    hF.comp continuous_snd
  have hg : Continuous g.uncurry := hgb.mul hF' 
  have hgc : HasCompactSupport g.uncurry := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_univ.prod hFc)
    rintro ⟨U,x⟩ hx
    refine ⟨Set.mem_univ U,subset_tsupport F ?_⟩
    intro he
    exact hx (by simp only [g,Function.uncurry_apply_pair,he,mul_zero])
  have hi (U : M.gaugeStabilizer q) :
      (∫ x, g U x) = ∫ x, b x * F x := by
    have hp := ((M.stabilizerNormalIsometry q U⁻¹).measurePreserving).integral_comp
      (M.stabilizerNormalIsometry q U⁻¹).toHomeomorph.measurableEmbedding
      (fun x => b x * F x)
    change (∫ x, b (M.stabilizerNormalIsometry q U⁻¹ x) * F (M.stabilizerNormalIsometry q U⁻¹ x)) = _ at hp
    simpa only [g,hFi] using hp
  calc
    (∫ x, M.normalInvariantDensity hN q b x * F x) = ∫ x, ∫ U, g U x ∂M.stabilizerHaar hN q := by
      apply integral_congr_ae
      filter_upwards with x
      exact (integral_mul_const (F x) (fun U => b (M.stabilizerNormalIsometry q U⁻¹ x))).symm
    _ = ∫ U, (∫ x, g U x) ∂M.stabilizerHaar hN q :=
      (integral_integral_swap_of_hasCompactSupport hg hgc).symm
    _ = ∫ U, (∫ x, b x * F x) ∂M.stabilizerHaar hN q := by simp_rw [hi]
    _ = ∫ x, b x * F x := by simp

end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory Set TopologicalSpace
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] gaugeAction

lemma normalAffine_isometry (q : Boson N) :
    Isometry (fun z : M.normalSlice q => q + (z : Boson N)) := by
  intro z w
  simp only [edist_dist,dist_add_left]
  rfl

lemma normalAffine_compactSupport (q : Boson N) (F : Boson N → ℝ)
    (hF : HasCompactSupport F) :
    HasCompactSupport (fun z : M.normalSlice q => F (q+(z : Boson N))) :=
  hF.comp_isClosedEmbedding (M.normalAffine_isometry q).isClosedEmbedding

theorem normalOrbit_measure (hN : 2 ≤ N) (q : Boson N) :
    ∃ (J : M.normalSlice q → ℝ) (V : Set (Boson N)) (δ : ℝ),
      Continuous J ∧ (∀ z, 0 ≤ J z) ∧ 0 < J 0 ∧ 0 < δ ∧
      (∀ z, ‖z‖ < δ → J 0 / 2 < J z ∧ J z < 2 * J 0) ∧
      (∀ U : M.gaugeStabilizer q, ∀ z, J (M.stabilizerNormalIsometry q U z) = J z) ∧
      IsOpen V ∧ M.gaugeOrbit q ⊆ V ∧
      (∀ U : unitary (ColorMatrix N), ∀ x, M.gaugeAction U x ∈ V ↔ x ∈ V) ∧
      ∀ (h : ℝ), 0 < h → ∀ F : Boson N → ℝ, Continuous F → HasCompactSupport F →
        (∀ U : unitary (ColorMatrix N), ∀ x, F (M.gaugeAction U x) = F x) →
        (∀ x ∈ Function.support F, h • x ∈ V) →
        (∫ x, F x) = (h ^ M.orbitDimension q)⁻¹ *
          ∫ z : M.normalSlice q, J (h • z) * F (h⁻¹ • q+(z : Boson N)) := by
  obtain ⟨J,V,_,hJ,hJn,hJ0,_,_,hV,hqV,hVi,hmeasure⟩ := M.normalSlice_measure_exists hN q
  let K := M.normalInvariantDensity hN q J
  have hK : Continuous K := M.normalInvariantDensity_continuous hN q J hJ
  have hK0 : 0 < K 0 := by
    dsimp [K]
    rwa [M.normalInvariantDensity_zero]
  have hneigh : {z : M.normalSlice q | K 0 / 2 < K z ∧ K z < 2 * K 0} ∈ nhds 0 := by
    apply (isOpen_lt continuous_const hK |>.inter (isOpen_lt hK continuous_const)).mem_nhds
    change K 0 / 2 < K 0 ∧ K 0 < 2 * K 0
    exact ⟨by linarith,by linarith⟩
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hneigh
  refine ⟨K,V,r,hK,M.normalInvariantDensity_nonneg hN q J hJn,hK0,hr,?_,
    M.normalInvariantDensity_invariant hN q J,hV,hqV,hVi,?_⟩
  · intro z hz
    exact hrsub (by simpa only [Metric.mem_ball,dist_zero_right] using hz)
  · intro h hh F hF hFK hFi hs
    apply M.normalSlice_scaled_measure q K V ?_ hh F hF hFK hFi hs
    intro G hG hGK hGi hGs
    rw [hmeasure G hG hGK hGi hGs]
    have hc : Continuous (fun z : M.normalSlice q => G (q+(z : Boson N))) :=
      hG.comp (continuous_const.add continuous_subtype_val)
    have hi (U : M.gaugeStabilizer q) (z : M.normalSlice q) :
        G (q+((M.stabilizerNormalIsometry q U z) : Boson N)) = G (q+(z : Boson N)) := by
      change G (q+M.gaugeAction U z) = G (q+(z : Boson N))
      have hU : M.gaugeAction U q = q := U.prop
      have ha : M.gaugeAction U (q+(z : Boson N)) = q+M.gaugeAction U z := by
        rw [M.gaugeAction_add,hU]
      rw [←ha,hGi]
    exact (M.normalInvariantDensity_integral hN q J _ hJ hc
      (M.normalAffine_compactSupport q G hGK) hi).symm

end
end BFSSQuantum.AlgebraData

end OAI
