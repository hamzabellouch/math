import Mathlib
import OAI.MathematicalPhysics.BFSS.OrbitDensity

namespace OAI

/-! Gauge-neighborhood cutoffs and local integral bounds. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory Set TopologicalSpace
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : AlgebraData N)
local instance gaugeMeasurableSpace₅ : MeasurableSpace (unitary (ColorMatrix N)) := borel _
local instance gaugeBorelSpace₅ : BorelSpace (unitary (ColorMatrix N)) := ⟨rfl⟩
attribute [local irreducible] gaugeAction

lemma gauge_neighborhood_cutoff (hN : 2 ≤ N) (q : Boson N)
    (V : Set (Boson N)) (hV : IsOpen V) (hq : q ∈ V)
    (hVi : ∀ U : unitary (ColorMatrix N), ∀ x, M.gaugeAction U x ∈ V ↔ x ∈ V) :
    ∃ φ : Boson N → ℝ, Continuous φ ∧ (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
      0 < φ q ∧ (∀ U : unitary (ColorMatrix N), ∀ x, φ (M.gaugeAction U x) = φ x) ∧
      Function.support φ ⊆ V := by
  obtain ⟨r,hr,hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hq)
  let b : ContDiffBump q := ⟨r/2,r,half_pos hr,half_lt_self hr⟩
  let φ := M.gaugeAverage hN b
  have hbq : (b : Boson N → ℝ) q = 1 :=
    b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
  have hbs : Function.support (b : Boson N → ℝ) ⊆ V := by
    apply (subset_tsupport b).trans
    rw [b.tsupport_eq]
    exact hrsub
  let : CompactSpace (unitary (ColorMatrix N)) :=
    isCompact_iff_compactSpace.mp (BFSSOrbit.unitary_compact hN)
  refine ⟨φ,M.gaugeAverage_continuous hN b b.continuous,?_,?_,
    M.gaugeAverage_invariant hN b,?_⟩
  · intro x
    have hc : Continuous (fun U : unitary (ColorMatrix N) => b (M.gaugeAction U⁻¹ x)) :=
      b.continuous.comp ((M.gaugeOrbitMap_continuous x).comp continuous_inv)
    have hi : Integrable (fun U : unitary (ColorMatrix N) => b (M.gaugeAction U⁻¹ x)) (gaugeHaar hN) :=
      hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    refine ⟨integral_nonneg (fun U => b.nonneg),?_⟩
    change (∫ U, b (M.gaugeAction U⁻¹ x) ∂gaugeHaar hN) ≤ 1
    calc
      _ ≤ ∫ _U : unitary (ColorMatrix N), (1 : ℝ) ∂gaugeHaar hN :=
        integral_mono hi (integrable_const 1) (fun _ => b.le_one)
      _ = 1 := by simp
  · exact M.gaugeAverage_pos hN b b.continuous (fun _ => b.nonneg) q (by rw [hbq]; norm_num)
  · intro x hx
    by_contra hnot
    apply hx
    apply integral_eq_zero_of_ae
    filter_upwards with U
    apply Function.notMem_support.mp
    intro hb
    exact hnot ((hVi U⁻¹ x).mp (hbs hb))

end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory Set TopologicalSpace
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] gaugeAction

theorem normalOrbit_local_integral_bound (hN : 2 ≤ N) (q : Boson N) :
    ∃ η B : ℝ, 0 < η ∧ 0 < B ∧
      ∀ h R : ℝ, 0 < h → 0 ≤ R → h * R < η →
      ∀ W : Boson N → ℝ, Continuous W → HasCompactSupport W →
        (∀ x, 0 ≤ W x) →
        (∀ U : unitary (ColorMatrix N), ∀ x, W (M.gaugeAction U x) = W x) →
        (h ^ M.orbitDimension q)⁻¹ *
          (∫ z : M.normalSlice q in Metric.closedBall 0 R, W (h⁻¹ • q+(z : Boson N))) ≤
          B * ∫ x, W x := by
  obtain ⟨J,V,δ,hJ,hJn,hJ0,hδ,hδJ,_,hV,hqV,hVi,hmeasure⟩ := M.normalOrbit_measure hN q
  obtain ⟨φ,hφ,hφb,hφq,hφi,hφs⟩ := M.gauge_neighborhood_cutoff hN q V hV
    (hqV (M.self_mem_gaugeOrbit q)) hVi
  obtain ⟨s,hs,hssub⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_lt continuous_const hφ).mem_nhds (half_lt_self hφq))
  let C : ℝ := J 0 / 2 * (φ q / 2)
  have hC : 0 < C := mul_pos (half_pos hJ0) (half_pos hφq)
  refine ⟨min δ s,C⁻¹,lt_min hδ hs,inv_pos.mpr hC,?_⟩
  intro h R hh hR hhR W hW hWK hWn hWi
  let F : Boson N → ℝ := fun x => φ (h • x) * W x
  have hsmul : Continuous (fun x : Boson N => h • x) :=
    (continuous_const : Continuous (fun _ : Boson N => h)).smul continuous_id
  have hFc : Continuous F := (hφ.comp hsmul).mul hW
  have hFK : HasCompactSupport F := hWK.mul_left
  have hFi (U : unitary (ColorMatrix N)) (x : Boson N) : F (M.gaugeAction U x) = F x := by
    dsimp [F]
    rw [←M.gaugeAction_smul,hφi,hWi]
  have hFs (x : Boson N) (hx : x ∈ Function.support F) : h • x ∈ V := by
    apply hφs
    intro hz
    exact hx (by simp only [F,hz,zero_mul])
  have hm := hmeasure h hh F hFc hFK hFi hFs
  let a : M.normalSlice q → Boson N := fun z => h⁻¹ • q+(z : Boson N)
  have ha : Continuous a := continuous_const.add continuous_subtype_val
  have hWa : Continuous (W ∘ a) := hW.comp ha
  have haiso : Isometry a := by
    intro z w
    simp only [a,edist_add_left]
    rfl
  have hWaK : HasCompactSupport (W ∘ a) := hWK.comp_isClosedEmbedding haiso.isClosedEmbedding
  have hWai : Integrable (W ∘ a) := hWa.integrable_of_hasCompactSupport hWaK
  let T : M.normalSlice q → ℝ := fun z => J (h • z) * F (a z)
  have hzsmul : Continuous (fun z : M.normalSlice q => h • z) :=
    (continuous_const : Continuous (fun _ : M.normalSlice q => h)).smul continuous_id
  have hTc : Continuous T := (hJ.comp hzsmul).mul (hFc.comp ha)
  have hTK : HasCompactSupport T :=
    (hFK.comp_isClosedEmbedding haiso.isClosedEmbedding).mul_left
  have hTi : Integrable T := hTc.integrable_of_hasCompactSupport hTK
  have hTn (z : M.normalSlice q) : 0 ≤ T z :=
    mul_nonneg (hJn _) (mul_nonneg (hφb _).1 (hWn _))
  have hscale (z : M.normalSlice q) : h • a z = q+h • (z : Boson N) := by
    dsimp [a]
    rw [smul_add,smul_smul,mul_inv_cancel₀ hh.ne',one_smul]
  have hlower (z : M.normalSlice q) (hz : z ∈ Metric.closedBall 0 R) :
      C * W (a z) ≤ T z := by
    have hzn : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    have hzh : ‖h • z‖ < min δ s := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hh]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hzn hh.le) hhR
    have hJz := (hδJ (h • z) (lt_of_lt_of_le hzh (min_le_left _ _))).1.le
    have hφz : φ q / 2 ≤ φ (q+h • (z : Boson N)) := by
      apply le_of_lt
      apply hssub
      simpa only [Metric.mem_ball,dist_self_add_left,norm_neg,dist_eq_norm,add_sub_cancel_left,
        norm_smul,Submodule.norm_coe] using
        (lt_of_lt_of_le hzh (min_le_right _ _))
    have hp : C ≤ J (h • z) * φ (q+h • (z : Boson N)) :=
      mul_le_mul hJz hφz (half_pos hφq).le (hJn _)
    dsimp [T,F]
    rw [hscale]
    nlinarith [mul_le_mul_of_nonneg_right hp (hWn (a z))]
  have hloc : C * (∫ z : M.normalSlice q in Metric.closedBall 0 R, W (a z)) ≤ ∫ z, T z := by
    calc
      _ = ∫ z : M.normalSlice q in Metric.closedBall 0 R, C * W (a z) :=
        (integral_const_mul _ _).symm
      _ ≤ ∫ z : M.normalSlice q in Metric.closedBall 0 R, T z :=
        setIntegral_mono_on (hWai.const_mul C).integrableOn hTi.integrableOn
          Metric.isClosed_closedBall.measurableSet hlower
      _ ≤ ∫ z, T z := integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall hTn) hTi
  have hFupper : (∫ x, F x) ≤ ∫ x, W x := by
    apply integral_mono (hFc.integrable_of_hasCompactSupport hFK)
      (hW.integrable_of_hasCompactSupport hWK)
    intro x
    exact mul_le_of_le_one_left (hWn x) (hφb _).2
  have hspos : 0 < (h ^ M.orbitDimension q)⁻¹ := inv_pos.mpr (pow_pos hh _)
  have hhbound := (mul_le_mul_of_nonneg_left hloc hspos.le).trans
    (by simpa only [T,a,←hm] using hFupper)
  have hh' : C * ((h ^ M.orbitDimension q)⁻¹ * ∫ z : M.normalSlice q in Metric.closedBall 0 R,
      W (h⁻¹ • q+(z : Boson N))) ≤ ∫ x, W x := by
    simpa only [a,mul_left_comm] using hhbound
  exact (le_inv_mul_iff₀ hC).mpr hh'

end
end BFSSQuantum.AlgebraData

end OAI
