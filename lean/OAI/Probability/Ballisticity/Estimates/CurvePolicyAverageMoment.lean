import Mathlib
import OAI.Probability.Ballisticity.Walk.CurvePolicyKernel
import OAI.Probability.Ballisticity.Estimates.CurveShortBlock
import OAI.Probability.Ballisticity.Estimates.SuccessfulAverageBind
import OAI.Probability.Ballisticity.Walk.KernelBoundedExpectation

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curvePolicy_average_moment {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (b : ℕ → ℝ) {A B ρ : ℝ} (hA : 0 ≤ A) (hAB : A < B) (hρ : 0 ≤ ρ)
    {H : ℕ} (hH : 0 < H) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (hd : signedCoordinate f dummy = b H) :
    let ℓ := realPosition (step e)
    let E := {u : Lattice d | |signedCoordinate f u-b H| ≤ ρ}
    let W := fun X : Path d => medianDeviation ℓ f b H X
    (∫ u, (signedCoordinate f u-b H)^2 ∂(curvePolicy_average ν ℓ f b B hH E hδ hα dummy).toMeasure) ≤
      ρ^2+A^2*(environmentLaw ν).real {ω | ¬ α*crossingQuenched ℓ 0 H ω ≤ curveIncrement ℓ f 0 b B H ω E}+
        2*(∫ X, if A < W X then (min (W X) B)^2 else 0 ∂successfulAverage ν ℓ H) := by
  let ℓ := realPosition (step e)
  let E := {u : Lattice d | |signedCoordinate f u-b H| ≤ ρ}
  let W := fun X : Path d => medianDeviation ℓ f b H X
  let T := fun X : Path d => if A < W X then (min (W X) B)^2 else 0
  let S := {ω | ¬ α*crossingQuenched ℓ 0 H ω ≤ curveIncrement ℓ f 0 b B H ω E}
  have hB : 0 ≤ B := hA.trans hAB.le
  have hW : Measurable W := measurable_medianDeviation ℓ f b H
  have hT : Measurable T := Measurable.ite (measurableSet_lt measurable_const hW)
    ((hW.min measurable_const).pow_const 2) measurable_const
  have hT0 : ∀ X, 0 ≤ T X := fun X => by dsimp [T]; split_ifs <;> positivity
  have hTB : ∀ X, T X ≤ B^2 := by
    intro X
    dsimp [T]
    split_ifs
    · exact pow_le_pow_left₀ (le_min (medianDeviation_nonneg ℓ f b H X) hB) (min_le_right _ _) 2
    · positivity
  have hQ : ∀ ω, successQuenchedKernel ℓ 0 H ω Set.univ ≤ 1 := by
    intro ω
    rw [successQuenchedKernel_apply _ _ _ _ _ MeasurableSet.univ,Set.univ_inter]
    exact ENNReal.inv_mul_le_one _
  have hTi : ∀ ω, Integrable T (successQuenchedKernel ℓ 0 H ω) := fun ω =>
    Integrable.of_bound hT.aestronglyMeasurable (B^2) (Eventually.of_forall fun X => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hT0 X)] using hTB X)
  have hTo := integrable_kernel_bounded_integral (environmentLaw ν) (successQuenchedKernel ℓ 0 H)
    T hT (sq_nonneg B) hT0 hTB hQ
  have hS : MeasurableSet S := (measurableSet_le
    (measurable_const.mul (measurable_crossingQuenched ℓ 0 H))
    ((Measure.measurable_coe E.to_countable.measurableSet).comp
      ((curveIncrement_rows ℓ f 0 b B hH).mono (rowSigma_le _) le_rfl))).compl
  have hI : Integrable (S.indicator (fun _ : Environment d => A^2)) (environmentLaw ν) :=
    (integrable_const (A^2)).indicator hS
  have hi := curvePolicy_square_outer_integrable ν e f 0 b hB hH E hδ hα dummy hd
  have hh := integral_mono_ae hi (((integrable_const (ρ^2)).add hI).add (hTo.const_mul 2)) (by
    filter_upwards [crossingQuenched_positive_ae ν hue ℓ (signed_direction_unit e) htrans] with ω hω
    have hm := curvePolicy_moment e f 0 b hA hAB hρ hH hδ hα dummy hd ω (hω 0 H)
    change (∫ u, (signedCoordinate f u-b H)^2 ∂curvePolicy ℓ f 0 b B H E δ α dummy ω) ≤
      ρ^2+S.indicator (fun _ => A^2) ω+2*(∫ X, T X ∂successQuenchedKernel ℓ 0 H ω)
    simp only [sub_zero] at hm
    change (∫ u, (signedCoordinate f u-b H)^2 ∂curvePolicy ℓ f 0 b B H E δ α dummy ω) ≤
      ρ^2+(if α*crossingQuenched ℓ 0 H ω ≤ curveIncrement ℓ f 0 b B H ω E then 0 else A^2)+
        2*(∫ X, T X ∂successQuenchedKernel ℓ 0 H ω) at hm
    simpa only [Set.indicator_apply,S,Set.mem_ofPred_eq,ite_not] using hm)
  simp only [Pi.add_apply] at hh
  have ha₁ := integral_add ((integrable_const (ρ^2)).add hI) (hTo.const_mul 2)
  have ha₂ := integral_add (integrable_const (ρ^2)) hI
  simp only [Pi.add_apply] at ha₁ ha₂
  rw [ha₁,ha₂,integral_const,probReal_univ,one_smul,
    integral_const_mul,integral_indicator hS,integral_const] at hh
  change (∫ u, (signedCoordinate f u-b H)^2 ∂(curvePolicy_average ν ℓ f b B hH E hδ hα dummy).toMeasure) ≤
    ρ^2+A^2*(environmentLaw ν).real S+2*(∫ X, T X ∂successfulAverage ν ℓ H)
  rw [curvePolicy_average_square ν e f b hB hH E hδ hα dummy hd,
    successfulAverage_integral ν ℓ H T hT hT0 hTi]
  simpa only [measureReal_restrict_apply_univ,smul_eq_mul,mul_comm (A^2)] using hh

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curvePolicy_average_zero_moment {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (b : ℕ → ℝ) {B : ℝ} (hB : 0 < B) {H : ℕ} (hH : 0 < H)
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (hd : signedCoordinate f dummy = b H) :
    let ℓ := realPosition (step e)
    let E := {u : Lattice d | |signedCoordinate f u-b H| ≤ 0}
    (∫ u, (signedCoordinate f u-b H)^2 ∂(curvePolicy_average ν ℓ f b B hH E hδ hα dummy).toMeasure) ≤
      2*(∫ X, (min (medianDeviation ℓ f b H X) B)^2 ∂successfulAverage ν ℓ H) := by
  have hm := curvePolicy_average_moment ν hue e f htrans b (A:=0) (ρ:=0)
    le_rfl hB le_rfl hH hδ hα dummy hd
  dsimp only at hm ⊢
  simp only [zero_pow (by omega : 2 ≠ 0),zero_mul,zero_add] at hm
  convert hm using 2
  apply integral_congr_ae
  filter_upwards [] with X
  split_ifs with h
  · rfl
  · have hz : medianDeviation (realPosition (step e)) f b H X=0 :=
      le_antisymm (not_lt.mp h) (medianDeviation_nonneg _ _ _ _ _)
    simp [hz,min_eq_left hB.le]
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience
lemma signedCoordinate_zsmul {d : ℕ} (e : Direction d) (a : ℤ) (x : Lattice d) :
    signedCoordinate e (a • x) = (a:ℝ)*signedCoordinate e x := by
  simp only [signedCoordinate,Pi.smul_apply,smul_eq_mul,Int.cast_mul]
  split <;> ring
lemma signedHeight_zsmul_other {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1) (a : ℤ) :
    signedHeight e (a • step f) = 0 := by
  simp [signedHeight,Pi.smul_apply,step,hef]
noncomputable def medianDummy {d : ℕ} (e f : Direction d) (H : ℕ) (b : ℤ) : Lattice d :=
  (H:ℤ) • step e+b • step f
lemma medianDummy_height {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1) (H : ℕ) (b : ℤ) :
    signedHeight e (medianDummy e f H b) = H := by
  rw [medianDummy,signedHeight_add,signedHeight_zsmul_step,signedHeight_zsmul_other e f hef,add_zero]
lemma medianDummy_coordinate {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1) (H : ℕ) (b : ℤ) :
    signedCoordinate f (medianDummy e f H b) = b := by
  rw [medianDummy,signedCoordinate_add,signedCoordinate_zsmul,signedCoordinate_zsmul,
    signedCoordinate_step_other f e hef.symm,signedCoordinate_step_self]
  ring
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience
lemma limsup_nonneg_const_mul (F : ℕ → ℝ) {C B : ℝ} (hC : 0 ≤ C)
    (hF : ∀ n, 0 ≤ F n) (hB : ∀ n, F n ≤ B) :
    limsup (fun n => C*F n) atTop = C*limsup F atTop := by
  have hb : IsBoundedUnder (· ≤ ·) atTop F := isBoundedUnder_of ⟨B,hB⟩
  have hc : IsBoundedUnder (· ≤ ·) atTop (fun _ : ℕ => C) := isBoundedUnder_of ⟨C,fun _ => le_rfl⟩
  have h1 := le_limsup_mul (u := F) (v := fun _ : ℕ => C)
    (Eventually.of_forall hF).frequently hb (Eventually.of_forall (fun _ => hC)) hc
  have h2 := limsup_mul_le (u := F) (v := fun _ : ℕ => C)
    (Eventually.of_forall hF).frequently hb (Eventually.of_forall (fun _ => hC)) hc
  change limsup F atTop * liminf (fun _ : ℕ => C) atTop ≤ limsup (fun n => F n*C) atTop at h1
  change limsup (fun n => F n*C) atTop ≤ limsup F atTop * limsup (fun _ : ℕ => C) atTop at h2
  simp only [liminf_const,limsup_const,mul_comm] at h1 h2
  exact le_antisymm h2 h1
end DirectionalTransience

end

end

end OAI
