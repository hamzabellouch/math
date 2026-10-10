import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Recursion.TensorCapCompact
import OAI.MeasureTheory.FalconerCompletion.Shells.PrefixCutoff
import OAI.MeasureTheory.FalconerCompletion.Shells.TransportedAngularField

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer
open scoped ContDiff
variable {n : ℕ}
namespace PositiveDistanceState
variable (e : PositiveDistanceState (n+1))

noncomputable def prefixSpatialLeft (p : PrefixAssignment n)
    (ξ : EuclideanSpace ℝ (Fin (n+1))) (z : ℝ × EuclideanSpace ℝ (Fin (n+1))) : ℂ :=
  Attempt4PrefixShell.spatialEndpointTransformND ((2:ℝ)^e.a)⁻¹ e.ρ (treeCell e.X)
    e.levelMass (e.prefixInverseLeft p) (ξ,z)
noncomputable def prefixSpatialRight (p : PrefixAssignment n)
    (ξ : EuclideanSpace ℝ (Fin (n+1))) (z : ℝ × EuclideanSpace ℝ (Fin (n+1))) : ℂ :=
  Attempt4PrefixShell.spatialEndpointTransformND ((2:ℝ)^e.a)⁻¹ e.ρ (treeCell e.Y)
    e.levelMass (e.prefixInverseRight p) (ξ,z)

lemma prefixSpatialLeft_measurable [SFinite e.ρ] (p : PrefixAssignment n)
    (ξ : EuclideanSpace ℝ (Fin (n+1))) : Measurable (e.prefixSpatialLeft p ξ) :=
  (Attempt4PrefixShell.spatialEndpointTransformND_measurable _ _ _ _
    (e.prefixInverseLeft_measurable p)).comp (measurable_const.prodMk measurable_id)
lemma prefixSpatialRight_measurable [SFinite e.ρ] (p : PrefixAssignment n)
    (ξ : EuclideanSpace ℝ (Fin (n+1))) : Measurable (e.prefixSpatialRight p ξ) :=
  (Attempt4PrefixShell.spatialEndpointTransformND_measurable _ _ _ _
    (e.prefixInverseRight_measurable p)).comp (measurable_const.prodMk measurable_id)

lemma prefixSpatial_global_bound [IsFiniteMeasure e.ρ] (p : PrefixAssignment n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ξ z, ‖e.prefixSpatialLeft p ξ z‖ ≤ B ∧
      ‖e.prefixSpatialRight p ξ z‖ ≤ B := by
  obtain ⟨D,hD,h⟩ := e.prefixInverse_global_bound p
  let B := |e.levelMass⁻¹| * (D*(e.ρ.restrict (treeCell e.X)).real univ)
  let C := |e.levelMass⁻¹| * (D*(e.ρ.restrict (treeCell e.Y)).real univ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨max B C,hB.trans (le_max_left _ _),?_⟩
  intro ξ z
  have hleft := Attempt4PrefixShell.spatialEndpointTransformND_bound ((2:ℝ)^e.a)⁻¹ e.ρ
    (treeCell e.X) e.levelMass (e.prefixInverseLeft p) (fun x w => (h x w).1) (ξ,z)
  have hright := Attempt4PrefixShell.spatialEndpointTransformND_bound ((2:ℝ)^e.a)⁻¹ e.ρ
    (treeCell e.Y) e.levelMass (e.prefixInverseRight p) (fun x w => (h x w).2) (ξ,z)
  exact ⟨hleft.trans (le_max_left _ _),hright.trans (le_max_right _ _)⟩

noncomputable def prefixAngularCorrelation (p : PrefixAssignment n)
    (ξ : EuclideanSpace ℝ (Fin (n+1))) (r : ℝ) : ℂ :=
  Attempt4PrefixShell.sourceAngularCorrelationND
    (Attempt4PrefixShell.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1))))
    e.prefixCutoff (e.prefixSpatialLeft p ξ) (e.prefixSpatialRight p ξ) r

noncomputable def prefixAngularHF (v : ℝ) (Ψ : ℝ → ℝ)
    (p : PrefixAssignment n) (ξ : EuclideanSpace ℝ (Fin (n+1))) : ℝ :=
  Attempt4PrefixShell.sourceAngularHFND (n+1)
    (Attempt4PrefixShell.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1))))
    e.a v Ψ e.prefixCutoff (e.prefixSpatialLeft p ξ) (e.prefixSpatialRight p ξ)

lemma prefixAngularCorrelation_measurable [SFinite e.ρ] (p : PrefixAssignment n)
    (ξ : EuclideanSpace ℝ (Fin (n+1))) : Measurable (e.prefixAngularCorrelation p ξ) :=
  Attempt4PrefixShell.sourceAngularCorrelationND_measurable _ e.prefixCutoff_contDiff.continuous.measurable
    (e.prefixSpatialLeft_measurable p ξ) (e.prefixSpatialRight_measurable p ξ)

lemma prefixAngularHF_integrable [IsFiniteMeasure e.ρ] (p : PrefixAssignment n)
    (ξ : EuclideanSpace ℝ (Fin (n+1))) (v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v))) :
    Integrable (fun r => Ψ (r/(2:ℝ)^v)*‖e.prefixAngularCorrelation p ξ r‖^2) := by
  obtain ⟨B,hB,hbound⟩ := e.prefixSpatial_global_bound p
  exact Attempt4PrefixShell.sourceAngularCorrelationND_weighted_integrable _
    e.prefixCutoff_contDiff.continuous.measurable
    (e.prefixSpatialLeft_measurable p ξ) (e.prefixSpatialRight_measurable p ξ)
    (by norm_num : (0:ℝ) ≤ 1) hB e.prefixCutoff_norm_le
    (fun r w => (hbound ξ (r,w)).1) (fun r w => (hbound ξ (r,w)).2) hΨ

lemma prefixAngularHF_nonneg (p : PrefixAssignment n)
    (ξ : EuclideanSpace ℝ (Fin (n+1))) (v : ℝ) (Ψ : ℝ → ℝ) (hΨ : ∀ r, 0 ≤ Ψ r) :
    0 ≤ e.prefixAngularHF v Ψ p ξ := by
  unfold prefixAngularHF Attempt4PrefixShell.sourceAngularHFND
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro r
  exact mul_nonneg (hΨ _) (sq_nonneg _)

end PositiveDistanceState
end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer
variable {n : ℕ}
namespace PositiveDistanceState
variable (e : PositiveDistanceState (n+1))

lemma prefixAngularHF_global_bound [IsFiniteMeasure e.ρ]
    (p : PrefixAssignment n) (v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v))) (hpos : ∀ r, 0 ≤ Ψ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ, e.prefixAngularHF v Ψ p ξ ≤ C := by
  obtain ⟨B,hB,hbound⟩ := e.prefixSpatial_global_bound p
  let μ := Attempt4PrefixShell.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))
  let D := B*B*μ.real univ
  let A := (2:ℝ)^(((n+1:ℕ):ℝ)*(v-e.a))*((2:ℝ)^v)⁻¹
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A*((∫ r, Ψ (r/(2:ℝ)^v))*D^2),mul_nonneg hA
    (mul_nonneg (integral_nonneg (fun r => hpos _)) (sq_nonneg _)),?_⟩
  intro ξ
  have hc : ∀ r, ‖e.prefixAngularCorrelation p ξ r‖ ≤ D := by
    intro r
    simpa only [prefixAngularCorrelation,one_mul,D,μ] using
      Attempt4PrefixShell.sourceAngularCorrelationND_bound μ e.prefixCutoff
        (e.prefixSpatialLeft p ξ) (e.prefixSpatialRight p ξ)
        (by norm_num : (0:ℝ) ≤ 1) hB e.prefixCutoff_norm_le
        (fun r w => (hbound ξ (r,w)).1) (fun r w => (hbound ξ (r,w)).2) r
  change A*(∫ r, Ψ (r/(2:ℝ)^v)*‖e.prefixAngularCorrelation p ξ r‖^2) ≤ _
  apply mul_le_mul_of_nonneg_left _ hA
  rw [← integral_mul_const]
  apply integral_mono (e.prefixAngularHF_integrable p ξ v Ψ hΨ) (hΨ.mul_const _)
  intro r
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hc r) 2) (hpos _)

lemma prefixInverseHF_finite_family [IsFiniteMeasure e.ρ] (J : ℕ)
    (v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v))) (hpos : ∀ r, 0 ≤ Ψ r) :
    ∃ BHF : ℝ, 0 ≤ BHF ∧ ∀ j ≤ J,
      ∀ p ∈ Attempt4PrefixShell.inverseAngularTermsND j
        (e.prefixDescriptors.disjSum e.prefixDescriptors), ∀ ξ,
        e.prefixAngularHF v Ψ p ξ ≤ BHF := by
  classical
  have h := fun p : PrefixAssignment n => e.prefixAngularHF_global_bound p v Ψ hΨ hpos
  choose C hC hbound using h
  let S : Finset (PrefixAssignment n) := (Finset.range (J+1)).biUnion fun j =>
    (Attempt4PrefixShell.inverseAngularTermsND j
      (e.prefixDescriptors.disjSum e.prefixDescriptors)).toFinset
  refine ⟨∑ p ∈ S, C p,Finset.sum_nonneg (fun p _ => hC p),?_⟩
  intro j hj p hp ξ
  have hpS : p ∈ S := by
    apply Finset.mem_biUnion.mpr
    exact ⟨j,Finset.mem_range.mpr (Nat.lt_succ_of_le hj),List.mem_toFinset.mpr hp⟩
  exact (hbound p ξ).trans (Finset.single_le_sum (fun p _ => hC p) hpS)

end PositiveDistanceState
end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer
open scoped ComplexConjugate

lemma bounded_angular_cauchy {V : Type*} [MeasurableSpace V]
    (μ : Measure V) [IsFiniteMeasure μ] {ψ U W : V → ℂ}
    (hψ : Measurable ψ) (hU : Measurable U) (hW : Measurable W)
    {B : ℝ} (hB : 0 ≤ B) (hbψ : ∀ w, ‖ψ w‖ ≤ 1)
    (hbU : ∀ w, ‖U w‖ ≤ B) (hbW : ∀ w, ‖W w‖ ≤ B) :
    ‖∫ w, ψ w*U w*conj (W w) ∂μ‖^2 ≤
      (∫ w, ‖U w‖^2 ∂μ)*(∫ w, ‖W w‖^2 ∂μ) := by
  have hup : MemLp U (ENNReal.ofReal 2) μ :=
    MemLp.of_bound hU.aestronglyMeasurable B (Filter.Eventually.of_forall hbU)
  have hwp : MemLp W (ENNReal.ofReal 2) μ :=
    MemLp.of_bound hW.aestronglyMeasurable B (Filter.Eventually.of_forall hbW)
  have hi : Integrable (fun w => ‖U w‖*‖W w‖) μ := by
    apply Integrable.of_bound (hU.norm.mul hW.norm).aestronglyMeasurable (B*B)
    filter_upwards with w
    change ‖‖U w‖*‖W w‖‖ ≤ B*B
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul (hbU w) (hbW w) (norm_nonneg _) hB
  have hb : ∀ w, ‖ψ w*U w*conj (W w)‖ ≤ ‖U w‖*‖W w‖ := by
    intro w
    simp only [norm_mul,Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (hbψ w) (norm_nonneg (U w)))
      (norm_nonneg _)
  have hic : Integrable (fun w => ‖ψ w*U w*conj (W w)‖) μ := by
    apply hi.mono' ((hψ.mul hU).mul (Complex.continuous_conj.measurable.comp hW)).norm.aestronglyMeasurable
    filter_upwards with w
    simpa only [norm_norm,Pi.mul_apply,Function.comp_apply] using hb w
  have hcs := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hup hwp
  simp only [show (2:ℝ)=(2:ℕ) by norm_num,Real.rpow_natCast] at hcs
  simp only [Nat.cast_ofNat] at hcs
  have hbnd : ‖∫ w, ψ w*U w*conj (W w) ∂μ‖ ≤
      Real.sqrt (∫ w, ‖U w‖^2 ∂μ)*Real.sqrt (∫ w, ‖W w‖^2 ∂μ) := by
    apply (norm_integral_le_integral_norm _).trans
    apply (integral_mono hic hi hb).trans
    simpa only [Real.sqrt_eq_rpow] using hcs
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hbnd 2
  rw [mul_pow,Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _)),
    Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))] at hsq
  exact hsq

variable {n : ℕ}
namespace PositiveDistanceState
variable (e : PositiveDistanceState (n+1))

noncomputable def prefixAngularH (v : ℝ) (Ψ : ℝ → ℝ)
    (p : PrefixAssignment n) (ξ : EuclideanSpace ℝ (Fin (n+1))) : ℝ :=
  Attempt4PrefixShell.sourceAngularHND (n+1)
    (Attempt4PrefixShell.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1))))
    e.a v Ψ (e.prefixSpatialLeft p ξ) (e.prefixSpatialRight p ξ)

lemma prefixAngularHF_le_H [IsFiniteMeasure e.ρ] (v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v))) (hpos : ∀ r, 0 ≤ Ψ r)
    (p : PrefixAssignment n) (ξ : EuclideanSpace ℝ (Fin (n+1))) :
    e.prefixAngularHF v Ψ p ξ ≤ e.prefixAngularH v Ψ p ξ := by
  obtain ⟨B,hB,hbound⟩ := e.prefixSpatial_global_bound p
  let μ := Attempt4PrefixShell.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))
  have hprod := Attempt4PrefixShell.graph_weighted_moments_integrableND μ
    (e.prefixSpatialLeft_measurable p ξ) (e.prefixSpatialRight_measurable p ξ)
    (fun r => Filter.Eventually.of_forall (fun w => (hbound ξ (r,w)).1))
    (fun r => Filter.Eventually.of_forall (fun w => (hbound ξ (r,w)).2)) hΨ
  unfold prefixAngularHF prefixAngularH Attempt4PrefixShell.sourceAngularHFND
    Attempt4PrefixShell.sourceAngularHND
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono (e.prefixAngularHF_integrable p ξ v Ψ hΨ) hprod
  intro r
  dsimp only
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (hpos _)
  exact bounded_angular_cauchy μ e.prefixCutoff_contDiff.continuous.measurable
    ((e.prefixSpatialLeft_measurable p ξ).comp (measurable_const.prodMk measurable_id))
    ((e.prefixSpatialRight_measurable p ξ).comp (measurable_const.prodMk measurable_id))
    hB e.prefixCutoff_norm_le (fun w => (hbound ξ (r,w)).1) (fun w => (hbound ξ (r,w)).2)

end PositiveDistanceState
end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
