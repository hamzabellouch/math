import Mathlib
import OAI.MeasureTheory.Falconer.Fourier.DistanceSincSpectralIdentity
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.MinimalDescriptorLength
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Fourier.MinimalMask
import OAI.MeasureTheory.FalconerCompletion.Graphs.AllMaskProductAdmissible2
import OAI.MeasureTheory.FalconerCompletion.Recursion.MaskScale2
import OAI.MeasureTheory.FalconerCompletion.Shells.PrefixShell

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer
open scoped ContDiff ComplexConjugate
variable {n : ℕ}
namespace PositiveDistanceState
variable (e : PositiveDistanceState (n+1))

noncomputable def prefixDescriptors : Finset PolicyDescriptor :=
  policyDescriptorList (adjustedProfile (d:=n+1) e.mass e.N) e.N e.q e.a e.t

noncomputable def prefixEndpointSmooth (x : EuclideanSpace ℝ (Fin (n+1)))
    (b : PolicyDescriptor) : Attempt4PrefixShell.SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))) :=
  ⟨fun w => (actualEndpointMask e.ρ e.mass e.N e.sig e.C e.J e.i b x w:ℂ),
    Complex.ofRealCLM.contDiff.comp (actualEndpointMask_smooth _ _ _ _ _ _ _ _ _)⟩

lemma prefix_pairMask_eq (z : EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))
    (w : EuclideanSpace ℝ (Fin (n+1))) :
    (Attempt4PrefixShell.pairMaskProductND e.prefixDescriptors e.prefixDescriptors
      e.prefixEndpointSmooth e.prefixEndpointSmooth z).1 w =
      ((∏ b∈e.prefixDescriptors, actualEndpointMask e.ρ e.mass e.N e.sig e.C e.J e.i b z.1 w*
        actualEndpointMask e.ρ e.mass e.N e.sig e.C e.J e.i b z.2 w:ℝ):ℂ) := by
  classical
  simp only [Attempt4PrefixShell.pairMaskProductND,Attempt4PrefixShell.smoothFinsetProductND,
    Finset.prod_disjSum,Sum.elim_inl,Sum.elim_inr,Attempt4PrefixShell.smoothStarND,
    prefixEndpointSmooth,Complex.star_def,Complex.conj_ofReal,Finset.prod_mul_distrib,
    Complex.ofReal_mul,Complex.ofReal_prod]

lemma prefix_pairMask_radial (z : EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) :
    (Attempt4PrefixShell.pairMaskProductND e.prefixDescriptors e.prefixDescriptors
      e.prefixEndpointSmooth e.prefixEndpointSmooth z).1 ((dist z.1 z.2)⁻¹ • (z.1-z.2))=
      (e.minimalMask z:ℂ) := by
  rw [e.prefix_pairMask_eq]
  rfl

lemma prefix_shell_transform_exact (r : ℝ) :
    Attempt4PrefixShell.weightedMaskTransformND e.prefixDescriptors e.prefixDescriptors
      e.prefixEndpointSmooth e.prefixEndpointSmooth (fun _ => 1) (fun _ => 1)
      e.ρ e.ρ (treeCell e.X) (treeCell e.Y) e.levelMass e.levelMass e.a r =
      charFun e.weightedDistance r := by
  rw [e.weightedDistance_fourier,Attempt4PrefixShell.weightedMaskTransformND]
  have hm : (e.levelMass*e.levelMass)⁻¹=e.levelMass^(-2:ℤ) := by
    simp [zpow_neg,pow_two]
  rw [hm]
  apply congrArg (fun z : ℂ => (e.levelMass^(-2:ℤ):ℝ) • z)
  apply integral_congr_ae
  filter_upwards with z
  simp only [map_one,one_mul,Attempt4PrefixShell.outgoingWeightedKernelND,
    e.prefix_pairMask_radial,Real.rpow_natCast,spatialWeight,Nat.cast_add,Nat.cast_one,
    add_sub_cancel_right,Complex.ofReal_mul]
  ring_nf

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
open Set MeasureTheory PlanarFalconer Filter
open scoped ContDiff
variable {n : ℕ}
namespace PositiveDistanceState
variable (e : PositiveDistanceState (n+1))

lemma prefixEndpoint_norm_le (x w : EuclideanSpace ℝ (Fin (n+1)))
    (b : PolicyDescriptor) (hw : ‖w‖=1) : ‖(e.prefixEndpointSmooth x b).1 w‖ ≤ 1 := by
  have h := actualEndpointMask_bounds e.ρ e.mass e.N e.sig e.C e.J e.i b x hw.le
  simpa only [prefixEndpointSmooth,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h.1] using h.2

lemma prefixDescriptors_card (hN : 1 ≤ e.N) (hq : 0 < e.q) :
    ((e.prefixDescriptors.card+e.prefixDescriptors.card:ℕ):ℝ) ≤ 16*(e.N:ℝ)^3 := by
  have h := actualPolicy_card_bound (adjustedProfile (d:=n+1) e.mass e.N)
    (a:=e.a) (t:=e.t) hN hq
  change (e.prefixDescriptors.card:ℝ) ≤ _ at h
  push_cast
  linarith

lemma prefixDescriptor_scale (hq : 0 < e.q) {b : PolicyDescriptor} (hb : b∈e.prefixDescriptors) :
    1 ≤ sourceMaskScaleND (descriptorLength b) ((2:ℝ)^e.N) e.sig ∧
    sourceMaskScaleND (descriptorLength b) ((2:ℝ)^e.N) e.sig ≤
      sourceMaskScaleND ((e.t-e.a)/2) ((2:ℝ)^e.N) e.sig := by
  exact ⟨sourceMaskScaleND_one_le _ _ _,sourceMaskScaleND_mono
    (policyDescriptor_length_le_half _ hq hb) (by positivity)⟩

lemma prefixShell_le_sourceShell [IsFiniteMeasure e.weightedDistance] (j : ℕ) :
    e.prefixShell j ≤ (2:ℝ)^(-(e.a:ℝ))*
      (∫ r in Icc ((2:ℝ)^(j:ℝ)/2) (2*(2:ℝ)^(j:ℝ)),
        ‖Attempt4PrefixShell.weightedMaskTransformND e.prefixDescriptors e.prefixDescriptors
          e.prefixEndpointSmooth e.prefixEndpointSmooth (fun _ => 1) (fun _ => 1)
          e.ρ e.ρ (treeCell e.X) (treeCell e.Y) e.levelMass e.levelMass e.a r‖^2) := by
  simp_rw [e.prefix_shell_transform_exact,Real.rpow_natCast]
  have hsub : Icc ((2:ℝ)^j) ((2:ℝ)^(j+1))⊆Icc ((2:ℝ)^j/2) (2*(2:ℝ)^j) := by
    intro r hr
    constructor
    · have h : 0 ≤ (2:ℝ)^j := by positivity
      linarith [hr.1]
    · simpa only [pow_succ,mul_comm] using hr.2
  have hi : Integrable (fun r => ‖charFun e.weightedDistance r‖^2)
      (volume.restrict (Icc ((2:ℝ)^j/2) (2*(2:ℝ)^j))) := by
    simpa only [one_mul] using charFun_sq_integrable_finite e.weightedDistance
      (volume.restrict (Icc ((2:ℝ)^j/2) (2*(2:ℝ)^j))) 1
  exact mul_le_mul_of_nonneg_left
    (integral_mono_measure (Measure.restrict_mono hsub le_rfl)
      (Filter.Eventually.of_forall (fun r => sq_nonneg ‖charFun e.weightedDistance r‖)) hi) (by positivity)

end PositiveDistanceState

lemma uniform_prefixEndpoint_derivatives (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (e : PositiveDistanceState (n+1)) (x : EuclideanSpace ℝ (Fin (n+1)))
      (b : PolicyDescriptor) (j : ℕ), j ≤ m  →  ∀ w,
      ‖iteratedFDeriv ℝ j (e.prefixEndpointSmooth x b).1 w‖ ≤
        D*(sourceMaskScaleND (descriptorLength b) ((2:ℝ)^e.N) e.sig)^j := by
  obtain ⟨D,hD,h⟩ := actualEndpointMask_derivatives (n+1) m
  refine ⟨D,hD,?_⟩
  intro e x b j hj w
  have he : (e.prefixEndpointSmooth x b).1=
      (actualEndpointSmooth e.ρ e.mass e.N e.sig e.C e.J e.i b x).1 := rfl
  rw [he,actualEndpointSmooth_derivative_norm]
  exact h e.ρ e.mass e.N e.sig e.C e.J e.i b j hj x w

lemma uniform_actual_prefix_pair_symbol (m : ℕ) {sig : ℝ} (hsig : 0 < sig) :
    ∀ᶠ N : ℕ in atTop, ∀ (e : PositiveDistanceState (n+1)), e.N=N  →  e.sig=sig  →  0 < e.q  →
      ∀ (z : EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))),
      ∀ j ≤ m, ∀ w, ‖w‖=1  →
      ‖iteratedFDeriv ℝ j
          (Attempt4PrefixShell.pairMaskProductND e.prefixDescriptors e.prefixDescriptors
            e.prefixEndpointSmooth e.prefixEndpointSmooth z).1 w‖ ≤
        (((2:ℝ)^N)^sig*sourceMaskScaleND ((e.t-e.a)/2) ((2:ℝ)^N) sig)^j := by
  classical
  obtain ⟨D,hD,hder⟩ := uniform_prefixEndpoint_derivatives (n:=n) m
  filter_upwards [Attempt4PrefixShell.pair_mask_product_admissibleND
      (ι:=PolicyDescriptor) (κ:=PolicyDescriptor) (n:=n) m 3 D 16 sig hD hsig,
    eventually_ge_atTop 1] with N hN hN₁
  intro e he hsig' hq z
  subst N
  rw [← hsig'] at hN ⊢
  apply hN e.prefixDescriptors e.prefixDescriptors e.prefixEndpointSmooth e.prefixEndpointSmooth
    (fun b => sourceMaskScaleND (descriptorLength b) ((2:ℝ)^e.N) e.sig)
    (fun b => sourceMaskScaleND (descriptorLength b) ((2:ℝ)^e.N) e.sig)
    (sourceMaskScaleND ((e.t-e.a)/2) ((2:ℝ)^e.N) e.sig) z
    (e.prefixDescriptors_card hN₁ hq) (fun b hb => e.prefixDescriptor_scale hq hb)
    (fun b hb => e.prefixDescriptor_scale hq hb) (sourceMaskScaleND_pos _ _ _).le
    (fun b _ w hw => e.prefixEndpoint_norm_le _ _ b hw)
    (fun b _ w hw => e.prefixEndpoint_norm_le _ _ b hw)
    (fun b _ j hj w _ => hder e _ b j hj w)
    (fun b _ j hj w _ => hder e _ b j hj w)

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
