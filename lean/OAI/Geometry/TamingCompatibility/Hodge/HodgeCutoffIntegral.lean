import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.ChartGarding
import OAI.Geometry.TamingCompatibility.Hodge.HodgeLocalCodifferential

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldVolume ManifoldLocalization GeometricAdjoint
open MeasureTheory Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

include hs in
lemma full_cutoff_energy_bound {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, Smooth a →
      (∫ x, pairing J α ht (fun y => f y • a y) (fun y => f y • a y) x ∂geometricVolume A J α) +
      (∫ x, pairing J α ht (codifferential J α ht (fun y => f y • a y))
        (codifferential J α ht (fun y => f y • a y)) x +
        pairing J α ht (codifferential J α ht (starTwo J α ht (fun y => f y • a y)))
          (codifferential J α ht (starTwo J α ht (fun y => f y • a y))) x ∂geometricVolume A J α) ≤
      C * ((∫ x, pairing J α ht a a x ∂geometricVolume A J α) +
        (∫ x, pairing J α ht (codifferential J α ht a) (codifferential J α ht a) x +
          pairing J α ht (codifferential J α ht (starTwo J α ht a))
            (codifferential J α ht (starTwo J α ht a)) x ∂geometricVolume A J α)) := by
  let := geometricVolume_finite A J α hs ht
  have hdf := scalarDifferential_smooth hf
  have hc := (pairing_one_smooth J α hs ht hdf hdf).continuous
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (f := fun x => (f x)^2 + 2*pairing J α ht (scalarDifferential f) (scalarDifferential f) x)
    ((hf.continuous.pow 2).add (hc.const_mul 2)).continuousOn
  obtain ⟨D,hD⟩ := isCompact_univ.exists_bound_of_continuousOn
    (f := fun x => 2*(f x)^2) ((hf.continuous.pow 2).const_mul 2).continuousOn
  let C := max 1 (max B D)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro a ha
  have hb₁ (x : X) : (f x)^2 + 2*pairing J α ht (scalarDifferential f) (scalarDifferential f) x ≤ C :=
    (le_abs_self _).trans ((hB x (mem_univ x)).trans ((le_max_left B D).trans (le_max_right 1 (max B D))))
  have hb₂ (x : X) : 2*(f x)^2 ≤ C :=
    (le_abs_self _).trans ((hD x (mem_univ x)).trans ((le_max_right B D).trans (le_max_right 1 (max B D))))
  have hi₁ (b : TwoForm X) (hb : Smooth b) :
      Integrable (fun x => pairing J α ht b b x) (geometricVolume A J α) :=
    (pairing_two_smooth J α hs ht hb hb).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi₂ (b : TwoForm X) (hb : Smooth b) :
      Integrable (fun x => pairing J α ht (codifferential J α ht b) (codifferential J α ht b) x +
        pairing J α ht (codifferential J α ht (starTwo J α ht b))
          (codifferential J α ht (starTwo J α ht b)) x) (geometricVolume A J α) := by
    have hd := codifferential_smooth J α hs ht hb
    have hds := codifferential_smooth J α hs ht (starTwo_smooth J α hs ht hb)
    exact ((pairing_one_smooth J α hs ht hd hd).continuous.add
      (pairing_one_smooth J α hs ht hds hds).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hfa := Smooth.fun_smul hf ha
  rw [← integral_add (hi₁ _ hfa) (hi₂ _ hfa),← integral_add (hi₁ _ ha) (hi₂ _ ha),← integral_const_mul]
  apply integral_mono ((hi₁ _ hfa).add (hi₂ _ hfa)) (((hi₁ _ ha).add (hi₂ _ ha)).const_mul C)
  intro x
  have hx := full_cutoff_delta_pointwise J α hs ht ha hf x
  have he : pairing J α ht (fun y => f y • a y) (fun y => f y • a y) x =
      (f x)^2 * pairing J α ht a a x := by
    let v : MetricForms.Form Space 2 := a x
    change MetricForms.pairing (pointMetric J α ht x) (f x • v) (f x • v) = _
    rw [MetricForms.pairing_smul_left,MetricForms.pairing_smul_right]
    change f x * (f x * MetricForms.pairing (pointMetric J α ht x) (a x) (a x)) = _
    dsimp [pairing]
    ring
  have h₁ := mul_le_mul_of_nonneg_right (hb₁ x) (MetricForms.pairing_self_nonneg (pointMetric J α ht x) (a x))
  have h₂ := mul_le_mul_of_nonneg_right (hb₂ x)
    (add_nonneg (MetricForms.pairing_self_nonneg (pointMetric J α ht x) (codifferential J α ht a x))
      (MetricForms.pairing_self_nonneg (pointMetric J α ht x) (codifferential J α ht (starTwo J α ht a) x)))
  simp only [Pi.add_apply]
  rw [he]
  change ((f x)^2 + 2*pairing J α ht (scalarDifferential f) (scalarDifferential f) x) *
    pairing J α ht a a x ≤ C * pairing J α ht a a x at h₁
  change 2*(f x)^2 * (pairing J α ht (codifferential J α ht a) (codifferential J α ht a) x +
    pairing J α ht (codifferential J α ht (starTwo J α ht a))
      (codifferential J α ht (starTwo J α ht a)) x) ≤ _ at h₂
  calc
    _ ≤ (f x)^2 * pairing J α ht a a x +
        (2*(f x)^2 * (pairing J α ht (codifferential J α ht a) (codifferential J α ht a) x +
          pairing J α ht (codifferential J α ht (starTwo J α ht a))
            (codifferential J α ht (starTwo J α ht a)) x) +
         2*pairing J α ht (scalarDifferential f) (scalarDifferential f) x * pairing J α ht a a x) :=
      add_le_add (le_refl _) hx
    _ = ((f x)^2+2*pairing J α ht (scalarDifferential f) (scalarDifferential f) x)*pairing J α ht a a x +
        2*(f x)^2 * (pairing J α ht (codifferential J α ht a) (codifferential J α ht a) x +
          pairing J α ht (codifferential J α ht (starTwo J α ht a))
            (codifferential J α ht (starTwo J α ht a)) x) := by ring
    _ ≤ C*pairing J α ht a a x + C*(pairing J α ht (codifferential J α ht a) (codifferential J α ht a) x +
          pairing J α ht (codifferential J α ht (starTwo J α ht a))
            (codifferential J α ht (starTwo J α ht a)) x) := add_le_add h₁ h₂
    _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume EuclideanEnergy
open Set MeasureTheory GeometricChart
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

include hs in

theorem scalar_garding (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, ∀ ha : IsSmooth a,
      (∫ z, HodgeMatrixEnergy.gradient (scalarSchwartz A J α ht (fun q => (D q).toData) hD p a ha) z) +
      (∫ z, ‖HodgeMatrixEnergy.value (scalarSchwartz A J α ht (fun q => (D q).toData) hD p a ha) z‖^2) ≤
      C * ((∫ x, GeometricAdjoint.pairing J α ht a a x ∂geometricVolume A J α) +
        (∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht a)
          (codifferential J α ht a) x +
          GeometricAdjoint.pairing J α ht (codifferential J α ht (starTwo J α ht a))
            (codifferential J α ht (starTwo J α ht a)) x ∂geometricVolume A J α)) := by
  obtain ⟨Cδ,hCδ,hδ⟩ := integral_system_bound A J α ht (fun q => (D q).toData) hD hs p
  obtain ⟨Cs,hCs,hS⟩ := integral_scalar_bound A J α hs ht (fun q => (D q).toData) hD p
  obtain ⟨Cf,hCf,hf⟩ := GeometricHilbert.full_cutoff_energy_bound A J α hs ht (A.partition p).contMDiff
  let K := (D p).fullEnergyConstant*Cδ + ((D p).fullLowerConstant+1)*Cs
  have hK : 0 < K := add_pos (mul_pos (D p).fullEnergy_pos hCδ)
    (mul_pos (by linarith [(D p).fullLower_pos]) hCs)
  refine ⟨K*Cf,mul_pos hK hCf,?_⟩
  intro a ha
  let f := scalarSchwartz A J α ht (fun q => (D q).toData) hD p a ha
  have hg := (D p).fullGarding f (fun j => scalarSchwartz_support A J α ht
    (fun q => (D q).toData) hD p a ha j)
  change (∫ z, HodgeMatrixEnergy.gradient f z) ≤ (D p).fullEnergyConstant *
    (∫ z, ‖system A J α ht (fun q => (D q).toData) hD p a ha z‖^2) + (D p).fullLowerConstant *
      (∫ z, ‖HodgeMatrixEnergy.value f z‖^2) at hg
  let L := ∫ x, GeometricAdjoint.pairing J α ht (cutoffForm A p a) (cutoffForm A p a) x ∂geometricVolume A J α
  let Q := ∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht (cutoffForm A p a))
      (codifferential J α ht (cutoffForm A p a)) x +
    GeometricAdjoint.pairing J α ht (codifferential J α ht (starTwo J α ht (cutoffForm A p a)))
      (codifferential J α ht (starTwo J α ht (cutoffForm A p a))) x ∂geometricVolume A J α
  have hL : 0 ≤ L := integral_nonneg (fun x => MetricForms.pairing_self_nonneg _ _)
  have hQ : 0 ≤ Q := integral_nonneg (fun x => add_nonneg
    (MetricForms.pairing_self_nonneg _ _) (MetricForms.pairing_self_nonneg _ _))
  have hδa := hδ a ha
  have hSa := hS a ha
  change _ ≤ Cδ*Q at hδa
  change (∫ z, ‖HodgeMatrixEnergy.value f z‖^2) ≤ Cs*L at hSa
  have hfa := hf a ha
  change L+Q ≤ _ at hfa
  have hpre : (∫ z, HodgeMatrixEnergy.gradient f z) +
      (∫ z, ‖HodgeMatrixEnergy.value f z‖^2) ≤ K*(L+Q) := by
    have hd := mul_le_mul_of_nonneg_left hδa (D p).fullEnergy_pos.le
    have hsl := mul_le_mul_of_nonneg_left hSa (by linarith [(D p).fullLower_pos] : 0 ≤ (D p).fullLowerConstant+1)
    have he₁ := mul_nonneg (mul_pos (D p).fullEnergy_pos hCδ).le hL
    have he₂ := mul_nonneg (mul_pos (by linarith [(D p).fullLower_pos] : 0 < (D p).fullLowerConstant+1) hCs).le hQ
    dsimp only [K]
    nlinarith
  exact hpre.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hfa hK.le)
end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
