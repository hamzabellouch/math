import OAI.MeasureTheory.Falconer.Fourier.JetAdmissible
import OAI.MeasureTheory.Falconer.Fourier.DescriptorJetRemoval
import OAI.MeasureTheory.Falconer.Fourier.MaskJetAlgebra

namespace OAI

/-! # The factorized symbols used by recursive angular states

The descriptor list is part of the type: every descriptor occurs once,
with an explicitly recorded jet. Passing to a deeper cell filters that
list and keeps the same spatial and smooth angular multipliers.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

structure DescriptorJetSymbol (n K L : ℕ) (F : Finset PolicyDescriptor) (D : ℝ) where
  jet : PolicyDescriptor → MaskJetIndex (n+2)
  order_le : (∑ b ∈ F, (jet b).order) ≤ K
  angular : Space (n+2) → ℂ
  angular_smooth : ContDiff ℝ ∞ angular
  angular_derivative : ∀ t ≤ L, ∀ w : Sphere (n+2), ‖iteratedFDeriv ℝ t angular w‖ ≤ D^t
  angular_control : ChartSymbolControl L
    (fun (_ : Space (n+2)) (w : Sphere (n+2)) => angular w) 1 D
  spatial : Space (n+2) → ℂ
  spatial_measurable : Measurable spatial
  spatial_bound : ∀ x, ‖spatial x‖ ≤ 1

namespace DescriptorJetSymbol
variable {n K L : ℕ} {F : Finset PolicyDescriptor} {D : ℝ}

noncomputable def restrict (f : DescriptorJetSymbol n K L F D)
    (G : Finset PolicyDescriptor) (hG : G ⊆ F) : DescriptorJetSymbol n K L G D where
  jet := f.jet
  order_le := (Finset.sum_le_sum_of_subset hG).trans f.order_le
  angular := f.angular
  angular_smooth := f.angular_smooth
  angular_derivative := f.angular_derivative
  angular_control := f.angular_control
  spatial := f.spatial
  spatial_measurable := f.spatial_measurable
  spatial_bound := f.spatial_bound

noncomputable def multiplier (f : DescriptorJetSymbol n K L F D) (A : ℝ)
    (x : Space (n+2)) (w : Sphere (n+2)) : ℂ :=
  f.spatial x*(A⁻¹ : ℝ)*f.angular w

 theorem multiplier_measurable (f : DescriptorJetSymbol n K L F D) (A : ℝ) :
    Measurable (Function.uncurry (f.multiplier A)) :=
  (f.spatial_measurable.comp measurable_fst).mul measurable_const |>.mul
    f.angular_control.measurable

 theorem multiplier_bound (f : DescriptorJetSymbol n K L F D) {A : ℝ} (hA : 0 < A)
    (x : Space (n+2)) (w : Sphere (n+2)) : ‖f.multiplier A x w‖ ≤ A⁻¹ := by
  rw [multiplier,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hA.le)]
  calc
    _ ≤ (1*A⁻¹)*1 := mul_le_mul
      (mul_le_mul_of_nonneg_right (f.spatial_bound x) (inv_nonneg.mpr hA.le))
      (f.angular_control.bound x w) (norm_nonneg _) (by positivity)
    _ = _ := by ring

noncomputable def value (f : DescriptorJetSymbol n K L F D)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (n+2))) (A : ℝ)
    (x : Space (n+2)) (w : Sphere (n+2)) : ℂ :=
  descriptorJetProduct Q ρ m N σ J i F id S
    (fun b => (f.jet b).order) (fun b _ => (f.jet b).vectors) x w *
      f.multiplier A x w

 theorem value_measurable (f : DescriptorJetSymbol n K L F D)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (n+2))) (A : ℝ) :
    Measurable (Function.uncurry (f.value Q ρ m N σ J i S A)) := by
  have hp := descriptorJetProduct_measurable Q ρ m N σ J i F id S
    (fun b => (f.jet b).order) (fun b _ => (f.jet b).vectors) (fun _ _ => measurable_const)
  exact hp.mul (f.multiplier_measurable A)

 theorem value_norm_le (f : DescriptorJetSymbol n K L F D)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hsep : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z →
      descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (x : Space (n+2)) (w : Sphere (n+2)) :
    ‖f.value Q ρ m N σ J i S A x w‖ ≤ ((descriptorJetBound (n+2) K)^K)*A⁻¹ := by
  rw [value,norm_mul]
  exact mul_le_mul
    (descriptorJetProduct_norm_le Q ρ m N σ J i F id S
      (fun b => (f.jet b).order) (fun b _ => (f.jet b).vectors)
      hsep f.order_le (fun b _ _ => (f.jet b).norm_vectors) x w)
    (f.multiplier_bound hA x w) (norm_nonneg _)
    (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _)

 theorem value_admissible (f : DescriptorJetSymbol n K L F D)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (n+2))) {A E : ℝ}
    (hA : 0 < A) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hjet : ChartSymbolControl L
      (descriptorJetProduct Q ρ m N σ J i F id S
        (fun b => (f.jet b).order) (fun b _ => (f.jet b).vectors)) A E) :
    AngularAdmissible L (D+E)
      {z | ∀ b ∈ F, z ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b}
      (f.value Q ρ m N σ J i S A) := by
  have h := (descriptorJetProduct_mul_admissible Q ρ m N σ J i F id S
    (fun b => (f.jet b).order) (fun b _ => (f.jet b).vectors) (fun w => f.angular w)
    hA (by norm_num) hE hD hjet f.angular_control).spatialMultiplier
      f.spatial f.spatial_measurable f.spatial_bound
  have he : f.value Q ρ m N σ J i S A = fun x w => f.spatial x*
      normalizedEndpoint A (fun x w => f.angular w*
        descriptorJetProduct Q ρ m N σ J i F id S
          (fun b => (f.jet b).order) (fun b _ => (f.jet b).vectors) x w) x w := by
    funext x w
    simp only [value,multiplier,normalizedEndpoint]
    ring
  rw [he]
  simpa only [one_mul,id_eq] using h

 theorem endpoint_restrict (f : DescriptorJetSymbol n K L F D)
    (Q : DyadicCube (n+2)) (hQ : 0 < Q.side)
    (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (X : List (Fin (n+2) → Bool)) (μ : Measure (Space (n+2)))
    (M r : ℝ) (w : Sphere (n+2)) :
    endpointTransform (μ.restrict (Q.descendant X).carrier) M
      (f.value Q ρ m N σ J i S A) r w =
      descriptorJetProduct Q ρ m N σ J i
        (F.filter (fun b => descriptorAnchor b ≤ X.length)) id S
        (fun b => (f.jet b).order) (fun b _ => (f.jet b).vectors) (Q.descendant X).center w *
      endpointTransform (μ.restrict (Q.descendant X).carrier) M
        ((f.restrict (F.filter (fun b => X.length < descriptorAnchor b))
          (Finset.filter_subset _ _)).value Q ρ m N σ J i S A) r w := by
  exact endpointTransform_descriptorJetProduct_split Q hQ ρ m N σ J i F id S
    (fun b => (f.jet b).order) (fun b _ => (f.jet b).vectors) X μ M
    (f.multiplier A) r w

 theorem energy_remove_reached (f g : DescriptorJetSymbol n K L F D)
    (Q : DyadicCube (n+2)) (hQ : 0 < Q.side)
    (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hsep : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z →
      descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (X Y : List (Fin (n+2) → Bool))
    (μ ν : Measure (Space (n+2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a t : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure t Ψ)] :
    independentAngularEnergy a t Ψ
      (fun z => endpointTransform (μ.restrict (Q.descendant X).carrier) M
        (f.value Q ρ m N σ J i S A) z.1 z.2)
      (fun z => endpointTransform (ν.restrict (Q.descendant Y).carrier) P
        (g.value Q ρ m N σ J i S A) z.1 z.2) ≤
    ((descriptorJetBound (n+2) K)^K)^2 * ((descriptorJetBound (n+2) K)^K)^2 *
    independentAngularEnergy a t Ψ
      (fun z => endpointTransform (μ.restrict (Q.descendant X).carrier) M
        ((f.restrict (F.filter (fun b => X.length < descriptorAnchor b))
          (Finset.filter_subset _ _)).value Q ρ m N σ J i S A) z.1 z.2)
      (fun z => endpointTransform (ν.restrict (Q.descendant Y).carrier) P
        ((g.restrict (F.filter (fun b => Y.length < descriptorAnchor b))
          (Finset.filter_subset _ _)).value Q ρ m N σ J i S A) z.1 z.2) := by
  exact independentAngularEnergy_descriptorJets_remove Q hQ ρ m N σ J i F F id id S
    (fun b => (f.jet b).order) (fun b => (g.jet b).order)
    (fun b _ => (f.jet b).vectors) (fun b _ => (g.jet b).vectors)
    hsep hsep f.order_le g.order_le
    (fun b _ _ => (f.jet b).norm_vectors) (fun b _ _ => (g.jet b).norm_vectors)
    (fun _ _ => measurable_const) (fun _ _ => measurable_const)
    X Y μ ν hM hP (f.multiplier A) (g.multiplier A)
    (f.multiplier_measurable A) (g.multiplier_measurable A)
    (inv_nonneg.mpr hA.le) (inv_nonneg.mpr hA.le)
    (f.multiplier_bound hA) (g.multiplier_bound hA) a t Ψ

end DescriptorJetSymbol
end Falconer

end OAI
