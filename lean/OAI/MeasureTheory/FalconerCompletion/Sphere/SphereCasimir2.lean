import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.SumSqWedge2

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open MeasureTheory Set
open scoped RealInnerProductSpace ContDiff
variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Fintype ι]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
noncomputable def sphereCasimirND (b : OrthonormalBasis ι ℝ V) (f : V → ℂ) (x : V) : ℂ :=
  (1/2:ℂ)*∑ i, ∑ j, angularDerivativeND (angularGeneratorND (b i) (b j))
    (angularDerivativeND (angularGeneratorND (b i) (b j)) f) x

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma sphereCasimirND_contDiff (b : OrthonormalBasis ι ℝ V) {f : V → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (sphereCasimirND b f) := by
  unfold sphereCasimirND
  apply contDiff_const.mul
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    angularDerivativeND_contDiff _ (angularDerivativeND_contDiff _ hf)

lemma sphereCasimirND_selfadjoint (b : OrthonormalBasis ι ℝ V)
    {f g : V → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    (∫ x, sphereCasimirND b f x*g x ∂canonicalSphereMeasureND V) =
      ∫ x, f x*sphereCasimirND b g x ∂canonicalSphereMeasureND V := by
  let H (f : V → ℂ) (i j : ι) := angularDerivativeND (angularGeneratorND (b i) (b j))
    (angularDerivativeND (angularGeneratorND (b i) (b j)) f)
  have hH {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (i j : ι) : Continuous (H f i j) :=
    (angularDerivativeND_contDiff _ (angularDerivativeND_contDiff _ hf)).continuous
  have hsum (F : ι → ι → V → ℂ) (hF : ∀ i j, Continuous (F i j)) :
      (∫ x, ∑ i, ∑ j, F i j x ∂canonicalSphereMeasureND V) =
        ∑ i, ∑ j, ∫ x, F i j x ∂canonicalSphereMeasureND V := by
    rw [integral_finsetSum _ (fun i _ => integrable_canonicalSphereMeasureND
      (continuous_finsetSum _ (fun j _ => hF i j)))]
    congr 1
    ext i
    exact integral_finsetSum _ (fun j _ => integrable_canonicalSphereMeasureND (hF i j))
  change (∫ x, ((1/2:ℂ)*∑ i, ∑ j, H f i j x)*g x ∂canonicalSphereMeasureND V) =
    ∫ x, f x*((1/2:ℂ)*∑ i, ∑ j, H g i j x) ∂canonicalSphereMeasureND V
  simp_rw [mul_assoc,Finset.sum_mul,Finset.mul_sum,mul_left_comm (f _) (1/2:ℂ)]
  rw [hsum (fun i j x => (1/2:ℂ)*(H f i j x*g x))
      (fun i j => continuous_const.mul ((hH hf i j).mul hg.continuous)),
    hsum (fun i j x => (1/2:ℂ)*(f x*H g i j x))
      (fun i j => continuous_const.mul (hf.continuous.mul (hH hg i j)))]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,integral_const_mul]
  congr 1
  exact sphere_angular_second_selfadjoint _ (angularGeneratorND_skew _ _) hf hg

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma sphereCasimirND_planeWave (b : OrthonormalBasis ι ℝ V) (Λ : ℝ) (e x : V) :
    sphereCasimirND b (spherePlaneWaveND Λ e) x =
      spherePlaneWaveND Λ e x *
        (-(Λ:ℂ)^2 * ((‖x‖:ℂ)^2*(‖e‖:ℂ)^2-(inner ℝ x e : ℂ)^2) -
          Complex.I*Λ*((Fintype.card ι:ℂ)-1)*(inner ℝ x e : ℂ)) := by
  unfold sphereCasimirND
  simp_rw [angularDerivativeND_planeWave_second,← Finset.mul_sum,
    Finset.sum_add_distrib,← Finset.mul_sum]
  have hs : (∑ i, ∑ j, (inner ℝ (angularGeneratorND (b i) (b j) x) e : ℂ)^2) =
      2*((‖x‖:ℂ)^2*(‖e‖:ℂ)^2-(inner ℝ x e : ℂ)^2) := by
    exact_mod_cast angularGeneratorND_sum_sq b x e
  have hl : (∑ i, ∑ j, (inner ℝ (angularGeneratorND (b i) (b j)
      (angularGeneratorND (b i) (b j) x)) e : ℂ)) =
      -(2*((Fintype.card ι:ℂ)-1))*(inner ℝ x e : ℂ) := by
    exact_mod_cast angularGeneratorND_sum_second b x e
  rw [hs,hl]
  ring

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open MeasureTheory Set Metric
open scoped ContDiff RealInnerProductSpace Topology
variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Fintype ι]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma spherePlaneWaveND_norm (Λ : ℝ) (e w : V) : ‖spherePlaneWaveND Λ e w‖ = 1 := by
  simp [spherePlaneWaveND,Complex.norm_exp,Complex.mul_re]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma spherePlaneWaveND_hasDerivAt (Λ : ℝ) (e w : V) :
    HasDerivAt (fun s => spherePlaneWaveND s e w)
      (spherePlaneWaveND Λ e w*(Complex.I*(inner ℝ w e : ℂ))) Λ := by
  simpa [spherePlaneWaveND,mul_assoc] using
    ((((hasDerivAt_id Λ).ofReal_comp.const_mul Complex.I).mul_const
      (inner ℝ w e : ℂ)).cexp)

lemma sphereAxisIntegralND_hasDerivAt {b : V → ℂ} (hb : Continuous b) (Λ : ℝ) (e : V) :
    HasDerivAt (fun s => sphereAxisIntegralND s e b)
      (Complex.I*sphereAxisIntegralND Λ e (fun w => (inner ℝ w e : ℂ)*b w)) Λ := by
  let F (s : ℝ) (w : V) := spherePlaneWaveND s e w * b w
  let F' (s : ℝ) (w : V) := spherePlaneWaveND s e w *
    (Complex.I*(inner ℝ w e : ℂ))*b w
  have hi : Continuous (fun w : V => (inner ℝ w e : ℂ)) := by fun_prop
  have hF (s : ℝ) : Continuous (F s) := (spherePlaneWaveND_contDiff s e).continuous.mul hb
  have hF' (s : ℝ) : Continuous (F' s) :=
    ((spherePlaneWaveND_contDiff s e).continuous.mul (continuous_const.mul hi)).mul hb
  obtain ⟨C,hC⟩ := (isCompact_sphere (0:V) 1).exists_bound_of_continuousOn hb.continuousOn
  have hbound : ∀ᵐ w ∂canonicalSphereMeasureND V, ∀ s ∈ (univ : Set ℝ),
      ‖F' s w‖ ≤ ‖e‖*C := by
    filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw s _
    dsimp [F']
    rw [norm_mul,norm_mul,spherePlaneWaveND_norm,one_mul,norm_mul,Complex.norm_I,one_mul,
      Complex.norm_real]
    apply mul_le_mul (by simpa [hw] using abs_real_inner_le_norm w e)
      (hC _ (by simpa using hw)) (norm_nonneg _) (norm_nonneg _)
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (x₀ := Λ) (μ := canonicalSphereMeasureND V) (F := F) (F' := F')
    (bound := fun _ => ‖e‖*C) Filter.univ_mem
    (Filter.Eventually.of_forall (fun s => (hF s).aestronglyMeasurable))
    (integrable_canonicalSphereMeasureND (hF Λ)) (hF' Λ).aestronglyMeasurable
    hbound (integrable_const _)
    (Filter.Eventually.of_forall (fun w s _ => (spherePlaneWaveND_hasDerivAt s e w).mul_const (b w)))
  have he : (∫ w, F' Λ w ∂canonicalSphereMeasureND V) =
      Complex.I*sphereAxisIntegralND Λ e (fun w => (inner ℝ w e : ℂ)*b w) := by
    unfold sphereAxisIntegralND
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with w
    dsimp [F',sphereAxisIntegralND,spherePlaneWaveND]
    ring
  simpa only [he,F,spherePlaneWaveND,sphereAxisIntegralND] using hparam.2

lemma sphereAxisIntegralND_casimir (B : OrthonormalBasis ι ℝ V) (Λ : ℝ) {e : V}
    (he : ‖e‖ = 1) {b : V → ℂ} (hb : ContDiff ℝ ∞ b) :
    sphereAxisIntegralND Λ e (sphereCasimirND B b) =
      -(Λ:ℂ)^2*sphereAxisIntegralND Λ e b +
        (Λ:ℂ)^2*sphereAxisIntegralND Λ e (fun w => (inner ℝ w e : ℂ)^2*b w) -
        Complex.I*Λ*((Fintype.card ι:ℂ)-1)*
          sphereAxisIntegralND Λ e (fun w => (inner ℝ w e : ℂ)*b w) := by
  have hi : Continuous (fun w : V => (inner ℝ w e : ℂ)) := by fun_prop
  have hw := (spherePlaneWaveND_contDiff Λ e).continuous
  have h₀ := integrable_canonicalSphereMeasureND (hw.mul hb.continuous)
  have h₁ := integrable_canonicalSphereMeasureND (hw.mul (hi.mul hb.continuous))
  have h₂ := integrable_canonicalSphereMeasureND (hw.mul ((hi.pow 2).mul hb.continuous))
  change (∫ w, spherePlaneWaveND Λ e w*sphereCasimirND B b w ∂canonicalSphereMeasureND V) = _
  rw [← sphereCasimirND_selfadjoint B (spherePlaneWaveND_contDiff Λ e) hb]
  calc
    (∫ w, sphereCasimirND B (spherePlaneWaveND Λ e) w*b w ∂canonicalSphereMeasureND V) =
        ∫ w, -(Λ:ℂ)^2*(spherePlaneWaveND Λ e w*b w) +
          (Λ:ℂ)^2*(spherePlaneWaveND Λ e w*((inner ℝ w e : ℂ)^2*b w)) -
          (Complex.I*Λ*((Fintype.card ι:ℂ)-1))*(spherePlaneWaveND Λ e w*((inner ℝ w e : ℂ)*b w))
          ∂canonicalSphereMeasureND V := by
      apply integral_congr_ae
      filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw
      rw [sphereCasimirND_planeWave,hw,he]
      push_cast
      ring
    _ = _ := by
      rw [integral_sub
        (f := fun w => -(Λ:ℂ)^2*(spherePlaneWaveND Λ e w*b w) +
          (Λ:ℂ)^2*(spherePlaneWaveND Λ e w*((inner ℝ w e : ℂ)^2*b w)))
        (g := fun w => (Complex.I*Λ*((Fintype.card ι:ℂ)-1))*
          (spherePlaneWaveND Λ e w*((inner ℝ w e : ℂ)*b w)))
        ((h₀.const_mul _).add (h₂.const_mul _)) (h₁.const_mul _),
        integral_add
          (f := fun w => -(Λ:ℂ)^2*(spherePlaneWaveND Λ e w*b w))
          (g := fun w => (Λ:ℂ)^2*(spherePlaneWaveND Λ e w*((inner ℝ w e : ℂ)^2*b w)))
          (h₀.const_mul _) (h₂.const_mul _)]
      simp only [integral_const_mul,spherePlaneWaveND,sphereAxisIntegralND]

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open MeasureTheory Set
open scoped RealInnerProductSpace ContDiff
variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Fintype ι]

lemma sphereAxisIntegralND_deriv {b : V → ℂ} (hb : Continuous b) (e : V) :
    deriv (fun s => sphereAxisIntegralND s e b) =
      fun s => Complex.I*sphereAxisIntegralND s e (fun w => (inner ℝ w e : ℂ)*b w) := by
  funext s
  exact (sphereAxisIntegralND_hasDerivAt hb s e).deriv

lemma sphereAxisIntegralND_deriv2 {b : V → ℂ} (hb : Continuous b) (s : ℝ) (e : V) :
    deriv (deriv (fun s => sphereAxisIntegralND s e b)) s =
      -sphereAxisIntegralND s e (fun w => (inner ℝ w e : ℂ)^2*b w) := by
  rw [sphereAxisIntegralND_deriv hb e,deriv_const_mul_field]
  have h₁ : Continuous (fun w => (inner ℝ w e : ℂ)*b w) := by fun_prop
  rw [(sphereAxisIntegralND_hasDerivAt h₁ s e).deriv]
  have he : (fun w => (inner ℝ w e : ℂ)*((inner ℝ w e : ℂ)*b w)) =
      fun w => (inner ℝ w e : ℂ)^2*b w := by funext w; ring
  rw [he,← mul_assoc,Complex.I_mul_I,neg_one_mul]

lemma sphereAxisIntegralND_helmholtz (B : OrthonormalBasis ι ℝ V) (s : ℝ) {e : V}
    (he : ‖e‖ = 1) {b : V → ℂ} (hb : ContDiff ℝ ∞ b) :
    sphereAxisIntegralND s e (sphereCasimirND B b) =
      -(s:ℂ)^2*(sphereAxisIntegralND s e b + deriv (deriv (fun s => sphereAxisIntegralND s e b)) s) -
      ((Fintype.card ι:ℂ)-1)*s*deriv (fun s => sphereAxisIntegralND s e b) s := by
  rw [sphereAxisIntegralND_deriv2 hb.continuous,sphereAxisIntegralND_deriv hb.continuous,
    sphereAxisIntegralND_casimir B s he hb]
  ring

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set
open scoped ContDiff RealInnerProductSpace
variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Fintype ι]
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma tsupport_angularDerivativeND_subset (A : V →L[ℝ] V) (f : V → ℂ) :
    tsupport (angularDerivativeND A f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hn
  have hz := fderiv_of_notMem_tsupport ℝ hn
  exact hx (by simp [angularDerivativeND,hz])

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma tsupport_sphereCasimirND_subset (B : OrthonormalBasis ι ℝ V) (f : V → ℂ) :
    tsupport (sphereCasimirND B f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hn
  have hz (i j : ι) : angularDerivativeND (angularGeneratorND (B i) (B j))
      (angularDerivativeND (angularGeneratorND (B i) (B j)) f) x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun h => hn ((tsupport_angularDerivativeND_subset _ _)
      ((tsupport_angularDerivativeND_subset _ _) h))
  exact hx (by simp [sphereCasimirND,hz])

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
