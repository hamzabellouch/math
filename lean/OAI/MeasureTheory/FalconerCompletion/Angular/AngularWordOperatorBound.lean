import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Angular.EndpointMask
import OAI.MeasureTheory.FalconerCompletion.Graphs.NormalizedAngularWord
import OAI.MeasureTheory.FalconerCompletion.Sphere.AngularDerivativeBound

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set
open scoped ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

lemma angularWordOperatorND_bound (L : List (V →L[ℝ] V)) (m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : SmoothFunctionND V) (A : ℝ) (s : ℕ), 1 ≤ A →
      (∀ j ≤ m+L.length, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b.1 w‖ ≤ C*A^(j+s)) →
      ∀ j ≤ m, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (angularWordOperatorND L b).1 w‖ ≤ D*A^(j+(s+L.length)) := by
  induction L generalizing m C with
  | nil =>
    refine ⟨C,hC,?_⟩
    intro b A s hA hb j hj w hw
    simpa [angularWordOperatorND] using hb j (by simpa using hj) w hw
  | cons T L ih =>
    obtain ⟨D,hD,hDb⟩ := ih (m+1) C hC
    obtain ⟨F,hF,hFb⟩ := angularDerivativeND_bound T m D hD
    refine ⟨F,hF,?_⟩
    intro b A s hA hb j hj w hw
    have hb' : ∀ k ≤ m+1+L.length, ∀ u, ‖u‖=1 →
        ‖iteratedFDeriv ℝ k b.1 u‖ ≤ C*A^(k+s) := fun k hk u hu => hb k (by simpa only [List.length_cons] using (show k ≤ m+(L.length+1) by omega)) u hu
    have hh := hFb (angularWordOperatorND L b).1 A (s+L.length)
      (smoothFunctionND_contDiff _) hA (hDb b A s hA hb') j hj w hw
    change ‖iteratedFDeriv ℝ j (angularDerivativeND T (angularWordOperatorND L b).1) w‖ ≤ _
    simpa only [List.length_cons,Nat.add_assoc] using hh

lemma normalizedAngularWordND_bound (L : List (V →L[ℝ] V)) (m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : SmoothFunctionND V) (A : ℝ), 1 ≤ A →
      (∀ j ≤ m+L.length, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b.1 w‖ ≤ C*A^j) →
      ∀ j ≤ m, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (normalizedAngularWordND A L b).1 w‖ ≤ D*A^j := by
  obtain ⟨D,hD,hDb⟩ := angularWordOperatorND_bound L m C hC
  refine ⟨D,hD,?_⟩
  intro b A hA hb j hj w hw
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hh := sphere_derivative_const_mul_bound ((A:ℂ)^L.length)⁻¹
    (smoothFunctionND_contDiff (angularWordOperatorND L b))
    (hDb b A 0 hA (by simpa only [Nat.add_zero] using hb)) j hj w hw
  change ‖iteratedFDeriv ℝ j (normalizedAngularWordND A L b).1 w‖ ≤ _ at hh
  apply hh.trans
  rw [norm_inv,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hAp]
  simp only [Nat.zero_add]
  rw [pow_add]
  have hn : A^L.length ≠ 0 := pow_ne_zero _ hAp.ne'
  field_simp
  exact le_rfl

lemma normalizedAngularWordND_finite_bound (W : Finset (List (V →L[ℝ] V)))
    (m b : ℕ) (hb : ∀ L ∈ W, L.length ≤ b) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L ∈ W, ∀ (f : SmoothFunctionND V) (A : ℝ), 1 ≤ A →
      (∀ j ≤ m+b, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j f.1 w‖ ≤ C*A^j) →
      ∀ j ≤ m, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (normalizedAngularWordND A L f).1 w‖ ≤ D*A^j := by
  choose D hD hDb using fun L => normalizedAngularWordND_bound (V := V) L m C hC
  refine ⟨∑ L ∈ W,D L,Finset.sum_nonneg (fun L _ => hD L),?_⟩
  intro L hL f A hA hf j hj w hw
  have hh := hDb L f A hA (fun k hk z hz => hf k (by have := hb L hL; omega) z hz) j hj w hw
  apply hh.trans
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun L _ => hD L) hL) (pow_nonneg (by linarith) _)

end CurrentFalconer
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer
open scoped ENNReal RealInnerProductSpace ContDiff Topology
variable {d : ℕ}
noncomputable def actualEndpointSmooth (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (x : EuclideanSpace ℝ (Fin d)) : SmoothFunctionND (EuclideanSpace ℝ (Fin d)) :=
  ⟨fun w => (actualEndpointMask ρ m N sig C J i b x w : ℂ),
    Complex.ofRealCLM.contDiff.comp (actualEndpointMask_smooth ρ m N sig C J i b x)⟩

lemma actualEndpointSmooth_support (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (x : EuclideanSpace ℝ (Fin d)) :
    tsupport (actualEndpointSmooth ρ m N sig C J i b x).1=
      tsupport (actualEndpointMask ρ m N sig C J i b x) := by
  apply congrArg closure
  ext w
  change (Complex.ofReal (actualEndpointMask ρ m N sig C J i b x w) ≠ 0) ↔ _
  exact not_congr Complex.ofReal_eq_zero

lemma actualEndpointSmooth_derivative_norm (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (x w : EuclideanSpace ℝ (Fin d)) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (actualEndpointSmooth ρ m N sig C J i b x).1 w‖=
      ‖iteratedFDeriv ℝ k (actualEndpointMask ρ m N sig C J i b x) w‖ := by
  exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left
    (actualEndpointMask_smooth ρ m N sig C J i b x).contDiffAt
    (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))

noncomputable def actualEndpointAngular
    (L : List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (N : ℕ)
    (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor) (x : EuclideanSpace ℝ (Fin d)) :
    SmoothFunctionND (EuclideanSpace ℝ (Fin d)) :=
  normalizedAngularWordND (sourceMaskScaleND (descriptorLength b) ((2:ℝ)^N) sig) L
    (actualEndpointSmooth ρ m N sig C J i b x)

lemma actualEndpointAngular_derivatives
    (W : Finset (List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))))
    (M B : ℕ) (hW : ∀ L ∈ W, L.length ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L ∈ W,
      ∀ (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (N : ℕ)
        (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor) (x : EuclideanSpace ℝ (Fin d)),
      ∀ j ≤ M, ∀ w, ‖w‖=1 →
      ‖iteratedFDeriv ℝ j (actualEndpointAngular L ρ m N sig C J i b x).1 w‖ ≤
        D*(sourceMaskScaleND (descriptorLength b) ((2:ℝ)^N) sig)^j := by
  obtain ⟨C₀,hC,hCb⟩ := actualEndpointMask_derivatives d (M+B)
  obtain ⟨D,hD,hDb⟩ := normalizedAngularWordND_finite_bound W M B hW C₀ hC
  refine ⟨D,hD,?_⟩
  intro L hL ρ m N sig C J i b x j hj w hw
  apply hDb L hL (actualEndpointSmooth ρ m N sig C J i b x)
    (sourceMaskScaleND (descriptorLength b) ((2:ℝ)^N) sig)
    (sourceMaskScaleND_one_le _ _ _) _ j hj w hw
  intro k hk z _hz
  rw [actualEndpointSmooth_derivative_norm]
  exact hCb ρ m N sig C J i b k hk x z

lemma uniform_actualEndpointAngular_support {sig : ℝ} (hsig : 0<sig) {J : ℕ} (hJ : 0<J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (ρ : Measure (EuclideanSpace ℝ (Fin d))), IsFiniteMeasure ρ →
      ∀ (m : ℝ → ℝ) (C : ℝ) (i : ℕ) (b : PolicyDescriptor), ValidDescriptor N b →
      ∀ (L : List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
        (k : ℕ) (x w : EuclideanSpace ℝ (Fin d)), ‖w‖=1 →
      w ∈ tsupport (iteratedFDeriv ℝ k (actualEndpointAngular L ρ m N sig C J i b x).1) →
      (x,w) ∈ endpointGood ρ m N sig C J (i+1) b := by
  obtain ⟨N₀,h₀⟩ := uniform_actualEndpointMask_support (d:=d) hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ρ hf m C i b hb L k x w hw hs
  have hs' := tsupport_iteratedFDeriv_subset k hs
  have hs'' := normalizedAngularWordND_support
    (sourceMaskScaleND (descriptorLength b) ((2:ℝ)^N) sig) L
    (actualEndpointSmooth ρ m N sig C J i b x) hs'
  rw [actualEndpointSmooth_support] at hs''
  apply h₀ N hN ρ hf m C i b hb 0 x w hw
  have he : tsupport (iteratedFDeriv ℝ 0 (actualEndpointMask ρ m N sig C J i b x))=
      tsupport (actualEndpointMask ρ m N sig C J i b x) := by
    apply congrArg closure
    ext u
    simp only [Function.mem_support]
    rw [← norm_ne_zero_iff,norm_iteratedFDeriv_zero,norm_ne_zero_iff]
  rw [he]
  exact hs''

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open scoped ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma angularDerivativeND_star (A : V →L[ℝ] V) (f : V → ℂ) :
    angularDerivativeND A (fun x => star (f x)) = fun x => star (angularDerivativeND A f x) := by
  funext x
  simp only [angularDerivativeND,fderiv_star,ContinuousLinearMap.comp_apply]
  rfl

lemma angularDerivativeND_even (A : V →L[ℝ] V) {f : V → ℂ}
    (hf : ContDiff ℝ ∞ f) (he : Function.Even f) : Function.Even (angularDerivativeND A f) := by
  have heq : f ∘ (fun x : V => -x) = f := funext he
  intro x
  have hd := fderiv_comp (𝕜 := ℝ) x (hf.differentiable (by simp) (-x))
    (differentiableAt_id.neg : DifferentiableAt ℝ (fun y : V => -y) x)
  have hneg : fderiv ℝ (fun y : V => -y) x = -ContinuousLinearMap.id ℝ V :=
    ContinuousLinearMap.fderiv (-ContinuousLinearMap.id ℝ V)
  rw [heq,hneg] at hd
  have hh := congrArg (fun T : V →L[ℝ] ℂ => T (A x)) hd
  simpa only [angularDerivativeND,Function.comp_apply,map_neg,ContinuousLinearMap.comp_apply,
    fderiv_fun_neg,fderiv_fun_id,neg_apply,ContinuousLinearMap.id_apply] using hh.symm

noncomputable def smoothStarND (f : SmoothFunctionND V) : SmoothFunctionND V :=
  ⟨fun x => star (f.1 x), by
    change ContDiff ℝ ∞ (fun x => star (f.1 x))
    simpa only [Complex.star_def,Function.comp_def,Complex.conjCLE_apply] using
      Complex.conjCLE.contDiff.comp (smoothFunctionND_contDiff f)⟩

lemma angularWordOperatorND_star (L : List (V →L[ℝ] V)) (f : SmoothFunctionND V) :
    angularWordOperatorND L (smoothStarND f)=smoothStarND (angularWordOperatorND L f) := by
  induction L with
  | nil => rfl
  | cons A L ih =>
    change angularOperatorND A (angularWordOperatorND L (smoothStarND f)) = _
    rw [ih]
    apply Subtype.ext
    exact angularDerivativeND_star A _

lemma angularWordOperatorND_even (L : List (V →L[ℝ] V)) (f : SmoothFunctionND V)
    (he : Function.Even f.1) : Function.Even (angularWordOperatorND L f).1 := by
  induction L with
  | nil => exact he
  | cons A L ih =>
    exact angularDerivativeND_even A (smoothFunctionND_contDiff _) ih

lemma normalizedAngularWordND_even (A : ℝ) (L : List (V →L[ℝ] V)) (f : SmoothFunctionND V)
    (he : Function.Even f.1) : Function.Even (normalizedAngularWordND A L f).1 := by
  intro x
  change ((A:ℂ)^L.length)⁻¹ * (angularWordOperatorND L f).1 (-x) =
    ((A:ℂ)^L.length)⁻¹ * (angularWordOperatorND L f).1 x
  rw [angularWordOperatorND_even L f he x]

lemma normalizedAngularWordND_star (A : ℝ) (L : List (V →L[ℝ] V)) (f : SmoothFunctionND V) :
    normalizedAngularWordND A L (smoothStarND f) = smoothStarND (normalizedAngularWordND A L f) := by
  apply Subtype.ext
  funext x
  simp only [normalizedAngularWordND,angularWordOperatorND_star]
  change ((A:ℂ)^L.length)⁻¹ * star ((angularWordOperatorND L f).1 x) =
    star (((A:ℂ)^L.length)⁻¹ * (angularWordOperatorND L f).1 x)
  simp only [map_mul,map_inv₀,map_pow,Complex.star_def,Complex.conj_ofReal]

end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI
