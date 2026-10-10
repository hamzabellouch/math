import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.AngularDerivativeEventuallyEq2

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set Metric MeasureTheory
open scoped ContDiff SchwartzMap RealInnerProductSpace
variable {n : ℕ}

noncomputable def sphereShiftND (n j : ℕ) : ℂ :=
  (j:ℂ)*(j+1)-((n/2:ℝ):ℂ)*((n/2:ℝ)-1)

lemma sphereJetPolynomialND_eq (j : ℕ) (b : SphereAmbientND n → ℂ) :
    sphereJetPolynomialND n j b = casimirPolynomialND (sphereBasisND n) (sphereShiftND n) j b := by
  induction j generalizing b with
  | zero => rfl
  | succ j ih =>
    unfold sphereJetPolynomialND casimirPolynomialND
    rw [ih,ih]
    rfl

lemma sphereJetPolynomialND_comp_isometry (j : ℕ) (Q : SphereAmbientND n ≃ₗᵢ[ℝ] SphereAmbientND n)
    {b : SphereAmbientND n → ℂ} (hb : ContDiff ℝ ∞ b) :
    sphereJetPolynomialND n j (b ∘ Q) = (sphereJetPolynomialND n j b) ∘ Q := by
  induction j generalizing b with
  | zero => rfl
  | succ j ih =>
    rw [sphereJetPolynomialND,sphereCasimirND_comp_isometry _ Q hb,
      ih (sphereCasimirND_contDiff _ hb),ih hb]
    rfl

lemma sphereJetPolynomialND_eventuallyEq (j : ℕ) {b c : SphereAmbientND n → ℂ}
    {w : SphereAmbientND n} (h : b =ᶠ[nhds w] c) :
    sphereJetPolynomialND n j b =ᶠ[nhds w] sphereJetPolynomialND n j c := by
  simp only [sphereJetPolynomialND_eq]
  exact casimirPolynomialND_eventuallyEq _ _ _ h

lemma sphereNorthPartND_tsupport (b : SphereAmbientND n → ℂ) :
    tsupport (sphereNorthPartND b) ⊆ {w | -(1/2:ℝ) ≤ (WithLp.ofLp w).2} := by
  have hcoord : Continuous (fun w : SphereAmbientND n => (WithLp.ofLp w).2) :=
    continuous_snd.comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).continuous
  apply closure_minimal _ (isClosed_le continuous_const hcoord)
  intro w hw
  by_contra hn
  have he := sphereNorthCutoffND_zero (le_of_lt (not_le.mp hn))
  exact hw (by simp [sphereNorthPartND,he])

noncomputable def northPartAmplitudeND (b : SphereAmbientND n → ℂ) (hb : ContDiff ℝ ∞ b) :
    NorthAmplitudeND n := ⟨sphereNorthPartND b,sphereNorthPartND_contDiff hb,sphereNorthPartND_tsupport b⟩

lemma sphereNorthPartND_eventuallyEq (b : SphereAmbientND n → ℂ) :
    sphereNorthPartND b =ᶠ[nhds (WithLp.toLp 2 (0,(1:ℝ)))] b := by
  have hcoord : Continuous (fun w : SphereAmbientND n => (WithLp.ofLp w).2) :=
    continuous_snd.comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).continuous
  have hh : {w : SphereAmbientND n | (1/2:ℝ) < (WithLp.ofLp w).2} ∈
      nhds (WithLp.toLp 2 (0,(1:ℝ))) :=
    (isOpen_lt continuous_const hcoord).mem_nhds (by norm_num)
  filter_upwards [hh] with w hw
  simp [sphereNorthPartND,sphereNorthCutoffND_one hw.le]

lemma sphereNorthPartND_polynomial (b : SphereAmbientND n → ℂ) (j : ℕ) :
    sphereJetPolynomialND n j (sphereNorthPartND b) (WithLp.toLp 2 (0,(1:ℝ))) =
      sphereJetPolynomialND n j b (WithLp.toLp 2 (0,(1:ℝ))) :=
  (sphereJetPolynomialND_eventuallyEq j (sphereNorthPartND_eventuallyEq b)).eq_of_nhds

noncomputable def sphereLND (n j : ℕ) (b : SphereAmbientND n → ℂ) (w : SphereAmbientND n) : ℂ :=
  sphereLeadingND n * ((2*Complex.I)^j * (j.factorial:ℂ))⁻¹ * sphereJetPolynomialND n j b w

lemma NorthAmplitudeND.expansion_global (b : NorthAmplitudeND n) (J : ℕ) {Λ : ℝ} (hΛ : 0 < Λ) :
    Complex.exp (Complex.I*Λ) *
      (fresnelCoefficientND (EuclideanSpace ℝ (Fin n)) (Λ/2) * quadraticExpansionND b.chart J (Λ/2)) =
      (Λ^(-(n/2:ℝ)) : ℝ) * Complex.exp (Complex.I*Λ) *
        ∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(- (j:ℤ)) * sphereLND n j b (WithLp.toLp 2 (0,(1:ℝ))) := by
  rw [fresnelCoefficientND_half hΛ,b.quadratic_series_global J hΛ]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [sphereLND,mul_inv_rev,zpow_neg,zpow_natCast]
  ring

theorem northAmplitude_stationary_globalND (C : ℝ) (hC : 0 ≤ C) (J : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : NorthAmplitudeND n) (A Λ : ℝ),
      1 ≤ A → 0 < Λ →
      (∀ j ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖ ≤ C*A^j) →
      ‖sphereAxisIntegralND Λ (WithLp.toLp 2 (0,(1:ℝ))) b -
        (Λ^(-(n/2:ℝ)) : ℝ) * Complex.exp (Complex.I*Λ) *
          ∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(- (j:ℤ)) * sphereLND n j b (WithLp.toLp 2 (0,(1:ℝ)))‖ ≤
        D * Λ^(-(n:ℝ)/2-(J+1:ℕ)) * A^(2*(J+1)+n+3) := by
  obtain ⟨D,hD,hlocal⟩ := sphere_stationaryND_uniform (n := n) (Real.sqrt (7/2:ℝ))
    (Real.sqrt_nonneg _) sqrt_seven_halves_lt_two C hC J
  refine ⟨D,hD,?_⟩
  intro b A Λ hA hΛ hderiv
  have hh := hlocal b A Λ b.smooth (fun w _ h => northAmplitudeND_vanish b w h) hA hΛ hderiv
  rw [← b.expansion_global J hΛ]
  exact hh

lemma sphereJetPolynomialND_star (j : ℕ) (b : SphereAmbientND n → ℂ) :
    sphereJetPolynomialND n j (fun w => star (b w)) = fun w => star (sphereJetPolynomialND n j b w) := by
  have hs (f : SphereAmbientND n → ℂ) :
      sphereCasimirND (sphereBasisND n) (fun w => star (f w)) =
        fun w => star (sphereCasimirND (sphereBasisND n) f w) := by
    have ha (A : SphereAmbientND n →L[ℝ] SphereAmbientND n) (f : SphereAmbientND n → ℂ) :
        angularDerivativeND A (fun w => star (f w)) = fun w => star (angularDerivativeND A f w) := by
      funext w
      unfold angularDerivativeND
      rw [fderiv_star]
      rfl
    funext w
    simp only [sphereCasimirND,ha]
    norm_num
  induction j generalizing b with
  | zero => rfl
  | succ j ih =>
    rw [sphereJetPolynomialND,hs,ih,ih]
    funext w
    simp [sphereJetPolynomialND]

lemma sphereReflectedSouthPartND_tsupport (b : SphereAmbientND n → ℂ) :
    tsupport (sphereReflectedSouthPartND b) ⊆ {w | -(1/2:ℝ) ≤ (WithLp.ofLp w).2} := by
  have hcoord : Continuous (fun w : SphereAmbientND n => (WithLp.ofLp w).2) :=
    continuous_snd.comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).continuous
  apply closure_minimal _ (isClosed_le continuous_const hcoord)
  intro w hw
  by_contra hn
  change ¬ -(1/2:ℝ) ≤ (WithLp.ofLp w).2 at hn
  have he : sphereReflectedSouthPartND b w = 0 :=
    sphereReflectedSouthPartND_support (by rw [Real.sq_sqrt (by norm_num)]; linarith [not_le.mp hn])
  exact hw he

noncomputable def southPartAmplitudeND (b : SphereAmbientND n → ℂ) (hb : ContDiff ℝ ∞ b) :
    NorthAmplitudeND n :=
  ⟨sphereReflectedSouthPartND b,sphereReflectedSouthPartND_contDiff hb,sphereReflectedSouthPartND_tsupport b⟩

lemma sphereReflectedSouthPartND_eventuallyEq (b : SphereAmbientND n → ℂ) :
    sphereReflectedSouthPartND b =ᶠ[nhds (WithLp.toLp 2 (0,(1:ℝ)))] (fun w => star (b (-w))) := by
  have hcoord : Continuous (fun w : SphereAmbientND n => (WithLp.ofLp w).2) :=
    continuous_snd.comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).continuous
  have hh : {w : SphereAmbientND n | (1/2:ℝ) < (WithLp.ofLp w).2} ∈
      nhds (WithLp.toLp 2 (0,(1:ℝ))) :=
    (isOpen_lt continuous_const hcoord).mem_nhds (by norm_num)
  filter_upwards [hh] with w hw
  have hn : (WithLp.ofLp (-w)).2 ≤ -(1/2:ℝ) := by
    change -(WithLp.ofLp w).2 ≤ -(1/2:ℝ)
    linarith
  simp [sphereReflectedSouthPartND,sphereNorthCutoffND_zero hn]

lemma sphereReflectedSouthPartND_polynomial {b : SphereAmbientND n → ℂ}
    (hb : ContDiff ℝ ∞ b) (j : ℕ) :
    sphereJetPolynomialND n j (sphereReflectedSouthPartND b) (WithLp.toLp 2 (0,(1:ℝ))) =
      star (sphereJetPolynomialND n j b (-WithLp.toLp 2 (0,(1:ℝ)))) := by
  rw [(sphereJetPolynomialND_eventuallyEq j (sphereReflectedSouthPartND_eventuallyEq b)).eq_of_nhds,
    sphereJetPolynomialND_star]
  have he := sphereJetPolynomialND_comp_isometry j (LinearIsometryEquiv.neg ℝ (E := SphereAmbientND n)) hb
  exact congrArg (fun f => star (f (WithLp.toLp 2 (0,(1:ℝ))))) he

noncomputable def sphereLMinusND (n j : ℕ) (b : SphereAmbientND n → ℂ) (w : SphereAmbientND n) : ℂ :=
  star (sphereLND n j (fun x => star (b x)) w)

lemma sphereLND_comp_isometry (j : ℕ) (Q : SphereAmbientND n ≃ₗᵢ[ℝ] SphereAmbientND n)
    {b : SphereAmbientND n → ℂ} (hb : ContDiff ℝ ∞ b) :
    sphereLND n j (b ∘ Q) = (sphereLND n j b) ∘ Q := by
  funext w
  simp only [sphereLND,sphereJetPolynomialND_comp_isometry j Q hb,Function.comp_apply]

lemma sphereLMinusND_comp_isometry (j : ℕ) (Q : SphereAmbientND n ≃ₗᵢ[ℝ] SphereAmbientND n)
    {b : SphereAmbientND n → ℂ} (hb : ContDiff ℝ ∞ b) :
    sphereLMinusND n j (b ∘ Q) = (sphereLMinusND n j b) ∘ Q := by
  have hbs : ContDiff ℝ ∞ (fun w => star (b w)) := by
    simpa only [Complex.star_def,Function.comp_def,Complex.conjCLE_apply] using Complex.conjCLE.contDiff.comp hb
  have he := sphereLND_comp_isometry j Q hbs
  funext w
  exact congrArg (fun f => star (f w)) he

lemma northPartAmplitudeND_L {b : SphereAmbientND n → ℂ} (hb : ContDiff ℝ ∞ b) (j : ℕ) :
    sphereLND n j (northPartAmplitudeND b hb) (WithLp.toLp 2 (0,(1:ℝ))) =
      sphereLND n j b (WithLp.toLp 2 (0,(1:ℝ))) := by
  unfold sphereLND
  change _ * sphereJetPolynomialND n j (sphereNorthPartND b) _ = _
  rw [sphereNorthPartND_polynomial]

lemma southPartAmplitudeND_L {b : SphereAmbientND n → ℂ} (hb : ContDiff ℝ ∞ b) (j : ℕ) :
    star (sphereLND n j (southPartAmplitudeND b hb) (WithLp.toLp 2 (0,(1:ℝ)))) =
      sphereLMinusND n j b (-WithLp.toLp 2 (0,(1:ℝ))) := by
  unfold sphereLMinusND
  simp only [sphereLND]
  change star (_ * sphereJetPolynomialND n j (sphereReflectedSouthPartND b) _) = _
  rw [sphereReflectedSouthPartND_polynomial hb,sphereJetPolynomialND_star]

theorem sphere_global_two_poleND (C : ℝ) (hC : 0 ≤ C) (J : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : SphereAmbientND n → ℂ) (A Λ : ℝ)
      (_hb : ContDiff ℝ ∞ b), 1 ≤ A → 0 < Λ →
      (∀ j ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖ ≤ C*A^j) →
      ‖sphereAxisIntegralND Λ (WithLp.toLp 2 (0,(1:ℝ))) b -
        (Λ^(-(n/2:ℝ)) : ℝ) *
          (Complex.exp (Complex.I*Λ) *
            ∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(- (j:ℤ)) * sphereLND n j b (WithLp.toLp 2 (0,(1:ℝ))) +
          Complex.exp (-(Complex.I*Λ)) *
            ∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(- (j:ℤ)) * sphereLMinusND n j b (-WithLp.toLp 2 (0,(1:ℝ))))‖ ≤
        D * Λ^(-(n:ℝ)/2-(J+1:ℕ)) * A^(2*(J+1)+n+3) := by
  obtain ⟨C',hC',hparts⟩ := sphere_parts_derivative_bound
    (V := EuclideanSpace ℝ (Fin n)) (2*(J+1)+n+3) C hC
  obtain ⟨D,hD,hlocal⟩ := northAmplitude_stationary_globalND (n := n) C' hC' J
  refine ⟨2*D,by positivity,?_⟩
  intro b A Λ hb hA hΛ hderiv
  have hN := hlocal (northPartAmplitudeND b hb) A Λ hA hΛ
    (fun j hj w hw => (hparts b A hb hA hderiv j hj w hw).1)
  have hS := hlocal (southPartAmplitudeND b hb) A Λ hA hΛ
    (fun j hj w hw => (hparts b A hb hA hderiv j hj w hw).2)
  simp only [northPartAmplitudeND_L] at hN
  have hstar := hS
  rw [← norm_star] at hstar
  simp only [star_sub,star_mul,star_sum,star_zpow₀,southPartAmplitudeND_L] at hstar
  simp only [Complex.star_def,Complex.conj_ofReal,← Complex.exp_conj,map_mul,Complex.conj_I] at hstar
  simp_rw [mul_comm (sphereLMinusND n _ b _) _] at hstar
  have hsplit := sphereOscillationND_split (V := EuclideanSpace ℝ (Fin n)) Λ hb.continuous
  change sphereAxisIntegralND Λ (WithLp.toLp 2 (0,(1:ℝ))) b =
    sphereAxisIntegralND Λ (WithLp.toLp 2 (0,(1:ℝ))) (northPartAmplitudeND b hb) +
      star (sphereAxisIntegralND Λ (WithLp.toLp 2 (0,(1:ℝ))) (southPartAmplitudeND b hb)) at hsplit
  rw [hsplit,mul_add,add_sub_add_comm]
  apply (norm_add_le _ _).trans
  have hh := add_le_add hN hstar
  convert hh using 1 <;> (try simp only [Complex.star_def]) <;> ring_nf

theorem sphere_global_rotatedND (C : ℝ) (hC : 0 ≤ C) (J : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : SphereAmbientND n → ℂ) (A Λ : ℝ)
      (e : SphereAmbientND n) (_hb : ContDiff ℝ ∞ b), 1 ≤ A → 0 < Λ → ‖e‖=1 →
      (∀ j ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖ ≤ C*A^j) →
      ‖sphereAxisIntegralND Λ e b -
        (Λ^(-(n/2:ℝ)) : ℝ) *
          (Complex.exp (Complex.I*Λ) *
            ∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(- (j:ℤ)) * sphereLND n j b e +
          Complex.exp (-(Complex.I*Λ)) *
            ∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(- (j:ℤ)) * sphereLMinusND n j b (-e))‖ ≤
        D * Λ^(-(n:ℝ)/2-(J+1:ℕ)) * A^(2*(J+1)+n+3) := by
  obtain ⟨D,hD,hfull⟩ := sphere_global_two_poleND (n := n) C hC J
  refine ⟨D,hD,?_⟩
  intro b A Λ e hb hA hΛ he hderiv
  let R := sphereAxisReflectionND (WithLp.toLp 2 (0,(1:ℝ))) e
  have hR : R (WithLp.toLp 2 (0,(1:ℝ))) = e :=
    sphereAxisReflectionND_apply (sphere_north_normND.trans he.symm)
  have hh := hfull (b ∘ R) A Λ (hb.comp R.toContinuousLinearEquiv.contDiff) hA hΛ (by
    intro j hj w hw
    rw [R.norm_iteratedFDeriv_comp_right]
    exact hderiv j hj (R w) (by simpa using hw))
  simp only [sphereLND_comp_isometry _ R hb,sphereLMinusND_comp_isometry _ R hb,
    Function.comp_apply,map_neg,hR] at hh
  rwa [← sphereAxisIntegralND_rotate R Λ, hR] at hh

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
open scoped ContDiff RealInnerProductSpace
variable {n : ℕ}

lemma casimirPolynomialND_const_mul {V ι : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [Fintype ι] (B : OrthonormalBasis ι ℝ V)
    (shift : ℕ → ℂ) (j : ℕ) {b : V → ℂ} (hb : ContDiff ℝ ∞ b) (c : ℂ) :
    casimirPolynomialND B shift j (fun w => c*b w) = fun w => c*casimirPolynomialND B shift j b w := by
  induction j generalizing b with
  | zero => rfl
  | succ j ih =>
    rw [casimirPolynomialND,sphereCasimirND_const_mul B hb c,
      ih (sphereCasimirND_contDiff B hb),ih hb]
    funext w
    simp only [casimirPolynomialND]
    ring

lemma sphereLND_const_mul (j : ℕ) {b : SphereAmbientND n → ℂ}
    (hb : ContDiff ℝ ∞ b) (c : ℂ) :
    sphereLND n j (fun w => c*b w) = fun w => c*sphereLND n j b w := by
  funext w
  simp only [sphereLND,sphereJetPolynomialND_eq,casimirPolynomialND_const_mul _ _ _ hb]
  ring

lemma sphereAxisIntegralND_const_mul {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (Λ : ℝ) (e : V) (b : V → ℂ) (c : ℂ) :
    sphereAxisIntegralND Λ e (fun w => c*b w) = c*sphereAxisIntegralND Λ e b := by
  simp only [sphereAxisIntegralND,mul_left_comm _ c,integral_const_mul]

noncomputable def NorthAmplitudeND.const_mul (b : NorthAmplitudeND n) (c : ℂ) : NorthAmplitudeND n where
  toFun := fun w => c*b w
  smooth := contDiff_const.mul b.smooth
  support := (tsupport_mul_subset_right (f := fun _ => c) (g := b.toFun)).trans b.support

noncomputable def northRemainderND (J : ℕ) (Λ : ℝ) (b : SphereAmbientND n → ℂ) : ℂ :=
  sphereAxisIntegralND Λ (WithLp.toLp 2 (0,(1:ℝ))) b -
    (Λ^(-(n/2:ℝ)) : ℝ) * Complex.exp (Complex.I*Λ) *
      ∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(- (j:ℤ)) * sphereLND n j b (WithLp.toLp 2 (0,(1:ℝ)))

lemma northRemainderND_const_mul (J : ℕ) (Λ : ℝ) {b : SphereAmbientND n → ℂ}
    (hb : ContDiff ℝ ∞ b) (c : ℂ) :
    northRemainderND J Λ (fun w => c*b w) = c*northRemainderND J Λ b := by
  simp only [northRemainderND,sphereAxisIntegralND_const_mul,sphereLND_const_mul _ hb,
    mul_left_comm _ c,← Finset.mul_sum]
  ring

theorem northAmplitude_stationary_shiftND (C : ℝ) (hC : 0 ≤ C) (J : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : NorthAmplitudeND n) (A Λ : ℝ) (s : ℕ),
      1 ≤ A → 0 < Λ →
      (∀ j ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖ ≤ C*A^(j+s)) →
      ‖northRemainderND J Λ b‖ ≤ D * Λ^(-(n:ℝ)/2-(J+1:ℕ)) * A^(2*(J+1)+n+3+s) := by
  obtain ⟨D,hD,hDb⟩ := northAmplitude_stationary_globalND (n := n) C hC J
  refine ⟨D,hD,?_⟩
  intro b A Λ s hA hΛ hderiv
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  let c : ℂ := ((A^s:ℝ):ℂ)⁻¹
  have hcnorm : ‖c‖ = (A^s)⁻¹ := by simp [c,Complex.norm_real,abs_of_pos hAp]
  have hh := hDb (b.const_mul c) A Λ hA hΛ (by
    intro j hj w hw
    change ‖iteratedFDeriv ℝ j (fun w => c • b w) w‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' ((b.smooth.of_le
      (show (j:ℕ∞ω) ≤ ∞ by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))).contDiffAt),norm_smul,hcnorm]
    calc
      _ ≤ (A^s)⁻¹*(C*A^(j+s)) := mul_le_mul_of_nonneg_left (hderiv j hj w hw) (inv_nonneg.mpr (pow_nonneg hAp.le s))
      _ = C*A^j := by rw [pow_add]; field_simp)
  change ‖northRemainderND J Λ (fun w => c*b w)‖ ≤ _ at hh
  rw [northRemainderND_const_mul J Λ b.smooth,norm_mul,hcnorm] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (pow_nonneg hAp.le s)
  have hcA : A^s ≠ 0 := ne_of_gt (pow_pos hAp s)
  have hleft : A^s*((A^s)⁻¹*‖northRemainderND J Λ b‖) = ‖northRemainderND J Λ b‖ := by
    rw [← mul_assoc,mul_inv_cancel₀ hcA,one_mul]
  have hright : A^s*(D*Λ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3)) =
      D*Λ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3+s) := by rw [pow_add]; ring
  rwa [hleft,hright] at hmul

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
