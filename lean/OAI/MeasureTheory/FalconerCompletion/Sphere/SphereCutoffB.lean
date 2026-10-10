import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.CompactMultiplierDerivativeShift
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereLPolynomial2

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set Metric MeasureTheory
open scoped ContDiff
variable {n : ℕ}

noncomputable def sphereCutoffBND (b : SmoothFunctionND (SphereAmbientND n)) (j : ℕ) :
    NorthAmplitudeND n := northPartAmplitudeND (sphereBND j b).1 (sphereBND j b).2

lemma sphereCutoffBND_bound (j m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : SmoothFunctionND (SphereAmbientND n)) (A : ℝ), 1 ≤ A →
      (∀ k ≤ m+2*j, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ k b.1 w‖ ≤ C*A^k) →
      ∀ k ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ k (sphereCutoffBND b j) w‖ ≤ D*A^(k+2*j) := by
  obtain ⟨B,hB,hBb⟩ := sphereBND_bound (n := n) j m C hC
  obtain ⟨D,hD,hDb⟩ := compact_multiplier_derivative_shiftND
    (w := sphereNorthCutoffND (V := EuclideanSpace ℝ (Fin n))) (isCompact_sphere 0 1)
    sphereNorthCutoffND_contDiff m B hB
  refine ⟨D,hD,?_⟩
  intro b A hA hb k hk w hw
  exact hDb (sphereBND j b).1 A (2*j) (sphereBND j b).2 hA
    (fun k hk w hw => hBb b A hA hb k hk w (by simpa using hw)) k hk w (by simpa using hw)

lemma sphere_inverse_cutoff_seriesND (J : ℕ) (Λ : ℝ)
    (b : SmoothFunctionND (SphereAmbientND n)) :
    (∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ)) *
      ∑ h ∈ Finset.range (J-j+1), (Λ:ℂ)^(-(h:ℤ)) *
        sphereLND n h (sphereCutoffBND b j) (WithLp.toLp 2 (0,(1:ℝ)))) = b.1 (WithLp.toLp 2 (0,(1:ℝ))) := by
  refine Eq.trans ?_ (sphere_inverse_triangleND J ((Λ:ℂ)⁻¹) b (WithLp.toLp 2 (0,(1:ℝ))))
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ J := by have := Finset.mem_range.mp hj; omega
  rw [Finset.mul_sum,show J-j+1=J+1-j by omega]
  apply Finset.sum_congr rfl
  intro h _
  simp only [sphereCutoffBND,northPartAmplitudeND,sphereLND,
    sphereNorthPartND_polynomial,zpow_neg,zpow_natCast,inv_pow,pow_add]
  ring

lemma sphere_inverse_cutoff_errorND (J : ℕ) {Λ : ℝ} (hΛ : 0 < Λ) (b : SmoothFunctionND (SphereAmbientND n)) :
    ((Λ^((n:ℝ)/2):ℝ):ℂ) *
        (∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ)) *
          sphereAxisIntegralND Λ (WithLp.toLp 2 (0,(1:ℝ))) (sphereCutoffBND b j)) -
      Complex.exp (Complex.I*Λ)*b.1 (WithLp.toLp 2 (0,(1:ℝ))) =
    ((Λ^((n:ℝ)/2):ℝ):ℂ) *
      (∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ)) * northRemainderND (J-j) Λ (sphereCutoffBND b j)) := by
  have hs := sphere_inverse_cutoff_seriesND J Λ b
  have hs' :
      (∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ)) *
        (((Λ^(-(n/2:ℝ)):ℝ):ℂ)*Complex.exp (Complex.I*Λ)*
          ∑ h ∈ Finset.range (J-j+1), (Λ:ℂ)^(-(h:ℤ))*sphereLND n h (sphereCutoffBND b j) (WithLp.toLp 2 (0,(1:ℝ))))) =
      ((Λ^(-(n:ℝ)/2):ℝ):ℂ)*Complex.exp (Complex.I*Λ)*b.1 (WithLp.toLp 2 (0,(1:ℝ))) := by
    rw [show -(n/2:ℝ)=-(n:ℝ)/2 by ring]
    calc
      _ = (((Λ^(-(n:ℝ)/2):ℝ):ℂ)*Complex.exp (Complex.I*Λ)) *
          (∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ)) *
            ∑ h ∈ Finset.range (J-j+1), (Λ:ℂ)^(-(h:ℤ)) *
              sphereLND n h (sphereCutoffBND b j) (WithLp.toLp 2 (0,(1:ℝ)))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hs]
  simp only [northRemainderND,mul_sub,Finset.sum_sub_distrib,mul_sub]
  rw [hs']
  have hc := sphere_half_cancelND hΛ n
  linear_combination congrArg (fun z : ℂ => z*Complex.exp (Complex.I*Λ)*b.1 (WithLp.toLp 2 (0,(1:ℝ)))) hc

theorem sphere_inverse_cutoff_remainderND (J : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : SmoothFunctionND (SphereAmbientND n)) (A Λ : ℝ),
      1 ≤ A → 0 < Λ →
      (∀ k ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ k b.1 w‖ ≤ C*A^k) →
      ‖((Λ^((n:ℝ)/2):ℝ):ℂ) *
          (∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ)) *
            sphereAxisIntegralND Λ (WithLp.toLp 2 (0,(1:ℝ))) (sphereCutoffBND b j)) -
        Complex.exp (Complex.I*Λ)*b.1 (WithLp.toLp 2 (0,(1:ℝ)))‖ ≤
      D*Λ^(-((J+1:ℕ):ℝ))*A^(2*(J+1)+n+3) := by
  have hbound (j : ℕ) := sphereCutoffBND_bound (n := n) j (2*(J-j+1)+n+3) C hC
  choose B hB hBb using hbound
  have hstationary (j : ℕ) := northAmplitude_stationary_shiftND (n := n) (B j) (hB j) (J-j)
  choose D hD hDb using hstationary
  refine ⟨∑ j ∈ Finset.range (J+1), D j,Finset.sum_nonneg (fun j _ => hD j),?_⟩
  intro b A Λ hA hΛ hb
  rw [sphere_inverse_cutoff_errorND J hΛ b,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hΛ _)]
  calc
    _ ≤ Λ^((n:ℝ)/2) * ∑ j ∈ Finset.range (J+1),
        ‖(Λ:ℂ)^(-(j:ℤ)) * northRemainderND (J-j) Λ (sphereCutoffBND b j)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.rpow_nonneg hΛ.le _)
    _ = ∑ j ∈ Finset.range (J+1), Λ^((n:ℝ)/2) *
        (‖(Λ:ℂ)^(-(j:ℤ))‖ * ‖northRemainderND (J-j) Λ (sphereCutoffBND b j)‖) := by
      rw [Finset.mul_sum]
      simp only [norm_mul]
    _ ≤ ∑ j ∈ Finset.range (J+1), D j*Λ^(-((J+1:ℕ):ℝ))*A^(2*(J+1)+n+3) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j ≤ J := by have := Finset.mem_range.mp hj; omega
      have hexp : 2*(J-j+1)+n+3+2*j=2*(J+1)+n+3 := by omega
      have hh := hDb j (sphereCutoffBND b j) A Λ (2*j) hA hΛ
        (hBb j b A hA (fun k hk w hw => hb k (by omega) w hw))
      have hm := mul_le_mul_of_nonneg_left hh
        (mul_nonneg (Real.rpow_nonneg hΛ.le ((n:ℝ)/2)) (norm_nonneg ((Λ:ℂ)^(-(j:ℤ)))))
      calc
        _ ≤ (Λ^((n:ℝ)/2)*‖(Λ:ℂ)^(-(j:ℤ))‖) *
            (D j*Λ^(-(n:ℝ)/2-((J-j+1:ℕ):ℝ))*A^(2*(J-j+1)+n+3+2*j)) := by
          simpa only [mul_assoc] using hm
        _ = D j*(Λ^((n:ℝ)/2)*‖(Λ:ℂ)^(-(j:ℤ))‖*Λ^(-(n:ℝ)/2-((J-j+1:ℕ):ℝ))) *
            A^(2*(J+1)+n+3) := by rw [hexp]; ring
        _ = _ := by rw [inverse_stationary_weightND n J j hj' hΛ]
    _ = _ := by rw [← Finset.sum_mul,← Finset.sum_mul]

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
open Set Metric MeasureTheory
open scoped ContDiff RealInnerProductSpace
variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype ι]

noncomputable def SmoothFunctionND.compIsometry (b : SmoothFunctionND V) (Q : V ≃ₗᵢ[ℝ] V) :
    SmoothFunctionND V := ⟨b.1 ∘ Q,(show ContDiff ℝ ∞ b.1 from b.2).comp
      Q.toContinuousLinearEquiv.contDiff⟩

lemma casimirOperatorND_pow_comp_isometry [FiniteDimensional ℝ V] (B : OrthonormalBasis ι ℝ V)
    (Q : V ≃ₗᵢ[ℝ] V) (k : ℕ) (b : SmoothFunctionND V) :
    (((casimirOperatorND B)^k) (b.compIsometry Q)).1 = (((casimirOperatorND B)^k) b).1 ∘ Q := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ',Module.End.mul_apply,Module.End.mul_apply]
    change sphereCasimirND B (((casimirOperatorND B)^k) (b.compIsometry Q)).1 =
      (sphereCasimirND B (((casimirOperatorND B)^k) b).1) ∘ Q
    rw [ih,sphereCasimirND_comp_isometry B Q ((((casimirOperatorND B)^k) b).2)]

lemma differentialPolynomialND_comp_isometry [FiniteDimensional ℝ V] (B : OrthonormalBasis ι ℝ V)
    (Q : V ≃ₗᵢ[ℝ] V) (p : Polynomial ℂ) (b : SmoothFunctionND V) :
    (differentialPolynomialND B p (b.compIsometry Q)).1 = (differentialPolynomialND B p b).1 ∘ Q := by
  rw [differentialPolynomialND_sum,differentialPolynomialND_sum]
  funext w
  simp only [casimirOperatorND_pow_comp_isometry,Function.comp_apply]

noncomputable def sphereAxisCutoffND (e w : V) : ℂ :=
  Real.smoothTransition (inner ℝ w e + 1/2)

lemma sphereAxisCutoffND_rotate (Q : V ≃ₗᵢ[ℝ] V) (e w : V) :
    sphereAxisCutoffND (Q e) (Q w) = sphereAxisCutoffND e w := by
  simp only [sphereAxisCutoffND,Q.inner_map_map]

lemma sphereAxisCutoffND_contDiff (e : V) : ContDiff ℝ ∞ (sphereAxisCutoffND e) :=
  Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
    ((contDiff_id.inner ℝ contDiff_const).add contDiff_const))

lemma sphereAxisCutoffND_zero (e w : V) (hw : inner ℝ w e ≤ -(1/2:ℝ)) :
    sphereAxisCutoffND e w = 0 := by
  rw [sphereAxisCutoffND,Real.smoothTransition.zero_of_nonpos (by linarith),Complex.ofReal_zero]

lemma sphereAxisCutoffND_one (e w : V) (hw : (1/2:ℝ) ≤ inner ℝ w e) :
    sphereAxisCutoffND e w = 1 := by
  rw [sphereAxisCutoffND,Real.smoothTransition.one_of_one_le (by linarith),Complex.ofReal_one]

variable {n : ℕ}

lemma sphereAxisCutoffND_north (w : SphereAmbientND n) :
    sphereAxisCutoffND (WithLp.toLp 2 (0,(1:ℝ))) w = sphereNorthCutoffND w := by
  simp [sphereAxisCutoffND,sphereNorthCutoffND,WithLp.prod_inner_apply]

lemma sphereBND_comp_isometry (Q : SphereAmbientND n ≃ₗᵢ[ℝ] SphereAmbientND n)
    (j : ℕ) (b : SmoothFunctionND (SphereAmbientND n)) :
    (sphereBND j (b.compIsometry Q)).1 = (sphereBND j b).1 ∘ Q :=
  differentialPolynomialND_comp_isometry _ Q _ b

noncomputable def sphereCutoffBAtND (e : SphereAmbientND n)
    (b : SmoothFunctionND (SphereAmbientND n)) (j : ℕ) (w : SphereAmbientND n) : ℂ :=
  sphereAxisCutoffND e w * (sphereBND j b).1 w

lemma sphereCutoffBAtND_rotate (Q : SphereAmbientND n ≃ₗᵢ[ℝ] SphereAmbientND n)
    (j : ℕ) (b : SmoothFunctionND (SphereAmbientND n)) :
    sphereCutoffBAtND (Q (WithLp.toLp 2 (0,(1:ℝ)))) b j ∘ Q =
      (sphereCutoffBND (b.compIsometry Q) j).toFun := by
  funext w
  simp only [Function.comp_apply,sphereCutoffBAtND,sphereAxisCutoffND_rotate,
    sphereAxisCutoffND_north,sphereCutoffBND,northPartAmplitudeND,sphereNorthPartND,
    sphereBND_comp_isometry]

lemma sphereCutoffBAtND_support (e : SphereAmbientND n)
    (b : SmoothFunctionND (SphereAmbientND n)) (j : ℕ) :
    tsupport (sphereCutoffBAtND e b j) ⊆ tsupport b.1 :=
  (tsupport_mul_subset_right (f := sphereAxisCutoffND e) (g := (sphereBND j b).1)).trans
    (sphereBND_support j b)

theorem sphere_inverse_rotatedND (J : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : SmoothFunctionND (SphereAmbientND n)) (A Λ : ℝ)
      (e : SphereAmbientND n), 1 ≤ A → 0 < Λ → ‖e‖=1 →
      (∀ k ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ k b.1 w‖ ≤ C*A^k) →
      ‖((Λ^((n:ℝ)/2):ℝ):ℂ) *
          (∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ)) *
            sphereAxisIntegralND Λ e (sphereCutoffBAtND e b j)) -
        Complex.exp (Complex.I*Λ)*b.1 e‖ ≤
      D*Λ^(-((J+1:ℕ):ℝ))*A^(2*(J+1)+n+3) := by
  obtain ⟨D,hD,hDb⟩ := sphere_inverse_cutoff_remainderND (n := n) J C hC
  refine ⟨D,hD,?_⟩
  intro b A Λ e hA hΛ he hb
  let Q := sphereAxisReflectionND (WithLp.toLp 2 (0,(1:ℝ))) e
  have hQ : Q (WithLp.toLp 2 (0,(1:ℝ))) = e :=
    sphereAxisReflectionND_apply (sphere_north_normND.trans he.symm)
  have hh := hDb (b.compIsometry Q) A Λ hA hΛ (by
    intro k hk w hw
    change ‖iteratedFDeriv ℝ k (b.1 ∘ Q) w‖ ≤ _
    rw [Q.norm_iteratedFDeriv_comp_right]
    exact hb k hk (Q w) (by simpa using hw))
  have hi (j : ℕ) : sphereAxisIntegralND Λ e (sphereCutoffBAtND e b j) =
      sphereAxisIntegralND Λ (WithLp.toLp 2 (0,(1:ℝ))) (sphereCutoffBND (b.compIsometry Q) j) := by
    rw [← hQ,sphereAxisIntegralND_rotate,sphereCutoffBAtND_rotate]
  simp only [hi]
  simpa only [SmoothFunctionND.compIsometry,Function.comp_apply,hQ] using hh

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
