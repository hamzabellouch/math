import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Estimates.CasimirOperatorPowBound2
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereLPolynomial
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereShift2

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

noncomputable def sphereLPolynomialND (n j : ℕ) : Polynomial ℂ :=
  stationaryLPolynomialND (sphereLeadingND n) (sphereShiftND n) j

noncomputable def sphereBPolynomialND (n j : ℕ) : Polynomial ℂ :=
  stationaryInversePolynomialND (sphereLPolynomialND n) (sphereLeadingND n)
    (sphereLeadingND_ne_zero n) j

noncomputable def sphereBND (j : ℕ) (b : SmoothFunctionND (SphereAmbientND n)) :
    SmoothFunctionND (SphereAmbientND n) :=
  differentialPolynomialND (sphereBasisND n) (sphereBPolynomialND n j) b

lemma sphereLPolynomialND_zero (n : ℕ) :
    sphereLPolynomialND n 0 = Polynomial.C (sphereLeadingND n) := stationaryLPolynomialND_zero ..

lemma sphereBPolynomialND_degree (n j : ℕ) : (sphereBPolynomialND n j).natDegree ≤ j :=
  stationaryInversePolynomialND_degree _ _ _ (sphereLPolynomialND_zero n)
    (stationaryLPolynomialND_degree _ _) j

lemma sphereLND_eq_polynomial (j : ℕ) (b : SmoothFunctionND (SphereAmbientND n)) :
    sphereLND n j b.1 = (differentialPolynomialND (sphereBasisND n) (sphereLPolynomialND n j) b).1 := by
  rw [sphereLPolynomialND,differentialPolynomialND_L]
  funext w
  simp only [sphereLND,sphereJetPolynomialND_eq]

lemma sphereBND_zero (b : SmoothFunctionND (SphereAmbientND n)) :
    (sphereBND 0 b).1 = fun w => (sphereLeadingND n)⁻¹ * b.1 w := by
  simp only [sphereBND,sphereBPolynomialND,stationaryInversePolynomialND_zero,differentialPolynomialND_C]
  rfl

lemma sphereBND_support (j : ℕ) (b : SmoothFunctionND (SphereAmbientND n)) :
    tsupport (sphereBND j b).1 ⊆ tsupport b.1 := differentialPolynomialND_support ..

noncomputable def NorthAmplitudeND.inverse (b : NorthAmplitudeND n) (j : ℕ) : NorthAmplitudeND n where
  toFun := (sphereBND j ⟨b.toFun,b.smooth⟩).1
  smooth := (sphereBND j ⟨b.toFun,b.smooth⟩).2
  support := (sphereBND_support j ⟨b.toFun,b.smooth⟩).trans b.support

lemma sphereBND_bound (j m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : SmoothFunctionND (SphereAmbientND n)) (A : ℝ), 1 ≤ A →
      (∀ k ≤ m+2*j, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ k b.1 w‖ ≤ C*A^k) →
      ∀ k ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ k (sphereBND j b).1 w‖ ≤ D*A^(k+2*j) := by
  obtain ⟨D,hD,hDb⟩ := differentialPolynomialND_bound (sphereBasisND n) (sphereBPolynomialND n j)
    j (sphereBPolynomialND_degree n j) m C hC
  refine ⟨D,hD,?_⟩
  intro b A hA hb
  simpa only [sphereBND,Nat.add_zero,Nat.zero_add] using hDb b A 0 hA (by simpa only [Nat.add_zero] using hb)

lemma sphere_inverse_cancellationND (k : ℕ) (b : SmoothFunctionND (SphereAmbientND n))
    (w : SphereAmbientND n) :
    (∑ h ∈ Finset.range (k+1), sphereLND n h (sphereBND (k-h) b).1 w) =
      if k=0 then b.1 w else 0 := by
  have he := differentialPolynomialND_inverse_convolution (sphereBasisND n) (sphereLPolynomialND n)
    (sphereLeadingND n) (sphereLeadingND_ne_zero n) (sphereLPolynomialND_zero n) k b
  have hh := congrArg (fun f : SmoothFunctionND (SphereAmbientND n) => f.1 w) he
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hh
  by_cases hk : k=0 <;>
    simpa [Submodule.coe_sum,Finset.sum_apply,sphereLND_eq_polynomial,sphereBND,
      sphereBPolynomialND,hk,Nat.succ_eq_add_one] using hh

lemma sphere_inverse_cancellation_reverseND (k : ℕ) (b : SmoothFunctionND (SphereAmbientND n))
    (w : SphereAmbientND n) :
    (∑ j ∈ Finset.range (k+1), sphereLND n (k-j) (sphereBND j b).1 w) =
      if k=0 then b.1 w else 0 := by
  rw [← sphere_inverse_cancellationND k b w,
    ← Finset.sum_range_reflect (fun h => sphereLND n h (sphereBND (k-h) b).1 w) (k+1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ k := by have := Finset.mem_range.mp hj; omega
  simp [Nat.sub_sub_self hj']

lemma sphere_inverse_triangleND (N : ℕ) (z : ℂ) (b : SmoothFunctionND (SphereAmbientND n))
    (w : SphereAmbientND n) :
    (∑ j ∈ Finset.range (N+1), ∑ h ∈ Finset.range (N+1-j),
      z^(j+h) * sphereLND n h (sphereBND j b).1 w) = b.1 w := by
  rw [← Finset.sum_range_diag_flip]
  have he : ∀ k ∈ Finset.range (N+1),
      (∑ j ∈ Finset.range (k+1), z^(j+(k-j))*sphereLND n (k-j) (sphereBND j b).1 w) =
        z^k*(if k=0 then b.1 w else 0) := by
    intro k _
    rw [← sphere_inverse_cancellation_reverseND k b w,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ k := by have := Finset.mem_range.mp hj; omega
    rw [Nat.add_sub_of_le hj']
  rw [Finset.sum_congr rfl he]
  simp

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
open scoped ContDiff
variable {n : ℕ}

lemma sphere_inverse_seriesND (J : ℕ) (Λ : ℝ) (b : NorthAmplitudeND n) :
    (∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ)) *
      ∑ h ∈ Finset.range (J-j+1), (Λ:ℂ)^(-(h:ℤ)) *
        sphereLND n h (b.inverse j) (WithLp.toLp 2 (0,(1:ℝ)))) = b (WithLp.toLp 2 (0,(1:ℝ))) := by
  refine Eq.trans ?_ (sphere_inverse_triangleND J ((Λ:ℂ)⁻¹) ⟨b.toFun,b.smooth⟩ (WithLp.toLp 2 (0,(1:ℝ))))
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ J := by have := Finset.mem_range.mp hj; omega
  rw [Finset.mul_sum,show J-j+1=J+1-j by omega]
  apply Finset.sum_congr rfl
  intro h _
  simp only [zpow_neg,zpow_natCast,inv_pow,pow_add,NorthAmplitudeND.inverse]
  ring

lemma sphere_half_cancelND {Λ : ℝ} (hΛ : 0 < Λ) (n : ℕ) :
    ((Λ^((n:ℝ)/2):ℝ):ℂ)*((Λ^(-(n:ℝ)/2):ℝ):ℂ) = 1 := by
  rw [← Complex.ofReal_mul,← Real.rpow_add hΛ,show (n:ℝ)/2+ -(n:ℝ)/2=0 by ring]
  simp

lemma sphere_inverse_errorND (J : ℕ) {Λ : ℝ} (hΛ : 0 < Λ) (b : NorthAmplitudeND n) :
    ((Λ^((n:ℝ)/2):ℝ):ℂ) *
        (∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ)) *
          sphereAxisIntegralND Λ (WithLp.toLp 2 (0,(1:ℝ))) (b.inverse j)) -
      Complex.exp (Complex.I*Λ)*b (WithLp.toLp 2 (0,(1:ℝ))) =
    ((Λ^((n:ℝ)/2):ℝ):ℂ) *
      (∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ)) * northRemainderND (J-j) Λ (b.inverse j)) := by
  have hs := sphere_inverse_seriesND J Λ b
  have hs' :
      (∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ)) *
        (((Λ^(-(n/2:ℝ)):ℝ):ℂ)*Complex.exp (Complex.I*Λ)*
          ∑ h ∈ Finset.range (J-j+1), (Λ:ℂ)^(-(h:ℤ))*sphereLND n h (b.inverse j) (WithLp.toLp 2 (0,(1:ℝ))))) =
      ((Λ^(-(n:ℝ)/2):ℝ):ℂ)*Complex.exp (Complex.I*Λ)*b (WithLp.toLp 2 (0,(1:ℝ))) := by
    rw [show -(n/2:ℝ)=-(n:ℝ)/2 by ring]
    calc
      _ = (((Λ^(-(n:ℝ)/2):ℝ):ℂ)*Complex.exp (Complex.I*Λ)) *
          (∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ)) *
            ∑ h ∈ Finset.range (J-j+1), (Λ:ℂ)^(-(h:ℤ)) *
              sphereLND n h (b.inverse j) (WithLp.toLp 2 (0,(1:ℝ)))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hs]
  simp only [northRemainderND,mul_sub,Finset.sum_sub_distrib,mul_sub]
  rw [hs']
  have hc := sphere_half_cancelND hΛ n
  linear_combination congrArg (fun z : ℂ => z*Complex.exp (Complex.I*Λ)*b (WithLp.toLp 2 (0,(1:ℝ)))) hc

lemma inverse_stationary_weightND (n J j : ℕ) (hj : j ≤ J) {Λ : ℝ} (hΛ : 0 < Λ) :
    Λ^((n:ℝ)/2) * ‖(Λ:ℂ)^(-(j:ℤ))‖ * Λ^(-(n:ℝ)/2-((J-j+1:ℕ):ℝ)) =
      Λ^(-((J+1:ℕ):ℝ)) := by
  have hz : ‖(Λ:ℂ)^(-(j:ℤ))‖ = Λ^(-(j:ℝ)) := by
    rw [norm_zpow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hΛ,← Real.rpow_intCast]
    congr 1
    simp
  rw [hz,← Real.rpow_add hΛ,← Real.rpow_add hΛ]
  congr 1
  rw [Nat.cast_add,Nat.cast_sub hj,Nat.cast_add]
  ring

theorem sphere_inverse_remainderND (J : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : NorthAmplitudeND n) (A Λ : ℝ),
      1 ≤ A → 0 < Λ →
      (∀ k ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ k b w‖ ≤ C*A^k) →
      ‖((Λ^((n:ℝ)/2):ℝ):ℂ) *
          (∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ)) *
            sphereAxisIntegralND Λ (WithLp.toLp 2 (0,(1:ℝ))) (b.inverse j)) -
        Complex.exp (Complex.I*Λ)*b (WithLp.toLp 2 (0,(1:ℝ)))‖ ≤
      D*Λ^(-((J+1:ℕ):ℝ))*A^(2*(J+1)+n+3) := by
  have hbound (j : ℕ) := sphereBND_bound (n := n) j (2*(J-j+1)+n+3) C hC
  choose B hB hBb using hbound
  have hstationary (j : ℕ) := northAmplitude_stationary_shiftND (n := n) (B j) (hB j) (J-j)
  choose D hD hDb using hstationary
  refine ⟨∑ j ∈ Finset.range (J+1), D j,Finset.sum_nonneg (fun j _ => hD j),?_⟩
  intro b A Λ hA hΛ hb
  rw [sphere_inverse_errorND J hΛ b,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hΛ _)]
  calc
    _ ≤ Λ^((n:ℝ)/2) * ∑ j ∈ Finset.range (J+1),
        ‖(Λ:ℂ)^(-(j:ℤ)) * northRemainderND (J-j) Λ (b.inverse j)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.rpow_nonneg hΛ.le _)
    _ = ∑ j ∈ Finset.range (J+1), Λ^((n:ℝ)/2) *
        (‖(Λ:ℂ)^(-(j:ℤ))‖ * ‖northRemainderND (J-j) Λ (b.inverse j)‖) := by
      rw [Finset.mul_sum]
      simp only [norm_mul]
    _ ≤ ∑ j ∈ Finset.range (J+1), D j*Λ^(-((J+1:ℕ):ℝ))*A^(2*(J+1)+n+3) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j ≤ J := by have := Finset.mem_range.mp hj; omega
      have hexp : 2*(J-j+1)+n+3+2*j=2*(J+1)+n+3 := by omega
      have hh := hDb j (b.inverse j) A Λ (2*j) hA hΛ
        (hBb j ⟨b.toFun,b.smooth⟩ A hA (fun k hk w hw => hb k (by omega) w hw))
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

end OAI
