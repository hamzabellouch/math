import OAI.NumberTheory.DirichletL.Descent.FullProfile
import OAI.NumberTheory.DirichletL.Descent.Canonical

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def secondNormProfile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 6 → ℝ → ℂ) (R : ℝ) (q : Fin 6 → ℝ) : ℂ :=
  (∏ i, V i (Real.log (q i))) * W₁ (q 0*q 2*q 4) * W₂ (q 0*q 2*q 5) *
    paperRadialFourier Φ (R*q 3/(q 1*(q 2)^2*q 4*q 5)) /
      ((q 1:ℂ)*(q 2:ℂ)*(Real.sqrt (q 4):ℂ)*(Real.sqrt (q 5):ℂ))

lemma secondPoissonProfile_log (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 6 → ℝ → ℂ) (R : ℝ) (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    secondPoissonProfile W₁ W₂ Φ V R (fun i => Real.log (q i)) =
      secondNormProfile W₁ W₂ Φ V R q := by
  have hleft : (∑ i, secondLeftSlope i * Real.log (q i)) =
      Real.log (q 0)+Real.log (q 2)+Real.log (q 4) := by
    simp [Fin.sum_univ_succ,secondLeftSlope]; ring
  have hright : (∑ i, secondRightSlope i * Real.log (q i)) =
      Real.log (q 0)+Real.log (q 2)+Real.log (q 5) := by
    simp [Fin.sum_univ_succ,secondRightSlope]; ring
  have hker : (∑ i, secondKernelSlope i * Real.log (q i)) =
      Real.log (q 3) - (Real.log (q 1)+Real.log (q 2)+Real.log (q 2)+Real.log (q 4)+Real.log (q 5)) := by
    simp [Fin.sum_univ_succ,secondKernelSlope]; ring
  unfold secondPoissonProfile secondNormProfile
  rw [hleft,hright,hker]
  simp only [Real.exp_add,Real.exp_sub,Real.exp_log (hq _)]
  have hk : R * (q 3/(q 1*q 2*q 2*q 4*q 5)) = R*q 3/(q 1*(q 2)^2*q 4*q 5) := by ring
  rw [hk]
  simp only [Fin.prod_univ_succ,secondRootWindows,inverseNormWindow,inverseRootWindow,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.isValue,Real.exp_log (hq _),Fin.prod_univ_zero,mul_one]
  simp only [Fin.succ,  Fin.val_mk]
  norm_num
  ring

theorem secondSourcePairKernel_profile {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0)
    (G V N M : Finset ι) (hVN : Disjoint V N) (hVM : Disjoint V M)
    (e k : Eis) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    (‖eisEmbedding e‖^2 : ℂ)⁻¹ * secondSourcePairKernel p e k
      (fun U => W₁ (primeProductNorm p G * primeProductNorm p U))
      (fun U => W₂ (primeProductNorm p G * primeProductNorm p U)) Φ Y (V ∪ N) (V ∪ M) =
    secondNormProfile (fun x => star (W₁ x)) W₂ Φ (fun _ _ => 1) Y
      ![primeProductNorm p G, ‖eisEmbedding e‖^2, primeProductNorm p V,
        ‖eisEmbedding k‖^2, primeProductNorm p N, primeProductNorm p M] := by
  have hs (S : Finset ι) : ‖eisEmbedding (∏ i ∈ S, p i)‖ = Real.sqrt (primeProductNorm p S) := by
    simp only [primeProductNorm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hV : 0 ≤ primeProductNorm p V := (primeProductNorm_pos p hp V).le
  have hroots : Real.sqrt (primeProductNorm p V*primeProductNorm p N) *
      Real.sqrt (primeProductNorm p V*primeProductNorm p M) =
      primeProductNorm p V * Real.sqrt (primeProductNorm p N) * Real.sqrt (primeProductNorm p M) := by
    rw [Real.sqrt_mul hV, Real.sqrt_mul hV]
    calc
      _ = (Real.sqrt (primeProductNorm p V))^2 * Real.sqrt (primeProductNorm p N) * Real.sqrt (primeProductNorm p M) := by ring
      _ = _ := by rw [Real.sq_sqrt hV]
  unfold secondSourcePairKernel secondNormProfile
  simp only [hs,primeProductNorm_union p V N hVN,primeProductNorm_union p V M hVM,
    Matrix.cons_val_zero,  Fin.isValue, Finset.prod_const_one, one_mul]
  have harg : Y * ‖eisEmbedding k‖^2 /
      (‖eisEmbedding e‖^2 * (primeProductNorm p V*primeProductNorm p N *
        (primeProductNorm p V*primeProductNorm p M))) =
      Y * ‖eisEmbedding k‖^2 / (‖eisEmbedding e‖^2 * (primeProductNorm p V)^2 *
        primeProductNorm p N * primeProductNorm p M) := by ring
  rw [harg]
  rw [← Complex.ofReal_mul, hroots]
  push_cast
  ring_nf

theorem secondNormProfile_nominal (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (G₀ E₀ V₀ K₀ X₀ Y : ℝ)
    (_hG : 0 < G₀) (hE : 0 < E₀) (hV : 0 < V₀) (hK : 0 < K₀) (hX : 0 < X₀)
    (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
      (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        secondNormProfile W₁ W₂ Φ (fun _ _ => 1)
          (Y*K₀/(E₀*V₀^2*X₀^2))
          ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] := by
  have hleft : (q 0/G₀)*(q 2/V₀)*(q 4/X₀) = q 0*q 2*q 4/(G₀*V₀*X₀) := by ring
  have hright : (q 0/G₀)*(q 2/V₀)*(q 5/X₀) = q 0*q 2*q 5/(G₀*V₀*X₀) := by ring
  have harg : (Y*K₀/(E₀*V₀^2*X₀^2))*(q 3/K₀)/
      ((q 1/E₀)*(q 2/V₀)^2*(q 4/X₀)*(q 5/X₀)) =
      Y*q 3/(q 1*(q 2)^2*q 4*q 5) := by
    field_simp
  have hroot : Real.sqrt (q 4/X₀)*Real.sqrt (q 5/X₀) =
      Real.sqrt (q 4)*Real.sqrt (q 5)/X₀ := by
    rw [Real.sqrt_div (hq 4).le,Real.sqrt_div (hq 5).le]
    rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hX.le]
  have hc0 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (0:Fin 6) = q 0/G₀ := rfl
  have hc1 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (1:Fin 6) = q 1/E₀ := rfl
  have hc2 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (2:Fin 6) = q 2/V₀ := rfl
  have hc3 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (3:Fin 6) = q 3/K₀ := rfl
  have hc4 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (4:Fin 6) = q 4/X₀ := rfl
  have hc5 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (5:Fin 6) = q 5/X₀ := rfl
  unfold secondNormProfile
  simp only [Finset.prod_const_one,one_mul,hc0,hc1,hc2,hc3,hc4,hc5]
  rw [hleft,hright,harg]
  have hrootC : (Real.sqrt (q 4/X₀):ℂ)*(Real.sqrt (q 5/X₀):ℂ) =
      (Real.sqrt (q 4):ℂ)*(Real.sqrt (q 5):ℂ)/(X₀:ℂ) := by exact_mod_cast hroot
  rw [show (↑(q 1/E₀):ℂ)*↑(q 2/V₀)*↑(Real.sqrt (q 4/X₀))*↑(Real.sqrt (q 5/X₀)) =
      (↑(q 1/E₀):ℂ)*↑(q 2/V₀)*(↑(Real.sqrt (q 4/X₀))*↑(Real.sqrt (q 5/X₀))) from by ring,
    hrootC]
  have hEc : (E₀:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hE.ne'
  have hVc : (V₀:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV.ne'
  have hXc : (X₀:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  push_cast
  field_simp [hEc,hVc,hXc]

end
end SevenEighths.InverseMoment

end OAI
