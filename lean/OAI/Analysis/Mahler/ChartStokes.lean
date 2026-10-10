import OAI.Analysis.Mahler.FormStokes
import OAI.Analysis.Mahler.DCForms
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

namespace OAI

noncomputable section
open Set MeasureTheory
namespace MahlerStokes

/-- Actual coefficient of an n-form in the oriented omitted-coordinate basis. -/
def orientedCoefficient {n : ℕ}
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (i : Fin (n+1)) (x : Fin (n+1) → ℝ) : ℝ :=
  (-1 : ℝ)^i.val * ω x (i.removeNth (coordinateBasis (n+1)))

lemma contDiff_orientedCoefficient {n : ℕ}
    {ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ}
    (hω : ContDiff ℝ 1 ω) (i : Fin (n+1)) : ContDiff ℝ 1 (orientedCoefficient ω i) := by
  have h := (((-1 : ℝ)^i.val • ContinuousAlternatingMap.apply ℝ _ ℝ
    (i.removeNth (coordinateBasis (n+1)))).contDiff.comp hω)
  change ContDiff ℝ 1 (fun x => (-1 : ℝ)^i.val * ω x (i.removeNth (coordinateBasis (n+1))))
  simpa only [Function.comp_def, smul_apply, smul_eq_mul, ContinuousAlternatingMap.apply_apply] using h

lemma extDeriv_eq_divergence {n : ℕ}
    {ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ}
    {x : Fin (n+1) → ℝ} (hω : DifferentiableAt ℝ ω x) :
    extDeriv ω x (coordinateBasis (n+1)) =
      ∑ i : Fin (n+1), fderiv ℝ (orientedCoefficient ω i) x (Pi.single i 1) := by
  rw [extDeriv_apply hω]
  apply Finset.sum_congr rfl
  intro i _
  have hd := (hω.continuousAlternatingMap_apply_const
    (i.removeNth (coordinateBasis (n+1)))).hasFDerivAt.const_mul ((-1 : ℝ)^i.val)
  change HasFDerivAt (orientedCoefficient ω i) _ x at hd
  rw [hd.fderiv]
  simp [coordinateBasis, zsmul_eq_mul]

/-- Coordinate Stokes on a box, for actual C1 differential forms. -/
theorem integral_extDeriv_box {n : ℕ} (a b : Fin (n+1) → ℝ) (hab : a ≤ b)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ 1 ω) :
    (∫ x in Icc a b, extDeriv ω x (coordinateBasis (n+1))) =
      ∑ i : Fin (n+1), (-1 : ℝ)^i.val *
        ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            ω (i.insertNth (b i) y) (i.removeNth (coordinateBasis (n+1)))) -
          ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            ω (i.insertNth (a i) y) (i.removeNth (coordinateBasis (n+1)))) := by
  have hc (i : Fin (n+1)) := contDiff_orientedCoefficient hω i
  have hd : Continuous (fun x => ∑ i : Fin (n+1),
      fderiv ℝ (orientedCoefficient ω i) x (Pi.single i 1)) := by
    apply continuous_finsetSum
    intro i _
    exact ((hc i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have he := integral_divergence_of_hasFDerivAt_off_countable' a b hab
    (orientedCoefficient ω) (fun i x => fderiv ℝ (orientedCoefficient ω i) x)
    ∅ countable_empty (fun i => (hc i).continuous.continuousOn)
    (fun x _ i => ((hc i).differentiable one_ne_zero x).hasFDerivAt)
    hd.continuousOn.integrableOn_Icc
  have hex (x : Fin (n+1) → ℝ) := extDeriv_eq_divergence (hω.differentiable one_ne_zero x)
  simp_rw [hex]
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  simp only [orientedCoefficient, integral_const_mul, mul_sub]

/-- Local boundary-chart Stokes after a cutoff kills all artificial faces.
Only the selected physical boundary face contributes. -/
theorem integral_extDeriv_box_one_face {n : ℕ} (a b : Fin (n+1) → ℝ) (hab : a ≤ b)
    (k : Fin (n+1))
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ 1 ω)
    (hback : ∀ i : Fin (n+1), ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      ω (i.insertNth (a i) y) (i.removeNth (coordinateBasis (n+1))) = 0)
    (hfront : ∀ i : Fin (n+1), i ≠ k → ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      ω (i.insertNth (b i) y) (i.removeNth (coordinateBasis (n+1))) = 0) :
    (∫ x in Icc a b, extDeriv ω x (coordinateBasis (n+1))) =
      (-1 : ℝ)^k.val * ∫ y in Icc (a ∘ k.succAbove) (b ∘ k.succAbove),
        ω (k.insertNth (b k) y) (k.removeNth (coordinateBasis (n+1))) := by
  have hb (i : Fin (n+1)) :
      (∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        ω (i.insertNth (a i) y) (i.removeNth (coordinateBasis (n+1)))) = 0 := by
    calc
      _ = ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), (0 : ℝ) :=
        setIntegral_congr_fun measurableSet_Icc (hback i)
      _ = 0 := by simp
  rw [integral_extDeriv_box a b hab ω hω]
  simp_rw [hb, sub_zero]
  apply Finset.sum_eq_single k
  · intro i _ hik
    have hi : (∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        ω (i.insertNth (b i) y) (i.removeNth (coordinateBasis (n+1)))) = 0 := by
      calc
        _ = ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), (0 : ℝ) :=
          setIntegral_congr_fun measurableSet_Icc (hfront i hik)
        _ = 0 := by simp
    rw [hi, mul_zero]
  · simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Stokes on a parametrized box. Every integrand is the actual pullback
along φ, including its derivative and orientation. This is the local chart
identity needed before assembling a compact regular sublevel. -/
theorem integral_pullback_extDeriv_box {n : ℕ} (a b : Fin (n+1) → ℝ) (hab : a ≤ b)
    (φ : (Fin (n+1) → ℝ) → E) (ω : E → E [⋀^Fin n]→L[ℝ] ℝ)
    (hφ : ContDiff ℝ 2 φ) (hω : Differentiable ℝ ω)
    (hpb : ContDiff ℝ 1 (pullbackForm φ ω)) :
    (∫ x in Icc a b,
      extDeriv ω (φ x) (fun i => fderiv ℝ φ x (coordinateBasis (n+1) i))) =
      ∑ i : Fin (n+1), (-1 : ℝ)^i.val *
        ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          pullbackForm φ ω (i.insertNth (b i) y) (i.removeNth (coordinateBasis (n+1)))) -
        ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          pullbackForm φ ω (i.insertNth (a i) y) (i.removeNth (coordinateBasis (n+1)))) := by
  have he (x : Fin (n+1) → ℝ) :
      extDeriv (pullbackForm φ ω) x =
        (extDeriv ω (φ x)).compContinuousLinearMap (fderiv ℝ φ x) :=
    extDeriv_pullback (hω (φ x)) (hφ.contDiffAt) (by simp)
  have h := integral_extDeriv_box a b hab (pullbackForm φ ω) hpb
  simpa only [he, ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def] using h

end MahlerStokes

end

end OAI
