import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCriticalTransform
import OAI.NumberTheory.CubicMoment.Estimates.RamifiedIdealParts

namespace OAI

/-! Exact extraction of the common critical-line kernel from a finite
retained frequency sum. No common-majorant hypothesis is introduced. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem metaplectic_finite_transform_critical {ι : Type*} (S : Finset ι)
    (b : ι → ℂ) (q : ι → ℝ) (hq : ∀ i ∈ S, 0 < q i)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A))
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A))
    (t : ℝ) :
    (∑ i ∈ S, b i*metaplecticTransform ℓ (fun x => W x*mellinPhase t x) A (c*q i)) =
      (Real.sqrt c:ℂ)*((1/(2*Real.pi):ℝ):ℂ)*
        ∫ τ : ℝ, metaplecticCriticalKernel ℓ W c
          (fun u => ∑ i ∈ S, b i*(Real.sqrt (q i):ℂ)*mellinPhase u (q i)) τ t := by
  let F : ι → ℝ → ℂ := fun i τ => b i*(Real.sqrt (c*q i):ℂ)*
    metaplecticCriticalKernel ℓ W (c*q i) (fun _ => 1) τ t
  have hF (i : ι) (_hi : i ∈ S) : Integrable (F i) := by
    exact (metaplecticCriticalKernel_integrable ℓ W hW hpos hsm (c*q i)
      (P := fun _ => 1) continuous_const (B := 1) (by intro u; norm_num) t).const_mul _
  have ht (i : ι) (hi : i ∈ S) :
      b i*metaplecticTransform ℓ (fun x => W x*mellinPhase t x) A (c*q i) =
        ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ, F i τ := by
    rw [metaplecticTransform_critical ℓ W hW hpos hsm hA (mul_pos hc (hq i hi)) hm hp t]
    dsimp [F]
    rw [integral_const_mul]
    ring
  have hf (τ : ℝ) : (∑ i ∈ S, F i τ) =
      (Real.sqrt c:ℂ)*metaplecticCriticalKernel ℓ W c
        (fun u => ∑ i ∈ S, b i*(Real.sqrt (q i):ℂ)*mellinPhase u (q i)) τ t := by
    unfold metaplecticCriticalKernel
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [F,metaplecticCriticalKernel]
    rw [Real.sqrt_mul hc.le,Complex.ofReal_mul,
      mellinPhase_mul_pos (τ-t) hc (hq i hi)]
    ring
  calc
    _ = ∑ i ∈ S, ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ, F i τ :=
      Finset.sum_congr rfl ht
    _ = ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ, ∑ i ∈ S, F i τ := by
      rw [integral_finsetSum S hF,Finset.mul_sum]
    _ = _ := by simp_rw [hf]; rw [integral_const_mul]; ring

end CubicFirstMoment

end

end OAI
