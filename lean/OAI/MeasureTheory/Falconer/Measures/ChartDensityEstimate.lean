import OAI.MeasureTheory.Falconer.Geometry.ChartNonstationary
import OAI.MeasureTheory.Falconer.Angular.InverseStationaryCutoff

namespace OAI

/-!
# Nonstationary chart integration with the surface density

The surface Jacobian is included in the differentiated amplitude. Its
derivatives are bounded on the fixed chart, uniformly in the remaining
coordinate parameters.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem density_tangent_chart_nonstationary (d n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (w y t v : E) (f : ℝ → ℂ),
      ‖w‖ = 1 → ‖t‖ = 1 → inner ℝ w y = 0 → inner ℝ w t = 0 →
      inner ℝ y t = 0 → ‖y‖ ≤ 1 → ContDiff ℝ ∞ f →
      ∀ (C D Λ τ : ℝ), 0 ≤ C → 1 ≤ D → 0 < Λ → 0 < τ →
      ‖v‖ ≤ τ*D → tsupport f ⊆ Icc (-1 : ℝ) 1 →
      (∀ u ∈ tsupport f,
        τ ≤ |deriv (fun x => inner ℝ (normalizedLine (w+y) t x) v) u|) →
      (∀ k ≤ n, ∀ u ∈ tsupport f, ‖iteratedDeriv k f u‖ ≤ C*D^k) →
      ‖∫ u, phaseOscillator (fun x => inner ℝ (normalizedLine (w+y) t x) v) Λ u *
        ((chartDensityKernel d (‖y‖,u) : ℂ) * f u)‖ ≤ A*C*(D/(Λ*τ))^n := by
  choose P hP hPb using chartDensityKernel_derivatives d
  let Q := ∑ k ∈ Finset.range (n+1), P k
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun k _ => hP k)
  have hPQ (k : ℕ) (hk : k ≤ n) : P k ≤ Q :=
    Finset.single_le_sum (fun i _ => hP i) (Finset.mem_range.mpr (by omega))
  obtain ⟨A,hA,he⟩ := tangent_chart_nonstationary (E := E) n
  refine ⟨A * 2^n * Q,by positivity,?_⟩
  intro w y t v f hw ht hwy hwt hyt hy hf C D Λ τ hC hD hΛ hτ hv hs hl hb
  let g : ℝ → ℂ := fun u => (chartDensityKernel d (‖y‖,u) : ℂ)
  have hg₀ : ContDiff ℝ ∞ (fun u => chartDensityKernel d (‖y‖,u)) :=
    (chartDensityKernel_smooth d).comp (contDiff_const.prodMk contDiff_id)
  have hg : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp hg₀
  have hsub : tsupport (fun u => g u * f u) ⊆ tsupport f := tsupport_mul_subset_right
  have hgb (k : ℕ) (hk : k ≤ n) (u : ℝ) (hu : u ∈ tsupport f) :
      ‖iteratedDeriv k g u‖ ≤ Q * D^k := by
    change ‖iteratedDeriv k (fun u => (chartDensityKernel d (‖y‖,u) : ℂ)) u‖ ≤ _
    rw [PlanarFalconer.iteratedDeriv_ofReal hg₀,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ P k := hPb k _ ⟨by linarith [norm_nonneg y],hy⟩ _ (hs hu)
      _ ≤ Q := hPQ k hk
      _ ≤ Q * D^k := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (one_le_pow₀ hD) hQ
  have hfb (k : ℕ) (hk : k ≤ n) (u : ℝ) (hu : u ∈ tsupport (fun u => g u*f u)) :
      ‖iteratedDeriv k (fun u => g u * f u) u‖ ≤ (2^n*Q*C)*D^k := by
    have hh := PlanarFalconer.complex_product_derivative_bound hg hf hQ hC
      (zero_le_one.trans hD) k u
      (fun j hj => hgb j (hj.trans hk) u (hsub hu))
      (fun j hj => hb j (hj.trans hk) u (hsub hu))
    apply hh.trans
    gcongr
    norm_num
  have hh := he w y t v (fun u => g u*f u) hw ht hwy hwt hyt hy (hg.mul hf)
    (2^n*Q*C) D Λ τ (by positivity) hD hΛ hτ hv (hsub.trans hs)
    (fun u hu => hl u (hsub hu)) hfb
  convert hh using 1; ring

end Falconer

end OAI
