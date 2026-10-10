import Mathlib
import OAI.Geometry.SmoothYau.Spectrum.ProductFrequencyTop
import OAI.Geometry.SmoothYau.Estimates.EventualProductScalarCorrectionRate

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
  (A : CompactMetricAtlas g k hs)

theorem eventually_product_scalar_factor_raw
    (hd : Module.finrank ℝ E=3) (tests : List (CoordinateTest E M))
    (N P B D : ℕ) (hNP : N ≤ 2*(k+1))
    (hN : Module.finrank ℝ E < 2*(2*((k+1:ℕ):ℝ)-N))
    (hD : (P+8)+((2*B+21)*(2*(k+1)+2)+10)+2 ≤ D)
    {C : ℝ} (hC : 0 < C) (U W : ℕ → M → ℝ)
    (hU : ∀ n, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (U n))
    (hW : ∀ n x, 0 < W n x)
    (hdata : ∀ᶠ n : ℕ in atTop,
      (∀ x, W n x/(productWaveFrequency n)^B ≤ |U n x|+
        Real.sqrt (coordinateGradientPair g (U n) (U n) x)/(productWaveFrequency n)) ∧
      (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ 2*(k+1)+2,
        ‖iteratedFDeriv ℝ j (U n ∘ (chartAt E (A.p i)).symm) y‖ ≤
          C*(productWaveFrequency n)^(j+4)*W n ((chartAt E (A.p i)).symm y)) ∧
      (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ 2*(k+1)+1,
        ‖iteratedFDeriv ℝ j
          ((fun x => laplaceBeltrami g (U n) x+productFrequency n*U n x) ∘
            (chartAt E (A.p i)).symm) y‖ ≤
          C*(productWaveFrequency n)^4/(productWaveFrequency n)^D*W n ((chartAt E (A.p i)).symm y))) :
    ∃ L > 0, ∀ᶠ n : ℕ in atTop,
      let b := intrinsicCorrectionB g (productWaveFrequency n) (productFrequency n) (U n)
      let s := intrinsicCorrectionS g (productWaveFrequency n) (productFrequency n) (U n)
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b ∧ ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ s ∧
      (∀ x, 0 < b x ∧ 0 < s x) ∧
      (∀ x, weightedLaplacian g b (U n) x+productFrequency n*s x*U n x=0) ∧
      (tsupport (fun x => b x-1) ⊆
        tsupport (fun x => laplaceBeltrami g (U n) x+productFrequency n*U n x)) ∧
      (tsupport (fun x => s x-1) ⊆
        tsupport (fun x => laplaceBeltrami g (U n) x+productFrequency n*U n x)) ∧
      ∃ v : M → ℝ, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v ∧ (∀ x, 0 < v x) ∧
        (∀ x, weightedLaplacian g b v x =
          productFrequency n*b x^3*v x^5-productFrequency n*s x*v x) ∧
        (∀ x, |b x-1| ≤ L*inverseFrequency n^P ∧
          |s x-1| ≤ L*inverseFrequency n^P ∧ |v x-1| ≤ L*inverseFrequency n^P) ∧
        (∀ t ∈ tests, ∀ y ∈ t.compactSet, ∀ j ≤ N,
          ‖iteratedFDeriv ℝ j ((fun x => b x-1) ∘ (chartAt E t.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
          ‖iteratedFDeriv ℝ j ((fun x => s x-1) ∘ (chartAt E t.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
          ‖iteratedFDeriv ℝ j ((fun x => v x-1) ∘ (chartAt E t.center).symm) y‖ ≤ L*inverseFrequency n^P) := by
  classical
  let b := fun n : ℕ => intrinsicCorrectionB g (productWaveFrequency n) (productFrequency n) (U n)
  let s := fun n : ℕ => intrinsicCorrectionS g (productWaveFrequency n) (productFrequency n) (U n)
  let Coeff : ∀ i, A.PatchCoefficients i := fun i => (A.nonempty_patchCoefficients i).some
  have hscalar := A.eventually_product_scalar_exactification (2*(k+1)) B (P+8) D (by omega) hD
    hC U W hU hW hdata
  have hsm : ∀ᶠ n : ℕ in atTop,
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (b n) ∧ ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (s n) :=
    hscalar.mono (fun n hn => ⟨hn.1,hn.2.1⟩)
  have hj : ∀ᶠ n : ℕ in atTop,
      A.ChartJetBound (2*(k+1)) (fun x => ((b n x-1:ℝ):ℂ)) (inverseFrequency n^(P+8)) ∧
      A.ChartJetBound (2*(k+1)) (fun x => ((s n x-1:ℝ):ℂ)) (inverseFrequency n^(P+8)) :=
    hscalar.mono (fun n hn => ⟨hn.2.2.2.2.1,hn.2.2.2.2.2.1⟩)
  have hfactor := A.eventually_product_positive_factor_of_eventual_jets hd Coeff N P hN b s hsm hj
  obtain ⟨T,hT,hraw⟩ := A.chartJetBound_controls_finite_real_raw tests N
  let L := 1+T+(Fintype.card A.t:ℝ)
  have hL : 0 < L := by dsimp [L]; positivity
  have hTL : T ≤ L := by dsimp [L]; have := Nat.cast_nonneg (α := ℝ) (Fintype.card A.t); linarith
  have hcardL : (Fintype.card A.t:ℝ) ≤ L := by dsimp [L]; linarith
  refine ⟨L,hL,?_⟩
  filter_upwards [hscalar,hj,hfactor,eventually_ge_atTop 1] with n hsc hj hv hn1
  obtain ⟨v,hv,hvpos,hveq,hvj⟩ := hv
  have hni : 0 ≤ inverseFrequency n := inv_nonneg.mpr (Nat.cast_nonneg n)
  have hni1 : inverseFrequency n ≤ 1 := by
    unfold inverseFrequency
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hn1)
  have hpow : inverseFrequency n^(P+8) ≤ inverseFrequency n^P :=
    pow_le_pow_of_le_one hni hni1 (by omega)
  have hbj : A.ChartJetBound N (fun x => ((b n x-1:ℝ):ℂ)) (inverseFrequency n^P) :=
    fun i j hjN y => (hj.1 i j (hjN.trans hNP) y).trans hpow
  have hsj : A.ChartJetBound N (fun x => ((s n x-1:ℝ):ℂ)) (inverseFrequency n^P) :=
    fun i j hjN y => (hj.2 i j (hjN.trans hNP) y).trans hpow
  have hrawb := hraw (fun x => b n x-1) (hsc.1.sub contMDiff_const)
    _ (pow_nonneg hni _) hbj
  have hraws := hraw (fun x => s n x-1) (hsc.2.1.sub contMDiff_const)
    _ (pow_nonneg hni _) hsj
  have hrawv := hraw (fun x => v x-1) (hv.sub contMDiff_const)
    _ (pow_nonneg hni _) hvj
  refine ⟨hsc.1,hsc.2.1,hsc.2.2.1,hsc.2.2.2.1,
    hsc.2.2.2.2.2.2.2.1,hsc.2.2.2.2.2.2.2.2,v,hv,hvpos,hveq,?_,?_⟩
  · intro x
    have value {f : M → ℝ}
        (hf : A.ChartJetBound N (fun y => ((f y:ℝ):ℂ)) (inverseFrequency n^P)) :
        |f x| ≤ L*inverseFrequency n^P := by
      have hh := A.chartJetBound_global_value (pow_nonneg hni _) hf x
      simp only [Complex.norm_real,Real.norm_eq_abs] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right hcardL (pow_nonneg hni _))
    exact ⟨value hbj,value hsj,value hvj⟩
  · intro t ht y hy j hj
    have hbound := mul_le_mul_of_nonneg_right hTL (pow_nonneg hni P)
    exact ⟨(hrawb t ht y hy j hj).trans hbound,
      (hraws t ht y hy j hj).trans hbound,(hrawv t ht y hy j hj).trans hbound⟩
end CompactMetricAtlas
end YauCounterexamples
end

end OAI
