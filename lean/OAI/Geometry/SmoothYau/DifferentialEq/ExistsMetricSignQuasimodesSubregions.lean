import Mathlib
import OAI.Geometry.SmoothYau.Estimates.FiniteSumTsupportSubset
import OAI.Geometry.SmoothYau.Estimates.QuarticReparameterization
import OAI.Geometry.SmoothYau.Limits.CompactActualWaveNoncancellation
import OAI.Geometry.SmoothYau.Limits.CompactActualWavesSubregionsSupported

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

lemma exp_profile_log_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} (hφ : Differentiable ℝ φ) {n H : ℝ} (hn : 0 ≤ n)
    (x : E) (hb : ‖fderiv ℝ φ x‖ ≤ H) :
    ‖fderiv ℝ (fun y => Real.exp (n*φ y)) x‖ ≤ H*n*Real.exp (n*φ x) := by
  rw [fderiv_exp ((hφ x).const_mul n),fderiv_const_mul (hφ x)]
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),abs_of_nonneg hn]
  calc
    _ ≤ Real.exp (n*φ x)*(n*H) := by gcongr
    _ = _ := by ring

lemma finiteWaveSuperposition_compact {E I : Type*} [TopologicalSpace E] [Fintype I]
    {U : I → Fin 3 → E → ℂ} (hU : ∀ i ℓ, HasCompactSupport (U i ℓ))
    (γ : I → Fin 3 → ℂ) : HasCompactSupport (finiteWaveSuperposition (fun _ => (0 : ℝ)) U γ) := by
  classical
  have h (i) (ℓ) : HasCompactSupport (fun x => (γ i ℓ*U i ℓ x).re) :=
    ((hU i ℓ).mul_left (f := fun _ => γ i ℓ)).comp_left (g := Complex.re) rfl
  have hs := HasCompactSupport.finset_sum (s := (Finset.univ : Finset I))
    (fun i _ => HasCompactSupport.finset_sum (s := (Finset.univ : Finset (Fin 3))) (fun ℓ _ => h i ℓ))
  have he : finiteWaveSuperposition (fun _ => (0 : ℝ)) U γ =
      ∑ i, ∑ ℓ, fun x => (γ i ℓ*U i ℓ x).re := by
    funext x
    simp only [finiteWaveSuperposition,zero_add,Finset.sum_apply]
  rw [he]
  exact hs

lemma norm_iteratedFDeriv_finiteWaveSum_uniform {E I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
    {U : I → Fin 3 → E → ℂ} (hU : ∀ i ℓ, ContDiff ℝ ∞ (U i ℓ))
    (γ : I → Fin 3 → ℂ) {n Q R : ℝ} (hn : 0 ≤ n) (hR : 0 ≤ R)
    (hcard : (Fintype.card I : ℝ) ≤ Q*n^3) (hγ : ∀ i ℓ, ‖γ i ℓ‖ ≤ n)
    (j : ℕ) (x : E) (hbound : ∀ i ℓ, ‖iteratedFDeriv ℝ j (U i ℓ) x‖ ≤ R) :
    ‖iteratedFDeriv ℝ j (fun y => ∑ i, ∑ ℓ, (γ i ℓ*U i ℓ y).re) x‖ ≤ 3*Q*n^4*R := by
  classical
  calc
    _ ≤ ∑ i, ∑ ℓ, ‖γ i ℓ‖*‖iteratedFDeriv ℝ j (U i ℓ) x‖ :=
      norm_iteratedFDeriv_finiteWaveSum hU γ j x
    _ ≤ ∑ _i : I, ∑ _ℓ : Fin 3, n*R := by
      apply Finset.sum_le_sum; intro i _
      exact Finset.sum_le_sum (fun ℓ _ => mul_le_mul (hγ i ℓ) (hbound i ℓ) (norm_nonneg _) hn)
    _ = (Fintype.card I : ℝ)*3*(n*R) := by simp; ring
    _ ≤ (Q*n^3)*3*(n*R) := by gcongr
    _ = _ := by ring

theorem exists_compact_metric_quasimodes
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    (hnc : ∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x)
    (hcrit : ∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v)
    (m D : ℕ) :
    ∃ C > 0, ∃ N : ℝ, 1 ≤ N ∧ ∀ n : ℝ, N ≤ n →
      ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
        (∀ x : NormalWaveSpace, ∀ j ≤ m,
          ‖iteratedFDeriv ℝ j u x‖ ≤ C*n^(j+4)*Real.exp (n*φ x) ∧
          ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami g u y + n*(n+2)*u y) x‖ ≤
            C*(n^(D+1))⁻¹*Real.exp (n*φ x)) ∧
        ∀ y ∈ normalWaveEquiv.symm '' K,
          1/n^110 ≤ ‖realWaveJet n (Real.exp (n*φ (normalWaveEquiv y)))
            (u ∘ normalWaveEquiv) y‖ := by
  classical
  let K' := normalWaveEquiv.symm '' K
  obtain ⟨B,hB,hBK⟩ := (hK.image normalWaveEquiv.symm.continuous).isBounded.exists_pos_norm_le
  let S : Set (Fin 3 → ℝ) := Metric.closedBall 0 B
  have hKS : K' ⊆ S := fun y hy => by simpa only [S,Metric.mem_closedBall,dist_zero_right] using hBK y hy
  have hφ' : ContDiff ℝ ∞ (φ ∘ normalWaveEquiv) := hφ.comp normalWaveEquiv.contDiff
  have hDφ := (hφ'.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ (∞ : ℕ∞ω) by simp)).continuous
  obtain ⟨H,hH,hDH⟩ := ((isCompact_closedBall (0 : Fin 3 → ℝ) B).image hDφ).isBounded.exists_pos_norm_le
  have hDbound (x) (hx : x ∈ S) : ‖fderiv ℝ (φ ∘ normalWaveEquiv) x‖ ≤ H :=
    hDH _ ⟨x,hx,rfl⟩
  obtain ⟨T,hT,A,hA,Q,hQ,N,hN,hdata⟩ := compact_actual_wave_noncancellation
    g φ hφ hK hnc hcrit m (D+4) 0 H (by norm_num) hH.le
  refine ⟨3*Q*T,by positivity,max N (A+1),le_max_of_le_left hN,?_⟩
  intro n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := hN.trans hnN
  have hn0 : 0 < n := zero_lt_one.trans_le hn1
  obtain ⟨t,p,U,ht,hU,hLaw⟩ := hdata n hnN
  let W : (Fin 3 → ℝ) → ℝ := fun y => Real.exp (n*φ (normalWaveEquiv y))
  have hW : Differentiable ℝ W := ((hφ'.differentiable (by simp)).const_mul n).exp
  have hgood := hLaw S (convex_closedBall _ _) K' hKS Subset.rfl 0 contDiff_const W hW
    (fun _ => Real.exp_pos _) (fun _ _ => le_rfl) (fun y _ => by dsimp [W]; nlinarith [pow_nonneg hn0.le 6,Real.exp_pos (n*φ (normalWaveEquiv y))])
    (fun y _ j _ => by simp [Function.comp_def,iteratedFDeriv_fun_zero])
    (fun y hy => exp_profile_log_derivative (hφ'.differentiable (by simp)) hn0.le y (hDbound y hy))
  let μ := Measure.pi (fun _ : t => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ))
  let Bad : Set (t → Fin 3 → ℂ) := {γ | (∃ i ℓ, n < ‖γ i ℓ‖) ∨ ∃ y ∈ K',
    ‖realWaveJet n (W y) (finiteWaveSuperposition ((fun _ : NormalWaveSpace => (0 : ℝ)) ∘ normalWaveEquiv)
      (fun i ℓ => U i ℓ ∘ normalWaveEquiv) γ) y‖ < 1/n^110}
  have hprob : μ Bad < 1 := by
    apply hgood.trans_lt
    apply ENNReal.ofReal_lt_one.mpr
    apply (div_lt_one (pow_pos hn0 5)).mpr
    have hAn : A < n := lt_of_lt_of_le (by linarith) ((le_max_right N (A+1)).trans hn)
    exact hAn.trans_le (by simpa only [pow_one] using pow_le_pow_right₀ hn1 (show 1 ≤ 5 by omega))
  obtain ⟨γ,hγ⟩ : ∃ γ, γ ∉ Bad := by
    by_contra h
    push Not at h
    have he : Bad = univ := Set.eq_univ_iff_forall.mpr h
    rw [he,measure_univ] at hprob
    exact (lt_irrefl (1 : ℝ≥0∞)) hprob
  have hcoef : ∀ i ℓ, ‖γ i ℓ‖ ≤ n := by
    intro i ℓ
    exact le_of_not_gt (fun hh => hγ (Or.inl ⟨i,ℓ,hh⟩))
  have hjet : ∀ y ∈ K', 1/n^110 ≤ ‖realWaveJet n (W y)
      (finiteWaveSuperposition ((fun _ : NormalWaveSpace => (0 : ℝ)) ∘ normalWaveEquiv) (fun i ℓ => U i ℓ ∘ normalWaveEquiv) γ) y‖ :=
    fun y hy => le_of_not_gt (fun hh => hγ (Or.inr ⟨y,hy,hh⟩))
  let u := finiteWaveSuperposition (fun _ => (0 : ℝ)) U γ
  have hu : ContDiff ℝ ∞ u := contDiff_finiteWaveSuperposition contDiff_const (fun i ℓ => (hU i ℓ).1) γ
  refine ⟨u,hu,finiteWaveSuperposition_compact (fun i ℓ => (hU i ℓ).2.1) γ,?_,?_⟩
  · intro x j hj
    have hcard : (Fintype.card t : ℝ) ≤ Q*n^3 := by simpa using ht
    have hj' : j ≤ max m 2 := hj.trans (le_max_left _ _)
    constructor
    · have hb := finiteWaveSum_derivative_bound (fun i ℓ => (hU i ℓ).1) γ hn0.le hT.le
        (Real.exp_pos _).le hcard hcoef j x (fun i ℓ => ((hU i ℓ).2.2.2 x j hj').1)
      have he : u = fun y => ∑ i, ∑ ℓ, (γ i ℓ*U i ℓ y).re := by
        funext y; exact zero_add _
      rw [he]
      exact hb
    · rw [finiteWaveSuperposition_residual g (fun i ℓ => (hU i ℓ).1) γ (n*(n+2))]
      let R : t → Fin 3 → NormalWaveSpace → ℂ := fun i ℓ y =>
        complexLaplaceBeltrami g (U i ℓ) y+(n : ℂ)*((n : ℂ)+2)*U i ℓ y
      have hR (i) (ℓ) : ContDiff ℝ ∞ (R i ℓ) :=
        (contDiff_complexLaplaceBeltrami_self g (hU i ℓ).1).add (contDiff_const.mul (hU i ℓ).1)
      have hb := norm_iteratedFDeriv_finiteWaveSum_uniform hR γ hn0.le
        (show 0 ≤ T*(n^((D+4)+1))⁻¹*Real.exp (n*φ x) by positivity)
        hcard hcoef j x (fun i ℓ => ((hU i ℓ).2.2.2 x j hj').2)
      simp only [Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_ofNat] at *
      apply hb.trans_eq
      simp only [show D+4+1 = (D+1)+4 by omega,pow_add]
      field_simp
  · intro y hy
    have he : u ∘ normalWaveEquiv = finiteWaveSuperposition ((fun _ : NormalWaveSpace => (0 : ℝ)) ∘ normalWaveEquiv)
        (fun i ℓ => U i ℓ ∘ normalWaveEquiv) γ := by
      funext x; rfl
    rw [he]
    exact hjet y hy

end


section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

theorem exists_metric_sign_quasimodes_supported
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ p₀ > 0,
    ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
    (∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x) →
    (∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v) →
    ∀ m D : ℕ, ∀ T₀ H : ℝ, 0 ≤ T₀ → 0 ≤ H → ∃ c₀ > 0, ∃ C > 0,
    ∃ N : ℝ, 1 ≤ N ∧ ∀ n : ℝ, N ≤ n →
      ∀ S : Set (Fin 3 → ℝ), Convex ℝ S →
        ∀ E : Set (Fin 3 → ℝ), E ⊆ S → E ⊆ normalWaveEquiv.symm '' K →
        ∀ w : NormalWaveSpace → ℝ, ContDiff ℝ ∞ w →
        ∀ W : (Fin 3 → ℝ) → ℝ, Differentiable ℝ W → (∀ y, 0 < W y) →
        (∀ y ∈ S, Real.exp (n*φ (normalWaveEquiv y)) ≤ W y) →
        (∀ y ∈ E, W y ≤ (1+n^6)*Real.exp (n*φ (normalWaveEquiv y))) →
        (∀ y ∈ S, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (w ∘ normalWaveEquiv) y‖ ≤ T₀*n^j*W y) →
        (∀ y ∈ S, ‖fderiv ℝ W y‖ ≤ H*n*W y) →
        (∀ y ∈ K, |w y| ≤ c₀*Real.exp (n*φ y)) →
        ∀ (P : Type) [Fintype P] (ℓ q : P → ℝ), (∀ a, 0 ≤ q a) →
        ∀ ν : P → Measure NormalWaveSpace, ∀ _ : ∀ a, IsFiniteMeasure (ν a),
        0 < ∑ a, q a*(ν a univ).toReal →
        (∀ a, ∀ᵐ x ∂ν a, x ∈ K ∧ profileFrequencyScale g φ x ≤ ℓ a ∧
          ℓ a ≤ 2*profileFrequencyScale g φ x ∧ (∀ j, packetAxisShift x n ε (ℓ a) j ∈ K)) →
        ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ tsupport u ⊆ O ∧
          (∀ x : NormalWaveSpace, ∀ j ≤ m,
            ‖iteratedFDeriv ℝ j u x‖ ≤ C*n^(j+4)*Real.exp (n*φ x) ∧
            ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami g u y+n*(n+2)*u y) x‖ ≤
              C*(n^(D+1))⁻¹*Real.exp (n*φ x)) ∧
          (∀ y ∈ E, 1/n^110 ≤ ‖realWaveJet n (W y) ((w+u) ∘ normalWaveEquiv) y‖) ∧
          (p₀/2)*(∑ a, q a*(ν a univ).toReal) <
            ∑ a, q a*∑ j : Fin 3, (ν a {x | (w+u) x *
              (w+u) (packetAxisShift x n ε (ℓ a) j) < 0}).toReal := by
  classical
  obtain ⟨ε,hε,hε1,p₀,hp₀,hdata⟩ := compact_actual_waves_regions_supported g hK hO hKO
  refine ⟨ε,hε,hε1,p₀,hp₀,?_⟩
  intro φ hφ hnc hcrit m D T₀ H hT₀ hH
  obtain ⟨c₀,hc₀,T,hT,c,hc,Q,hQ,N,hN,hdata⟩ := hdata φ hφ hnc hcrit m (D+4) T₀ H hT₀ hH
  have hN1 : 1 ≤ N := by linarith
  refine ⟨c₀,hc₀,3*Q*T,by positivity,N^4,one_le_pow₀ hN1,?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (one_le_pow₀ hN1 : 1 ≤ N^4).trans hn
  have hn0 : 0 < n := zero_lt_one.trans_le hn1
  obtain ⟨s,hs,hs4⟩ := quartic_reparameterization
    (fun x => ∃ s : ℝ, N ≤ s ∧ s^4 = x) hN1 (fun s hs => ⟨s,hs,rfl⟩) n hn
  have hh := hdata s hs
  dsimp only at hh
  rw [hs4] at hh
  obtain ⟨t,p,U,hSupport,ht,hU,hgood⟩ := hh
  intro S hS E hES hEK w hw W hW hW0 hWlower hWupper hwbound hlog hb P _ ℓ q hq ν hν hv hregion
  obtain ⟨γ,hcoef,hjet,hscore⟩ := hgood S hS E hES hEK w hw W hW hW0 hWlower hWupper
    hwbound hlog hb P ℓ q hq ν hν hv hregion
  let u := finiteWaveSuperposition (fun _ => (0 : ℝ)) U γ
  have hu : ContDiff ℝ ∞ u := contDiff_finiteWaveSuperposition contDiff_const (fun i j => (hU i j).1) γ
  have he : w+u = finiteWaveSuperposition w U γ := by
    funext x
    change w x + (0+_) = w x + _
    rw [zero_add]
  have he' : (w+u) ∘ normalWaveEquiv =
      finiteWaveSuperposition (w ∘ normalWaveEquiv) (fun i j => U i j ∘ normalWaveEquiv) γ := by
    rw [he]; rfl
  refine ⟨u,hu,finiteWaveSuperposition_compact (fun i j => (hU i j).2.1) γ,
    finiteWaveSuperposition_tsupport hSupport γ,?_,?_,?_⟩
  · intro x j hj
    have hcard : (Fintype.card t : ℝ) ≤ Q*n^3 := by simpa using ht
    have hj' : j ≤ max m 2 := hj.trans (le_max_left _ _)
    constructor
    · have hbound (i) (ℓ) : ‖iteratedFDeriv ℝ j (U i ℓ) x‖ ≤ T*n^j*Real.exp (n*φ x) := by
        apply ((hU i ℓ).2.2.2 x j hj').1.trans
        apply mul_le_of_le_one_right (by positivity)
        apply Real.exp_le_one_iff.mpr
        exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hn0.le) (sq_nonneg _)
      have hsum := finiteWaveSum_derivative_bound (fun i ℓ => (hU i ℓ).1) γ hn0.le hT.le
        (Real.exp_pos _).le hcard hcoef j x hbound
      have he₀ : u = fun y => ∑ i, ∑ ℓ, (γ i ℓ*U i ℓ y).re := by
        funext y; exact zero_add _
      rw [he₀]
      exact hsum
    · rw [finiteWaveSuperposition_residual g (fun i ℓ => (hU i ℓ).1) γ (n*(n+2))]
      let R : t → Fin 3 → NormalWaveSpace → ℂ := fun i ℓ y =>
        complexLaplaceBeltrami g (U i ℓ) y+(n : ℂ)*((n : ℂ)+2)*U i ℓ y
      have hR (i) (ℓ) : ContDiff ℝ ∞ (R i ℓ) :=
        (contDiff_complexLaplaceBeltrami_self g (hU i ℓ).1).add (contDiff_const.mul (hU i ℓ).1)
      have hb := norm_iteratedFDeriv_finiteWaveSum_uniform hR γ hn0.le
        (show 0 ≤ T*(n^((D+4)+1))⁻¹*Real.exp (n*φ x) by positivity)
        hcard hcoef j x (fun i ℓ => ((hU i ℓ).2.2.2 x j hj').2)
      simp only [Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_ofNat] at *
      apply hb.trans_eq
      simp only [show D+4+1 = (D+1)+4 by omega,pow_add]
      field_simp
  · rw [he']; exact hjet
  · rw [he]; exact hscore
end


open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

theorem exists_metric_sign_quasimodes_subregions_supported
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ p₀ > 0,
    ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
    (∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x) →
    (∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v) →
    ∀ m D : ℕ, ∀ T₀ H : ℝ, 0 ≤ T₀ → 0 ≤ H → ∃ c₀ > 0, ∃ C > 0,
    ∃ N : ℝ, 1 ≤ N ∧ ∀ n : ℝ, N ≤ n →
      ∀ S : Set (Fin 3 → ℝ), Convex ℝ S →
        ∀ E : Set (Fin 3 → ℝ), E ⊆ S → E ⊆ normalWaveEquiv.symm '' K →
        ∀ w : NormalWaveSpace → ℝ, ContDiff ℝ ∞ w →
        ∀ W : (Fin 3 → ℝ) → ℝ, Differentiable ℝ W → (∀ y, 0 < W y) →
        (∀ y ∈ S, Real.exp (n*φ (normalWaveEquiv y)) ≤ W y) →
        (∀ y ∈ E, W y ≤ (1+n^6)*Real.exp (n*φ (normalWaveEquiv y))) →
        (∀ y ∈ S, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (w ∘ normalWaveEquiv) y‖ ≤ T₀*n^j*W y) →
        (∀ y ∈ S, ‖fderiv ℝ W y‖ ≤ H*n*W y) →
        ∀ J : Set NormalWaveSpace, J ⊆ K →
        (∀ y ∈ J, |w y| ≤ c₀*Real.exp (n*φ y)) →
        ∀ (P : Type) [Fintype P] (ℓ q : P → ℝ), (∀ a, 0 ≤ q a) →
        ∀ ν : P → Measure NormalWaveSpace, ∀ _ : ∀ a, IsFiniteMeasure (ν a),
        0 < ∑ a, q a*(ν a univ).toReal →
        (∀ a, ∀ᵐ x ∂ν a, x ∈ J ∧ profileFrequencyScale g φ x ≤ ℓ a ∧
          ℓ a ≤ 2*profileFrequencyScale g φ x ∧ (∀ j, packetAxisShift x n ε (ℓ a) j ∈ J)) →
        ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ tsupport u ⊆ O ∧
          (∀ x : NormalWaveSpace, ∀ j ≤ m,
            ‖iteratedFDeriv ℝ j u x‖ ≤ C*n^(j+4)*Real.exp (n*φ x) ∧
            ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami g u y+n*(n+2)*u y) x‖ ≤
              C*(n^(D+1))⁻¹*Real.exp (n*φ x)) ∧
          (∀ y ∈ E, 1/n^110 ≤ ‖realWaveJet n (W y) ((w+u) ∘ normalWaveEquiv) y‖) ∧
          (p₀/2)*(∑ a, q a*(ν a univ).toReal) <
            ∑ a, q a*∑ j : Fin 3, (ν a {x | (w+u) x *
              (w+u) (packetAxisShift x n ε (ℓ a) j) < 0}).toReal := by
  classical
  obtain ⟨ε,hε,hε1,p₀,hp₀,hdata⟩ := compact_actual_waves_subregions_supported g hK hO hKO
  refine ⟨ε,hε,hε1,p₀,hp₀,?_⟩
  intro φ hφ hnc hcrit m D T₀ H hT₀ hH
  obtain ⟨c₀,hc₀,T,hT,c,hc,Q,hQ,N,hN,hdata⟩ := hdata φ hφ hnc hcrit m (D+4) T₀ H hT₀ hH
  have hN1 : 1 ≤ N := by linarith
  refine ⟨c₀,hc₀,3*Q*T,by positivity,N^4,one_le_pow₀ hN1,?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (one_le_pow₀ hN1 : 1 ≤ N^4).trans hn
  have hn0 : 0 < n := zero_lt_one.trans_le hn1
  obtain ⟨s,hs,hs4⟩ := quartic_reparameterization
    (fun x => ∃ s : ℝ, N ≤ s ∧ s^4 = x) hN1 (fun s hs => ⟨s,hs,rfl⟩) n hn
  have hh := hdata s hs
  dsimp only at hh
  rw [hs4] at hh
  obtain ⟨t,p,U,hSupport,ht,hU,hgood⟩ := hh
  intro S hS E hES hEK w hw W hW hW0 hWlower hWupper hwbound hlog J hJK hb P _ ℓ q hq ν hν hv hregion
  obtain ⟨γ,hcoef,hjet,hscore⟩ := hgood S hS E hES hEK w hw W hW hW0 hWlower hWupper
    hwbound hlog J hJK hb P ℓ q hq ν hν hv hregion
  let u := finiteWaveSuperposition (fun _ => (0 : ℝ)) U γ
  have hu : ContDiff ℝ ∞ u := contDiff_finiteWaveSuperposition contDiff_const (fun i j => (hU i j).1) γ
  have he : w+u = finiteWaveSuperposition w U γ := by
    funext x
    change w x + (0+_) = w x + _
    rw [zero_add]
  have he' : (w+u) ∘ normalWaveEquiv =
      finiteWaveSuperposition (w ∘ normalWaveEquiv) (fun i j => U i j ∘ normalWaveEquiv) γ := by
    rw [he]; rfl
  refine ⟨u,hu,finiteWaveSuperposition_compact (fun i j => (hU i j).2.1) γ,
    finiteWaveSuperposition_tsupport hSupport γ,?_,?_,?_⟩
  · intro x j hj
    have hcard : (Fintype.card t : ℝ) ≤ Q*n^3 := by simpa using ht
    have hj' : j ≤ max m 2 := hj.trans (le_max_left _ _)
    constructor
    · have hbound (i) (ℓ) : ‖iteratedFDeriv ℝ j (U i ℓ) x‖ ≤ T*n^j*Real.exp (n*φ x) := by
        apply ((hU i ℓ).2.2.2 x j hj').1.trans
        apply mul_le_of_le_one_right (by positivity)
        apply Real.exp_le_one_iff.mpr
        exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hn0.le) (sq_nonneg _)
      have hsum := finiteWaveSum_derivative_bound (fun i ℓ => (hU i ℓ).1) γ hn0.le hT.le
        (Real.exp_pos _).le hcard hcoef j x hbound
      have he₀ : u = fun y => ∑ i, ∑ ℓ, (γ i ℓ*U i ℓ y).re := by
        funext y; exact zero_add _
      rw [he₀]
      exact hsum
    · rw [finiteWaveSuperposition_residual g (fun i ℓ => (hU i ℓ).1) γ (n*(n+2))]
      let R : t → Fin 3 → NormalWaveSpace → ℂ := fun i ℓ y =>
        complexLaplaceBeltrami g (U i ℓ) y+(n : ℂ)*((n : ℂ)+2)*U i ℓ y
      have hR (i) (ℓ) : ContDiff ℝ ∞ (R i ℓ) :=
        (contDiff_complexLaplaceBeltrami_self g (hU i ℓ).1).add (contDiff_const.mul (hU i ℓ).1)
      have hb := norm_iteratedFDeriv_finiteWaveSum_uniform hR γ hn0.le
        (show 0 ≤ T*(n^((D+4)+1))⁻¹*Real.exp (n*φ x) by positivity)
        hcard hcoef j x (fun i ℓ => ((hU i ℓ).2.2.2 x j hj').2)
      simp only [Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_ofNat] at *
      apply hb.trans_eq
      simp only [show D+4+1 = (D+1)+4 by omega,pow_add]
      field_simp
  · rw [he']; exact hjet
  · rw [he]; exact hscore


end YauCounterexamples
end

end OAI
