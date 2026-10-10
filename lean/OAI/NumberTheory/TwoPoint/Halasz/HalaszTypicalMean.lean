import OAI.NumberTheory.TwoPoint.Halasz.HalaszMixedEstimate
import OAI.NumberTheory.TwoPoint.Halasz.HalaszMixedNumeric
import OAI.NumberTheory.TwoPoint.Halasz.HalaszNumericalErrors
import OAI.NumberTheory.TwoPoint.Halasz.HalaszSmoothBounds
import OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalSmooth
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalOutside

namespace OAI

/-! Ordinary prefixes of the literal typical coefficient. The prime
cutoff stays above all selected bands throughout both convolutions. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem halasz_typical_mean_value : ∃ C X₀ : ℝ, 0  <  C ∧
    ∀ N : ℕ, X₀  ≤  N → ∀ F : ℕ → ℂ, F 1=1 →
      (∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) → OneBounded F →
      ∀ {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ),
      (∀ j ∈ J, P j  ⊆  primesUpTo N) → Set.PairwiseDisjoint (J : Set ι) P →
      ∀ R : ℝ, 1 ≤ R → Real.log (N:ℝ)^16 ≤ R → R ≤ (N:ℝ)/2 →
      (∀ j ∈ J, ∀ p ∈ P j, (p:ℝ) ≤ R) → ∀ M : ℝ, 0 ≤ M →
      (∀ t ∈ Set.Icc (-(Real.log (N:ℝ)^8)) (Real.log (N:ℝ)^8),
        M ≤ squaredDistance F (mrtArchimedeanTwist t) N) →
      ‖∑ n ∈ Icc 1 N, mrtTypicalCoefficient J P F n‖  ≤  C*N*
        ((M+1)*Real.exp (-M/2)+(1+Real.log R)*Real.log (Real.log N)/Real.log N) := by
  obtain ⟨C₁,T₀,hC₁,hT₀,hdouble⟩ := halasz_mixed_double_estimate
  obtain ⟨H₀,hH₀,hEuler⟩ := halasz_typical_smooth_distance_bound
  let H := max 1 H₀
  let D := 2*C₁*H+8*C₁+halaszMixedNumericConstant
  let C := 1+C₁*H+D
  have hH : 1 ≤ H := le_max_left _ _
  have hH₀H : H₀ ≤ H := le_max_right _ _
  have hD : 0 ≤ D := by
    dsimp [D]
    have := halaszMixedNumericConstant_nonneg
    positivity
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp ((halasz_eventually_numeric_scale T₀).and
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))))
  refine ⟨C,X₀,hC,?_⟩
  intro N hXN F hF1 hFm hFb ι J P hP hdis R hR hRlo hRhi hupper M hM hdist
  obtain ⟨⟨hNr,hll,hl4,hl16,hBT⟩,hlog⟩ := hX₀ N hXN
  have hN : 3 ≤ N := by exact_mod_cast hNr
  have hN2 : 2 ≤ N := by omega
  have hlog0 : 0 < Real.log (N:ℝ) := by linarith
  have hl4N : Real.log (N:ℝ)^4 ≤ N :=
    (pow_le_pow_right₀ hlog (by norm_num : (4:ℕ) ≤ 16)).trans (by linarith)
  let B := mrtTypicalCoefficient J P F
  have hB : OneBounded B := mrtTypicalCoefficient_oneBounded J P F hFb
  have hpr : ∀ j ∈ J, ∀ p ∈ P j, p.Prime := by
    intro j hj p hp
    exact (mem_filter.mp (hP j hj hp)).2
  have hmul : ∀ p : ℕ, p.Prime → R < (p:ℝ) → ∀ m : ℕ, 0 < m → B (p*m)=F p*B m := by
    intro p hp hRp m hm
    have ha : mrtPrimeAvoids (J.biUnion P) p := by
      apply mrtPrimeAvoids_prime_outside _ (fun q hq => ?_) hp
      · intro hmem
        obtain ⟨j,hj,hpj⟩ := mem_biUnion.mp hmem
        exact (not_le_of_gt hRp) (hupper j hj p hpj)
      · obtain ⟨j,hj,hqj⟩ := mem_biUnion.mp hq
        exact hpr j hj q hqj
    exact mrtTypicalCoefficient_mul_of_avoids J P hpr F hFm hp.pos hm ha
  let m := ⌈(N:ℝ)/Real.log (N:ℝ)^4⌉₊
  obtain ⟨hm,hmN,_,hml,hmu⟩ := halasz_smoothing_integer hN2 hl4 hl4N
  have hglobal (t : ℝ) : ‖LSeries (halaszSmoothFunction B N) (1+(t:ℂ)*Complex.I)‖  ≤
      H*Real.log N := by
    have he := hEuler F hF1 hFm hFb N hN2 t J P hP hdis
    have hd := halasz_distance_nonneg F hFb N t
    have hx : Real.exp (-squaredDistance F (mrtArchimedeanTwist t) N/2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    calc
      _  ≤  H₀*Real.log N*Real.exp (-squaredDistance F (mrtArchimedeanTwist t) N/2) := he
      _  ≤  H₀*Real.log N := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ H₀*Real.log (N:ℝ))
      _  ≤  _ := mul_le_mul_of_nonneg_right hH₀H hlog0.le
  have hcentral (t : ℝ) (ht : t ∈ Set.Icc (-(Real.log (N:ℝ)^8)) (Real.log (N:ℝ)^8)) :
      ‖LSeries (halaszSmoothFunction B N) (1+(t:ℂ)*Complex.I)‖  ≤
        (H*Real.log N)*Real.exp (-(M/2)) := by
    apply (hEuler F hF1 hFm hFb N hN2 t J P hP hdis).trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hH₀H hlog0.le
    · apply Real.exp_le_exp.mpr
      linarith [hdist t ht]
    · positivity
    · positivity
  have hb := hdouble F B hFb hB N m R (Real.log N^8) (H*Real.log N)
    (H*Real.log N) (M/2) hN2 hm hmN hR
    (by rw [←pow_mul]; norm_num; exact hRlo) hBT
    (le_mul_of_one_le_left hlog0.le hH) (by positivity) (by positivity) hcentral hglobal
  have herr := halasz_numerical_errors hN hC₁.le (by linarith : 0 ≤ H) hlog hm hml hmu
  have hr := Real.log_nonneg hR
  have hreduce := halasz_mixed_mean_numeric F B hFb hB N hR hRhi hll hmul
  have hsmall : (2*C₁*H+8*C₁)*N  ≤
      (2*C₁*H+8*C₁)*N*(1+Real.log R)*Real.log (Real.log N) := by
    calc
      _ ≤ (2*C₁*H+8*C₁)*N*(1+Real.log R) :=
        le_mul_of_one_le_right (by positivity) (by linarith)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hll
  have hmain : Real.log (N:ℝ)*‖∑ n ∈ Icc 1 N, B n‖  ≤
      C₁*N*(H*Real.log N)*(M+1)*Real.exp (-M/2)+
        D*N*(1+Real.log R)*Real.log (Real.log N) := by
    have hmfac : C₁*N*(H*Real.log N)*(M/2+1)*Real.exp (-(M/2))  ≤
        C₁*N*(H*Real.log N)*(M+1)*Real.exp (-M/2) := by
      rw [show -(M/2) = -M/2 by ring]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    dsimp [D]
    nlinarith
  have hdiv := div_le_div_of_nonneg_right hmain hlog0.le
  have heq : (C₁*N*(H*Real.log N)*(M+1)*Real.exp (-M/2)+
      D*N*(1+Real.log R)*Real.log (Real.log N))/Real.log N =
      C₁*H*N*((M+1)*Real.exp (-M/2))+
        D*N*((1+Real.log R)*Real.log (Real.log N)/Real.log N) := by field_simp
  rw [mul_div_cancel_left₀ _ hlog0.ne',heq] at hdiv
  have hc1 : C₁*H ≤ C := by dsimp [C]; linarith
  have hc2 : D ≤ C := by dsimp [C]; linarith [show 0 ≤ C₁*H by positivity]
  calc
    _  ≤  C₁*H*N*((M+1)*Real.exp (-M/2))+
        D*N*((1+Real.log R)*Real.log (Real.log N)/Real.log N) := hdiv
    _  ≤  C*N*((M+1)*Real.exp (-M/2))+
        C*N*((1+Real.log R)*Real.log (Real.log N)/Real.log N) := by gcongr
    _ = _ := by ring

end TwoPointCorrelations

end OAI
