import Mathlib
import OAI.Probability.SKGap.Localization.EmpiricalLaw
import OAI.Probability.SKGap.Matrix.NormalLogConst

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
namespace SKGap

variable {ι : Type*} [Fintype ι] [Nonempty ι]

end SKGap

namespace SKGap
variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
lemma gaussian_tilt_mass (f : ℝ →ᵇ ℝ) (d : ℝ) {s : ℝ} (hs : 0 < s) (r : ℝ) :
    (∫ y : ι → ℝ, exp ((Fintype.card ι : ℝ)*r -
      (Fintype.card ι : ℝ)*log (∫ x, exp (f x) ∂gaussianReal d s.toNNReal)) *
      (exp (∑ i, f (y i))*productNormal d s y)) = exp ((Fintype.card ι : ℝ)*r) := by
  rw [integral_const_mul, product_tiltedNormal_integral f d hs, ← exp_add]
  congr 1
  ring

theorem gaussian_covered_laplace {X : Type*} (C : Finset X) (f : X → ℝ →ᵇ ℝ)
    (d₀ s₀ : X → ℝ) (hs₀ : ∀ x ∈ C, 0 < s₀ x)
    (d s ψ : (ι → ℝ) → ℝ) (R r : ℝ) {E : Set (ι → ℝ)} (hE : MeasurableSet E)
    (hpos : ∀ y ∈ E, 0 < s y)
    (hmom : ∀ y ∈ E, ∑ i, (y i)^2 ≤ (Fintype.card ι : ℝ)*R)
    (hcover : ∀ y ∈ E, ∃ x ∈ C,
      ψ y-(∫ u, f x u ∂empiricalLaw y)+normalDensityError R (d y) (s y) (d₀ x) (s₀ x)+
        log (∫ u, exp (f x u) ∂gaussianReal (d₀ x) (s₀ x).toNNReal) < r) :
    (∫⁻ y in E, ENNReal.ofReal (exp ((Fintype.card ι : ℝ)*ψ y)*productNormal (d y) (s y) y)) ≤
      ENNReal.ofReal ((C.card : ℝ)*exp ((Fintype.card ι : ℝ)*r)) := by
  classical
  let F (x : X) (y : ι → ℝ) : ℝ :=
    exp ((Fintype.card ι : ℝ)*r-(Fintype.card ι : ℝ)*
      log (∫ u, exp (f x u) ∂gaussianReal (d₀ x) (s₀ x).toNNReal)) *
      (exp (∑ i, f x (y i))*productNormal (d₀ x) (s₀ x) y)
  have hFi (x : X) : Integrable (F x) :=
    (product_tiltedNormal_integrable (f x) (d₀ x) (s₀ x)).const_mul _
  have hFnn (x : X) (y : ι → ℝ) : 0 ≤ F x y :=
    mul_nonneg (exp_pos _).le (mul_nonneg (exp_pos _).le (productNormal_nonneg _ _ _))
  have hnorm (x : X) (hx : x ∈ C) : ∫ y, F x y = exp ((Fintype.card ι : ℝ)*r) :=
    gaussian_tilt_mass (f x) (d₀ x) (hs₀ x hx) r
  have hdom (y : ι → ℝ) (hy : y ∈ E) :
      exp ((Fintype.card ι : ℝ)*ψ y)*productNormal (d y) (s y) y ≤ ∑ x ∈ C, F x y := by
    obtain ⟨x,hx,hc⟩ := hcover y hy
    have hdens := normalLogDensity_sum_sub_le (hmom y hy) (d y) (s y) (d₀ x) (s₀ x)
    change _ ≤ (Fintype.card ι : ℝ)*normalDensityError R (d y) (s y) (d₀ x) (s₀ x) at hdens
    have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (Fintype.card_pos (α := ι))
    have hc' := mul_lt_mul_of_pos_left hc hn
    have hemp := card_mul_integral_empiricalLaw y (f x)
    have hsmall : exp ((Fintype.card ι : ℝ)*ψ y)*productNormal (d y) (s y) y ≤ F x y := by
      dsimp only [F]
      rw [productNormal_eq_exp _ (hpos y hy), productNormal_eq_exp _ (hs₀ x hx),
        ← exp_add, ← exp_add, ← exp_add]
      apply exp_le_exp.mpr
      nlinarith
    exact hsmall.trans (Finset.single_le_sum (fun a _ => hFnn a y) hx)
  have hsumI : Integrable (fun y => ∑ x ∈ C, F x y) := integrable_finsetSum C (fun x _ => hFi x)
  calc
    _ ≤ ∫⁻ y in E, ENNReal.ofReal (∑ x ∈ C, F x y) := lintegral_mono_ae
      ((ae_restrict_mem hE).mono (fun y hy => ENNReal.ofReal_le_ofReal (hdom y hy)))
    _ ≤ ∫⁻ y, ENNReal.ofReal (∑ x ∈ C, F x y) := lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ = ENNReal.ofReal (∫ y, ∑ x ∈ C, F x y) :=
      (ofReal_integral_eq_lintegral_ofReal hsumI (ae_of_all _ (fun y => Finset.sum_nonneg (fun x _ => hFnn x y)))).symm
    _ = _ := by
      rw [integral_finsetSum C (fun x _ => hFi x)]
      simp_rw [Finset.sum_congr rfl hnorm]
      simp

end SKGap

namespace SKGap

theorem gaussian_compact_laplace {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {P : X → ProbabilityMeasure ℝ} {d s ψ : X → ℝ}
    (hP : ContinuousOn P K) (hd : ContinuousOn d K) (hs : ContinuousOn s K)
    (hψ : ContinuousOn ψ K) (hpos : ∀ x ∈ K, 0 < s x) (R r : ℝ)
    (hW : ∀ x ∈ K, ∃ f : ℝ →ᵇ ℝ, ψ x-(∫ y, f y ∂P x)+
      log (∫ y, exp (f y) ∂gaussianReal (d x) (s x).toNNReal) < r) :
    ∃ M : ℕ, ∀ n : ℕ, ∀ hn : 0 < n, ∀ z : (Fin n → ℝ) → X,
      ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, z y ∈ K) →
      (∀ y ∈ E, P (z y) = @empiricalLaw (Fin n) _ ⟨⟨0,hn⟩⟩ y) →
      (∀ y ∈ E, ∑ i, (y i)^2 ≤ (n:ℝ)*R) →
      (∫⁻ y in E, ENNReal.ofReal (exp ((n:ℝ)*ψ (z y))*productNormal (d (z y)) (s (z y)) y)) ≤
        ENNReal.ofReal ((M:ℝ)*exp ((n:ℝ)*r)) := by
  classical
  obtain ⟨C,f,hC⟩ := finite_gaussian_test_cover hK hP hd hs hψ hpos R r hW
  refine ⟨C.card, ?_⟩
  intro n hn z E hE hz hemp hmom
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hh := gaussian_covered_laplace C f (fun x : K => d x) (fun x : K => s x)
      (fun x _ => hpos x x.2) (fun y => d (z y)) (fun y => s (z y))
      (fun y => ψ (z y)) R r hE (fun y hy => hpos (z y) (hz y hy))
      (by simpa only [Fintype.card_fin] using hmom) (fun y hy => by
        obtain ⟨x,hx,hcx⟩ := hC (z y) (hz y hy)
        rw [hemp y hy] at hcx
        exact ⟨x,hx,hcx⟩)
  simpa only [Fintype.card_fin] using hh

lemma absorb_finite_exponential_factor (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ r : ℝ,
      (M:ℝ)*exp ((n:ℝ)*r) ≤ exp ((n:ℝ)*(r+ε)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (log ((M:ℝ)+1)/ε)
  refine ⟨N,?_⟩
  intro n hn r
  have hcast : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hnlog : log ((M:ℝ)+1) ≤ (n:ℝ)*ε := by
    have h := (div_lt_iff₀ hε).mp hN
    nlinarith
  have he : (M:ℝ) ≤ exp ((n:ℝ)*ε) := by
    have h := exp_le_exp.mpr hnlog
    rw [exp_log (by positivity)] at h
    linarith
  calc
    _ ≤ exp ((n:ℝ)*ε)*exp ((n:ℝ)*r) := mul_le_mul_of_nonneg_right he (exp_pos _).le
    _ = _ := by rw [← exp_add]; congr 1; ring

theorem gaussian_compact_rate {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {P : X → ProbabilityMeasure ℝ} {d s ψ : X → ℝ}
    (hP : ContinuousOn P K) (hd : ContinuousOn d K) (hs : ContinuousOn s K)
    (hψ : ContinuousOn ψ K) (hpos : ∀ x ∈ K, 0 < s x) (R r : ℝ)
    (hW : ∀ x ∈ K, ∃ f : ℝ →ᵇ ℝ, ψ x-(∫ y, f y ∂P x)+
      log (∫ y, exp (f y) ∂gaussianReal (d x) (s x).toNNReal) < r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ hn : 0 < n, ∀ z : (Fin n → ℝ) → X,
      ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, z y ∈ K) →
      (∀ y ∈ E, P (z y) = @empiricalLaw (Fin n) _ ⟨⟨0,hn⟩⟩ y) →
      (∀ y ∈ E, ∑ i, (y i)^2 ≤ (n:ℝ)*R) →
      (∫⁻ y in E, ENNReal.ofReal (exp ((n:ℝ)*ψ (z y))*productNormal (d (z y)) (s (z y)) y)) ≤
        ENNReal.ofReal (exp ((n:ℝ)*(r+ε))) := by
  obtain ⟨M,hM⟩ := gaussian_compact_laplace hK hP hd hs hψ hpos R r hW
  obtain ⟨N,hN⟩ := absorb_finite_exponential_factor M hε
  refine ⟨N,?_⟩
  intro n hn hn' z E hE hz hemp hmom
  exact (hM n hn' z E hE hz hemp hmom).trans (ENNReal.ofReal_le_ofReal (hN n hn r))

end SKGap

end
end
end
end
end
end
end

end OAI
