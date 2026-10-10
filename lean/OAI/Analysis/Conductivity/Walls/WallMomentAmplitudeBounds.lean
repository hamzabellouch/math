import Mathlib
import OAI.Analysis.Conductivity.Walls.CriticalWallHomogeneous

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology

def wallMomentAmplitude (χ η : ℝ → ℝ) (σ lam : ℝ) (c : Fin 3 → ℝ) (q : ℝ×ℝ) : ℝ :=
  (χ q.1*(c ⬝ᵥ wallMomentBasis σ lam q.1))*η q.2

def wallMomentTest (χ η : ℝ → ℝ) (σ lam : ℝ) (i : Fin 3) (q : ℝ×ℝ) : ℝ :=
  (χ q.1*wallMomentBasis σ lam q.1 i)*η q.2

lemma wallMomentTest_smooth {χ η : ℝ → ℝ} (σ lam : ℝ)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hη : ContDiff ℝ (↑(⊤ : ℕ∞)) η) (i : Fin 3) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallMomentTest χ η σ lam i) :=
  ((hχ.mul (wallMomentBasis_smooth σ lam i)).comp contDiff_fst).mul (hη.comp contDiff_snd)

lemma wallMomentTest_compact {χ η : ℝ → ℝ} (σ lam : ℝ)
    (hsχ : HasCompactSupport χ) (hsη : HasCompactSupport η) (i : Fin 3) :
    HasCompactSupport (wallMomentTest χ η σ lam i) :=
  by
    have h : HasCompactSupport (fun s => χ s*wallMomentBasis σ lam s i) := hsχ.mul_right
    exact (surface_product_compact (f := fun s => χ s*wallMomentBasis σ lam s i) h hsη).1

lemma wallMomentAmplitude_sum (χ η : ℝ → ℝ) (σ lam : ℝ) (c : Fin 3 → ℝ) :
    wallMomentAmplitude χ η σ lam c=(fun q => ∑ i,c i • wallMomentTest χ η σ lam i q) := by
  funext q
  simp only [wallMomentAmplitude,dotProduct,Finset.mul_sum,Finset.sum_mul,wallMomentTest,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma wall_moment_amplitude_C1 {χ η : ℝ → ℝ} {σ lam : ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hη : ContDiff ℝ (↑(⊤ : ℕ∞)) η)
    (hsχ : HasCompactSupport χ) (hsη : HasCompactSupport η) :
    ∃ B : ℝ,0<B ∧ ∀ (c : Fin 3 → ℝ) (A : ℝ),0≤A →
      (∀ i,‖c i‖≤A) → ∀ q,
        |wallMomentAmplitude χ η σ lam c q|≤B*A ∧
        |fderiv ℝ (wallMomentAmplitude χ η σ lam c) q (1,0)|≤B*A := by
  let g := wallMomentTest χ η σ lam
  have hg := wallMomentTest_smooth σ lam hχ hη
  have hsg := wallMomentTest_compact σ lam hsχ hsη
  obtain ⟨B₀,hB₀,hb₀⟩ := fixed_smooth_tests_bound g hg hsg 0
  obtain ⟨B₁,hB₁,hb₁⟩ := fixed_smooth_tests_bound g hg hsg 1
  refine ⟨B₀+B₁,add_pos hB₀ hB₁,?_⟩
  intro c A hA hc q
  rw [wallMomentAmplitude_sum]
  have hv := hb₀ c A hA hc q
  rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at hv
  have hd := hb₁ c A hA hc q
  rw [norm_iteratedFDeriv_one] at hd
  have hpoint : |fderiv ℝ (fun q => ∑ i,c i • g i q) q (1,0)|≤B₁*A := by
    have h := ContinuousLinearMap.le_opNorm (fderiv ℝ (fun q => ∑ i,c i • g i q) q) (1,0)
    have hn : ‖((1,0):ℝ×ℝ)‖=1 := by norm_num
    simpa only [hn,mul_one,Real.norm_eq_abs] using h.trans (by simpa only [hn,mul_one] using hd)
  exact ⟨hv.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB₁.le) hA),
    hpoint.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB₀.le) hA)⟩

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology
variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P] [LocallyCompactSpace P]

theorem actual_wall_amplitude_inverse {l r a b σ lam : ℝ}
    (hlr : l<r) (hab : a<b) (hσ : σ≠0) (hlam : lam≠0)
    {v : P → Box3 → ℝ} {p₀ : P}
    (hv₀ : ContDiff ℝ (↑(⊤ : ℕ∞)) (v p₀))
    (hv : Continuous (fun pq : P×Box3 => v pq.1 pq.2))
    (hvs : Continuous (fun pq : P×Box3 => wallAlong (1,0) (v pq.1) pq.2))
    (hlim : ∀ q : ℝ×ℝ,v p₀ (q,0)=σ*Real.exp (-lam*q.1)) :
    ∃ B : ℝ,0<B ∧ ∀ᶠ p in 𝓝 p₀,∀ m : Fin 3 → ℝ,
      ∃ f : (ℝ×ℝ) → ℝ,ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f ∧
        tsupport f⊆Icc l r ×ˢ Ioo a b ∧
        (∀ i,(∫ q,f q*wallActualMoment (v p) q i)=m i) ∧
        (∀ q,|f q|≤B*‖m‖ ∧ |fderiv ℝ f q (1,0)|≤B*‖m‖) := by
  obtain ⟨χ,η,hχ,hη,hsχ,hsη,hvχ,hvη,C,hC,hinv⟩ :=
    actual_wall_moment_uniform_inverse hlr hab hσ hlam hv₀ hv hvs hlim
  obtain ⟨D,hD,hbound⟩ := wall_moment_amplitude_C1 (σ:=σ) (lam:=lam) hχ hη hsχ hsη
  refine ⟨D*C,mul_pos hD hC,?_⟩
  filter_upwards [hinv] with p hp
  intro m
  obtain ⟨c,hc,hf,hsf,hvf,hm⟩ := hp m
  refine ⟨wallMomentAmplitude χ η σ lam c,hf,hsf,hvf,hm,?_⟩
  intro q
  simpa only [mul_assoc] using hbound c (C*‖m‖) (mul_nonneg hC.le (norm_nonneg _)) hc q

end ScalarConductivity

end

end OAI
