import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.RadialBundleSources

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.RadialPotential

lemma finite_radialJet_constant (D : ℕ → ℝ) (hD : ∀ k, 0 ≤ D k)
    (D₀ : ℝ) (hD₀ : 0 ≤ D₀) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ D₀ ≤ C ∧ ∀ k ≤ N, D k ≤ C/(5:ℝ)^k := by
  let C := D₀ + ∑ k ∈ Finset.range (N+1), D k * (5:ℝ)^k
  have hc : D₀ ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ => mul_nonneg (hD k) (pow_nonneg (by norm_num) k)))
  refine ⟨C,hD₀.trans hc,hc,?_⟩
  intro k hk
  apply (le_div_iff₀ (by positivity : 0 < (5:ℝ)^k)).mpr
  have hkC : D k * (5:ℝ)^k ≤ ∑ i ∈ Finset.range (N+1), D i * (5:ℝ)^i :=
    Finset.single_le_sum (fun i _ => mul_nonneg (hD i) (pow_nonneg (by norm_num) i))
      (Finset.mem_range.mpr (by omega))
  exact hkC.trans (le_add_of_nonneg_left hD₀)

lemma radialJet_rescale {C D r : ℝ} (hr : 0 < r) (k d : ℕ)
    (h : D ≤ C/(5:ℝ)^k) :
    D/r^(k+d) ≤ (C/r^d)/(5*r)^k := by
  calc
    _ ≤ (C/(5:ℝ)^k)/r^(k+d) := div_le_div_of_nonneg_right h (pow_nonneg hr.le _)
    _ = _ := by rw [mul_pow,pow_add]; field_simp
end TamingCompatibility.RadialPotential

end
end

section

noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]
variable (a ρ : E → ℝ) (V : E → E)
  (ha : ContDiff ℝ ∞ a) (hρ : ContDiff ℝ ∞ ρ) (hV : ContDiff ℝ ∞ V)

include hρ in

lemma logShellSchwartz_uniform_inputs {K : Set E} (hK : IsCompact K) (R : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ∀ hr : r ∈ Ioc (0:ℝ) R, ∀ s, ∀ hs : s ∈ Ioc (0:ℝ) r, ∀ b ∈ K,
      (∀ z, |logShellSchwartz a V ha hV hr.1 hs.1 b z| ≤ C/r) ∧
      (∀ n ≤ N, ∀ z, ‖iteratedFDeriv ℝ n
        (fun z => ρ z * logShellSchwartz a V ha hV hr.1 hs.1 b z) z‖ ≤ (C/r)/(5*r)^n) := by
  classical
  obtain ⟨D₀,hD₀,hb₀⟩ := shiftedLogShell_derivatives_bounded a V ha hV hK R 0
  choose D hD hb using fun n => shiftedLogShell_derivatives_bounded a
    (fun w => ρ w • V w) ha (hρ.smul hV) hK R n
  obtain ⟨C,hC,hC₀,hCD⟩ := finite_radialJet_constant D hD D₀ hD₀ N
  refine ⟨C,hC,?_⟩
  intro r hr s hs b hbK
  constructor
  · intro z
    have h := hb₀ r hr s ⟨hs.1.le,hs.2⟩ b hbK z
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,zero_add,pow_one] at h
    exact h.trans (by simpa using div_le_div_of_nonneg_right hC₀ (show 0 ≤ r from hr.1.le))
  · intro n hn z
    have he : (fun z => ρ z * logShellSchwartz a V ha hV hr.1 hs.1 b z) =
        shiftedLogShell a (fun w => ρ w • V w) r s b :=
      funext (shiftedLogShell_weight a ρ V r s b)
    rw [he]
    have h := hb n r hr s ⟨hs.1.le,hs.2⟩ b hbK z
    apply h.trans
    simpa only [add_zero,pow_zero,pow_one,div_one] using radialJet_rescale
      (hr.1) n 1 (hCD n hn)

include hρ in

lemma logInnerSchwartz_uniform_inputs {K : Set E} (hK : IsCompact K) (R : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ∀ hs : s ∈ Ioc (0:ℝ) R, ∀ b ∈ K,
      (∀ z, |logInnerSchwartz a V ha hV hs.1 b z| ≤ C/s) ∧
      (∀ n ≤ N, ∀ z, ‖iteratedFDeriv ℝ n
        (fun z => ρ z * logInnerSchwartz a V ha hV hs.1 b z) z‖ ≤ (C/s)/(5*s)^n) := by
  classical
  obtain ⟨D₀,hD₀,hb₀⟩ := shiftedLogInner_derivatives_bounded a V ha hV hK R 0
  choose D hD hb using fun n => shiftedLogInner_derivatives_bounded a
    (fun w => ρ w • V w) ha (hρ.smul hV) hK R n
  obtain ⟨C,hC,hC₀,hCD⟩ := finite_radialJet_constant D hD D₀ hD₀ N
  refine ⟨C,hC,?_⟩
  intro s hs b hbK
  constructor
  · intro z
    have h := hb₀ s hs b hbK z
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,zero_add,pow_one] at h
    exact h.trans (by simpa using div_le_div_of_nonneg_right hC₀ (show 0 ≤ s from hs.1.le))
  · intro n hn z
    have he : (fun z => ρ z * logInnerSchwartz a V ha hV hs.1 b z) =
        shiftedLogInner a (fun w => ρ w • V w) s b :=
      funext (shiftedLogInner_weight a ρ V s b)
    rw [he]
    have h := hb n s hs b hbK z
    apply h.trans
    simpa only [add_zero,pow_zero,pow_one,div_one] using radialJet_rescale
      (hs.1) n 1 (hCD n hn)

include hρ in

lemma sqrtShellSchwartz_uniform_inputs {K : Set E} (hK : IsCompact K) (R : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ∀ hr : r ∈ Ioc (0:ℝ) R, ∀ s, ∀ hs : s ∈ Ioc (0:ℝ) r, ∀ b ∈ K,
      (∀ z, |sqrtShellSchwartz a V ha hV hr.1 hs.1 b z| ≤ C) ∧
      (∀ n ≤ N, ∀ z, ‖iteratedFDeriv ℝ n
        (fun z => ρ z * sqrtShellSchwartz a V ha hV hr.1 hs.1 b z) z‖ ≤ (C)/(5*r)^n) := by
  classical
  obtain ⟨D₀,hD₀,hb₀⟩ := shiftedSqrtShell_derivatives_bounded a V ha hV hK R 0
  choose D hD hb using fun n => shiftedSqrtShell_derivatives_bounded a
    (fun w => ρ w • V w) ha (hρ.smul hV) hK R n
  obtain ⟨C,hC,hC₀,hCD⟩ := finite_radialJet_constant D hD D₀ hD₀ N
  refine ⟨C,hC,?_⟩
  intro r hr s hs b hbK
  constructor
  · intro z
    have h := hb₀ r hr s ⟨hs.1.le,hs.2⟩ b hbK z
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,pow_zero,div_one] at h
    exact h.trans (by exact hC₀)
  · intro n hn z
    have he : (fun z => ρ z * sqrtShellSchwartz a V ha hV hr.1 hs.1 b z) =
        shiftedSqrtShell a (fun w => ρ w • V w) r s b :=
      funext (shiftedSqrtShell_weight a ρ V r s b)
    rw [he]
    have h := hb n r hr s ⟨hs.1.le,hs.2⟩ b hbK z
    apply h.trans
    simpa only [add_zero,pow_zero,pow_one,div_one] using radialJet_rescale
      (hr.1) n 0 (hCD n hn)

include hρ in

lemma sqrtInnerSchwartz_uniform_inputs {K : Set E} (hK : IsCompact K) (R : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ∀ hs : s ∈ Ioc (0:ℝ) R, ∀ b ∈ K,
      (∀ z, |sqrtInnerSchwartz a V ha hV hs.1 b z| ≤ C) ∧
      (∀ n ≤ N, ∀ z, ‖iteratedFDeriv ℝ n
        (fun z => ρ z * sqrtInnerSchwartz a V ha hV hs.1 b z) z‖ ≤ (C)/(5*s)^n) := by
  classical
  obtain ⟨D₀,hD₀,hb₀⟩ := shiftedSqrtInner_derivatives_bounded a V ha hV hK R 0
  choose D hD hb using fun n => shiftedSqrtInner_derivatives_bounded a
    (fun w => ρ w • V w) ha (hρ.smul hV) hK R n
  obtain ⟨C,hC,hC₀,hCD⟩ := finite_radialJet_constant D hD D₀ hD₀ N
  refine ⟨C,hC,?_⟩
  intro s hs b hbK
  constructor
  · intro z
    have h := hb₀ s hs b hbK z
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,pow_zero,div_one] at h
    exact h.trans (by exact hC₀)
  · intro n hn z
    have he : (fun z => ρ z * sqrtInnerSchwartz a V ha hV hs.1 b z) =
        shiftedSqrtInner a (fun w => ρ w • V w) s b :=
      funext (shiftedSqrtInner_weight a ρ V s b)
    rw [he]
    have h := hb n s hs b hbK z
    apply h.trans
    simpa only [add_zero,pow_zero,pow_one,div_one] using radialJet_rescale
      (hs.1) n 0 (hCD n hn)

end TamingCompatibility.RadialPotential

end
end

end
end

end OAI
