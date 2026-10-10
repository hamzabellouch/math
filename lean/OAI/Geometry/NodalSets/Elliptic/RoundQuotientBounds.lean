import OAI.Geometry.NodalSets.Elliptic.LocalFrequencyLeibniz
import OAI.Geometry.NodalSets.Elliptic.RoundReciprocalDerivatives

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem round_quotient_finite_bound {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (r : ℕ) {A : ℝ} (hA : 0 < A) :
    ∃ C > 0, ∀ (u R H : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ u → ContDiff ℝ ∞ R →
      tsupport R ⊆ Q → (∀ x, 0 < H x) → ∀ (n : ℕ), 0 < n → ∀ eps : ℝ, 0 < eps →
      (∀ x ∈ Q, ∀ i, i ≤ r+1 → ‖iteratedFDeriv ℝ i u x‖ ≤ A*(n:ℝ)^(i+3)*H x) →
      (∀ x ∈ Q, ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i R x‖ ≤ eps*H x) →
      (∀ x ∈ Q, ((n:ℝ)^65)⁻¹*H x ≤ sourceFirstJetSize u n x) →
      let f := fun x ↦ R x / roundCorrectionDenominator u n x
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ tsupport R ∧
      ∀ x, ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i f x‖ ≤
        C*eps*(n:ℝ)^(137*i+128)*(H x)⁻¹ := by
  obtain ⟨B,hB,hrec⟩ := round_reciprocal_finite_bound hQ r hA
  refine ⟨(2:ℝ)^r*B,by positivity,?_⟩
  intro u R H hu hR hs hH n hn eps heps hub hRb hjet
  let D := roundCorrectionDenominator u n
  have hD : ContDiff ℝ ∞ D := roundCorrectionDenominator_smooth u hu n
  have hDQ (x : Yau.Jets.Coord) (hx : x ∈ Q) : D x ≠ 0 :=
    (roundCorrectionDenominator_pos u hn x (hH x) (hjet x hx)).ne'
  have hf := Yau.smooth_quotient_on_residual_support hR hD (fun x hx ↦ hDQ x (hs hx))
  refine ⟨hf,Yau.quotient_compact_support (hQ.of_isClosed_subset isClosed_closure hs),
    Yau.quotient_tsupport_subset R D,?_⟩
  intro x i hi
  have hHx := hH x
  by_cases hx : x ∈ Q
  · let U : Set Yau.Jets.Coord := {y | D y ≠ 0}
    have hU : IsOpen U := isOpen_ne_fun hD.continuous continuous_const
    have hxU : x ∈ U := hDQ x hx
    have hiD : ContDiffOn ℝ ∞ (fun y ↦ (D y)⁻¹) U :=
      hD.contDiffOn.inv (fun y hy ↦ hy)
    have hN : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hbR (j : ℕ) (hj : j ≤ i) :
        ‖iteratedFDeriv ℝ j R x‖ ≤ eps*(n:ℝ)^(137*j+0)*H x := by
      exact (hRb x hx j (by omega)).trans (by
        have hp : 1 ≤ (n:ℝ)^(137*j+0) := one_le_pow₀ hN
        nlinarith [mul_nonneg (sub_nonneg.mpr hp) (mul_nonneg heps.le (hH x).le)])
    have hbI (j : ℕ) (hj : j ≤ i) :
        ‖iteratedFDeriv ℝ j (fun y ↦ (D y)⁻¹) x‖ ≤
          B*(n:ℝ)^(137*j+128)*((H x)^2)⁻¹ :=
      hrec u hu n hn x hx (H x) (hH x) (hub x hx) (hjet x hx) j (by omega)
    have h := scaled_frequency_product_on R (fun y ↦ (D y)⁻¹) hU hR.contDiffOn hiD
      x hxU i 137 0 128 (by positivity) heps.le hB.le (hH x).le (by positivity) hbR hbI
    have he : H x*((H x)^2)⁻¹ = (H x)⁻¹ := by field_simp [(hH x).ne']
    simp only [Nat.add_zero,he] at h
    change ‖iteratedFDeriv ℝ i (fun y ↦ R y / D y) x‖ ≤ _
    simp only [div_eq_mul_inv]
    refine h.trans ?_
    calc
      _ ≤ (2:ℝ)^r*eps*B*(n:ℝ)^(137*i+128)*(H x)⁻¹ := by gcongr; norm_num
      _ = _ := by ring
  · have hxs : x ∉ tsupport (fun y ↦ R y / D y) :=
      fun h ↦ hx (hs (Yau.quotient_tsupport_subset R D h))
    have hz := (notMem_tsupport_iff_eventuallyEq.mp hxs).iteratedFDeriv ℝ i
    rw [hz.eq_of_nhds]
    simp only [iteratedFDeriv_zero,Pi.zero_apply,norm_zero]
    positivity

end
end Yau.Target

end OAI
