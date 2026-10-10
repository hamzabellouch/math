import Mathlib

namespace OAI

open Matrix

namespace CurrentKS.Calculus
noncomputable section
open Filter Set
open scoped Topology

variable {E F G D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

lemma bilinear_iterated_bound (B : E →L[ℝ] F →L[ℝ] G) {f : D → E} {g : D → F}
    {x : D} {n : ℕ} (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x)
    (hB : ‖B‖ ≤ 1) :
    ‖iteratedFDeriv ℝ n (fun y => B (f y) (g y)) x‖ ≤
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ := by
  obtain ⟨u,hu,hxu,hfu⟩ := hf.contDiffOn' le_rfl (by simp)
  obtain ⟨v,hv,hxv,hgv⟩ := hg.contDiffOn' le_rfl (by simp)
  let s := u ∩ v
  have hs : IsOpen s := hu.inter hv
  have hx : x ∈ s := ⟨hxu,hxv⟩
  have hfs : ContDiffOn ℝ n f s := (by simpa using hfu : ContDiffOn ℝ n f u).mono inter_subset_left
  have hgs : ContDiffOn ℝ n g s := (by simpa using hgv : ContDiffOn ℝ n g v).mono inter_subset_right
  have hb := B.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
    hfs hgs hs.uniqueDiffOn hx (le_refl (n : WithTop ℕ∞)) hB
  have hres : ContDiffAt ℝ n (fun y => B (f y) (g y)) x := B.isBoundedBilinearMap.contDiff.comp_contDiffAt x (hf.prodMk hg)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn hres hx] at hb
  convert hb using 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn (hf.of_le (by exact_mod_cast hi')) hx,
    iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn (hg.of_le (by exact_mod_cast Nat.sub_le n i)) hx]

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R] [NormedAlgebra ℝ R]

lemma contDiffAt_inverse_of_unit {x : R} (hx : IsUnit x) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (@Ring.inverse R _) x := by
  obtain ⟨x,rfl⟩ := hx
  exact contDiffAt_ringInverse ℝ x

lemma fderiv_inverse_eq {x : R} (hx : IsUnit x) :
    fderiv ℝ (@Ring.inverse R _) x =
      -ContinuousLinearMap.mulLeftRight ℝ R (Ring.inverse x) (Ring.inverse x) := by
  obtain ⟨x,rfl⟩ := hx
  simpa only [Ring.inverse_unit] using fderiv_inverse (𝕜 := ℝ) x

lemma inverse_succ_bound {x : R} (hx : IsUnit x) (n : ℕ) :
    ‖iteratedFDeriv ℝ (n+1) (@Ring.inverse R _) x‖ ≤
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (@Ring.inverse R _) x‖ *
        ‖iteratedFDeriv ℝ (n-i) (@Ring.inverse R _) x‖ := by
  have he : fderiv ℝ (@Ring.inverse R _) =ᶠ[𝓝 x]
      fun y => -ContinuousLinearMap.mulLeftRight ℝ R (Ring.inverse y) (Ring.inverse y) := by
    filter_upwards [Units.isOpen.mem_nhds hx] with y hy
    exact fderiv_inverse_eq hy
  have he' : fderiv ℝ (@Ring.inverse R _) =ᶠ[𝓝 x]
      -(fun y => ContinuousLinearMap.mulLeftRight ℝ R (Ring.inverse y) (Ring.inverse y)) := by
    exact he
  rw [← norm_iteratedFDeriv_fderiv, (he'.iteratedFDeriv ℝ n).eq_of_nhds,
    iteratedFDeriv_neg_apply, norm_neg]
  exact bilinear_iterated_bound _ (contDiffAt_inverse_of_unit hx)
    (contDiffAt_inverse_of_unit hx) (ContinuousLinearMap.opNorm_mulLeftRight_le ℝ R)

theorem inverse_first_three {x : R} (hx : IsUnit x) :
    ‖fderiv ℝ (@Ring.inverse R _) x‖ ≤ ‖Ring.inverse x‖^2 ∧
    ‖iteratedFDeriv ℝ 2 (@Ring.inverse R _) x‖ ≤ 2*‖Ring.inverse x‖^3 ∧
    ‖iteratedFDeriv ℝ 3 (@Ring.inverse R _) x‖ ≤ 6*‖Ring.inverse x‖^4 := by
  have h₁ : ‖fderiv ℝ (@Ring.inverse R _) x‖ ≤ ‖Ring.inverse x‖^2 := by
    rw [fderiv_inverse_eq hx, norm_neg, pow_two]
    exact ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℝ R _ _
  have h₂ := inverse_succ_bound hx 1
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,
    Nat.choose_self,Nat.cast_one,one_mul,zero_add] at h₂
  change ‖iteratedFDeriv ℝ 2 (@Ring.inverse R _) x‖ ≤
    ‖iteratedFDeriv ℝ 0 (@Ring.inverse R _) x‖ * ‖iteratedFDeriv ℝ 1 (@Ring.inverse R _) x‖ +
    ‖iteratedFDeriv ℝ 1 (@Ring.inverse R _) x‖ * ‖iteratedFDeriv ℝ 0 (@Ring.inverse R _) x‖ at h₂
  simp only [norm_iteratedFDeriv_zero,norm_iteratedFDeriv_one] at h₂
  have h₂' : ‖iteratedFDeriv ℝ 2 (@Ring.inverse R _) x‖ ≤ 2*‖Ring.inverse x‖^3 := by
    calc
      _ ≤ ‖Ring.inverse x‖ * ‖fderiv ℝ (@Ring.inverse R _) x‖ +
          ‖fderiv ℝ (@Ring.inverse R _) x‖ * ‖Ring.inverse x‖ := h₂
      _ ≤ ‖Ring.inverse x‖ * ‖Ring.inverse x‖^2 + ‖Ring.inverse x‖^2 * ‖Ring.inverse x‖ := by gcongr
      _ = _ := by ring
  have h₃ := inverse_succ_bound hx 2
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,
    Nat.choose_self,Nat.choose_one_right,Nat.cast_one,Nat.cast_ofNat,one_mul,zero_add] at h₃
  change ‖iteratedFDeriv ℝ 3 (@Ring.inverse R _) x‖ ≤
    ‖iteratedFDeriv ℝ 0 (@Ring.inverse R _) x‖ * ‖iteratedFDeriv ℝ 2 (@Ring.inverse R _) x‖ +
    2*‖iteratedFDeriv ℝ 1 (@Ring.inverse R _) x‖ * ‖iteratedFDeriv ℝ 1 (@Ring.inverse R _) x‖ +
    ‖iteratedFDeriv ℝ 2 (@Ring.inverse R _) x‖ * ‖iteratedFDeriv ℝ 0 (@Ring.inverse R _) x‖ at h₃
  simp only [norm_iteratedFDeriv_zero,norm_iteratedFDeriv_one] at h₃
  refine ⟨h₁,h₂',h₃.trans ?_⟩
  calc
    _ ≤ ‖Ring.inverse x‖*(2*‖Ring.inverse x‖^3) +
        2*‖Ring.inverse x‖^2*‖Ring.inverse x‖^2 +
        (2*‖Ring.inverse x‖^3)*‖Ring.inverse x‖ := by gcongr
    _ = _ := by ring

end
end CurrentKS.Calculus

end OAI
