import OAI.NumberTheory.CubicMoment.Estimates.MellinFiniteSeminorm

namespace OAI

/-! The two Mellin moments and the edge decay needed for prime contour
shifts are controlled by finitely many norms of the logarithmic cutoff. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff SchwartzMap
namespace CubicFirstMoment

structure PrimeMellinControl (W : ℝ → ℂ) (D : ℝ) : Prop where
  nonneg : 0 ≤ D
  decay : ∀ σ : ℝ, |σ| ≤ 2 → ∀ t : ℝ,
    (1+|t|)^2*‖mellin W ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤ D
  mass : ∀ σ : ℝ, |σ| ≤ 2 →
    (∫ t : ℝ, ‖mellin W ((σ:ℂ)+(t:ℂ)*Complex.I)‖) ≤ D
  moment : ∀ σ : ℝ, |σ| ≤ 2 →
    (∫ t : ℝ, |t|^2*‖mellin W ((σ:ℂ)+(t:ℂ)*Complex.I)‖) ≤ D

theorem primeMellinControl_finite_seminorm {R : ℝ} (hR : 0 ≤ R) :
    ∃ (J : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : ℝ → ℂ) (hW : HasCompactSupport W)
      (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W),
      (∀ u ∈ tsupport (fun v : ℝ => W (Real.exp (-v))), |u| ≤ R) →
      PrimeMellinControl W (C*(J.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2))
        (mellinLogSchwartz W hW hpos hsm 0)) := by
  let n : ℕ := (volume : Measure ℝ).integrablePower
  let I : Finset (ℕ × ℕ) := Finset.Iic ((2,0) : ℕ × ℕ) ∪ {(0,0),(n,0),(2+n,0)}
  obtain ⟨J,C,hC,hbound⟩ := mellinVertical_finite_seminorm hR (by norm_num : (0:ℝ) ≤ 2) I
  let A : ℝ := 2^n*(∫ t : ℝ, (1+‖t‖)^(-(n:ℝ)))
  have hA : 0 ≤ A := mul_nonneg (by positivity)
    (integral_nonneg (fun _ => Real.rpow_nonneg (by positivity) _))
  refine ⟨J,(4+2*A)*C,by positivity,?_⟩
  intro W hW hpos hsm hsupport
  let B := (J.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2))
    (mellinLogSchwartz W hW hpos hsm 0)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hI (σ : ℝ) (hσ : |σ| ≤ 2) := hbound W hW hpos hsm hsupport σ hσ
  have hsem (σ : ℝ) (hσ : |σ| ≤ 2) (i : ℕ × ℕ) (hi : i ∈ I) :
      SchwartzMap.seminorm ℝ i.1 i.2 (mellinVerticalSchwartz W hW hpos hsm σ) ≤ C*B :=
    (Seminorm.le_def.mp (Finset.le_sup (f := fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) hi)
      _).trans (hI σ hσ)
  have hm (σ : ℝ) (hσ : |σ| ≤ 2) (k : ℕ) (hk : (k+n,0) ∈ I) :
      (∫ t : ℝ, |t|^k*‖mellin W ((σ:ℂ)+(t:ℂ)*Complex.I)‖) ≤ 2*A*C*B := by
    let F := mellinVerticalSchwartz W hW hpos hsm σ
    have hb := SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℝ volume F k 0
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at hb
    change (∫ t : ℝ, |t|^k*‖F t‖) ≤
      A*(SchwartzMap.seminorm ℝ 0 0 F+SchwartzMap.seminorm ℝ (k+n) 0 F) at hb
    have he : (∫ t : ℝ, |t|^k*‖F t‖) =
        ∫ t : ℝ, |t|^k*‖mellin W ((σ:ℂ)+(t:ℂ)*Complex.I)‖ := by
      simp only [F,mellinVerticalSchwartz_apply]
    rw [he] at hb
    have hz := hsem σ hσ (0,0) (by simp [I])
    have hh := hsem σ hσ (k+n,0) hk
    exact hb.trans (by dsimp [F] at *; nlinarith)
  refine ⟨by positivity,?_,?_,?_⟩
  · intro σ hσ t
    have hp := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (2,0)) (k := 2) (n := 0) le_rfl le_rfl
      (mellinVerticalSchwartz W hW hpos hsm σ) t
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,mellinVerticalSchwartz_apply] at hp
    have hsub : Finset.Iic ((2,0) : ℕ × ℕ) ⊆ I := Finset.subset_union_left
    have hs := Seminorm.le_def.mp (show
      (Finset.Iic ((2,0) : ℕ × ℕ)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) ≤
        I.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) from Finset.sup_mono hsub)
      (mellinVerticalSchwartz W hW hpos hsm σ)
    have hh := hI σ hσ
    dsimp [B] at *
    nlinarith [mul_nonneg hA (mul_nonneg hC.le hB)]
  · intro σ hσ
    have h := hm σ hσ 0 (by simp [I])
    simp only [pow_zero,one_mul] at h
    dsimp [B] at *
    nlinarith
  · intro σ hσ
    have h := hm σ hσ 2 (by simp [I])
    dsimp [B] at *
    nlinarith

end CubicFirstMoment

end

end OAI
