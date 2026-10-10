import OAI.NumberTheory.CubicMoment.Estimates.MellinWeightFamily

namespace OAI

/-! Finite seminorm control of vertical Mellin transforms. This keeps the
cost of a varying smooth cutoff visible instead of hiding it in a constant. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff SchwartzMap FourierTransform
namespace CubicFirstMoment

lemma mellinLogSchwartz_seminorm_cost {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℝ → ℂ) (hW : HasCompactSupport W)
      (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W),
      (∀ u ∈ tsupport (fun v : ℝ => W (Real.exp (-v))), |u| ≤ R) →
      ∀ σ : ℝ, |σ| ≤ M →
      SchwartzMap.seminorm ℝ k n (mellinLogSchwartz W hW hpos hsm σ) ≤
        C*((Finset.Iic ((0,n) : ℕ × ℕ)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2))
          (mellinLogSchwartz W hW hpos hsm 0) := by
  let A := ∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*M^i*Real.exp (M*R)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => by positivity)
  refine ⟨1+R^k*A,by positivity,?_⟩
  intro W hW hpos hsm hsupport σ hσ
  let G := mellinLogSchwartz W hW hpos hsm 0
  let B := ((Finset.Iic ((0,n) : ℕ × ℕ)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)) G
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hg (i : ℕ) (hi : i ≤ n) (u : ℝ) : ‖iteratedFDeriv ℝ i G u‖ ≤ B := by
    apply (show ‖iteratedFDeriv ℝ i G u‖ ≤ SchwartzMap.seminorm ℝ 0 i G from by
      simpa only [pow_zero,one_mul] using SchwartzMap.le_seminorm ℝ 0 i G u).trans
    exact Seminorm.le_def.mp (Finset.le_sup (f := fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)
      (show (0,i) ∈ Finset.Iic ((0,n) : ℕ × ℕ) from by simpa using hi)) G
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro u
  by_cases hu : |u| ≤ R
  · have he : ContDiff ℝ ∞ (fun v : ℝ => Real.exp (-σ*v)) := by fun_prop
    have hd := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) he (G.smooth ⊤) u
      (n := n) (mod_cast le_top)
    have hfun : (mellinLogSchwartz W hW hpos hsm σ : ℝ → ℂ)=
        fun v => Real.exp (-σ*v) • G v := by
      ext v
      simp [G,mellinLogSchwartz_apply]
    have hexp (i : ℕ) : ‖iteratedFDeriv ℝ i (fun v : ℝ => Real.exp (-σ*v)) u‖ ≤
        M^i*Real.exp (M*R) := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_exp_const_mul]
      simp only [norm_mul,Real.norm_eq_abs,abs_pow,abs_neg,abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hσ i) _ (by positivity) (by positivity)
      apply Real.exp_le_exp.mpr
      calc
        -σ*u ≤ |-σ*u| := le_abs_self _
        _ = |σ| * |u| := by rw [abs_mul,abs_neg]
        _ ≤ M*R := mul_le_mul hσ hu (abs_nonneg _) hM
    have hb : ‖iteratedFDeriv ℝ n (mellinLogSchwartz W hW hpos hsm σ) u‖ ≤ A*B := by
      rw [hfun]
      apply hd.trans
      dsimp [A]
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _hi
      calc
        _ ≤ (n.choose i:ℝ)*(M^i*Real.exp (M*R))*B := by
          gcongr
          · exact hexp i
          · exact hg (n-i) (Nat.sub_le _ _) u
        _ = _ := by ring
    calc
      ‖u‖^k*‖iteratedFDeriv ℝ n (mellinLogSchwartz W hW hpos hsm σ) u‖ ≤ R^k*(A*B) := by
        rw [Real.norm_eq_abs]
        gcongr
      _ ≤ (1+R^k*A)*B := by nlinarith
  · have hz : iteratedFDeriv ℝ n (mellinLogSchwartz W hW hpos hsm σ) u=0 := by
      by_contra hn
      have hs := support_iteratedFDeriv_subset (𝕜 := ℝ)
        (f := mellinLogSchwartz W hW hpos hsm σ) n hn
      have hs' : u ∈ tsupport (fun v : ℝ => W (Real.exp (-v))) :=
        tsupport_smul_subset_right (fun v : ℝ => Real.exp (-σ*v))
          (fun v : ℝ => W (Real.exp (-v))) hs
      exact hu (hsupport u hs')
    rw [hz,norm_zero,mul_zero]
    positivity

def mellinVerticalCLM : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
  (SchwartzMap.compCLM ℝ (by
    simp only [div_eq_mul_inv]
    fun_prop : (fun t : ℝ => t/(2*Real.pi)).HasTemperateGrowth)
    mellin_frequency_growth).comp (SchwartzMap.fourierTransformCLM ℝ)

theorem mellinVertical_finite_seminorm {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (I : Finset (ℕ × ℕ)) :
    ∃ (J : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : ℝ → ℂ) (hW : HasCompactSupport W)
      (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W),
      (∀ u ∈ tsupport (fun v : ℝ => W (Real.exp (-v))), |u| ≤ R) →
      ∀ σ : ℝ, |σ| ≤ M →
      (I.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2))
        (mellinVerticalSchwartz W hW hpos hsm σ) ≤
      C*(J.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2))
        (mellinLogSchwartz W hW hpos hsm 0) := by
  let q : Seminorm ℝ 𝓢(ℝ,ℂ) := I.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)
  have hq : Continuous q := Seminorm.continuous_finsetSup
    (fun i _ => (schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm i)
  obtain ⟨s,C,hC,hb⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℂ)
    (q.comp mellinVerticalCLM.toLinearMap) (hq.comp mellinVerticalCLM.continuous)
  choose D hD hd using fun i : ℕ × ℕ => mellinLogSchwartz_seminorm_cost hR hM i.1 i.2
  let J := s.biUnion (fun i => Finset.Iic ((0,i.2) : ℕ × ℕ))
  let E := 1+∑ i ∈ s, D i
  have hE : 0 < E := by
    have hh := Finset.sum_nonneg (fun i (_ : i ∈ s) => (hD i).le)
    dsimp [E]
    linarith
  refine ⟨J,(C:ℝ)*E,mul_pos (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hC)) hE,?_⟩
  intro W hW hpos hsm hsupport σ hσ
  let B := (J.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2))
    (mellinLogSchwartz W hW hpos hsm 0)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hi (i : ℕ × ℕ) (his : i ∈ s) :
      SchwartzMap.seminorm ℝ i.1 i.2 (mellinLogSchwartz W hW hpos hsm σ) ≤ E*B := by
    have hsub : Finset.Iic ((0,i.2) : ℕ × ℕ) ⊆ J := by
      intro m hm
      exact Finset.mem_biUnion.mpr ⟨i,his,hm⟩
    have hsup := Seminorm.le_def.mp (show
      (Finset.Iic ((0,i.2) : ℕ × ℕ)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) ≤
        J.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) from Finset.sup_mono hsub)
      (mellinLogSchwartz W hW hpos hsm 0)
    have hDE : D i ≤ E := by
      have hh := Finset.single_le_sum (fun j (_ : j ∈ s) => (hD j).le) his
      dsimp [E]
      linarith
    exact (hd i W hW hpos hsm hsupport σ hσ).trans
      ((mul_le_mul_of_nonneg_left hsup (hD i).le).trans
        (mul_le_mul_of_nonneg_right hDE hB))
  have hsup : (s.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2))
      (mellinLogSchwartz W hW hpos hsm σ) ≤ E*B :=
    Seminorm.finset_sup_apply_le (by positivity) hi
  have ht := Seminorm.le_def.mp hb (mellinLogSchwartz W hW hpos hsm σ)
  change q (mellinVerticalSchwartz W hW hpos hsm σ) ≤
    (C:ℝ)*(s.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2))
      (mellinLogSchwartz W hW hpos hsm σ) at ht
  exact ht.trans (by
    change (C:ℝ)*_ ≤ (C:ℝ)*E*B
    nlinarith [C.coe_nonneg])

end CubicFirstMoment

end

end OAI
