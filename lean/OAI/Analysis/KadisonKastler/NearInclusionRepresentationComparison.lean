import OAI.Analysis.KadisonKastler.NearInclusionDistance
import OAI.Analysis.KadisonKastler.NormalRepresentationRange

namespace OAI

/-! # Transporting near inclusions through a uniform comparison of representations -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M N : VonNeumannAlgebra H} {P Q : VonNeumannAlgebra K}

theorem representation_symm_norm_le
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra P) (x : Algebra P) : ‖e.symm x‖ ≤ ‖x‖ :=
  NonUnitalStarAlgHom.norm_apply_le e.symm x

theorem exists_approx_of_representation_comparison
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra P) (f : Algebra N ≃⋆ₐ[ℂ] Algebra Q)
    {C γ : ℝ}
    (hcomp : ∀ (a : Algebra M) (b : Algebra N), ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      ‖(e a).val - (f b).val‖ ≤ C + ‖a.val - b.val‖)
    (hMN : NearInclusion M N γ) (x : K →L[ℂ] K) (hx : x ∈ unitBall P) :
    ∃ y ∈ Q, ‖x - y‖ < C + 2 * γ := by
  let a : Algebra M := e.symm ⟨x, hx.1⟩
  have ha : ‖a‖ ≤ 1 := (representation_symm_norm_le e ⟨x, hx.1⟩).trans hx.2
  obtain ⟨y, hy, hay⟩ := exists_unitBall_approx_of_nearInclusion hMN ⟨a.property, ha⟩
  let b : Algebra N := ⟨y, hy.1⟩
  refine ⟨(f b).val, (f b).property, ?_⟩
  have he : (e a).val = x := congrArg (fun t : Algebra P => t.val) (e.apply_symm_apply ⟨x, hx.1⟩)
  calc
    ‖x - (f b).val‖ = ‖(e a).val - (f b).val‖ :=
      congrArg (fun T : K →L[ℂ] K => ‖T - (f b).val‖) he.symm
    _ ≤ C + ‖a.val - b.val‖ := hcomp a b ha hy.2
    _ < C + 2 * γ := by change C + ‖a.val - y‖ < _; linarith

theorem nearInclusion_of_representation_comparison
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra P) (f : Algebra N ≃⋆ₐ[ℂ] Algebra Q)
    {C γ : ℝ} (hγ : 0 < γ)
    (hcomp : ∀ (a : Algebra M) (b : Algebra N), ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      ‖(e a).val - (f b).val‖ ≤ C + ‖a.val - b.val‖)
    (hMN : NearInclusion M N γ) : NearInclusion P Q (C + 2 * γ) := by
  obtain ⟨δ, hδ, happrox⟩ := hMN
  let r := (max 0 δ + γ) / 2
  have hr : r < γ := by dsimp [r]; linarith [max_lt hγ hδ]
  have hδr : δ < r := by
    have h0 := le_max_right (0 : ℝ) δ
    have h1 := max_lt hγ hδ
    dsimp [r]
    linarith
  have hnear : NearInclusion M N r := ⟨δ, hδr, happrox⟩
  refine ⟨C + 2 * r, by linarith, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := exists_approx_of_representation_comparison e f hcomp hnear x hx
  exact (Metric.infDist_le_dist_of_mem hy).trans (by simpa only [dist_eq_norm] using hxy.le)

theorem reverse_nearInclusion_of_representation_comparison
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra P) (f : Algebra N ≃⋆ₐ[ℂ] Algebra Q)
    {C γ : ℝ} (hγ : 0 < γ)
    (hcomp : ∀ (a : Algebra M) (b : Algebra N), ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      ‖(e a).val - (f b).val‖ ≤ C + ‖a.val - b.val‖)
    (hNM : NearInclusion N M γ) : NearInclusion Q P (C + 2 * γ) := by
  apply nearInclusion_of_representation_comparison f e hγ _ hNM
  intro b a hb ha
  simpa only [norm_sub_rev] using hcomp a b ha hb

end

end KadisonKastler

end OAI
