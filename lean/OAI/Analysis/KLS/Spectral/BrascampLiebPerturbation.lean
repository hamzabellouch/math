import OAI.Analysis.KLS.Spectral.BrascampLiebCurvature
import OAI.Analysis.KLS.Convexity.HessianConvexity

namespace OAI

noncomputable section
open Set Filter Matrix
open scoped BigOperators ContDiff Topology Matrix.Norms.Elementwise

namespace LeanBlast.KLS

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (V h q : E → ℝ)

def blPerturbation (p : ℝ × E) : ℝ := V p.2 + p.1 * h p.2 + p.1 ^ 2 / 2 * q p.2

variable {V h q}

theorem contDiff_blPerturbation (hV : ContDiff ℝ ∞ V) (hh : ContDiff ℝ ∞ h)
    (hq : ContDiff ℝ ∞ q) : ContDiff ℝ ∞ (blPerturbation V h q) := by
  unfold blPerturbation
  fun_prop

theorem fderiv_blPerturbation_apply (hV : ContDiff ℝ ∞ V) (hh : ContDiff ℝ ∞ h)
    (hq : ContDiff ℝ ∞ q) (p w : ℝ × E) :
    fderiv ℝ (blPerturbation V h q) p w =
      fderiv ℝ V p.2 w.2 + p.1 * fderiv ℝ h p.2 w.2 +
        p.1 ^ 2 / 2 * fderiv ℝ q p.2 w.2 + w.1 * (h p.2 + p.1 * q p.2) := by
  have ht : HasFDerivAt (fun r : ℝ × E => r.1) (ContinuousLinearMap.fst ℝ ℝ E) p :=
    hasFDerivAt_fst
  have hx : HasFDerivAt (fun r : ℝ × E => r.2) (ContinuousLinearMap.snd ℝ ℝ E) p :=
    hasFDerivAt_snd
  have hv' := (hV.differentiable (by simp) p.2).hasFDerivAt.comp p hx
  have hh' := (hh.differentiable (by simp) p.2).hasFDerivAt.comp p hx
  have hq' := (hq.differentiable (by simp) p.2).hasFDerivAt.comp p hx
  have hd := (hv'.add (ht.mul hh')).add (((ht.pow 2).mul_const (2 : ℝ)⁻¹).mul hq')
  simp only [Pi.add_def, Pi.mul_def, Function.comp_def] at hd
  change (fderiv ℝ (fun r : ℝ × E => V r.2 + r.1 * h r.2 + r.1 ^ 2 / 2 * q r.2) p) w = _
  simp only [div_eq_mul_inv]
  rw [hd.fderiv]
  simp
  ring

theorem second_fderiv_blPerturbation_apply (hV : ContDiff ℝ ∞ V) (hh : ContDiff ℝ ∞ h)
    (hq : ContDiff ℝ ∞ q) (p w : ℝ × E) :
    fderiv ℝ (fderiv ℝ (blPerturbation V h q)) p w w =
      fderiv ℝ (fderiv ℝ V) p.2 w.2 w.2 +
      p.1 * fderiv ℝ (fderiv ℝ h) p.2 w.2 w.2 +
      p.1 ^ 2 / 2 * fderiv ℝ (fderiv ℝ q) p.2 w.2 w.2 +
      2 * w.1 * (fderiv ℝ h p.2 w.2 + p.1 * fderiv ℝ q p.2 w.2) +
      w.1 ^ 2 * q p.2 := by
  have hF := contDiff_blPerturbation hV hh hq
  have heval := (((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p).hasFDerivAt.clm_apply
    (hasFDerivAt_const w p)).fderiv
  have he : fderiv ℝ (fderiv ℝ (blPerturbation V h q)) p w w =
      fderiv ℝ (fun r => fderiv ℝ (blPerturbation V h q) r w) p w := by
    rw [heval]
    simp
  rw [he]
  simp_rw [fderiv_blPerturbation_apply hV hh hq]
  have ht : HasFDerivAt (fun r : ℝ × E => r.1) (ContinuousLinearMap.fst ℝ ℝ E) p :=
    hasFDerivAt_fst
  have hx : HasFDerivAt (fun r : ℝ × E => r.2) (ContinuousLinearMap.snd ℝ ℝ E) p :=
    hasFDerivAt_snd
  have hDV := ((((hV.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p.2).hasFDerivAt.clm_apply
    (hasFDerivAt_const w.2 p.2))).comp p hx
  have hDh := ((((hh.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p.2).hasFDerivAt.clm_apply
    (hasFDerivAt_const w.2 p.2))).comp p hx
  have hDq := ((((hq.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p.2).hasFDerivAt.clm_apply
    (hasFDerivAt_const w.2 p.2))).comp p hx
  have hh' := (hh.differentiable (by simp) p.2).hasFDerivAt.comp p hx
  have hq' := (hq.differentiable (by simp) p.2).hasFDerivAt.comp p hx
  have hd := (((hDV.add (ht.mul hDh)).add (((ht.pow 2).mul_const (2 : ℝ)⁻¹).mul hDq)).add
    ((hh'.add (ht.mul hq')).const_mul w.1))
  simp only [Pi.add_def, Pi.mul_def, Function.comp_def] at hd
  simp only [div_eq_mul_inv]
  rw [hd.fderiv]
  simp
  ring

end Calculus

theorem second_fderiv_blPerturbation_zero_pos {n : ℕ} {V h : Space n → ℝ}
    (hV : ContDiff ℝ ∞ V) (hh : ContDiff ℝ ∞ h)
    (hpos : ∀ x, (hessianMatrix V x).PosDef) {δ : ℝ} (hδ : 0 < δ)
    (x : Space n) (w : ℝ × Space n) (hw : w ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (blPerturbation V h (fun y => steinGamma V h h y + δ)))
      (0, x) w w := by
  have hq : ContDiff ℝ ∞ (fun y => steinGamma V h h y + δ) :=
    (contDiff_steinGamma_self hV hh hpos).add contDiff_const
  rw [second_fderiv_blPerturbation_apply hV hh hq]
  simp only [zero_mul, zero_pow (by norm_num : 2 ≠ 0), zero_div, add_zero]
  rw [second_fderiv_eq_hessianMatrix,
    fderiv_eq_gradient_dotProduct (hh.differentiable (by simp) x), steinGamma_self_eq_dotProduct]
  have hw' : w.1 ≠ 0 ∨ (fun i => w.2 i) ≠ 0 := by
    by_cases hs : w.1 = 0
    · right
      intro hv
      apply hw
      apply Prod.ext hs
      ext i
      exact congrFun hv i
    · exact Or.inl hs
  convert quadratic_schur_positive (hpos x) (fun i => gradient h x i) (fun i => w.2 i) hδ w.1 hw' using 1
  ring

theorem exists_blPerturbation_convex {n : ℕ} {V h : Space n → ℝ}
    (hV : ContDiff ℝ ∞ V) (hh : IsTestFunction h)
    (hpos : ∀ x, (hessianMatrix V x).PosDef) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ConvexOn ℝ (Ioo (-ε) ε ×ˢ (univ : Set (Space n)))
        (blPerturbation V h (fun x => steinGamma V h h x + δ)) := by
  let q : Space n → ℝ := steinGamma V h h
  let F : ℝ × Space n → ℝ := blPerturbation V h (fun x => q x + δ)
  let S : Set (Space n) := tsupport h ∪ tsupport q
  have hq : ContDiff ℝ ∞ q := contDiff_steinGamma_self hV hh.1 hpos
  have hqc : HasCompactSupport q := hasCompactSupport_steinGamma_self V hh
  have hS : IsCompact S := hh.2.isCompact.union hqc.isCompact
  have hF : ContDiff ℝ ∞ F := contDiff_blPerturbation hV hh.1 (hq.add contDiff_const)
  have hF2 : Continuous (fderiv ℝ (fderiv ℝ F)) :=
    ((hF.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).continuous
  let Ψ : ℝ × (Space n × (ℝ × Space n)) → ℝ :=
    fun p => fderiv ℝ (fderiv ℝ F) (p.1, p.2.1) p.2.2 p.2.2
  have hΨ : Continuous Ψ := by
    have ha : Continuous (fun p : ℝ × (Space n × (ℝ × Space n)) => (p.1, p.2.1)) := by fun_prop
    have hb : Continuous (fun p : ℝ × (Space n × (ℝ × Space n)) => p.2.2) := by fun_prop
    exact ((hF2.comp ha).clm_apply hb).clm_apply hb
  have hopen : IsOpen {p | 0 < Ψ p} := isOpen_lt continuous_const hΨ
  have hprod : ({0} : Set ℝ) ×ˢ (S ×ˢ Metric.sphere (0 : ℝ × Space n) 1) ⊆
      {p | 0 < Ψ p} := by
    rintro ⟨t, x, w⟩ ⟨ht, _, hw⟩
    have ht0 : t = 0 := by simpa using ht
    subst t
    have hw0 : w ≠ 0 := by
      intro heq
      simp [heq] at hw
    exact second_fderiv_blPerturbation_zero_pos hV hh.1 hpos hδ x w hw0
  obtain ⟨U, W, hU, _, h0U, hKW, hUW⟩ := generalized_tube_lemma
    isCompact_singleton (hS.prod (isCompact_sphere (0 : ℝ × Space n) 1)) hopen hprod
  have hzU : (0 : ℝ) ∈ U := h0U (by simp)
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzU)
  let ε : ℝ := min r 1
  have hε : 0 < ε := lt_min hr (by norm_num)
  refine ⟨ε, hε, min_le_right _ _, ?_⟩
  have hFtwo : ContDiff ℝ 2 F := hF.of_le (WithTop.coe_le_coe.mpr le_top)
  apply convexOn_of_second_fderiv_nonneg hFtwo
    ((convex_Ioo _ _).prod convex_univ)
  rintro ⟨t, x⟩ ⟨ht, _⟩ w
  by_cases hx : x ∈ S
  · by_cases hw : w = 0
    · simp [hw]
    · let u : ℝ × Space n := ‖w‖⁻¹ • w
      have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
      have hu : u ∈ Metric.sphere (0 : ℝ × Space n) 1 := by
        change dist (‖w‖⁻¹ • w) 0 = 1
        rw [dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
      have htU : t ∈ U := hrU (by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero]
        exact (abs_lt.mpr ht).trans_le (min_le_left r 1))
      have hp : 0 < Ψ (t, x, u) := hUW ⟨htU, hKW ⟨hx, hu⟩⟩
      change 0 < fderiv ℝ (fderiv ℝ F) (t, x) (‖w‖⁻¹ • w) (‖w‖⁻¹ • w) at hp
      simp only [map_smul, _root_.smul_apply, smul_eq_mul] at hp
      exact ((mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp
        ((mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp hp)).le
  · have hx' : x ∉ tsupport h ∧ x ∉ tsupport q := by simpa only [S, mem_union, not_or] using hx
    have hh0 : h =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx'.1
    have hq0 : q =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx'.2
    have hqc0 : (fun y => q y + δ) =ᶠ[𝓝 x] (fun _ => δ) := by
      filter_upwards [hq0] with y hy
      simp only [Pi.zero_apply] at hy
      simp only [hy, zero_add]
    have hh1 : fderiv ℝ h x = 0 := by simpa using hh0.fderiv_eq (𝕜 := ℝ)
    have hh2 : fderiv ℝ (fderiv ℝ h) x = 0 := by
      simpa using (hh0.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    have hq1 : fderiv ℝ (fun y => q y + δ) x = 0 := by
      simpa using hqc0.fderiv_eq (𝕜 := ℝ)
    have hq2 : fderiv ℝ (fderiv ℝ (fun y => q y + δ)) x = 0 := by
      simpa using (hqc0.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    change 0 ≤ fderiv ℝ (fderiv ℝ (blPerturbation V h (fun y => q y + δ))) (t, x) w w
    rw [second_fderiv_blPerturbation_apply hV hh.1 (hq.add contDiff_const)]
    simp only [hh1, hh2, hq1, hq2, _root_.zero_apply,
      mul_zero, add_zero, hqc0.eq_of_nhds]
    apply add_nonneg
    · rw [second_fderiv_eq_hessianMatrix]
      simpa only [star_trivial] using
        (hpos x).posSemidef.dotProduct_mulVec_nonneg (fun i => w.2 i)
    · positivity

end LeanBlast.KLS

end

end OAI
