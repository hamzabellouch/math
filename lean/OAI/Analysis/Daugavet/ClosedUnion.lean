import OAI.Analysis.Daugavet.Stages

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace ExactModuli.KW

lemma constructedSpace_infiniteDimensional : ¬ FiniteDimensional ℝ constructedSpace := by
  intro hfinite
  let : FiniteDimensional ℝ constructedSpace := hfinite
  have hstrict : StrictMono (fun n => Module.finrank ℝ (stageSpace n)) := by
    intro n m hnm
    exact Submodule.finrank_lt_finrank_of_lt (stageSpace_strictMono hnm)
  have hle := hstrict.id_le (Module.finrank ℝ constructedSpace + 1)
  have hbound := Submodule.finrank_mono (stageSpace_le_constructed (Module.finrank ℝ constructedSpace + 1))
  change Module.finrank ℝ constructedSpace + 1 ≤ Module.finrank ℝ (stageSpace (Module.finrank ℝ constructedSpace + 1)) at hle
  omega

lemma constructed_union_approx {x : KWL1} (hx : x ∈ constructedSpace)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ∃ y ∈ stageSpace n, ‖x-y‖ < ε := by
  have hx' : x ∈ closure (unionSpace : Set KWL1) := hx
  obtain ⟨y,hy,hxy⟩ := Metric.mem_closure_iff.mp hx' ε hε
  obtain ⟨n,hn⟩ := (Submodule.mem_iSup_of_directed stageSpace stageSpace_mono.directed_le).mp hy
  exact ⟨max n N, le_max_right _ _, y, stageSpace_mono (le_max_left _ _) hn, by simpa [dist_eq_norm] using hxy⟩

lemma constructed_ball_approx {x : KWL1} (hx : x ∈ constructedSpace) (hxn : ‖x‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ∃ y ∈ stageSpace n, ‖y‖ ≤ 1 ∧ ‖x-y‖ < ε := by
  obtain ⟨n,hn,y,hy,hxy⟩ := constructed_union_approx hx (half_pos hε) N
  refine ⟨n,hn,normalizeL1 y,normalizeL1_mem _ hy,normalizeL1_norm _,?_⟩
  exact (normalizeL1_approx x y hxn).trans_lt (by linarith)

lemma constructed_sphere_approx {x : KWL1} (hx : x ∈ constructedSpace) (hxn : ‖x‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ∃ y ∈ stageSpace n, ‖y‖ = 1 ∧ ‖x-y‖ < ε := by
  obtain ⟨n,hn,y,hy,hxy⟩ := constructed_union_approx hx (lt_min (half_pos hε) (by norm_num : (0:ℝ)<1/2)) N
  have hy0 : y ≠ 0 := by
    intro hy0
    rw [hy0, sub_zero, hxn] at hxy
    have hh := hxy.trans_le (min_le_right _ _)
    norm_num at hh
  refine ⟨n,hn,‖y‖⁻¹ • y,(stageSpace n).smul_mem _ hy,norm_smul_inv_norm hy0,?_⟩
  exact (sphere_normalize_approx x y hxn hy0).trans_lt (by linarith [hxy.trans_le (min_le_left _ _)])

lemma stageError_tendsto : Tendsto stageError atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).mul_const (1/2:ℝ)
  change Tendsto (fun n : ℕ => (1/2:ℝ)^(n+1)) atTop (𝓝 0)
  simpa only [zero_mul, pow_succ] using h

lemma stageError_eventually_small {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, stageError n < ε :=
  eventually_atTop.mp (stageError_tendsto.eventually_lt_const hε)

/-- The exact telescoping finite-stage error; the remaining tail equals 2 h_b. -/
lemma stage_ball_control (b a : ℕ) (hba : b ≤ a) :
    ∀ g ∈ stageSpace a, ‖g‖ ≤ 1 → ∃ ψ ∈ stageSpace b, ‖ψ‖ ≤ 1 ∧
      measureDistance kwMeasure g ψ ≤ 2 * stageError b - 2 * stageError a := by
  induction a, hba using Nat.le_induction with
  | base =>
    intro g hg hgn
    exact ⟨g,hg,hgn,by simp [measureDistance_self]⟩
  | succ a hba ih =>
    intro g hg hgn
    obtain ⟨y,hy,hyn,hgy⟩ := (step_estimates a).wholeBall g hg hgn
    obtain ⟨ψ,hψ,hψn,hyψ⟩ := ih y hy hyn
    refine ⟨ψ,hψ,hψn,?_⟩
    have ht := measureDistance_triangle g y ψ
    rw [stageError_succ]
    linarith

lemma stage_ball_control_uniform (b a : ℕ) (g : KWL1) (hg : g ∈ stageSpace a) (hgn : ‖g‖ ≤ 1) :
    ∃ ψ ∈ stageSpace b, ‖ψ‖ ≤ 1 ∧ measureDistance kwMeasure g ψ ≤ 2 * stageError b := by
  by_cases hba : b ≤ a
  · obtain ⟨ψ,hψ,hψn,hgψ⟩ := stage_ball_control b a hba g hg hgn
    exact ⟨ψ,hψ,hψn,hgψ.trans (by linarith [stageError_pos a])⟩
  · exact ⟨g,stageSpace_mono (le_of_not_ge hba) hg,hgn,by rw [measureDistance_self]; exact (mul_pos (by norm_num) (stageError_pos b)).le⟩

lemma constructed_ball_stage_control (b : ℕ) (x : KWL1) (hx : x ∈ constructedSpace) (hxn : ‖x‖ ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ ψ ∈ stageSpace b, ‖ψ‖ ≤ 1 ∧ measureDistance kwMeasure x ψ ≤ 2 * stageError b + η := by
  obtain ⟨a,ha,y,hy,hyn,hxy⟩ := constructed_ball_approx hx hxn (sq_pos_of_pos hη) 0
  obtain ⟨ψ,hψ,hψn,hyψ⟩ := stage_ball_control_uniform b a y hy hyn
  refine ⟨ψ,hψ,hψn,?_⟩
  have hd := measureDistance_le_of_norm_sub_lt_sq x y hη hxy
  have ht := measureDistance_triangle x y ψ
  linarith

lemma constructedSpace_measurePrecompact : MeasurePrecompactBall kwMeasure constructedSpace := by
  classical
  intro ε hε
  obtain ⟨b,hb⟩ := stageError_eventually_small (show 0 < ε/8 by positivity)
  have hb' := hb b le_rfl
  obtain ⟨t,hts,htfin,hcover⟩ := (isCompact_closedBall (0 : stageSpace b) 1).finite_cover_balls
    (sq_pos_of_pos (show 0 < ε/4 by positivity))
  refine ⟨htfin.toFinset.image (fun z : stageSpace b => (z : KWL1)), ?_⟩
  intro x hxn
  obtain ⟨ψ,hψ,hψn,hxψ⟩ := constructed_ball_stage_control b x x.property hxn (show 0 < ε/4 by positivity)
  have hcov := hcover (show (⟨ψ,hψ⟩ : stageSpace b) ∈ Metric.closedBall 0 1 by simpa using hψn)
  simp only [Set.mem_iUnion, Metric.mem_ball, dist_eq_norm] at hcov
  obtain ⟨z,hz,hψz⟩ := hcov
  refine ⟨(z : KWL1),Finset.mem_image.mpr ⟨z,htfin.mem_toFinset.mpr hz,rfl⟩,?_⟩
  have hd := measureDistance_le_of_norm_sub_lt_sq ψ (z : KWL1) (show 0 < ε/4 by positivity) hψz
  have ht := measureDistance_triangle (x : KWL1) ψ (z : KWL1)
  linarith

end ExactModuli.KW

end

end OAI
