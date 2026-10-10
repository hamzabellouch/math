import OAI.Probability.LatticePassage.CalibrationL2

namespace OAI

namespace CompanionFPP
open MeasureTheory Real Filter Topology

lemma convex_calibrationL2_Icc (u v : CalibrationL2) : Convex ℝ (Set.Icc u v) := by
  intro f hf g hg a b ha hb hab
  have hu₁ := (Lp.coeFn_le u f).mpr hf.1
  have hv₁ := (Lp.coeFn_le f v).mpr hf.2
  have hu₂ := (Lp.coeFn_le u g).mpr hg.1
  have hv₂ := (Lp.coeFn_le g v).mpr hg.2
  have he : ∀ᵐ ω ∂environmentLaw, (a • f + b • g) ω = a*f ω+b*g ω := by
    filter_upwards [Lp.coeFn_add (a • f) (b • g), Lp.coeFn_smul a f, Lp.coeFn_smul b g]
      with ω h₁ h₂ h₃
    simp only [h₁, Pi.add_apply, h₂, h₃, Pi.smul_apply, smul_eq_mul]
  constructor
  · apply (Lp.coeFn_le _ _).mp
    filter_upwards [hu₁,hu₂,he] with ω h₁ h₂ he
    rw [he]
    calc
      u ω = a*u ω+b*u ω := by rw [← add_mul, hab, one_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h₁ ha) (mul_le_mul_of_nonneg_left h₂ hb)
  · apply (Lp.coeFn_le _ _).mp
    filter_upwards [hv₁,hv₂,he] with ω h₁ h₂ he
    rw [he]
    calc
      _ ≤ a*v ω+b*v ω := add_le_add (mul_le_mul_of_nonneg_left h₁ ha) (mul_le_mul_of_nonneg_left h₂ hb)
      _ = v ω := by rw [← add_mul, hab, one_mul]

lemma approxL2_mem_Icc (d a b : Vertex) (n : ℕ) (x y : Vertex) :
    approxL2 d a b n x y ∈ Set.Icc (-passageL2 x y) (passageL2 x y) := by
  have he : ∀ᵐ ω ∂environmentLaw,
      -(passageL2 x y) ω ≤ (approxL2 d a b n x y) ω ∧
      (approxL2 d a b n x y) ω ≤ (passageL2 x y) ω := by
    filter_upwards [coe_approxL2 d a b n x y, coe_passageL2 x y,
      planarTargetCocycle_dominated d a b ((n+1)*(n+1)) (n+1) (by nlinarith) (by omega)] with ω hc hp hd
    rw [hc,hp]
    exact abs_le.mp (hd x y)
  constructor
  · apply (Lp.coeFn_le _ _).mp
    filter_upwards [he,Lp.coeFn_neg (passageL2 x y)] with ω h hn
    simpa only [hn, Pi.neg_apply] using h.1
  · exact (Lp.coeFn_le _ _).mp (he.mono (fun _ h => h.2))

lemma weakLimit_mem_Icc {f : ℕ → CalibrationL2} {u v B : CalibrationL2}
    {l : Filter ℕ} [l.NeBot]
    (hconv : Tendsto (fun n => toWeakSpace ℝ CalibrationL2 (f n)) l
      (𝓝 (toWeakSpace ℝ CalibrationL2 B))) (hb : ∀ n, f n ∈ Set.Icc u v) :
    B ∈ Set.Icc u v := by
  have hc := isClosed_weakImage (convex_calibrationL2_Icc u v) isClosed_Icc
  have hmem := hc.mem_of_tendsto hconv (Eventually.of_forall (fun n => ⟨f n,hb n,rfl⟩))
  obtain ⟨g,hg,he⟩ := hmem
  have heq := (toWeakSpace ℝ CalibrationL2).injective he
  exact heq ▸ hg

noncomputable def meanL2 : CalibrationL2 →L[ℝ] ℝ :=
  innerSL ℝ ((memLp_const (μ := environmentLaw) (p := 2) (1 : ℝ)).toLp (fun _ => 1))

lemma meanL2_eq_integral (f : CalibrationL2) : meanL2 f = ∫ ω, f ω ∂environmentLaw := by
  change inner ℝ _ f = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (memLp_const (μ := environmentLaw) (p := 2) (1 : ℝ))] with ω hω
  simp [RCLike.inner_apply]

lemma weak_eval_continuous (F : CalibrationL2 →L[ℝ] ℝ) :
    Continuous (fun f : WeakSpace ℝ CalibrationL2 => F ((toWeakSpace ℝ CalibrationL2).symm f)) :=
  WeakBilin.eval_continuous _ F

lemma approxL2_swap (d a b : Vertex) (n : ℕ) (x y : Vertex) :
    approxL2 d a b n x y = approxL2 d b a n x y := by
  apply Lp.ext
  filter_upwards [coe_approxL2 d a b n x y, coe_approxL2 d b a n x y] with ω h₁ h₂
  rw [h₁,h₂]
  exact planarTargetCocycle_swap d a b _ _ ω x y

theorem calibration_weak_limit_properties (d a b : Vertex)
    (B : Vertex → Vertex → CalibrationL2) (l : Filter ℕ) [l.NeBot] (hle : l ≤ atTop)
    (hconv : ∀ x y, Tendsto (fun n => toWeakSpace ℝ CalibrationL2 (approxL2 d a b n x y)) l
      (𝓝 (toWeakSpace ℝ CalibrationL2 (B x y)))) :
    (∀ x y, B x y ∈ Set.Icc (-passageL2 x y) (passageL2 x y)) ∧
    (∀ x y z, B x z = B x y + B y z) ∧
    meanL2 (B 0 d) = directionalMeanConstant d ∧
    (∀ x y, translationL2 a (B x y) = B (a+x) (a+y)) ∧
    (∀ x y, translationL2 b (B x y) = B (b+x) (b+y)) := by
  refine ⟨fun x y => weakLimit_mem_Icc (hconv x y) (fun n => approxL2_mem_Icc d a b n x y), ?_, ?_, ?_, ?_⟩
  · intro x y z
    apply (toWeakSpace ℝ CalibrationL2).injective
    have h := (hconv x y).add (hconv y z)
    simp only [← map_add, ← approxL2_add] at h
    exact tendsto_nhds_unique (hconv x z) h
  · have hm := ((weak_eval_continuous meanL2).tendsto _).comp (hconv 0 d)
    have he : ∀ n, meanL2 (approxL2 d a b n 0 d) =
        ∫ ω, calibrationApprox d a b n ω 0 d ∂environmentLaw := by
      intro n
      rw [meanL2_eq_integral]
      exact integral_congr_ae (coe_approxL2 d a b n 0 d)
    have hm' : Tendsto (fun n => meanL2 (approxL2 d a b n 0 d)) l
        (𝓝 (directionalMeanConstant d)) := by
      simp_rw [he]
      exact (calibrationApprox_mean_tendsto d a b).mono_left hle
    exact tendsto_nhds_unique hm hm'
  · intro x y
    have h := (((WeakSpace.map (translationL2 a)).continuous.tendsto _).comp (hconv x y)).sub
      (hconv (a+x) (a+y))
    have hz := (toWeakSpaceCLM ℝ CalibrationL2).continuous.tendsto 0 |>.comp
      ((approxL2_shift_tendsto d a b x y).mono_left hle)
    have he : toWeakSpace ℝ CalibrationL2 (translationL2 a (B x y) - B (a+x) (a+y)) =
        toWeakSpace ℝ CalibrationL2 0 := tendsto_nhds_unique h hz
    exact sub_eq_zero.mp ((toWeakSpace ℝ CalibrationL2).injective he)
  · intro x y
    have h := (((WeakSpace.map (translationL2 b)).continuous.tendsto _).comp (hconv x y)).sub
      (hconv (b+x) (b+y))
    have hz' := approxL2_shift_tendsto d b a x y
    simp_rw [approxL2_swap d b a] at hz'
    have hz := (toWeakSpaceCLM ℝ CalibrationL2).continuous.tendsto 0 |>.comp (hz'.mono_left hle)
    have he : toWeakSpace ℝ CalibrationL2 (translationL2 b (B x y) - B (b+x) (b+y)) =
        toWeakSpace ℝ CalibrationL2 0 := tendsto_nhds_unique h hz
    exact sub_eq_zero.mp ((toWeakSpace ℝ CalibrationL2).injective he)

theorem exists_directional_calibrationL2 (d a b : Vertex) :
    ∃ B : Vertex → Vertex → CalibrationL2,
    (∀ x y, B x y ∈ Set.Icc (-passageL2 x y) (passageL2 x y)) ∧
    (∀ x y z, B x z = B x y + B y z) ∧
    meanL2 (B 0 d) = directionalMeanConstant d ∧
    (∀ x y, translationL2 a (B x y) = B (a+x) (a+y)) ∧
    (∀ x y, translationL2 b (B x y) = B (b+x) (b+y)) := by
  obtain ⟨B,l,hl,hle,hconv⟩ := exists_calibration_weak_limit d a b
  let : l.NeBot := hl
  exact ⟨B, calibration_weak_limit_properties d a b B l hle hconv⟩

end CompanionFPP

end OAI
