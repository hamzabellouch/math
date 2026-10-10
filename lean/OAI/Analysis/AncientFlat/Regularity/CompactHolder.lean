import OAI.Analysis.AncientFlat.Regularity.HolderContinuity

namespace OAI
noncomputable section
open Set Filter Topology Metric
open scoped ContDiff NNReal
namespace ParabolicLocalization
open ParabolicInterior
variable {V : Type} {E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
lemma norm_pair_sub_le_pdist (p q : V × ℝ) (hd : pdist p q≤1) : ‖p-q‖≤pdist p q := by
  have ht : |p.2-q.2|^((1:ℝ)/4)≤1 := (le_add_of_nonneg_left (norm_nonneg _)).trans hd
  have htr : |p.2-q.2|≤1 := by
    by_contra h
    have hh := Real.one_lt_rpow (lt_of_not_ge h) (by norm_num : (0:ℝ)<1/4)
    linarith
  have htime := Real.self_le_rpow_of_le_one (abs_nonneg (p.2-q.2)) htr (by norm_num : (1:ℝ)/4≤1)
  rw [Prod.norm_def]
  exact max_le (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _))
    (by simpa only [Real.norm_eq_abs, Prod.snd_sub, pdist] using htime.trans (le_add_of_nonneg_left (norm_nonneg (p.1-q.1))))
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedSpace ℝ E] in
lemma holder_of_bounded_lipschitz (α B : ℝ) (hα : 0<α) (hα1 : α≤1) (hB : 0≤B)
    (L : ℝ≥0) (f : V × ℝ → E) (hf : LipschitzWith L f)
    (hb : ∀ p, ‖f p‖≤B) : HolderBound α univ f (2*B+L) := by
  refine ⟨fun p _ => (hb p).trans (by linarith [L.coe_nonneg] : B≤2*B+(L:ℝ)),?_⟩
  intro p _ q _
  have hd : 0≤pdist p q := pdist_nonneg p q
  by_cases h : pdist p q≤1
  · have hpow := Real.self_le_rpow_of_le_one hd h hα1
    have hl := hf.norm_sub_le p q
    calc
      _≤(L:ℝ)*‖p-q‖ := hl
      _≤(L:ℝ)*pdist p q := mul_le_mul_of_nonneg_left (norm_pair_sub_le_pdist p q h) L.coe_nonneg
      _≤(L:ℝ)*pdist p q^α := mul_le_mul_of_nonneg_left hpow L.coe_nonneg
      _≤_ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hd _)
  · have hpow : 1≤pdist p q^α := Real.one_le_rpow (le_of_not_ge h) hα.le
    have hb' := (norm_sub_le (f p) (f q)).trans (add_le_add (hb p) (hb q))
    nlinarith [mul_nonneg L.coe_nonneg (Real.rpow_nonneg hd α),mul_nonneg hB (sub_nonneg.mpr hpow)]
lemma compact_lipschitz {W G : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (f : W → G)
    (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    ∃ L : ℝ≥0, LipschitzWith L f := by
  obtain ⟨B,hB⟩ := (hs.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv (by norm_num))
  let L : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  refine ⟨L,lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ) (hf.differentiable (by norm_num)) ?_⟩
  intro p
  change ‖fderiv ℝ f p‖₊≤L
  exact_mod_cast (hB p).trans (le_max_left B 0)

omit [FiniteDimensional ℝ V] in
lemma compact_contDiff_holder (α : ℝ) (hα : 0<α) (hα1 : α≤1)
    (f : V × ℝ → E) (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    ∃ C : ℝ, 0<C ∧ HolderBound α univ f C := by
  obtain ⟨B,hB⟩ := hs.exists_bound_of_continuous hf.continuous
  obtain ⟨L,hL⟩ := compact_lipschitz f hf hs
  have hh := holder_of_bounded_lipschitz α (max B 0) hα hα1 (le_max_right _ _) L f hL
    (fun p => (hB p).trans (le_max_left _ _))
  refine ⟨2*max B 0+L+1,by positivity,hh.mono (by linarith)⟩
end ParabolicLocalization

end

end OAI
