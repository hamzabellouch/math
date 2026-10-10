import Mathlib
import OAI.Probability.SKValue.GroundState.FiniteBranching

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
namespace SKValueG

lemma lipschitz_integrable_comp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} (hi : Integrable f μ)
    {ψ : ℝ → ℝ} {L : ℝ≥0} (hψ : LipschitzWith L ψ) : Integrable (fun ω ↦ ψ (f ω)) μ := by
  apply ((hi.norm.const_mul (L : ℝ)).add (integrable_const ‖ψ 0‖)).mono'
    (hψ.continuous.comp_aestronglyMeasurable hi.aestronglyMeasurable)
  exact Eventually.of_forall (fun ω ↦ by
    have h : ‖ψ (f ω)-ψ 0‖ ≤ (L : ℝ)*‖f ω‖ := by simpa only [sub_zero] using hψ.norm_sub_le (f ω) 0
    have htri := norm_add_le (ψ (f ω)-ψ 0) (ψ 0)
    simp only [sub_add_cancel] at htri
    change ‖ψ (f ω)‖ ≤ (L : ℝ)*‖f ω‖+‖ψ 0‖
    linarith)

noncomputable def gumbelSmooth (m : ℝ) (ψ : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ g, ψ (g/m+s) ∂gumbelLaw

lemma gumbelSmooth_lipschitz {m : ℝ} {ψ : ℝ → ℝ} {L : ℝ≥0}
    (hψ : LipschitzWith L ψ) : LipschitzWith L (gumbelSmooth m ψ) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  have hix := lipschitz_integrable_comp ((gumbel_integrable.div_const m).add (integrable_const x)) hψ
  have hiy := lipschitz_integrable_comp ((gumbel_integrable.div_const m).add (integrable_const y)) hψ
  change |(∫ g, ψ (g/m+x) ∂gumbelLaw)-(∫ g, ψ (g/m+y) ∂gumbelLaw)|≤L*|x-y|
  rw [←integral_sub (f := fun g ↦ ψ (g/m+x)) (g := fun g ↦ ψ (g/m+y)) hix hiy]
  have hbound (g : ℝ) : ‖ψ (g/m+x)-ψ (g/m+y)‖≤(L : ℝ)*|x-y| := by
    simpa only [Real.norm_eq_abs,add_sub_add_left_eq_sub] using hψ.norm_sub_le (g/m+x) (g/m+y)
  simpa using norm_integral_le_of_norm_le_const (μ := gumbelLaw) (Eventually.of_forall hbound)

lemma integral_comp_diff_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Ω → ℝ} (hi : Integrable s μ)
    {ψ : ℝ → ℝ} {L : ℝ≥0} (hψ : LipschitzWith L ψ) (c : ℝ) :
    |(∫ ω,ψ (s ω) ∂μ)-ψ c|≤(L : ℝ)*(∫ ω,|s ω-c| ∂μ) := by
  have his := lipschitz_integrable_comp hi hψ
  have hie : Integrable (fun ω ↦ |s ω-c|) μ := (hi.sub (integrable_const c)).abs
  calc
    _ = |∫ ω,ψ (s ω)-ψ c ∂μ| := by rw [integral_sub his (integrable_const _)]; simp
    _ ≤ ∫ ω,|ψ (s ω)-ψ c| ∂μ := by simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (fun ω ↦ ψ (s ω)-ψ c)
    _ ≤ ∫ ω,(L : ℝ)*|s ω-c| ∂μ := integral_mono
      (his.sub (integrable_const _)).abs (hie.const_mul _)
      (fun ω ↦ by simpa only [Real.norm_eq_abs] using hψ.norm_sub_le (s ω) c)
    _ = _ := integral_const_mul _ _

lemma scaled_gumbel_test_integral {ι : Type*} [Fintype ι] [Nonempty ι]
    (d : ι → ℝ) {m : ℝ} (hm : 0 < m) (ψ : ℝ → ℝ) (hψ : Measurable ψ) :
    (∫ z,ψ (finiteMaximum (fun i ↦ d i+z i/m)-Real.log (Fintype.card ι : ℝ)/m)
      ∂Measure.pi (fun _ : ι ↦ gumbelLaw))=
      gumbelSmooth m ψ (Real.log ((∑ i,Real.exp (m*d i))/(Fintype.card ι : ℝ))/m) := by
  have hmmax : Measurable (fun z : ι → ℝ ↦ finiteMaximum (fun i ↦ m*d i+z i)) :=
    (continuous_finiteMaximum.comp (continuous_const.add continuous_id)).measurable
  have ht : Measurable (fun y : ℝ ↦ ψ (y/m-Real.log (Fintype.card ι : ℝ)/m)) := by fun_prop
  have h := congrArg (fun μ : Measure ℝ ↦ ∫ y,ψ (y/m-Real.log (Fintype.card ι : ℝ)/m) ∂μ)
    (gumbel_max_law (fun i ↦ m*d i))
  rw [integral_map hmmax.aemeasurable ht.aestronglyMeasurable,
    integral_map (by fun_prop) ht.aestronglyMeasurable] at h
  have he (z : ι → ℝ) : finiteMaximum (fun i ↦ d i+z i/m)=
      finiteMaximum (fun i ↦ m*d i+z i)/m := by
    rw [←finiteMaximum_div_pos _ hm]
    congr 1; ext i; field_simp
  simp_rw [he]
  rw [h]
  apply integral_congr_ae
  exact Eventually.of_forall (fun g ↦ by
    apply congrArg ψ
    rw [Real.log_div (exp_sum_pos _).ne' (by positivity)]
    dsimp [logSumExp]
    ring)

theorem marked_branching_limit {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    {m : ℝ} (hm : 0 < m) (hi : Integrable (X 0) μ)
    (he : Integrable (fun ω ↦ Real.exp (m*X 0 ω)) μ)
    (hind : Pairwise (Function.onFun (fun x1 x2 ↦ x1 ⟂ᵢ[μ] x2) X))
    (hid : ∀ i,IdentDistrib (X i) (X 0) μ μ)
    {ψ : ℝ → ℝ} {L : ℝ≥0} (hψ : LipschitzWith L ψ) :
    Tendsto (fun n ↦ ∫ ω,
      (∫ z,ψ (finiteMaximum (fun i : Fin (n+1) ↦ X i ω+z i/m)-Real.log (n+1 : ℝ)/m)
        ∂Measure.pi (fun _ : Fin (n+1) ↦ gumbelLaw)) ∂μ)
      atTop (𝓝 (gumbelSmooth m ψ (Real.log (∫ ω,Real.exp (m*X 0 ω) ∂μ)/m))) := by
  let Y := fun i ω ↦ Real.exp (m*X i ω)
  have hf : Measurable (fun x : ℝ ↦ Real.exp (m*x)) := by fun_prop
  have hl : Integrable (fun ω ↦ Real.log (Y 0 ω)) μ := by
    simpa only [Y,Real.log_exp] using hi.const_mul m
  have hiY (i) : Integrable (Y i) μ := ((hid i).comp hf).integrable_iff.mpr he
  have hilogY (i) : Integrable (fun ω ↦ Real.log (Y i ω)) μ :=
    (((hid i).comp hf).comp Real.measurable_log).integrable_iff.mpr hl
  have hpY (i) : ∀ᵐ ω ∂μ,0<Y i ω := Eventually.of_forall (fun ω ↦ Real.exp_pos _)
  have hlim := log_empiricalMean_L1 Y he hl hpY
    (fun i j hij ↦ (hind hij).comp hf hf) (fun i ↦ (hid i).comp hf)
  let c := Real.log (∫ ω,Y 0 ω ∂μ)/m
  let s := fun n ω ↦ Real.log (empiricalMean Y n ω)/m
  have his (n) : Integrable (s n) μ :=
    (empiricalMean_log_integrable Y hiY hilogY hpY n).div_const m
  have herr (n) : (∫ ω,|s n ω-c| ∂μ)=
      (∫ ω,|Real.log (empiricalMean Y n ω)-Real.log (∫ ω,Y 0 ω ∂μ)| ∂μ)/m := by
    rw [←integral_div]
    apply integral_congr_ae
    exact Eventually.of_forall (fun ω ↦ by dsimp [s,c]; rw [←sub_div,abs_div,abs_of_pos hm])
  have ht : Tendsto (fun n ↦ ∫ ω,|s n ω-c| ∂μ) atTop (𝓝 0) := by
    simpa only [herr,zero_div] using hlim.div_const m
  have hg := gumbelSmooth_lipschitz (m := m) hψ
  have hb (n) := integral_comp_diff_le (his n) hg c
  have hx : Tendsto (fun n ↦ |(∫ ω,gumbelSmooth m ψ (s n ω) ∂μ)-gumbelSmooth m ψ c|)
      atTop (𝓝 0) := squeeze_zero (fun n ↦ abs_nonneg _) hb (by simpa using ht.const_mul (L : ℝ))
  have hconv : Tendsto (fun n ↦ ∫ ω,gumbelSmooth m ψ (s n ω) ∂μ) atTop
      (𝓝 (gumbelSmooth m ψ c)) := tendsto_iff_norm_sub_tendsto_zero.mpr (by
        simpa only [Real.norm_eq_abs] using hx)
  have heq (n : ℕ) : (∫ ω,(∫ z,ψ (finiteMaximum (fun i : Fin (n+1) ↦ X i ω+z i/m)-
      Real.log (n+1 : ℝ)/m) ∂Measure.pi (fun _ : Fin (n+1) ↦ gumbelLaw)) ∂μ)=
      ∫ ω,gumbelSmooth m ψ (s n ω) ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun ω ↦ by
      have hh := scaled_gumbel_test_integral (fun i : Fin (n+1) ↦ X i ω) hm ψ hψ.continuous.measurable
      rw [Fin.sum_univ_eq_sum_range (fun i ↦ Real.exp (m*X i ω))] at hh
      simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one,empiricalMean,Y,s] using hh)
  simpa only [heq,c,Y] using hconv

end SKValueG

end

end OAI
