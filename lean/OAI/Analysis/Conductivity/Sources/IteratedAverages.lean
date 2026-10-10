import Mathlib
import OAI.Analysis.Conductivity.Sources.CopiedEnergyAlgebra
import OAI.Analysis.Conductivity.Sources.WordTrace

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceAveragePullIter_mean_bound (N : ℕ) (h : H1) (c K : ℝ)
    (hm : ∀ ν : SourceWord,ν.length=N →
      abs (sourceMeanCLM 0 (sourceWordPull ν h)-c) ≤ K) :
    abs (sourceMeanCLM 0 (sourceAveragePullIter N h)-c) ≤ K := by
  induction N generalizing h with
  | zero => exact hm [] rfl
  | succ N ih =>
    change abs (sourceMeanCLM 0 (sourceAveragePullIter N (sourceAveragePull h))-c) ≤ K
    apply ih
    intro ν hν
    have h0 := abs_le.mp (hm (0::ν) (by simp only [List.length_cons,hν]))
    have h1 := abs_le.mp (hm (1::ν) (by simp only [List.length_cons,hν]))
    change abs (sourceMeanCLM 0 (sourceWordPull ν ((1/2:ℝ) • (childH1Pullback 0 h+childH1Pullback 1 h)))-c) ≤ K
    simp only [map_smul,map_add,smul_eq_mul]
    simp only [sourceWordPull,ContinuousLinearMap.comp_apply] at h0 h1
    apply abs_le.mpr
    constructor <;> linarith [h0.1,h0.2,h1.1,h1.2]

lemma sourceAveragePullIter_mean_eq (N : ℕ) (h : H1) (c : ℝ)
    (hm : ∀ ν : SourceWord,ν.length=N → sourceMeanCLM 0 (sourceWordPull ν h)=c) :
    sourceMeanCLM 0 (sourceAveragePullIter N h)=c := by
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  apply sourceAveragePullIter_mean_bound N h c 0
  intro ν hν
  rw [hm ν hν,sub_self,abs_zero]

lemma sourceAverageDifference_mean_bound (N : ℕ) (h : H1) (K : ℝ)
    (hm : ∀ ν : SourceWord,ν.length=N+1 → abs (sourceMeanCLM 0 (sourceWordPull ν h)) ≤ K) :
    abs (sourceMeanCLM 0 (sourceAveragePullIter N (sourceDifferencePull h))) ≤ 2*K := by
  have hh := sourceAveragePullIter_mean_bound N (sourceDifferencePull h) 0 (2*K) (by
    intro ν hν
    change abs (sourceMeanCLM 0 (sourceWordPull ν (childH1Pullback 0 h-childH1Pullback 1 h))-0) ≤ _
    rw [map_sub,map_sub,sub_zero]
    have h0 := hm (0::ν) (by simp only [List.length_cons,hν])
    have h1 := hm (1::ν) (by simp only [List.length_cons,hν])
    simp only [sourceWordPull,ContinuousLinearMap.comp_apply] at h0 h1
    exact (abs_sub _ _).trans (by linarith))
  simpa only [sub_zero] using hh

namespace BoundedRootSources
variable (r : BoundedRootSources)

lemma finiteSource_weighted_bound {u : H1} (hu : r.sourceHarmonic u) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ᵐ x∂ballMeasure,abs (weakValue u x) ≤ M)
    {f : R3 → ℝ} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hc : HasCompactSupport f)
    {L D : ℝ} (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hlip : ∀ x y,abs (f x-f y) ≤ L*dist x y)
    (hdiam : ∀ ν θ,dist (sourceWordBoundary ν θ) (sourceWordMap ν 0) ≤ D*sourceScale^ν.length)
    (N : ℕ) :
    abs (r.form (r.finiteSource N).val
      (originalMulH1CLM hf hc (u-constantH1 (sourceMeanCLM 0 u)))) ≤
        (4*M*L*D)*sourceScale^N := by
  rw [r.form_finiteSource]
  have hh := sourceAverageDifference_mean_bound N
    (originalMulH1CLM hf hc (u-constantH1 (sourceMeanCLM 0 u)))
    ((2*M*L*D)*sourceScale^(N+1)) (by
      intro ν hν
      simpa only [hν] using sourceWord_weighted_mean_bound r hu hM hb hf hc hL hD hlip hdiam ν)
  apply hh.trans
  rw [pow_succ]
  have hs : sourceScale ≤ 1 := by norm_num [sourceScale]
  have hs0 : 0 ≤ sourceScale := by norm_num [sourceScale]
  have hn : 0 ≤ (4*M*L*D)*sourceScale^N := by positivity
  nlinarith

lemma form_weighted_test (W u : H1) (c : ℝ) {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hc : HasCompactSupport f) :
    r.form W (originalMulH1CLM hf hc (u-constantH1 c))=
      ∫ x,r.coefficient x*inner ℝ (weakGradient W x)
        ((weakValue u x-c) • gradient f x+f x • weakGradient u x) ∂ballMeasure := by
  rw [r.form_apply]
  apply integral_congr_ae
  filter_upwards [originalMulH1_gradient hf hc (u-constantH1 c),
    (H1_sub_constant_spec u c).1,(H1_sub_constant_spec u c).2] with x hx hv hg
  rw [hx,hv,hg]

theorem nested_source_weighted {w : H1}
    (hw : Tendsto (fun N => (r.finiteSource N).val) atTop (𝓝 w))
    {u : H1} (hu : Harmonic r.coefficient u)
    (hb : ∃ M : ℝ,∀ᵐ x∂ballMeasure,abs (weakValue u x) ≤ M) :
    WeightedAnnihilation r.coefficient w u (sourceMeanCLM 0 u) := by
  obtain ⟨M,hb⟩ := hb
  let P := max M 0
  have hP : 0 ≤ P := le_max_right _ _
  have hb' : ∀ᵐ x∂ballMeasure,abs (weakValue u x) ≤ P := hb.mono (fun x hx => hx.trans (le_max_left _ _))
  apply weighted_annihilation_of_geometric_error r.coefficient r.coefficient_measurable.aestronglyMeasurable
    (max r.C 1) ((by norm_num : (0:ℝ) ≤ 1).trans (le_max_right _ _)) r.coefficient_bound hw hb'
    (sourceMeanCLM 0 u) sourceScale (by norm_num [sourceScale]) (by norm_num [sourceScale])
  intro f hf hc hsupp
  obtain ⟨L,hL,hlip⟩ := compact_smooth_lipschitz_bound f hf hc
  obtain ⟨D,hD,hdiam⟩ := sourceWordBoundary_radius
  refine ⟨4*P*L*D,?_⟩
  intro N
  rw [←r.form_weighted_test (r.finiteSource N).val u (sourceMeanCLM 0 u) hf hc]
  exact r.finiteSource_weighted_bound (r.harmonic_sourceHarmonic hu) hP hb' hf hc hL hD hlip hdiam N

end BoundedRootSources
end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
local instance iteratedAveragesMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance iteratedAveragesIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma sourceRootBoundary_mem_closure (θ : UnitAddTorus (Fin 2)) :
    WithLp.toLp 2 (physicalOuterBoundary 0 θ)∈closure sourceDomain := by
  rw [sourceDomain_closure_time]
  change 0 ≤ sourceCollarTime (sourceAngularCollar 0 θ)
  rw [sourceAngular_time (by norm_num)]

lemma sourceWordBoundary_mem_cell (ν : SourceWord) (θ : UnitAddTorus (Fin 2)) :
    sourceWordBoundary ν θ∈sourceWordCell ν :=
  ⟨WithLp.toLp 2 (physicalOuterBoundary 0 θ),sourceRootBoundary_mem_closure θ,rfl⟩

lemma sourceWordMean_smooth_constant (ν : SourceWord) {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) {c : ℝ}
    (hfc : ∀ θ,f (sourceWordBoundary ν θ)=c) :
    sourceMeanCLM 0 (sourceWordPull ν (smoothH1 f hf))=c := by
  rw [sourceMean_eq_integral]
  change (∫ θ,sourceWordTraceCLM ν (smoothH1 f hf) θ)=c
  rw [integral_congr_ae (sourceWordTrace_smooth ν hf)]
  simp [hfc]

lemma source_first_children_separator : ∃ f : R3 → ℝ,
    ContDiff ℝ (↑(⊤:ℕ∞)) f ∧
    (∀ ν θ,f (sourceWordBoundary (0::ν) θ)=1) ∧
    (∀ ν θ,f (sourceWordBoundary (1::ν) θ)=0) := by
  let A := sourceChildEuclidean (actualChildSign 0) '' closure sourceDomain
  let B := sourceChildEuclidean (actualChildSign 1) '' closure sourceDomain
  have hA : IsClosed A := (sourceClosure_isCompact.image (sourceChildEuclidean (actualChildSign 0)).continuous).isClosed
  have hB : IsClosed B := (sourceClosure_isCompact.image (sourceChildEuclidean (actualChildSign 1)).continuous).isClosed
  obtain ⟨f,hf0,hf1,hfb⟩ := exists_contMDiffMap_zero_one_of_isClosed
    (modelWithCornersSelf ℝ R3) hB hA (source_child_closed_disjoint (by decide : (1:Fin 2)≠0))
    (n:=↑(⊤:ℕ∞))
  refine ⟨f,f.contMDiff.contDiff,?_,?_⟩
  · intro ν θ
    exact hf1 (sourceWordCell_cons_subset 0 ν (sourceWordBoundary_mem_cell (0::ν) θ))
  · intro ν θ
    exact hf0 (sourceWordCell_cons_subset 1 ν (sourceWordBoundary_mem_cell (1::ν) θ))

namespace BoundedRootSources
variable (r : BoundedRootSources)

lemma finiteSource_separator : ∃ ψ : H1,∀ N,r.form (r.finiteSource N).val ψ=1 := by
  obtain ⟨f,hf,hf0,hf1⟩ := source_first_children_separator
  let ψ := smoothH1 f hf
  refine ⟨ψ,?_⟩
  intro N
  rw [r.form_finiteSource]
  apply sourceAveragePullIter_mean_eq N (sourceDifferencePull ψ) 1
  intro ν hν
  change sourceMeanCLM 0 (sourceWordPull ν (childH1Pullback 0 ψ-childH1Pullback 1 ψ))=1
  rw [map_sub,map_sub]
  have h0 := sourceWordMean_smooth_constant (0::ν) hf (hf0 ν)
  have h1 := sourceWordMean_smooth_constant (1::ν) hf (hf1 ν)
  change sourceMeanCLM 0 (sourceWordPull ν (childH1Pullback 0 ψ))=1 at h0
  change sourceMeanCLM 0 (sourceWordPull ν (childH1Pullback 1 ψ))=0 at h1
  rw [h0,h1,sub_zero]

lemma nested_source_nonzero {w : H1}
    (hw : Tendsto (fun N => (r.finiteSource N).val) atTop (𝓝 w)) :
    w≠0 ∧ 0<ballMeasure {x | weakValue w x≠0} := by
  obtain ⟨ψ,hψ⟩ := r.finiteSource_separator
  apply source_energy_nonzero r.coefficient r.coefficient_measurable.aestronglyMeasurable
    ((by norm_num : (0:ℝ) ≤ 1).trans (le_max_right _ _)) r.coefficient_bound hw ψ
  apply Eventually.of_forall
  intro N
  rw [←r.form_apply]
  exact hψ N

end BoundedRootSources
end ScalarConductivity

end
end

end OAI
