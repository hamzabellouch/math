import Mathlib
import OAI.Geometry.BallPacking.Degree.HomotopyFlux

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.Degree

section
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
variable {d k : ℕ}

lemma supported_indicator_smooth {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {S K : Set (CoordinateSpace d)} (hS : IsOpen S) (hK : IsClosed K) (hKS : K⊆S)
    {f : CoordinateSpace d → Z} (hf : ContDiffOn ℝ ∞ f S)
    (hz : ∀ x∈S,x∉K →f x=0) : ContDiff ℝ ∞ (S.indicator f) := by
  classical
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x∈S
  · apply (hf.contDiffAt (hS.mem_nhds hx)).congr_of_eventuallyEq
    filter_upwards [hS.mem_nhds hx] with y hy
    exact indicator_of_mem hy _
  · apply (contDiffAt_const (c := (0:Z))).congr_of_eventuallyEq
    filter_upwards [hK.isOpen_compl.mem_nhds (fun h => hx (hKS h))] with y hy
    by_cases hys : y∈S
    · rw [indicator_of_mem hys,hz y hys hy]
    · exact indicator_of_notMem hys _

lemma extDeriv_supported_indicator
    {S K : Set (CoordinateSpace d)} (hS : IsOpen S) (hK : IsClosed K) (hKS : K⊆S)
    {w : CoordinateSpace d → CoordinateSpace d [⋀^Fin k]→L[ℝ] ℝ}
    (hz : ∀ x∈S,x∉K →w x=0) : extDeriv (S.indicator w)=S.indicator (extDeriv w) := by
  classical
  funext x
  by_cases hx : x∈S
  · have he : S.indicator w =ᶠ[𝓝 x] w := by
      filter_upwards [hS.mem_nhds hx] with y hy
      exact indicator_of_mem hy _
    rw [he.extDeriv_eq,indicator_of_mem hx]
  · have he : S.indicator w =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hK.isOpen_compl.mem_nhds (fun h => hx (hKS h))] with y hy
      by_cases hys : y∈S
      · rw [indicator_of_mem hys,hz y hys hy]
      · exact indicator_of_notMem hys _
    rw [he.extDeriv_eq,indicator_of_notMem hx]
    ext v
    rw [extDeriv_apply (differentiableAt_const _)]
    simp

variable {M I : Type*} [TopologicalSpace M] [T2Space M]
  {a : SignedSmoothAtlas M I d} (α : AtlasForm a k)

omit [T2Space M] in
lemma AtlasForm.supporting_chart_compact [T2Space M] {K : Set M} (hK : IsCompact K)
    (i : I) (hi : K⊆(a.chart i).source) : IsCompact (a.chart i '' K) :=
  hK.image_of_continuousOn ((a.chart i).continuousOn.mono hi)

omit [T2Space M] in
lemma AtlasForm.supporting_chart_zero [T2Space M] {K : Set M} (hα : α.SupportedIn K)
    (i : I) {q : CoordinateSpace d} (hq : q∈(a.chart i).target) (hqn : q∉a.chart i '' K) :
    α.form i q=0 :=
  hα i q hq (fun hk => hqn ⟨_,hk,(a.chart i).right_inv hq⟩)

def AtlasForm.chartExtension (i : I) :
    CoordinateSpace d → CoordinateSpace d [⋀^Fin k]→L[ℝ] ℝ :=
  (a.chart i).target.indicator (α.form i)

lemma AtlasForm.chartExtension_zero {K : Set M} (hα : α.SupportedIn K)
    (i : I) {q : CoordinateSpace d} (hqn : q∉a.chart i '' K) : α.chartExtension i q=0 := by
  classical
  by_cases hq : q∈(a.chart i).target
  · rw [chartExtension,indicator_of_mem hq]
    exact α.supporting_chart_zero hα i hq hqn
  · exact indicator_of_notMem hq _

lemma AtlasForm.chartExtension_smooth {K : Set M} (hK : IsCompact K)
    (hα : α.SupportedIn K) (i : I) (hi : K⊆(a.chart i).source) :
    ContDiff ℝ ∞ (α.chartExtension i) := by
  apply supported_indicator_smooth (a.chart i).open_target (AtlasForm.supporting_chart_compact (a := a) hK i hi).isClosed
  · rintro _ ⟨x,hx,rfl⟩
    exact (a.chart i).map_source (hi hx)
  · exact α.smooth i
  · exact fun q hq hn => α.supporting_chart_zero hα i hq hn

lemma AtlasForm.chartExtension_support {K : Set M} (hK : IsCompact K)
    (hα : α.SupportedIn K) (i : I) (hi : K⊆(a.chart i).source) :
    HasCompactSupport (α.chartExtension i) :=
  HasCompactSupport.intro (AtlasForm.supporting_chart_compact (a := a) hK i hi) (fun _ h => α.chartExtension_zero hα i h)

lemma AtlasForm.exterior_chartExtension {K : Set M} (hK : IsCompact K)
    (hα : α.SupportedIn K) (i : I) (hi : K⊆(a.chart i).source) :
    α.exterior.chartExtension i=extDeriv (α.chartExtension i) := by
  symm
  apply extDeriv_supported_indicator (a.chart i).open_target (AtlasForm.supporting_chart_compact (a := a) hK i hi).isClosed
  · rintro _ ⟨x,hx,rfl⟩
    exact (a.chart i).map_source (hi hx)
  · exact fun q hq hn => α.supporting_chart_zero hα i hq hn

def AtlasForm.chartMass {a : SignedSmoothAtlas M I d} (α : AtlasForm a d) (i : I) : ℝ :=
  ∫ q,a.sign i*α.chartExtension i q coordinateVector

lemma AtlasForm.chart_coefficient_integrable {a : SignedSmoothAtlas M I d}
    (α : AtlasForm a d) {K : Set M} (hK : IsCompact K)
    (hα : α.SupportedIn K) (i : I) (hi : K⊆(a.chart i).source) :
    Integrable (fun q => a.sign i*α.chartExtension i q coordinateVector) := by
  have hc : Continuous (fun q => a.sign i*α.chartExtension i q coordinateVector) :=
    continuous_const.mul ((ContinuousAlternatingMap.apply ℝ _ ℝ coordinateVector).continuous.comp
      (α.chartExtension_smooth hK hα i hi).continuous)
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (AtlasForm.supporting_chart_compact (a := a) hK i hi)
  intro q hq
  rw [α.chartExtension_zero hα i hq]
  exact mul_zero _

lemma AtlasForm.chartMass_exterior_zero {a : SignedSmoothAtlas M I (k+1)}
    (α : AtlasForm a k) {K : Set M} (hK : IsCompact K)
    (hα : α.SupportedIn K) (i : I) (hi : K⊆(a.chart i).source) :
    α.exterior.chartMass i=0 := by
  unfold chartMass
  rw [α.exterior_chartExtension hK hα i hi,integral_const_mul,
    compact_euclidean_stokes ((α.chartExtension_smooth hK hα i hi).of_le (by
      exact WithTop.coe_le_coe.mpr le_top)) (α.chartExtension_support hK hα i hi),mul_zero]


end
section
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
variable {M I : Type*} [TopologicalSpace M] [T2Space M] {d k : ℕ}
  {a : SignedSmoothAtlas M I d}

lemma AtlasForm.chartMass_eq_compact_integral (α : AtlasForm a d)
    {K : Set M} (hK : IsCompact K) (hα : α.SupportedIn K) (i : I) (hi : K⊆(a.chart i).source) :
    α.chartMass i=∫q in a.chart i '' K,a.sign i*α.form i q coordinateVector := by
  unfold chartMass
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero (s := a.chart i '' K)]
  · apply setIntegral_congr_fun
    · exact (hK.image_of_continuousOn ((a.chart i).continuousOn.mono hi)).measurableSet
    · intro q hq
      obtain ⟨x,hx,rfl⟩ := hq
      dsimp only
      rw [chartExtension,indicator_of_mem ((a.chart i).map_source (hi hx))]
  · intro q hq
    rw [α.chartExtension_zero hα i hq]
    exact mul_zero _

lemma AtlasForm.chartMass_change (α : AtlasForm a d)
    {K : Set M} (hK : IsCompact K) (hα : α.SupportedIn K)
    (i j : I) (hi : K⊆(a.chart i).source) (hj : K⊆(a.chart j).source) :
    α.chartMass i=α.chartMass j := by
  rw [α.chartMass_eq_compact_integral hK hα i hi,α.chartMass_eq_compact_integral hK hα j hj]
  apply topForm_chartMass_change (a.chart j) (a.chart i) hK hi hj (a.transition_smooth i j)
  · rintro q ⟨x,hx,rfl⟩
    apply α.compatible i j
    exact ⟨(a.chart i).map_source (hi hx),by
      change (a.chart i).symm ((a.chart i) x)∈(a.chart j).source
      rw [(a.chart i).left_inv (hi hx)]; exact hj hx⟩
  · rintro q ⟨x,hx,rfl⟩
    apply a.orientation i j
    exact ⟨(a.chart i).map_source (hi hx),by
      change (a.chart i).symm ((a.chart i) x)∈(a.chart j).source
      rw [(a.chart i).left_inv (hi hx)]; exact hj hx⟩

omit [T2Space M] in
lemma AtlasForm.chartMass_sum [T2Space M] {J : Type*} [Fintype J]
    (Ω : AtlasForm a d) (β : J → AtlasForm a d) (i : I)
    (he : ∀ q∈(a.chart i).target,Ω.form i q=∑j,(β j).form i q)
    (hi : ∀ j,Integrable (fun q => a.sign i*(β j).chartExtension i q coordinateVector)) :
    Ω.chartMass i=∑j,(β j).chartMass i := by
  classical
  change (∫q,a.sign i*Ω.chartExtension i q coordinateVector)=∑j,∫q,a.sign i*(β j).chartExtension i q coordinateVector
  rw [←integral_finsetSum _ (fun j _ => hi j)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  by_cases hq : q∈(a.chart i).target
  · simp only [AtlasForm.chartExtension,indicator_of_mem hq,he q hq]
    rw [ContinuousAlternatingMap.sum_apply,Finset.mul_sum]
  · simp only [AtlasForm.chartExtension,indicator_of_notMem hq]
    change a.sign i*0=∑j,a.sign i*0
    simp

variable [Fintype I]
structure AtlasPartition (a : SignedSmoothAtlas M I d) (K : Set M) where
  weight : I → M → ℝ
  smooth : ∀ i j,ContDiffOn ℝ ∞ (weight i ∘ (a.chart j).symm) (a.chart j).target
  sum_one : ∀ x∈K,∑i,weight i x=1
  subordinate : ∀ i,tsupport (weight i)⊆(a.chart i).source

namespace AtlasPartition
variable {K : Set M} (p : AtlasPartition a K)

def mass (Ω : AtlasForm a d) : ℝ :=
  ∑i,(Ω.smul (p.weight i) (p.smooth i)).chartMass i

omit [T2Space M] in
lemma smul_sum [T2Space M] (Ω : AtlasForm a k) (hΩ : Ω.SupportedIn K) (i : I) {q : CoordinateSpace d}
    (hq : q∈(a.chart i).target) :
    ∑j,(Ω.smul (p.weight j) (p.smooth j)).form i q=Ω.form i q := by
  change (∑j,p.weight j ((a.chart i).symm q) • Ω.form i q)=Ω.form i q
  rw [←Finset.sum_smul]
  by_cases hx : (a.chart i).symm q∈K
  · rw [p.sum_one _ hx,one_smul]
  · rw [hΩ i q hq hx,smul_zero]

lemma mass_eq_chartMass {L : Set M} (hL : IsCompact L) (hLK : L⊆K)
    (Ω : AtlasForm a d) (hΩ : Ω.SupportedIn L)
    (j : I) (hj : L⊆(a.chart j).source) : p.mass Ω=Ω.chartMass j := by
  classical
  let D : I → AtlasForm a d := fun i => Ω.smul (p.weight i) (p.smooth i)
  let C : I → Set M := fun i => L∩tsupport (p.weight i)
  have hC (i : I) : IsCompact (C i) := hL.inter_right (isClosed_tsupport _)
  have hD (i : I) : (D i).SupportedIn (C i) := Ω.smul_supported _ _ hΩ
  have hci (i : I) : C i⊆(a.chart i).source := fun _ h => p.subordinate i h.2
  have hcj (i : I) : C i⊆(a.chart j).source := fun _ h => hj h.1
  have hm (i : I) : (D i).chartMass i=(D i).chartMass j :=
    (D i).chartMass_change (hC i) (hD i) i j (hci i) (hcj i)
  change (∑i,(D i).chartMass i)=_
  simp_rw [hm]
  symm
  apply Ω.chartMass_sum D j
  · intro q hq
    have hΩK : Ω.SupportedIn K := fun i q hq hn => hΩ i q hq (fun hx => hn (hLK hx))
    exact (p.smul_sum Ω hΩK j hq).symm
  · exact fun i => (D i).chart_coefficient_integrable (hC i) (hD i) j (hcj i)

end AtlasPartition

end
section
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
variable {M I : Type*} [TopologicalSpace M] [T2Space M] [Fintype I] {d k : ℕ}
  {a : SignedSmoothAtlas M I d} {K : Set M}

lemma AtlasPartition.mass_sum (p : AtlasPartition a K) (hK : IsCompact K)
    {J : Type*} [Fintype J] (Ω : AtlasForm a d) (β : J → AtlasForm a d)
    (hβ : ∀ j,(β j).SupportedIn K)
    (he : ∀ i q,q∈(a.chart i).target → Ω.form i q=∑j,(β j).form i q) :
    p.mass Ω=∑j,p.mass (β j) := by
  classical
  unfold mass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply AtlasForm.chartMass_sum _ (fun j => (β j).smul (p.weight i) (p.smooth i)) i
  · intro q hq
    change p.weight i ((a.chart i).symm q) • Ω.form i q=
      ∑j,p.weight i ((a.chart i).symm q) • (β j).form i q
    rw [he i q hq,Finset.smul_sum]
  · intro j
    exact ((β j).smul (p.weight i) (p.smooth i)).chart_coefficient_integrable
      (hK.inter_right (isClosed_tsupport _)) ((β j).smul_supported _ _ (hβ j)) i
      (fun _ h => p.subordinate i h.2)

lemma extDeriv_fintype_sum {J : Type*} [Fintype J]
    (β : J → CoordinateSpace d → CoordinateSpace d [⋀^Fin k]→L[ℝ] ℝ)
    (q : CoordinateSpace d) (hβ : ∀ j,DifferentiableAt ℝ (β j) q) :
    extDeriv (fun y => ∑j,β j y) q=∑j,extDeriv (β j) q := by
  classical
  simp only [extDeriv,fderiv_fun_sum (fun j _ => hβ j)]
  exact map_sum (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ _ ℝ) _ _

theorem AtlasPartition.compact_stokes {a : SignedSmoothAtlas M I (k+1)}
    (p : AtlasPartition a K) (hK : IsCompact K)
    (α : AtlasForm a k) (hα : α.SupportedIn K) : p.mass α.exterior=0 := by
  classical
  let β : I → AtlasForm a k := fun i => α.smul (p.weight i) (p.smooth i)
  let L : I → Set M := fun i => K∩tsupport (p.weight i)
  have hL (i : I) : IsCompact (L i) := hK.inter_right (isClosed_tsupport _)
  have hβ (i : I) : (β i).SupportedIn (L i) := α.smul_supported _ _ hα
  have hLi (i : I) : L i⊆(a.chart i).source := fun _ h => p.subordinate i h.2
  have hdβ (i : I) : (β i).exterior.SupportedIn K := by
    have hs := (β i).exterior_supported (hL i).isClosed (hβ i)
    exact fun j q hq hn => hs j q hq (fun h => hn h.1)
  have hsum (i : I) (q : CoordinateSpace (k+1)) (hq : q∈(a.chart i).target) :
      α.exterior.form i q=∑j,(β j).exterior.form i q := by
    have he : α.form i =ᶠ[𝓝 q] fun y => ∑j,(β j).form i y := by
      filter_upwards [(a.chart i).open_target.mem_nhds hq] with y hy
      exact (p.smul_sum α hα i hy).symm
    change extDeriv (α.form i) q=∑j,extDeriv ((β j).form i) q
    rw [he.extDeriv_eq]
    apply extDeriv_fintype_sum
    intro j
    exact (((β j).smooth i).contDiffAt ((a.chart i).open_target.mem_nhds hq)).differentiableAt (by simp)
  rw [p.mass_sum hK α.exterior (fun j => (β j).exterior) hdβ hsum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [p.mass_eq_chartMass (hL i) inter_subset_left (β i).exterior
    ((β i).exterior_supported (hL i).isClosed (hβ i)) i (hLi i)]
  exact (β i).chartMass_exterior_zero (hL i) (hβ i) i (hLi i)


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {A B Z : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] {k : ℕ}

def alternationCLM : (ContinuousMultilinearMap ℝ (fun _ : Fin k => A) ℝ) →L[ℝ]
    (A [⋀^Fin k]→L[ℝ] ℝ) where
  toFun := ContinuousMultilinearMap.alternatization
  map_add' := map_add _
  map_smul' r f := by
    ext v
    simp only [RingHom.id_apply,ContinuousMultilinearMap.alternatization_apply_apply,
      smul_apply,ContinuousAlternatingMap.smul_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    exact smul_comm _ _ _
  cont := by
    rw [ContinuousAlternatingMap.isEmbedding_toContinuousMultilinearMap.continuous_iff]
    change Continuous (fun f : ContinuousMultilinearMap ℝ (fun _ : Fin k => A) ℝ =>
      ∑σ : Equiv.Perm (Fin k),Equiv.Perm.sign σ • f.domDomCongr σ)
    apply continuous_finsetSum
    intro σ hσ
    exact (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ A ℝ σ).continuous.const_smul _

lemma alternationCLM_alternating (w : A [⋀^Fin k]→L[ℝ] ℝ) :
    alternationCLM w.toContinuousMultilinearMap=(k.factorial:ℝ) • w := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  change (ContinuousMultilinearMap.alternatization w.toContinuousMultilinearMap).toAlternatingMap=_
  rw [ContinuousMultilinearMap.alternatization_apply_toAlternatingMap]
  change MultilinearMap.alternatization w.toAlternatingMap.toMultilinearMap=
    (k.factorial:ℝ) • w.toAlternatingMap
  simpa only [Fintype.card_fin,Nat.cast_smul_eq_nsmul] using w.toAlternatingMap.coe_alternatization

lemma contDiffOn_alternating_of_multilinear {f : Z → A [⋀^Fin k]→L[ℝ] ℝ} {S : Set Z}
    (hf : ContDiffOn ℝ ∞ (fun z => (f z).toContinuousMultilinearMap) S) : ContDiffOn ℝ ∞ f S := by
  have h := (alternationCLM (A := A) (k := k)).contDiff.comp_contDiffOn hf
  have hn : (k.factorial:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  convert h.const_smul (k.factorial:ℝ)⁻¹ using 1
  funext z
  simp only [Function.comp_apply]
  rw [alternationCLM_alternating,smul_smul,inv_mul_cancel₀ hn,one_smul]

lemma contDiffOn_alternating_comp {f : Z → B [⋀^Fin k]→L[ℝ] ℝ}
    {g : Z → A →L[ℝ] B} {S : Set Z}
    (hf : ContDiffOn ℝ ∞ f S) (hg : ContDiffOn ℝ ∞ g S) :
    ContDiffOn ℝ ∞ (fun z => (f z).compContinuousLinearMap (g z)) S := by
  apply contDiffOn_alternating_of_multilinear
  have hp : ContDiffOn ℝ ∞ (fun z => ((fun _ : Fin k => g z),(f z).toContinuousMultilinearMap)) S :=
    (contDiffOn_pi.mpr (fun _ => hg)).prodMk
      ((ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ : (B [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => B) ℝ).contDiff.comp_contDiffOn hf)
  have ha : ContDiff ℝ ∞ (fun p : (Fin k → A →L[ℝ] B) ×
      ContinuousMultilinearMap ℝ (fun _ : Fin k => B) ℝ => p.2.compContinuousLinearMap p.1) :=
    (show AnalyticOnNhd ℝ _ univ from ContinuousMultilinearMap.analyticOnNhd_uncurry_compContinuousLinearMap).contDiff
  exact ha.comp_contDiffOn hp


end
section
open scoped ContDiff Topology Manifold
open Set Function Filter
variable {M I P : Type*} [TopologicalSpace M]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  {d k : ℕ} {a : SignedSmoothAtlas M I d}

structure AtlasSmoothMap (a : SignedSmoothAtlas M I d) (P : Type*)
    [NormedAddCommGroup P] [NormedSpace ℝ P] where
  map : M → P
  smooth : ∀ i,ContDiffOn ℝ ∞ (map ∘ (a.chart i).symm) (a.chart i).target

namespace AtlasSmoothMap
variable (f : AtlasSmoothMap a P)
lemma derivative_transition (i j : I) {q : CoordinateSpace d}
    (hq : q∈((a.chart i).symm ≫ₕ a.chart j).source) :
    fderiv ℝ (f.map ∘ (a.chart i).symm) q=
      (fderiv ℝ (f.map ∘ (a.chart j).symm) (a.chart j ((a.chart i).symm q))).comp
        (fderiv ℝ (a.chart j ∘ (a.chart i).symm) q) := by
  let g := a.chart j ∘ (a.chart i).symm
  have he : (f.map ∘ (a.chart i).symm) =ᶠ[𝓝 q] ((f.map ∘ (a.chart j).symm) ∘ g) := by
    filter_upwards [((a.chart i).symm ≫ₕ a.chart j).open_source.mem_nhds hq] with r hr
    simp only [Function.comp_apply,g]
    exact congrArg f.map ((a.chart j).left_inv hr.2).symm
  rw [he.fderiv_eq]
  apply fderiv_comp
  · exact ((f.smooth j).contDiffAt ((a.chart j).open_target.mem_nhds ((a.chart j).map_source hq.2))).differentiableAt (by simp)
  · exact ((a.transition_smooth i j).contDiffAt (((a.chart i).symm ≫ₕ a.chart j).open_source.mem_nhds hq)).differentiableAt (by simp)

def pullback (w : P → P [⋀^Fin k]→L[ℝ] ℝ) (hw : ContDiff ℝ ∞ w) : AtlasForm a k where
  form i q := (w (f.map ((a.chart i).symm q))).compContinuousLinearMap
    (fderiv ℝ (f.map ∘ (a.chart i).symm) q)
  smooth i := contDiffOn_alternating_comp (hw.comp_contDiffOn (f.smooth i))
    ((contDiffOn_infty_iff_fderiv_of_isOpen (a.chart i).open_target).mp (f.smooth i)).2
  compatible i j q hq := by
    change (w (f.map ((a.chart i).symm q))).compContinuousLinearMap _=
      ((w (f.map ((a.chart j).symm (a.chart j ((a.chart i).symm q))))).compContinuousLinearMap _).compContinuousLinearMap _
    have he := (a.chart j).left_inv hq.2
    simp only [OpenPartialHomeomorph.symm_symm] at he
    rw [he,f.derivative_transition i j hq]
    rfl

lemma pullback_exterior (w : P → P [⋀^Fin k]→L[ℝ] ℝ) (hw : ContDiff ℝ ∞ w)
    (i : I) {q : CoordinateSpace d} (hq : q∈(a.chart i).target) :
    (f.pullback w hw).exterior.form i q=
      (extDeriv w (f.map ((a.chart i).symm q))).compContinuousLinearMap
        (fderiv ℝ (f.map ∘ (a.chart i).symm) q) := by
  exact extDeriv_pullback (hw.differentiable (by simp) _)
    ((f.smooth i).contDiffAt ((a.chart i).open_target.mem_nhds hq)) (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top)

lemma pullback_supported (w : P → P [⋀^Fin k]→L[ℝ] ℝ) (hw : ContDiff ℝ ∞ w)
    {K : Set M} (hK : ∀ x : M,x∉K →w (f.map x)=0) : (f.pullback w hw).SupportedIn K := by
  intro i q hq hn
  change (w (f.map ((a.chart i).symm q))).compContinuousLinearMap _=0
  rw [hK _ hn]
  ext v
  rfl

end AtlasSmoothMap

end
open scoped ContDiff Topology
open Set Filter MeasureTheory
variable {m : ℕ}

def spatialBox (R : ℝ) : Set (CoordinateSpace m) := Icc (fun _ => -R) (fun _ => R)
def lowerCorner (R : ℝ) : CoordinateSpace (m+1) := Fin.cons 0 (fun _ => -R)
def upperCorner (R : ℝ) : CoordinateSpace (m+1) := Fin.cons 1 (fun _ => R)

def exitFaces (R : ℝ) : Set (CoordinateSpace (m+1)) :=
  Icc (lowerCorner R) (upperCorner R) ∩
    ({v | v 0=1} ∪ ⋃ i : Fin m,{v | v i.succ = -R} ∪ {v | v i.succ=R})

lemma corners_le {R : ℝ} (hR : 0≤R) : lowerCorner (m := m) R≤upperCorner R := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · norm_num [lowerCorner,upperCorner]
  · simpa [lowerCorner,upperCorner] using neg_le_self hR

lemma exitFaces_compact (R : ℝ) : IsCompact (exitFaces (m := m) R) := by
  apply isCompact_Icc.inter_right
  apply IsClosed.union
  · exact isClosed_eq (continuous_apply _) continuous_const
  · exact isClosed_iUnion_of_finite (fun i : Fin m => (isClosed_eq (continuous_apply _) continuous_const).union
      (isClosed_eq (continuous_apply _) continuous_const))

lemma tail_mem_spatialBox {R : ℝ} {v : CoordinateSpace (m+1)}
    (hv : v∈Icc (lowerCorner R) (upperCorner R)) : Fin.tail v∈spatialBox R := by
  exact ⟨fun i => hv.1 i.succ,fun i => hv.2 i.succ⟩

lemma time_mem_interval {R : ℝ} {v : CoordinateSpace (m+1)}
    (hv : v∈Icc (lowerCorner R) (upperCorner R)) : v 0∈Icc (0:ℝ) 1 :=
  ⟨hv.1 0,hv.2 0⟩

lemma timeFace_mem_box {R : ℝ} {t : ℝ} {x : CoordinateSpace m}
    (ht : t∈Icc (0:ℝ) 1) (hx : x∈spatialBox R) :
    timeFace t x∈Icc (lowerCorner R) (upperCorner R) := by
  constructor
  · intro i
    exact Fin.cases ht.1 hx.1 i
  · intro i
    exact Fin.cases ht.2 hx.2 i

lemma initialFace_box (R : ℝ) :
    Icc (lowerCorner (m := m) R ∘ (0:Fin (m+1)).succAbove)
      (upperCorner R ∘ (0:Fin (m+1)).succAbove)=spatialBox R := by
  simp only [Fin.succAbove_zero,lowerCorner,upperCorner,Function.comp_def,Fin.cons_succ,spatialBox]

lemma insertNth_mem_box {a b : CoordinateSpace (m+1)} (_hab : a≤b) (i : Fin (m+1))
    {c : ℝ} (hc : c∈Icc (a i) (b i)) {y : CoordinateSpace m}
    (hy : y∈Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) : i.insertNth c y∈Icc a b := by
  constructor
  · change ∀ j,a j ≤ i.insertNth (α := fun _ => ℝ) c y j
    rw [Fin.forall_iff_succAbove i]
    exact ⟨by simpa using hc.1,fun j => by simpa using hy.1 j⟩
  · change ∀ j,i.insertNth (α := fun _ => ℝ) c y j ≤ b j
    rw [Fin.forall_iff_succAbove i]
    exact ⟨by simpa using hc.2,fun j => by simpa using hy.2 j⟩

lemma sideFace_mem_exit (R : ℝ) (hR : 0≤R) (i : Fin (m+1)) (hi : i≠0)
    {y : CoordinateSpace m}
    (hy : y∈Icc (lowerCorner R ∘ i.succAbove) (upperCorner R ∘ i.succAbove)) :
    i.insertNth (upperCorner R i) y∈exitFaces R ∧
      i.insertNth (lowerCorner R i) y∈exitFaces R := by
  have hab := corners_le (m := m) hR
  have hi' : ∃ j : Fin m,i=j.succ := by
    rcases Fin.eq_zero_or_eq_succ i with h|⟨j,h⟩
    · exact (hi h).elim
    · exact ⟨j,h⟩
  obtain ⟨j,rfl⟩ := hi'
  constructor
  · refine ⟨insertNth_mem_box hab j.succ ⟨hab j.succ,le_rfl⟩ hy,Or.inr ?_⟩
    exact mem_iUnion.mpr ⟨j,Or.inr (by simp [upperCorner])⟩
  · refine ⟨insertNth_mem_box hab j.succ ⟨le_rfl,hab j.succ⟩ hy,Or.inr ?_⟩
    exact mem_iUnion.mpr ⟨j,Or.inl (by simp [lowerCorner])⟩

lemma norm_ball_subset_spatialBox {R r : ℝ} (hr : r≤R) :
    Metric.ball (0:CoordinateSpace m) r⊆spatialBox R := by
  intro x hx
  have hnorm : ‖x‖<r := by simpa only [Metric.mem_ball,dist_zero_right] using hx
  have hb (i : Fin m) : |x i|≤R := by
    have hi : ‖x i‖≤‖x‖ := norm_le_pi_norm x i
    exact (Real.norm_eq_abs (x i) ▸ hi).trans ((le_of_lt hnorm).trans hr)
  exact ⟨fun i => (abs_le.mp (hb i)).1,fun i => (abs_le.mp (hb i)).2⟩

lemma separating_bump {K : Set (CoordinateSpace m)} (hK : IsCompact K)
    (h0 : (0:CoordinateSpace m)∉K) {R : ℝ} (hR : 0<R) :
    ∃ b : ContDiffBump (0:CoordinateSpace m),b.rOut<R ∧ ∀ x∈K,b x=0 := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl 0 h0
  let r := min ε R/2
  have hr : 0<r := div_pos (lt_min hε hR) (by norm_num)
  let b : ContDiffBump (0:CoordinateSpace m) := ⟨r/2,r,by positivity,by linarith⟩
  have hrε : r<ε := (half_lt_self (lt_min hε hR)).trans_le (min_le_left _ _)
  have hrR : r<R := (half_lt_self (lt_min hε hR)).trans_le (min_le_right _ _)
  refine ⟨b,hrR,?_⟩
  intro x hx
  apply b.zero_of_le_dist
  by_contra hn
  have hxball : x∈Metric.ball (0:CoordinateSpace m) ε :=
    (lt_of_not_ge hn).trans hrε
  exact hball hxball hx

lemma bump_initial_integral_pos (b : ContDiffBump (0:CoordinateSpace m)) {R : ℝ}
    (hb : b.rOut≤R) : 0<∫ y in spatialBox R,b y := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact b.integral_pos
  · intro x hx
    by_contra hbx
    have hxs : x∈Function.support b := hbx
    rw [b.support_eq] at hxs
    exact hx (norm_ball_subset_spatialBox hb hxs)



end HigherDimensionalBallPacking.Rigidity.Degree
end

end OAI
