import Mathlib

namespace OAI

/-! Analytic identity detection by strict submersions and pathwise eventual vanishing. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

namespace PathSelection.Detection

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

 
def IsStrictSubmersionAt (e : E → F) (x : E) : Prop :=
  ∃ e' : E →L[ℝ] F, HasStrictFDerivAt e e' x ∧ e'.range = ⊤

omit [CompleteSpace E] [CompleteSpace F] in
lemma IsStrictSubmersionAt.continuousAt {e : E → F} {x : E}
    (he : IsStrictSubmersionAt e x) : ContinuousAt e x := by
  obtain ⟨e', hd, _⟩ := he
  exact hd.continuousAt

lemma IsStrictSubmersionAt.map_nhds_eq {e : E → F} {x : E}
    (he : IsStrictSubmersionAt e x) : map e (𝓝 x) = 𝓝 (e x) := by
  obtain ⟨e', hd, hr⟩ := he
  exact hd.map_nhds_eq_of_surj hr

 

theorem nowhereDense_zeros_of_submersion
    {U : Set F} {V : Set E} {f : F → G} {e : E → F}
    (hf : AnalyticOnNhd ℝ f U) (hU : IsPreconnected U)
    (hnonzero : ¬ EqOn f 0 U)
    (hV : IsOpen V) (heU : MapsTo e V U)
    (he : ∀ x ∈ V, IsStrictSubmersionAt e x) :
    IsNowhereDense {x | x ∈ V ∧ f (e x) = 0} := by
  let Z : Set V := {x | f (e x) = 0}
  have hcont : Continuous (fun x : V => f (e x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((hf (e x) (heU x.property)).continuousAt.comp
      (he x x.property).continuousAt).comp continuous_subtype_val.continuousAt
  have hclosed : IsClosed Z := isClosed_eq hcont continuous_const
  have hinterior : interior Z = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hz : ∀ᶠ y : V in 𝓝 x, f (e y) = 0 :=
      mem_interior_iff_mem_nhds.mp hx
    have hz' : ∀ᶠ y in 𝓝 (x : E), f (e y) = 0 := by
      rw [← hV.isOpenEmbedding_subtypeVal.map_nhds_eq x]
      exact hz
    have hz'' : f =ᶠ[𝓝 (e x)] 0 := by
      rw [← (he x x.property).map_nhds_eq]
      exact hz'
    exact hnonzero
      (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU (heU x.property) hz'')
  have hnd : IsNowhereDense Z := hclosed.isNowhereDense_iff.mpr hinterior
  have himage : (Subtype.val '' Z : Set E) = {x | x ∈ V ∧ f (e x) = 0} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hx, hz⟩
      exact ⟨⟨x, hx⟩, hz, rfl⟩
  rw [← himage]
  exact Topology.IsInducing.subtypeVal.isNowhereDense_image hnd

 

theorem eqOn_zero_of_integer_evaluations
    {U : Set F} {V : Set E} {f : F → G}
    (hf : AnalyticOnNhd ℝ f U) (hU : IsPreconnected U)
    (hV : IsOpen V) (hVne : V.Nonempty)
    (D : ℕ → Set E) (hD : ∀ N, IsOpen (D N))
    (e : ℕ → E → F) (heU : ∀ N, MapsTo (e N) (D N) U)
    (he : ∀ N x, x ∈ D N → IsStrictSubmersionAt (e N) x)
    (hzero : ∀ x ∈ V, ∃ N, x ∈ D N ∧ f (e N x) = 0) :
    EqOn f 0 U := by
  by_contra hn
  have hnd : ∀ N, IsNowhereDense {x | x ∈ D N ∧ f (e N x) = 0} :=
    fun N => nowhereDense_zeros_of_submersion hf hU hn (hD N) (heU N) (he N)
  have hmeagre : IsMeagre (⋃ N, {x | x ∈ D N ∧ f (e N x) = 0}) :=
    isMeagre_iUnion (fun N => (hnd N).isMeagre)
  exact not_isMeagre_of_isOpen hV hVne (hmeagre.mono (by
    intro x hx
    obtain ⟨N, hNx, hz⟩ := hzero x hx
    exact mem_iUnion.mpr ⟨N, hNx, hz⟩))

 

theorem eqOn_zero_of_pathwise_eventually_zero
    {U : Set F} {V : Set E} {f : F → G}
    (hf : AnalyticOnNhd ℝ f U) (hU : IsPreconnected U)
    (hV : IsOpen V) (hVne : V.Nonempty)
    (D : ℕ → Set E) (hD : ∀ N, IsOpen (D N))
    (e : ℕ → E → F) (heU : ∀ N, MapsTo (e N) (D N) U)
    (he : ∀ N x, x ∈ D N → IsStrictSubmersionAt (e N) x)
    (hzero : ∀ x ∈ V, ∀ᶠ N in atTop, x ∈ D N ∧ f (e N x) = 0) :
    EqOn f 0 U := by
  apply eqOn_zero_of_integer_evaluations hf hU hV hVne D hD e heU he
  intro x hx
  exact (hzero x hx).exists

 
theorem eqOn_zero_of_analytic_evaluations
    {U : Set F} {V : Set E} {f : F → G}
    (hf : AnalyticOnNhd ℝ f U) (hU : IsPreconnected U)
    (hV : IsOpen V) (hVne : V.Nonempty)
    (D : ℕ → Set E) (hD : ∀ N, IsOpen (D N))
    (e : ℕ → E → F) (heU : ∀ N, MapsTo (e N) (D N) U)
    (he : ∀ N, AnalyticOnNhd ℝ (e N) (D N))
    (hsub : ∀ N x, x ∈ D N → (fderiv ℝ (e N) x).range = ⊤)
    (hzero : ∀ x ∈ V, ∀ᶠ N in atTop, x ∈ D N ∧ f (e N x) = 0) :
    EqOn f 0 U := by
  apply eqOn_zero_of_pathwise_eventually_zero hf hU hV hVne D hD e heU _ hzero
  intro N x hx
  exact ⟨fderiv ℝ (e N) x, (he N x hx).hasStrictFDerivAt, hsub N x hx⟩

 

theorem family_zero_of_pathwise_eventually_zero
    {Y : Type*} {U : Set F} {V : Set E} {W : Set Y} {f : F → Y → G}
    (hf : ∀ y ∈ W, AnalyticOnNhd ℝ (fun x => f x y) U)
    (hU : IsPreconnected U) (hV : IsOpen V) (hVne : V.Nonempty)
    (D : ℕ → Set E) (hD : ∀ N, IsOpen (D N))
    (e : ℕ → E → F) (heU : ∀ N, MapsTo (e N) (D N) U)
    (he : ∀ N x, x ∈ D N → IsStrictSubmersionAt (e N) x)
    (hzero : ∀ x ∈ V, ∀ y ∈ W,
      ∀ᶠ N in atTop, x ∈ D N ∧ f (e N x) y = 0) :
    ∀ x ∈ U, ∀ y ∈ W, f x y = 0 := by
  intro x hx y hy
  exact eqOn_zero_of_pathwise_eventually_zero (hf y hy) hU hV hVne D hD e heU he
    (fun t ht => hzero t ht y hy) hx

omit [CompleteSpace E] [CompleteSpace F] in
 

lemma IsStrictSubmersionAt.triangular
    {e : E → F} {p : E × ℝ → ℝ} {x : E × ℝ}
    (he : IsStrictSubmersionAt e x.1)
    {p' : E × ℝ →L[ℝ] ℝ} (hp : HasStrictFDerivAt p p' x)
    (hne : p' (0, 1) ≠ 0) :
    IsStrictSubmersionAt (fun q : E × ℝ => (e q.1, p q)) x := by
  obtain ⟨e', hd, hr⟩ := he
  let D : E × ℝ →L[ℝ] F × ℝ :=
    (e'.comp (ContinuousLinearMap.fst ℝ E ℝ)).prod p'
  refine ⟨D, (hd.comp x hasStrictFDerivAt_fst).prodMk hp, ?_⟩
  apply LinearMap.range_eq_top.mpr
  intro y
  obtain ⟨v, hv⟩ := LinearMap.range_eq_top.mp hr y.1
  let t := (y.2 - p' (v, 0)) / p' (0, 1)
  refine ⟨(v, t), ?_⟩
  have hsplit : p' (v, t) = p' (v, 0) + t * p' (0, 1) := by
    have ht : (v, t) = (v, (0 : ℝ)) + t • ((0 : E), (1 : ℝ)) := by simp
    rw [ht, map_add, map_smul]
    rfl
  apply Prod.ext
  · exact hv
  · change p' (v, t) = y.2
    rw [hsplit]
    dsimp only [t]
    rw [div_mul_cancel₀ _ hne]
    ring

end PathSelection.Detection
end

end OAI
