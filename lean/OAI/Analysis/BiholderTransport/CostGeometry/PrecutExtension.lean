import Mathlib
import OAI.Analysis.BiholderTransport.Contact.GraphCompact

namespace OAI

noncomputable section

namespace WeakMTWTransport
open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma eventually_uniform_graph_precut {v : M → ℝ} (hv : Continuous v) {T : ℝ}
    (hID : ∀ x : M, ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x),
      T • p ∈ injectivityDomain x) :
    ∀ᶠ t in 𝓝 T, ∀ x : M, ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x),
      t • p ∈ injectivityDomain x := by
  let : CompactSpace (subgradientGraph (n := n) (cTransform v)) :=
    isCompact_iff_compactSpace.mp (isCompact_subgradientGraph hv)
  have hf : Continuous (fun q : ℝ × subgradientGraph (n := n) (cTransform v) => tangentScale q.1 q.2.1) :=
    contMDiff_tangentScale.continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have H : ∀ᶠ t in 𝓝 T, ∀ z : subgradientGraph (n := n) (cTransform v),
      t • z.1.2 ∈ injectivityDomain z.1.1 := by
    have HH : ∀ᶠ t in 𝓝 T, ∀ z ∈ (univ : Set (subgradientGraph (n := n) (cTransform v))),
        t • z.1.2 ∈ injectivityDomain z.1.1 := by
      apply isCompact_univ.eventually_forall_of_forall_eventually
      intro z _
      exact (isOpen_total_injectivityDomain.preimage hf).mem_nhds
        (hID z.1.1 z.1.2 (normalSubdifferential_subset_active_hull hv z.1.1 z.2))
    exact HH.mono (fun _ h z => h z (mem_univ z))
  filter_upwards [H] with t ht x p hp
  exact ht ⟨⟨x,p⟩,active_hull_subset_normalSubdifferential hv x hp⟩

lemma scaled_injectivityDomain_of_le {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t S : ℝ} (hS : 0<S) (ht : 0≤t) (htS : t≤S) (hp : S • p ∈ injectivityDomain x) :
    t • p ∈ injectivityDomain x := by
  rcases eq_or_lt_of_le ht with h0 | ht0
  · rw [←h0,zero_smul]
    exact zero_mem_injectivityDomain x
  rcases eq_or_lt_of_le htS with he | hlt
  · rwa [he]
  have hh := contracted_minimizer_mem_injectivityDomain (injectivityDomain_subset_minimizingVectors x hp)
    (div_pos ht0 hS) ((div_lt_one hS).mpr hlt)
  simpa only [smul_smul,div_mul_cancel₀ _ hS.ne'] using hh

lemma exists_extended_uniform_precut {v : M → ℝ} (hv : Continuous v)
    {T : ℝ} (hT : 0<T) (hT1 : T<1)
    (hID : ∀ x : M, ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x),
      T • p ∈ injectivityDomain x) :
    ∃ S, T<S ∧ S<1 ∧ ∀ x : M, ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x),
      ∀ t ∈ Icc (0:ℝ) S, t • p ∈ injectivityDomain x := by
  obtain ⟨S,hTS,hS1,hS⟩ := ((frequently_gt_nhds T).and_eventually
    ((eventually_lt_nhds hT1).and (eventually_uniform_graph_precut hv hID))).exists
  refine ⟨S,hTS,hS1,?_⟩
  intro x p hp t ht
  exact scaled_injectivityDomain_of_le (hT.trans hTS) ht.1 ht.2 (hS x p hp)

end WeakMTWTransport

open Set Filter
open scoped Topology

lemma eventually_injective_of_uniform_local_injective
    {P X Y Z : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [CompactSpace X] [TopologicalSpace Y] [T2Space Y] [PseudoMetricSpace Z]
    (F : P → X → Y) (hF : Continuous (fun p : P × X => F p.1 p.2))
    (q : X → Z) (hq : Continuous q) {T : P} {δ : ℝ} (hδ : 0<δ)
    (hT : Function.Injective (F T))
    (hloc : ∀ᶠ t in 𝓝 T, ∀ x y, dist (q x) (q y)<δ → F t x=F t y → x=y) :
    ∀ᶠ t in 𝓝 T, Function.Injective (F t) := by
  have hopen : IsOpen {p : P × (X × X) |
      dist (q p.2.1) (q p.2.2)<δ ∨ F p.1 p.2.1 ≠ F p.1 p.2.2} :=
    (isOpen_lt ((hq.comp (continuous_fst.comp continuous_snd)).dist
      (hq.comp (continuous_snd.comp continuous_snd))) continuous_const).union
      (isOpen_ne_fun (hF.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
        (hF.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))
  have hfar : ∀ᶠ t in 𝓝 T, ∀ xy ∈ (univ : Set (X×X)),
      dist (q xy.1) (q xy.2)<δ ∨ F t xy.1 ≠ F t xy.2 := by
    apply isCompact_univ.eventually_forall_of_forall_eventually
    intro xy _
    apply hopen.mem_nhds
    by_cases hxy : xy.1=xy.2
    · exact Or.inl (by simpa only [hxy,dist_self] using hδ)
    · exact Or.inr (fun he => hxy (hT he))
  filter_upwards [hloc,hfar] with t ht hf x y he
  rcases hf (x,y) (mem_univ _) with hclose | hne
  · exact ht x y hclose he
  · exact (hne he).elim

end

end OAI
