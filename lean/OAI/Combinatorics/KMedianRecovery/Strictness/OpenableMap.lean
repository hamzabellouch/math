import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Entry
import OAI.Combinatorics.KMedianRecovery.Recovery.Mono
import OAI.Combinatorics.KMedianRecovery.Strictness.OpenPaymentZero
import OAI.Combinatorics.KMedianRecovery.Geometry.NearestImages

namespace OAI

namespace MetricKMedianRecovery.PhaseParameterTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma openable_map (loc : D → X) (F W : Finset X) (r : X → X)
    (v z lam lam' eta eps : ℝ) (hv : 0 < v) (hvsmall : v < 1/6)
    (heps : 0 ≤ eps) (hprice : lam ≤ lam')
    (herror : lam'-lam+(Fintype.card D:ℝ)*((1-3*v)*eps) ≤ (Fintype.card D:ℝ)*eta)
    (hshrink : ∀ j, ∀ x ∈ W, dist (loc j) (r x) ≤ dist (loc j) x)
    (hloss : ∀ j, ∀ x ∈ W, dist (loc j) x ≤ dist (loc j) (r x)+eps)
    (i : X) (hop : etaOpenable loc F W (1-3*v) (1+v^2) v z lam 0 i) :
    etaOpenable loc F (W.image r) (1-3*v) (1+v^2) v z lam' eta i := by
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  have ht1 : 1-3*v ≤ 1 := by linarith only [hv]
  by_cases hW : W.Nonempty
  · have hh (j : D) := LeafTransfer.nearest_images W hW id r (loc j) eps
      (hshrink j) (hloss j)
    simp only [Finset.image_id] at hh
    exact ClippingTransfer.openable_transfer loc F W (W.image r) (1-3*v) (1+v^2)
      v z lam lam' eta eps hW (hW.image r) ht ht1 heps
      (fun j => (hh j).1) (fun j => (hh j).2) hprice herror i hop
  · have hW0 : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    subst W
    simp only [Finset.image_empty]
    obtain ⟨tau,hb,hp,hd⟩ := hop
    refine ⟨tau,hb,?_,fun i hi a ha => (hd i hi a ha).trans hprice⟩
    simp only [mul_zero,sub_zero] at hp
    have hnonneg : 0 ≤ (Fintype.card D:ℝ)*((1-3*v)*eps) := by positivity
    linarith only [hp,herror,hnonneg]

omit [Fintype D] [PseudoMetricSpace X] in
lemma image_regular_union {F B : Finset X} {r : X → X}
    (hfix : ∀ i ∈ F, r i = i) : (F ∪ B).image r ⊆ F ∪ B.image r := by
  intro x hx
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
  rcases Finset.mem_union.mp hi with hi | hi
  · exact Finset.mem_union_left _ ((hfix i hi).symm ▸ hi)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)

theorem prefix_map (loc : D → X) (F B Q : Finset X) (H : List X) (r : X → X)
    (v z lam lam' eta eps : ℝ) (hv : 0 < v) (hvsmall : v < 1/6)
    (heps : 0 ≤ eps) (hprice : lam ≤ lam')
    (herror : lam'-lam+(Fintype.card D:ℝ)*((1-3*v)*eps) ≤ (Fintype.card D:ℝ)*eta)
    (hinj : Function.Injective r) (hfix : ∀ i ∈ F, r i = i)
    (hshrink : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) (r x) ≤ dist (loc j) x)
    (hloss : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) x ≤ dist (loc j) (r x)+eps)
    (hp : PhaseSequence.Prefix loc F B v z lam 0 Q H) :
    PhaseSequence.Prefix loc F (B.image r) v z lam' eta (Q.image r) (H.map r) := by
  induction hp with
  | nil => exact PhaseSequence.Prefix.nil _
  | @cons Q i H hi htail ih =>
    apply PhaseSequence.Prefix.cons
    · refine ⟨?_,?_⟩
      · intro hh
        obtain ⟨a,ha,har⟩ := Finset.mem_image.mp hh
        exact hi.1 ((hinj har) ▸ ha)
      · rcases hi.2 with hb | ⟨hiF,W,hQ,hW,hop⟩
        · exact Or.inl (Finset.mem_image.mpr ⟨i,hb,rfl⟩)
        · have hir := hfix i hiF
          apply Or.inr
          refine ⟨hir.symm ▸ hiF,W.image r,Finset.image_subset_image hQ,?_,?_⟩
          · exact (Finset.image_subset_image hW).trans (image_regular_union hfix)
          · rw [hir]
            exact openable_map loc F W r v z lam lam' eta eps hv hvsmall heps hprice herror
              (fun j x hx => hshrink j x (hW hx))
              (fun j x hx => hloss j x (hW hx)) i hop
    · simpa only [Finset.image_insert] using ih

theorem valid_map (loc : D → X) (F B Q : Finset X) (H : List X) (r : X → X)
    (v z lam lam' eta eps : ℝ) (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z)
    (hlam : 0 < lam) (heps : 0 ≤ eps) (hprice : lam ≤ lam')
    (herror : lam'-lam+(Fintype.card D:ℝ)*((1-3*v)*eps) ≤ (Fintype.card D:ℝ)*eta)
    (hinj : Function.Injective r) (hfix : ∀ i ∈ F, r i = i)
    (hQ : Q ⊆ F ∪ B)
    (hshrink : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) (r x) ≤ dist (loc j) x)
    (hloss : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) x ≤ dist (loc j) (r x)+eps)
    (hbase : ∀ i ∈ F, bidRow loc (1-3*v) z (Q ∪ H.toFinset) i ≤ lam)
    (hp : PhaseSequence.Valid loc F B Q v z lam 0 H) :
    PhaseSequence.Valid loc F (B.image r) (Q.image r) v z lam' eta (H.map r) := by
  refine ⟨prefix_map loc F B Q H r v z lam lam' eta eps hv hvsmall heps hprice herror
    hinj hfix hshrink hloss hp.1,?_⟩
  have hsub : Q ∪ H.toFinset ⊆ F ∪ B := Finset.union_subset hQ hp.1.opened_subset
  change ∀ i ∈ F, i ∉ Q.image r ∪ (H.map r).toFinset → _
  have hEq : Q.image r ∪ (H.map r).toFinset = (Q ∪ H.toFinset).image r := by
    ext x
    simp only [Finset.mem_union,Finset.mem_image,List.mem_toFinset,List.mem_map]
    aesop
  rw [hEq]
  by_cases hne : (Q ∪ H.toFinset).Nonempty
  · have hd (j : D) := LeafTransfer.nearest_images (Q ∪ H.toFinset) hne id r (loc j) eps
      (fun x hx => hshrink j x (hsub hx)) (fun x hx => hloss j x (hsub hx))
    simp only [Finset.image_id] at hd
    exact PriceTransfer.maximal_shrink loc F _ _ v z lam lam' hne (hne.image r)
      hv hvsmall hz hlam hbase hp.2 hprice (fun j => (hd j).1)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hne
    have hh := PriceTransfer.maximal_price_mono loc F (Q ∪ H.toFinset) v z lam lam'
      hv hvsmall hz hlam hbase hp.2 hprice
    simpa only [he,Finset.image_empty] using hh

end MetricKMedianRecovery.PhaseParameterTransfer

end OAI
