import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation

namespace OAI

universe uE uF uι uH

open Set
open scoped Pointwise

namespace Paper092.SupportGeometry

variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def support (K : Set E) (f : E →L[ℝ] ℝ) : ℝ := sSup (f '' K)

theorem le_support {K : Set E} (hK : IsCompact K) (f : E →L[ℝ] ℝ)
    {x : E} (hx : x ∈ K) : f x ≤ support K f :=
  le_csSup (hK.image f.continuous).bddAbove (mem_image_of_mem f hx)

theorem support_le {K : Set E} (hK : K.Nonempty) (f : E →L[ℝ] ℝ)
    {a : ℝ} (ha : ∀ x ∈ K, f x ≤ a) : support K f ≤ a :=
  csSup_le (hK.image f) (by rintro _ ⟨x, hx, rfl⟩; exact ha x hx)

theorem exists_support {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (f : E →L[ℝ] ℝ) : ∃ x ∈ K, f x = support K f :=
  (hK.image f.continuous).sSup_mem (hne.image f)

theorem support_add {A B : Set E} (hA : IsCompact A) (hneA : A.Nonempty)
    (hB : IsCompact B) (hneB : B.Nonempty) (f : E →L[ℝ] ℝ) :
    support (A + B) f = support A f + support B f := by
  unfold support
  rw [image_add]
  exact csSup_add (hneA.image f) (hA.image f.continuous).bddAbove
    (hneB.image f) (hB.image f.continuous).bddAbove

theorem support_smul (K : Set E) (f : E →L[ℝ] ℝ) {c : ℝ} (hc : 0 ≤ c) :
    support (c • K) f = c * support K f := by
  unfold support
  rw [image_smul_comm f c K (fun x => f.map_smul c x), Real.sSup_smul_of_nonneg hc]
  rfl

theorem support_prod {A : Set E} {B : Set F} (hA : IsCompact A) (hneA : A.Nonempty)
    (hB : IsCompact B) (hneB : B.Nonempty) (f : E →L[ℝ] ℝ) (g : F →L[ℝ] ℝ) :
    support (A ×ˢ B) (f.coprod g) = support A f + support B g := by
  unfold support
  have himage : f.coprod g '' (A ×ˢ B) = f '' A + g '' B := by
    change (fun x : E × F => f x.1 + g x.2) '' (A ×ˢ B) = _
    rw [image_prod (fun x y => f x + g y), ← image2_add,
      image2_image_left, image2_image_right]
  rw [himage]
  exact csSup_add (hneA.image f) (hA.image f.continuous).bddAbove
    (hneB.image g) (hB.image g.continuous).bddAbove

theorem support_sum {ι : Type uι} (s : Finset ι) (K : ι → Set E)
    (hK : ∀ i ∈ s, IsCompact (K i)) (hne : ∀ i ∈ s, (K i).Nonempty)
    (f : E →L[ℝ] ℝ) : support (∑ i ∈ s, K i) f = ∑ i ∈ s, support (K i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [support]
  | @insert i s hi ih =>
    have hKs : ∀ j ∈ s, IsCompact (K j) := fun j hj => hK j (Finset.mem_insert_of_mem hj)
    have hnes : ∀ j ∈ s, (K j).Nonempty := fun j hj => hne j (Finset.mem_insert_of_mem hj)
    have hcompact : IsCompact (∑ j ∈ s, K j) :=
      Finset.sum_induction K IsCompact (fun _ _ ha hb => ha.add hb)
        isCompact_singleton hKs
    have hnonempty : (∑ j ∈ s, K j).Nonempty :=
      Finset.sum_induction K Set.Nonempty (fun _ _ ha hb => ha.add hb)
        (singleton_nonempty 0) hnes
    rw [Finset.sum_insert hi,
      support_add (hK i (Finset.mem_insert_self i s)) (hne i (Finset.mem_insert_self i s))
        hcompact hnonempty, ih hKs hnes, Finset.sum_insert hi]

theorem mem_iff_le_support {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (hconv : Convex ℝ K) {x : E} :
    x ∈ K ↔ ∀ f : E →L[ℝ] ℝ, f x ≤ support K f := by
  refine ⟨fun hx f => le_support hK f hx, fun h => ?_⟩
  by_contra hx
  obtain ⟨f, u, hu, hux⟩ := geometric_hahn_banach_closed_point hconv hK.isClosed hx
  exact (hux.trans_le ((h f).trans (support_le hne f fun y hy => (hu y hy).le))).false

theorem eq_of_support_eq {A B : Set E} (hA : IsCompact A) (hneA : A.Nonempty)
    (hconvA : Convex ℝ A) (hB : IsCompact B) (hneB : B.Nonempty)
    (hconvB : Convex ℝ B) (h : ∀ f : E →L[ℝ] ℝ, support A f = support B f) : A = B := by
  ext x
  simp only [mem_iff_le_support hA hneA hconvA, mem_iff_le_support hB hneB hconvB, h]

theorem isCompact_segment (x y : E) : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image]
  exact isCompact_Icc.image (by fun_prop)

theorem support_segment (x y : E) (f : E →L[ℝ] ℝ) :
    support (segment ℝ x y) f = max (f x) (f y) := by
  unfold support
  rw [show f '' segment ℝ x y = segment ℝ (f x) (f y) from
    image_segment ℝ f.toLinearMap.toAffineMap x y]
  rw [segment_eq_Icc', csSup_Icc (min_le_max)]

theorem support_centered_segment (v : E) (f : E →L[ℝ] ℝ) :
    support (segment ℝ (-(1 / 2 : ℝ) • v) ((1 / 2 : ℝ) • v)) f = |f v| / 2 := by
  simp only [support_segment, map_smul, smul_eq_mul, neg_mul]
  rw [max_comm, ← abs_eq_max_neg, abs_mul]
  norm_num
  ring

theorem support_sum_centered_segments {ι : Type uι} (s : Finset ι) (v : ι → E)
    (f : E →L[ℝ] ℝ) :
    support (∑ i ∈ s, segment ℝ (-(1 / 2 : ℝ) • v i) ((1 / 2 : ℝ) • v i)) f =
      (1 / 2 : ℝ) * ∑ i ∈ s, |f (v i)| := by
  rw [support_sum s _ (fun _ _ => isCompact_segment _ _)
    (fun _ _ => ⟨_, left_mem_segment ℝ _ _⟩)]
  simp_rw [support_centered_segment, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  ring

theorem eq_sum_centered_segments_iff {ι : Type uι} {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) (hconv : Convex ℝ K) (s : Finset ι) (v : ι → E) :
    K = ∑ i ∈ s, segment ℝ (-(1 / 2 : ℝ) • v i) ((1 / 2 : ℝ) • v i) ↔
      ∀ f : E →L[ℝ] ℝ, support K f = (1 / 2 : ℝ) * ∑ i ∈ s, |f (v i)| := by
  constructor
  · intro h f
    rw [h, support_sum_centered_segments]
  · intro h
    apply eq_of_support_eq hK hne hconv
    · exact Finset.sum_induction _ IsCompact (fun _ _ ha hb => ha.add hb)
        isCompact_singleton (fun _ _ => isCompact_segment _ _)
    · exact Finset.sum_induction _ Set.Nonempty (fun _ _ ha hb => ha.add hb)
        (singleton_nonempty 0) (fun _ _ => ⟨_, left_mem_segment ℝ _ _⟩)
    · exact Finset.sum_induction _ (Convex ℝ) (fun _ _ ha hb => ha.add hb)
        (convex_singleton 0) (fun _ _ => convex_segment _ _)
    · intro f
      rw [h f, support_sum_centered_segments]

section InnerProduct

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem mem_iff_inner_le_support {K : Set H} (hK : IsCompact K) (hne : K.Nonempty)
    (hconv : Convex ℝ K) {x : H} :
    x ∈ K ↔ ∀ u : H, inner ℝ u x ≤ support K (innerSL ℝ u) := by
  rw [mem_iff_le_support hK hne hconv]
  constructor
  · intro h u
    exact h (innerSL ℝ u)
  · intro h f
    obtain ⟨u, rfl⟩ := (InnerProductSpace.toDual ℝ H).surjective f
    exact h u

theorem halfSpaces_eq_of_eq_support {K : Set H} (hK : IsCompact K) (hne : K.Nonempty)
    (hconv : Convex ℝ K) (p : H → ℝ) (hp : ∀ u, p u = support K (innerSL ℝ u)) :
    {x | ∀ u : H, inner ℝ u x ≤ p u} = K := by
  ext x
  simp_rw [mem_ofPred_eq, hp]
  exact (mem_iff_inner_le_support hK hne hconv).symm

theorem eq_of_inner_support_eq {A B : Set H} (hA : IsCompact A) (hneA : A.Nonempty)
    (hconvA : Convex ℝ A) (hB : IsCompact B) (hneB : B.Nonempty)
    (hconvB : Convex ℝ B)
    (h : ∀ u : H, support A (innerSL ℝ u) = support B (innerSL ℝ u)) : A = B := by
  ext x
  simp only [mem_iff_inner_le_support hA hneA hconvA,
    mem_iff_inner_le_support hB hneB hconvB, h]

end InnerProduct

end Paper092.SupportGeometry

end OAI
