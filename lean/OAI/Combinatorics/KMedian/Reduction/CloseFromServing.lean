import Mathlib
import OAI.Combinatorics.KMedian.Reduction.LocalCompletion
import OAI.Combinatorics.KMedian.Reduction.DeletionGeometry

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}
local instance closeFromServingPseudoMetric : PseudoMetricSpace (Fin I.n) := I.pseudoMetric

namespace Serving
variable {U O : Finset (Fin I.n)} {δ : ℝ}

noncomputable def bad (D : Serving (I:=I) U) (O : Finset (Fin I.n)) (δ : ℝ) : Finset ↥U :=
  univ.filter (fun t => δ*D.radius t ≤ nearest I t O)

noncomputable def good (D : Serving (I:=I) U) (O : Finset (Fin I.n)) (δ : ℝ) : Finset (Fin I.n) :=
  (univ \ D.bad O δ).image Subtype.val

theorem good_sub (D : Serving (I:=I) U) : D.good O δ ⊆ U := by
  intro i hi
  obtain ⟨t,_,rfl⟩ := mem_image.mp hi
  exact t.property

theorem good_close (D : Serving (I:=I) U) (t : ↥(D.good O δ)) :
    nearest I t O < δ*D.radius ⟨t.val,D.good_sub t.property⟩ := by
  obtain ⟨u,hu,he⟩ := mem_image.mp t.property
  have hn : ¬δ*D.radius u ≤ nearest I u O := by
    intro hb
    exact (mem_sdiff.mp hu).2 (mem_filter.mpr ⟨mem_univ _,hb⟩)
  have heq : u=⟨t.val,D.good_sub t.property⟩ := Subtype.ext he
  rw [heq] at hn
  exact lt_of_not_ge hn

theorem good_bad_card (D : Serving (I:=I) U) :
    (D.good O δ).card+(D.bad O δ).card=U.card := by
  rw [good,card_image_of_injective _ Subtype.val_injective,
    card_sdiff_add_card_eq_card (subset_univ _),card_univ,Fintype.card_coe]

theorem closeCenters_exists (D : Serving (I:=I) U) (hO : O.Nonempty) :
    ∃ C : CloseCenters I (D.good O δ) O δ,
      ∀ t, C.radius t=D.radius ⟨t.val,D.good_sub t.property⟩ := by
  have hm : ∀ t : ↥(D.good O δ), ∃ o ∈ O, nearest I t O=dist t.val o := by
    intro t
    exact I.nearest_attained t O hO
  choose m hm hdist using hm
  refine ⟨⟨(fun t => D.radius ⟨t.val,D.good_sub t.property⟩),
    (fun t => D.radius_nonneg _),?_,m,hm,?_⟩,fun _ => rfl⟩
  · intro t u htu
    apply D.other_nearest ⟨t.val,D.good_sub t.property⟩ ⟨u.val,D.good_sub u.property⟩
    intro he
    exact htu (Subtype.ext (congrArg Subtype.val he).symm)
  · intro t
    rw [← hdist t]
    exact D.good_close t

theorem backup_card_bound (D : Serving (I:=I) U)
    (C : CloseCenters I (D.good O δ) O δ) (hδ : 0 ≤ δ) (hsmall : δ < 1/2)
    (hk : O.card ≤ U.card) : C.backup.card ≤ (D.bad O δ).card := by
  have hc := card_sdiff_add_card_eq_card C.matched_sub
  have hm : C.matched.card=(D.good O δ).card := by
    rw [CloseCenters.matched,card_image_of_injective _ (C.match_injective hδ hsmall),
      card_univ,Fintype.card_coe]
  change C.backup.card+C.matched.card=O.card at hc
  rw [hm] at hc
  have htotal := D.good_bad_card (O:=O) (δ:=δ)
  omega

end Serving
end MetricKMedian.Reduction
end
end

end OAI
