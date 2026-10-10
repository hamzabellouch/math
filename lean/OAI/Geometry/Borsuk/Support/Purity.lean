import Mathlib
import OAI.Geometry.Borsuk.Projectors.ChartSurgery
import OAI.Geometry.Borsuk.MatrixGeometry.CenterApproximation

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace
open Set
section Purity
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

lemma Admissible.maximal_support_complement_bound {f : E → ι → ℝ} (hf : Admissible f)
    (hdim : Fintype.card (UpperTriangle (Fin (k+1))) = Fintype.card ι)
    (hn : 1 < Fintype.card ι) {w : E} (hw : ‖w‖ = 1)
    (hmax : ∀ u : E, ‖u‖ = 1 → positiveSupport f w ⊆ positiveSupport f u →
      positiveSupport f u = positiveSupport f w) :
    Fintype.card ↥((positiveSupport f w)ᶜ : Finset ι) ≤ Fintype.card (UpperTriangle (Fin k)) := by
  classical
  by_contra hb
  have hd : Fintype.card (UpperTriangle (Fin k)) <
      Fintype.card ↥((positiveSupport f w)ᶜ : Finset ι) := lt_of_not_ge hb
  let I := positiveSupport f w
  have hI : I.Nonempty := hf.support_nonempty hw
  have hr : ∀ i ∈ I, 0 < f w i := fun i hi => (mem_positiveSupport f w i).mp hi
  have hro : ∀ i ∉ I, f w i = 0 := by
    intro i hi
    exact le_antisymm (not_lt.mp (fun hp => hi ((mem_positiveSupport f w i).mpr hp))) (hf.nonneg w hw i)
  obtain ⟨C,hCK,hCD,hcover⟩ := compact_disjoint_chambers (hf.orientedLevel_compact w (f w))
    (fun u hu => hf.commonPositiveCone_interior_safe I (orientedLevel_cone hr hu))
  let c : ↥C → E := Subtype.val
  have hc : ∀ j, c j ∈ commonPositiveCone f I := fun j => orientedLevel_cone hr (hCK j.property)
  have hcn : ∀ j, ‖c j‖ = 1 := fun j => (hCK j.property).1
  obtain ⟨z,hz,hzs,g,hg,hgs,hge,hgm⟩ := hf.finite_center_approximations hd c
    (fun j => hf.commonPositiveCone_safe I (hc j)) hcn
  have hj : 0 < Fintype.card ↥(Iᶜ : Finset ι) := lt_of_le_of_lt (Nat.zero_le _) hd
  let : Nonempty ↥(Iᶜ : Finset ι) := Fintype.card_pos_iff.mp hj
  have hε : 0 < (2*(Fintype.card ↥(Iᶜ : Finset ι):ℝ))⁻¹ := by positivity
  exact hf.chart_surgery_impossible hdim hn hI hmax hw hr hr hro (hf.sum_one w hw)
    c hc hcn hCD hcover hε g hg hgs hge z hz hzs hgm

end Purity
end BorsukNine

namespace BorsukNine
open scoped RealInnerProductSpace
section PureFacets
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι]
omit [InnerProductSpace ℝ E] [DecidableEq ι] in
lemma exists_maximal_support (f : E → ι → ℝ) {w : E} (hw : ‖w‖ = 1) :
    ∃ u, ‖u‖ = 1 ∧ positiveSupport f w ⊆ positiveSupport f u ∧
      ∀ v, ‖v‖ = 1 → positiveSupport f u ⊆ positiveSupport f v →
        positiveSupport f v = positiveSupport f u := by
  classical
  let S : Set (Finset ι) := {s | ∃ u, ‖u‖ = 1 ∧ positiveSupport f w ⊆ s ∧ positiveSupport f u = s}
  obtain ⟨s,hs,hm⟩ := (Set.toFinite S).exists_maximal (show S.Nonempty from ⟨_,w,hw,Finset.Subset.rfl,rfl⟩)
  obtain ⟨u,hu,hwu,rfl⟩ := hs
  refine ⟨u,hu,hwu,?_⟩
  intro v hv huv
  exact le_antisymm (hm ⟨v,hv,hwu.trans huv,rfl⟩ huv) huv
end PureFacets

lemma Admissible.maximal_support_card_four {f : Vector4 → Fin 10 → ℝ} (hf : Admissible f)
    {w : Vector4} (hw : ‖w‖ = 1)
    (hm : ∀ u, ‖u‖ = 1 → positiveSupport f w ⊆ positiveSupport f u →
      positiveSupport f u = positiveSupport f w) : (positiveSupport f w).card = 4 := by
  have hl := hf.support_card_four_le hw
  have hb := hf.maximal_support_complement_bound (k := 3) (by decide) (by decide) hw hm
  have hc : Fintype.card (UpperTriangle (Fin 3)) = 6 := by decide
  rw [Fintype.card_coe,Finset.card_compl,Fintype.card_fin,hc] at hb
  omega

lemma Admissible.maximal_support_card_three {f : EuclideanSpace ℝ (Fin 3) → Fin 6 → ℝ}
    (hf : Admissible f) {w : EuclideanSpace ℝ (Fin 3)} (hw : ‖w‖ = 1)
    (hm : ∀ u, ‖u‖ = 1 → positiveSupport f w ⊆ positiveSupport f u →
      positiveSupport f u = positiveSupport f w) : (positiveSupport f w).card = 3 := by
  have hl := hf.support_card_three_le hw
  have hb := hf.maximal_support_complement_bound (k := 2) (by decide) (by decide) hw hm
  have hc : Fintype.card (UpperTriangle (Fin 2)) = 3 := by decide
  rw [Fintype.card_coe,Finset.card_compl,Fintype.card_fin,hc] at hb
  omega

lemma Admissible.support_extends_four {f : Vector4 → Fin 10 → ℝ} (hf : Admissible f)
    {w : Vector4} (hw : ‖w‖ = 1) :
    ∃ u, ‖u‖ = 1 ∧ positiveSupport f w ⊆ positiveSupport f u ∧ (positiveSupport f u).card = 4 := by
  obtain ⟨u,hu,hwu,hm⟩ := exists_maximal_support f hw
  exact ⟨u,hu,hwu,hf.maximal_support_card_four hu hm⟩

lemma Admissible.support_extends_three {f : EuclideanSpace ℝ (Fin 3) → Fin 6 → ℝ}
    (hf : Admissible f) {w : EuclideanSpace ℝ (Fin 3)} (hw : ‖w‖ = 1) :
    ∃ u, ‖u‖ = 1 ∧ positiveSupport f w ⊆ positiveSupport f u ∧ (positiveSupport f u).card = 3 := by
  obtain ⟨u,hu,hwu,hm⟩ := exists_maximal_support f hw
  exact ⟨u,hu,hwu,hf.maximal_support_card_three hu hm⟩
end BorsukNine

open Set MeasureTheory

end OAI
