import Mathlib
import OAI.Geometry.Borsuk.Support.Purity
import OAI.Geometry.Borsuk.LocalParity.NoFreeRidge

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace
section SupportIncidence
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
def SupportFace (f : V → ι → ℝ) (S : Finset ι) : Prop :=
  ∃ u : V, ‖u‖ = 1 ∧ S ⊆ positiveSupport f u
omit [InnerProductSpace ℝ V] [DecidableEq ι] in
lemma SupportFace.mono {f : V → ι → ℝ} {S U : Finset ι} (h : SupportFace f S) (hUS : U ⊆ S) : SupportFace f U := by
  obtain ⟨u,hu,hSu⟩ := h
  exact ⟨u,hu,hUS.trans hSu⟩
end SupportIncidence

lemma exists_unit_orthogonal_dim {k n : ℕ} (hn : n < k) (v : Fin n → EuclideanSpace ℝ (Fin k)) :
    ∃ w : EuclideanSpace ℝ (Fin k), ‖w‖ = 1 ∧ ∀ i, ⟪v i,w⟫ = 0 := by
  classical
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin k)) := Submodule.span ℝ (Set.range v)
  have hW : W ≠ ⊤ := by
    intro he
    have hh := finrank_le_of_span_eq_top he
    have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := by simp
    rw [hd,Fintype.card_fin] at hh
    omega
  have hO : Wᗮ ≠ ⊥ := fun he => hW (Submodule.orthogonal_eq_bot_iff.mp he)
  obtain ⟨w,hw,hwne⟩ := (Submodule.ne_bot_iff Wᗮ).mp hO
  refine ⟨(‖w‖⁻¹ : ℝ) • w,norm_smul_inv_norm hwne,?_⟩
  intro i
  rw [inner_smul_right,Submodule.inner_right_of_mem_orthogonal
    (show v i ∈ W from Submodule.subset_span (Set.mem_range_self i)) hw,mul_zero]

lemma Admissible.exists_label_absent_dim {k n : ℕ} {ι : Type*} [Fintype ι]
    {f : EuclideanSpace ℝ (Fin k) → ι → ℝ} (hf : Admissible f) (hn : n < k)
    (v : Fin n → EuclideanSpace ℝ (Fin k)) (hv : ∀ j, ‖v j‖ = 1) :
    ∃ i, ∀ j, i ∉ positiveSupport f (v j) := by
  obtain ⟨w,hw,hvw⟩ := exists_unit_orthogonal_dim hn v
  obtain ⟨i,hi⟩ := hf.support_nonempty hw
  exact ⟨i,fun j hj => Finset.disjoint_left.mp (hf.disjoint_supports (hv j) hw (hvw j)) hj hi⟩

section SixPure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin 3)
lemma Admissible.support_card_three_le_of_card {f : E → ι → ℝ}
    (hf : Admissible f) (hcard : Fintype.card ι = 6) {u : E} (hu : ‖u‖ = 1) :
    (positiveSupport f u).card ≤ 3 := by
  classical
  obtain ⟨e,he⟩ := orthogonal_isometry 2 hu
  let s := (positiveSupport f u)ᶜ
  have hzero : ∀ x, ‖x‖ = 1 → ∀ i ∉ s, f (e x) i = 0 := by
    intro x hx i hi
    have hip : 0 < f u i := (mem_positiveSupport _ _ _).mp (by simpa [s] using hi)
    have hn := hf.nonneg (e x) (by simpa using hx) i
    exact le_antisymm (le_of_not_gt (fun hp => hf.orthogonal u (e x) hu
      (by simpa using hx) (he x) i ⟨hip,hp⟩)) hn
  have hb := ((hf.comp_isometry e).restrict_labels s hzero).label_bound
  have hc : Fintype.card (UpperTriangle (Fin 2)) = 3 := by decide
  rw [hc,Fintype.card_coe,Finset.card_compl,hcard] at hb
  omega

lemma Admissible.support_extends_three_of_card {f : E → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {w : E} (hw : ‖w‖ = 1) :
    ∃ u, ‖u‖ = 1 ∧ positiveSupport f w ⊆ positiveSupport f u ∧ (positiveSupport f u).card = 3 := by
  obtain ⟨u,hu,hwu,hm⟩ := exists_maximal_support f hw
  have hl := hf.support_card_three_le_of_card hcard hu
  have hdim : Fintype.card (UpperTriangle (Fin 3)) = Fintype.card ι := by rw [hcard]; decide
  have hb := hf.maximal_support_complement_bound (k := 2) hdim (by omega) hu hm
  have hc : Fintype.card (UpperTriangle (Fin 2)) = 3 := by decide
  rw [Fintype.card_coe,Finset.card_compl,hcard,hc] at hb
  exact ⟨u,hu,hwu,by omega⟩

lemma Admissible.face_extends_three {f : E → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {U : Finset ι} (hU : SupportFace f U) :
    ∃ I : Finset ι, I.card = 3 ∧ SupportFace f I ∧ U ⊆ I := by
  obtain ⟨w,hw,hUw⟩ := hU
  obtain ⟨u,hu,hwu,huc⟩ := hf.support_extends_three_of_card hcard hw
  exact ⟨positiveSupport f u,huc,⟨u,hu,Finset.Subset.refl _⟩,hUw.trans hwu⟩

lemma Admissible.triangle_no_free_edge {f : E → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {I U : Finset ι} (hIc : I.card = 3)
    (hIf : SupportFace f I) (hUI : U ⊆ I) (hUc : U.card = 2) :
    ∃ I' : Finset ι, I'.card = 3 ∧ SupportFace f I' ∧ U ⊆ I' ∧ I' ≠ I := by
  classical
  obtain ⟨w,hw,hIw⟩ := hIf
  have hmax (u : E) (hu : ‖u‖ = 1) (hIu : I ⊆ positiveSupport f u) : positiveSupport f u = I :=
    (Finset.eq_of_subset_of_card_le hIu (by rw [hIc]; exact hf.support_card_three_le_of_card hcard hu)).symm
  have hcomp : (Iᶜ : Finset ι).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_compl,hcard,hIc]
    decide
  let : Nonempty ↥(Iᶜ : Finset ι) := hcomp.to_subtype
  have hdim : Fintype.card (UpperTriangle (Fin 3)) = Fintype.card ι := by rw [hcard]; decide
  obtain ⟨u,hu,hUu,hnu⟩ := hf.no_free_ridge (k := 2) (by decide) hdim (by omega) hIc hUI hUc hmax hw
    (fun i hi => (mem_positiveSupport f w i).mp (hIw hi))
  obtain ⟨I',hI'c,hI'f,hI'u⟩ := hf.face_extends_three hcard (⟨u,hu,Finset.Subset.refl _⟩ : SupportFace f (positiveSupport f u))
  exact ⟨I',hI'c,hI'f,hUu.trans hI'u,fun he => hnu (he ▸ hI'u)⟩
end SixPure

end BorsukNine

end OAI
