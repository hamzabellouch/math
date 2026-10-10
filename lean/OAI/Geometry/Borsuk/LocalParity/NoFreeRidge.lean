import Mathlib
import OAI.Geometry.Borsuk.LocalParity.MatrixParity
import OAI.Geometry.Borsuk.LocalParity.SphereParity

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Set SimplicialChains
open scoped RealInnerProductSpace
section NoFreeRidge
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
lemma Admissible.no_free_indexed_facet {f : E → ι → ℝ} (hf : Admissible f)
    (hk : 0 < k) (hdim : Fintype.card (UpperTriangle (Fin (k+1))) = Fintype.card ι)
    (hn : 1 < Fintype.card ι) {I : Finset ι} [Nonempty ↥(Iᶜ : Finset ι)]
    (a : Fin (k+1) ≃ ↥I)
    (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w : E} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i) :
    ∃ u : E, ‖u‖ = 1 ∧ (∀ j : Fin k, 0 < f u (a j.succ).val) ∧ ¬ positiveSupport f u ⊆ I := by
  classical
  by_contra hnfree
  push Not at hnfree
  obtain ⟨e,z,he,hes,hz,hr,hfin⟩ := hf.exists_regular_facet_point a hw hwi
  have ho := hf.regular_facet_level_odd hdim hn a hmax hw hwi e he hes hz hr hfin
  have heven := hf.regular_facet_level_even hk a hnfree hw hwi e he hes hz hr hfin
  rw [heven] at ho
  exact zero_ne_one ho

lemma Admissible.no_free_ridge {f : E → ι → ℝ} (hf : Admissible f)
    (hk : 0 < k) (hdim : Fintype.card (UpperTriangle (Fin (k+1))) = Fintype.card ι)
    (hn : 1 < Fintype.card ι) {I U : Finset ι} [Nonempty ↥(Iᶜ : Finset ι)]
    (hI : I.card = k+1) (hUI : U ⊆ I) (hU : U.card = k)
    (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w : E} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i) :
    ∃ u : E, ‖u‖ = 1 ∧ U ⊆ positiveSupport f u ∧ ¬ positiveSupport f u ⊆ I := by
  classical
  have hdiff : (I \ U).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_sdiff_of_subset hUI,hI,hU]
    omega
  obtain ⟨i,hi⟩ := hdiff
  have hiI := (Finset.mem_sdiff.mp hi).1
  have hiU := (Finset.mem_sdiff.mp hi).2
  let b : Fin (k+1) ≃ ↥I := (Fintype.equivFinOfCardEq (by simpa using hI)).symm
  let a : Fin (k+1) ≃ ↥I := (Equiv.swap 0 (b.symm ⟨i,hiI⟩)).trans b
  have ha : (a 0).val = i := by simp [a]
  obtain ⟨u,hu,hup,hnot⟩ := hf.no_free_indexed_facet hk hdim hn a hmax hw hwi
  refine ⟨u,hu,?_,hnot⟩
  intro j hj
  obtain ⟨l,hl⟩ := a.surjective ⟨j,hUI hj⟩
  have hlj : (a l).val = j := congrArg Subtype.val hl
  have hl0 : l ≠ 0 := by
    intro hl0
    rw [hl0,ha] at hlj
    exact hiU (hlj ▸ hj)
  obtain ⟨q,rfl⟩ := Fin.eq_succ_of_ne_zero hl0
  rw [← hlj]
  exact (mem_positiveSupport f u _).mpr (hup q)
end NoFreeRidge
end BorsukNine

end OAI
