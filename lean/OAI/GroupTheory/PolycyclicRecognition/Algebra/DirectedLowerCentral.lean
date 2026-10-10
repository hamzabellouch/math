import OAI.GroupTheory.PolycyclicRecognition.Algebra.LocallyNilpotentDimension
import Mathlib.Order.Zorn

namespace OAI

/-! # Directed unions with a uniform lower-central bound

The lower-central terms of a directed union are witnessed in its constituent
subgroups. The uniform bound from integral cohomological dimension therefore
allows Zorn's lemma to produce a maximal nilpotent normal subgroup.
-/

namespace PolycyclicRecognition

variable {G : Type} [Group G]

def directedLowerCentral (C : Set (Subgroup G)) (hC : C.Nonempty)
    (hdir : DirectedOn (· ≤ ·) C) (n : ℕ) : Subgroup G where
  carrier := {g | ∃ H ∈ C, g ∈ H.lowerCentralSeries n}
  one_mem' := by
    obtain ⟨H, hH⟩ := hC
    exact ⟨H, hH, Subgroup.one_mem _⟩
  mul_mem' := by
    rintro x y ⟨H, hH, hx⟩ ⟨K, hK, hy⟩
    obtain ⟨L, hL, hHL, hKL⟩ := hdir H hH K hK
    exact ⟨L, hL, Subgroup.mul_mem _
      (Subgroup.lowerCentralSeries_mono n hHL hx)
      (Subgroup.lowerCentralSeries_mono n hKL hy)⟩
  inv_mem' := by
    rintro x ⟨H, hH, hx⟩
    exact ⟨H, hH, Subgroup.inv_mem _ hx⟩

theorem sSup_lowerCentralSeries_le_directedLowerCentral
    (C : Set (Subgroup G)) (hC : C.Nonempty) (hdir : DirectedOn (· ≤ ·) C) (n : ℕ) :
    (sSup C).lowerCentralSeries n ≤ directedLowerCentral C hC hdir n := by
  induction n with
  | zero =>
    intro g hg
    exact (Subgroup.mem_sSup_of_directedOn hC hdir).mp hg
  | succ n ih =>
    rw [Subgroup.lowerCentralSeries_succ]
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    obtain ⟨H, hH, hxH⟩ := ih hx
    obtain ⟨K, hK, hyK⟩ := (Subgroup.mem_sSup_of_directedOn hC hdir).mp hy
    obtain ⟨L, hL, hHL, hKL⟩ := hdir H hH K hK
    exact ⟨L, hL, Subgroup.commutator_mem_commutator
      (Subgroup.lowerCentralSeries_mono n hHL hxH) (hKL hyK)⟩

theorem sSup_lowerCentralSeries_eq_bot
    (C : Set (Subgroup G)) (hC : C.Nonempty) (hdir : DirectedOn (· ≤ ·) C)
    (n : ℕ) (hn : ∀ H ∈ C, H.lowerCentralSeries n = ⊥) :
    (sSup C).lowerCentralSeries n = ⊥ := by
  apply eq_bot_iff.mpr
  intro g hg
  obtain ⟨H, hH, hgH⟩ := sSup_lowerCentralSeries_le_directedLowerCentral C hC hdir n hg
  simpa only [hn H hH] using hgH

theorem exists_maximal_nilpotent_normal_subgroup
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ F : Subgroup G, F.Normal ∧ Group.IsNilpotent F ∧
      ∀ N : Subgroup G, N.Normal → Group.IsNilpotent N → F ≤ N → N = F := by
  obtain ⟨d, hd⟩ := hG
  let := hd
  let P : Set (Subgroup G) := {N | N.Normal ∧ Group.IsNilpotent N}
  obtain ⟨F, hF, hmax⟩ := zorn_le₀ P (by
    intro C hC hchain
    rcases C.eq_empty_or_nonempty with rfl | hne
    · exact ⟨⊥, ⟨inferInstance, inferInstance⟩, by simp⟩
    · have hnormal : (sSup C).Normal := Subgroup.sSup_normal C (fun N hN => (hC hN).1)
      have hnil : Group.IsNilpotent (sSup C : Subgroup G) := by
        apply (Subgroup.isNilpotent_iff_lowerCentralSeries (sSup C)).mpr
        refine ⟨2 * d, sSup_lowerCentralSeries_eq_bot C hne hchain.directedOn _ ?_⟩
        intro N hN
        let := (hC hN).2
        exact Subgroup.lowerCentralSeries_eq_bot_of_nilpotencyClass_le
          (nilpotent_subgroup_class_le d N)
      exact ⟨sSup C, ⟨hnormal, hnil⟩, fun N hN => le_sSup hN⟩)
  exact ⟨F, hF.1, hF.2, fun N hn hnil hFN => le_antisymm (hmax ⟨hn, hnil⟩ hFN) hFN⟩

end PolycyclicRecognition

end OAI
