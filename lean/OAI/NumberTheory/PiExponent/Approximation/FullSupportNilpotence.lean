import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Noetherian.Nilpotent

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme}

lemma idealSheaf_le_nilradical_of_fullSupport (I : X.IdealSheafData)
    (hI : I.support = ⊤) : I ≤ X.nilradical := by
  have h : (⊤ : Closeds X) ≤ I.support := by rw [hI]
  simpa only [Scheme.IdealSheafData.vanishingIdeal_top] using
    Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp h

lemma affineIdeal_isNilpotent_of_fullSupport [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I.support = ⊤) (U : X.affineOpens) :
    IsNilpotent (I.ideal U) := by
  let := IsLocallyNoetherian.component_noetherian U
  apply (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)).mpr
  exact idealSheaf_le_nilradical_of_fullSupport I hI U

theorem exists_pos_pow_eq_bot_of_fullSupport [IsNoetherian X]
    (I : X.IdealSheafData) (hI : I.support = ⊤) :
    ∃ n : ℕ, 0 < n ∧ I ^ n = ⊥ := by
  classical
  have hlocal : ∀ U : X.affineOpens, ∃ n : ℕ, I.ideal U ^ n = ⊥ :=
    fun U => affineIdeal_isNilpotent_of_fullSupport I hI U
  choose n hn using hlocal
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => (U.1 : Set X)) (fun U => U.1.isOpen)
    (by
      intro x _
      have hx : x ∈ (⨆ U : X.affineOpens, U.1) := by
        rw [iSup_affineOpens_eq_top X]
        trivial
      obtain ⟨U, hU⟩ := Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨U, hU⟩)
  refine ⟨S.sup n + 1, Nat.succ_pos _, ?_⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top (fun U : S => U.val)
  · apply top_unique
    intro x _
    obtain ⟨U, hU⟩ := Set.mem_iUnion.mp (hS (show x ∈ Set.univ from trivial))
    obtain ⟨hUS, hxU⟩ := Set.mem_iUnion.mp hU
    exact Opens.mem_iSup.mpr ⟨⟨U, hUS⟩, hxU⟩
  · intro U
    change I.ideal U.val ^ (S.sup n + 1) = ⊥
    apply le_bot_iff.mp
    calc
      I.ideal U.val ^ (S.sup n + 1) ≤ I.ideal U.val ^ n U.val :=
        Ideal.pow_le_pow_right ((Finset.le_sup U.property).trans (Nat.le_succ _))
      _ = ⊥ := hn U.val

theorem exists_pos_pow_eq_bot_of_support_univ [IsNoetherian X]
    (I : X.IdealSheafData) (hI : (I.support : Set X) = Set.univ) :
    ∃ n : ℕ, 0 < n ∧ I ^ n = ⊥ :=
  exists_pos_pow_eq_bot_of_fullSupport I (SetLike.coe_injective hI)

theorem exists_pos_nilradical_pow_eq_bot [IsNoetherian X] :
    ∃ n : ℕ, 0 < n ∧ X.nilradical ^ n = ⊥ :=
  exists_pos_pow_eq_bot_of_fullSupport X.nilradical X.support_nilradical

end
end PiExponentSeshadri.Geometry

end OAI
