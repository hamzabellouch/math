import OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X Y B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

lemma invertible_top (f : Y ⟶ X) : InvertiblePullbackIdeal ⊤ f := by
  apply InvertibleLocal.invertible_of_local_equations
  intro y
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : Y.Opens) from trivial)
  refine ⟨⟨U, hU⟩, hyU, 1, isRegular_one, ?_⟩
  simp

lemma isBlowup_id (hI : InvertiblePullbackIdeal I (𝟙 X)) :
    IsBlowup I (𝟙 X) := by
  refine ⟨hI, fun Y f _ => ⟨f, by simp, ?_⟩⟩
  intro g hg
  simpa using hg

lemma IsBlowup.isIso_of_invertible (hπ : IsBlowup I π)
    (hI : InvertiblePullbackIdeal I (𝟙 X)) : IsIso π := by
  have hπe : (hπ.iso (isBlowup_id hI)).hom = π := by
    simpa using hπ.iso_hom_comp (isBlowup_id hI)
  rw [← hπe]
  infer_instance

lemma IsBlowup.isIso_over_complement (hπ : IsBlowup I π) :
    IsIso (pullback.fst (Scheme.Opens.ι (X := X) I.support.compl) π) := by
  apply (hπ.open_baseChange (Scheme.Opens.ι (X := X) I.support.compl)).isIso_of_invertible
  have he : I.comap (Scheme.Opens.ι (X := X) I.support.compl) = ⊤ := by
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
    rw [Scheme.IdealSheafData.support_comap]
    ext x
    change (x.val ∈ I.support ↔ False)
    exact iff_false_intro x.property
  rw [he]
  exact invertible_top _

end
end PiExponentSeshadri.Geometry

end OAI
