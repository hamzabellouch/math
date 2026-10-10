import OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal

namespace OAI

namespace PiExponentSeshadri.IdealPullback
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
variable {X Y : Scheme}

lemma comap_pow (I : X.IdealSheafData) (f : Y ⟶ X) (m : ℕ) :
    (I^m).comap f = (I.comap f)^m := by
  have hc : ∀ y : Y, ∃ (U : Y.affineOpens) (V : X.affineOpens),
      y ∈ U.1 ∧ U.1 ≤ f ⁻¹ᵁ V.1 := by
    intro y
    obtain ⟨V, hV, hyV, _⟩ := exists_isAffineOpen_mem_and_subset
      (show f y ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset
      (show y ∈ f ⁻¹ᵁ V from hyV)
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hyU, hUV⟩
  choose U V hy hUV using hc
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hy y⟩
  · intro y
    rw [comap_ideal (I^m) f (U y) (V y) (hUV y)]
    change (I.ideal (V y)^m).map _ = ((I.comap f).ideal (U y))^m
    rw [Ideal.map_pow, comap_ideal I f (U y) (V y) (hUV y)]

lemma specIdeal_pow {R : Type} [CommRing R] (I : Ideal R) (m : ℕ) :
    specIdeal (I^m) = (specIdeal I)^m := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  simpa only [specIdeal_top, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply] using
    Ideal.map_pow (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom I m

end
end PiExponentSeshadri.IdealPullback

end OAI
