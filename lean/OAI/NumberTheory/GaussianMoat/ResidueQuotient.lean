import OAI.NumberTheory.GaussianMoat.FiniteEntropy

namespace OAI

namespace GaussianMoat

noncomputable def multiples (π : GaussianInt) : Submodule ℤ GaussianInt :=
  (twoVectorMap π (π * ⟨0,1⟩)).range

lemma twoVectorMap_mul_i (π z : GaussianInt) :
    twoVectorMap π (π * ⟨0,1⟩) z = π*z := by
  rw [twoVectorMap_apply]
  ext <;> simp [zsmul_eq_mul,Zsqrtd.re_mul,Zsqrtd.im_mul] <;> ring

lemma mem_multiples (π z : GaussianInt) : z ∈ multiples π ↔ π ∣ z := by
  simp only [multiples, LinearMap.mem_range, twoVectorMap_mul_i]
  exact ⟨fun ⟨a,ha⟩ => ⟨a,ha.symm⟩,fun ⟨a,ha⟩ => ⟨a,ha.symm⟩⟩

lemma multiples_index {π : GaussianInt} (hπ : π ≠ 0) :
    Nat.card (GaussianInt ⧸ multiples π) = π.norm.natAbs := by
  have he : π.re*(π*⟨0,1⟩).im-π.im*(π*⟨0,1⟩).re = π.norm := by
    simp [Zsqrtd.re_mul,Zsqrtd.im_mul,Zsqrtd.norm]
  have hn : π.norm ≠ 0 := (GaussianInt.norm_pos.mpr hπ).ne'
  have h := twoVectorMap_quotient_card (a := π) (b := π*⟨0,1⟩) (he.trans_ne hn)
  simpa only [multiples,he] using h

noncomputable def gaussianResidue (π z : GaussianInt) : GaussianInt ⧸ multiples π :=
  Submodule.Quotient.mk z

lemma gaussianResidue_eq (π z w : GaussianInt) :
    gaussianResidue π z = gaussianResidue π w ↔ π ∣ z-w := by
  rw [gaussianResidue,gaussianResidue,Submodule.Quotient.eq,mem_multiples]

instance : Countable GaussianInt := latticeCoords.injective.countable

instance (π : GaussianInt) : Countable (GaussianInt ⧸ multiples π) :=
  (Submodule.Quotient.mk_surjective (p := multiples π)).countable

noncomputable def residueCode (π z : GaussianInt) : ℕ := by
  let := Encodable.ofCountable (GaussianInt ⧸ multiples π)
  exact Encodable.encode (gaussianResidue π z)

lemma residueCode_eq (π z w : GaussianInt) :
    residueCode π z = residueCode π w ↔ π ∣ z-w := by
  let := Encodable.ofCountable (GaussianInt ⧸ multiples π)
  change Encodable.encode (gaussianResidue π z) = Encodable.encode (gaussianResidue π w) ↔ _
  rw [Encodable.encode_inj,gaussianResidue_eq]

lemma residueCode_sub {π x y x' y' : GaussianInt}
    (hx : residueCode π x = residueCode π x') (hy : residueCode π y = residueCode π y') :
    residueCode π (x-y) = residueCode π (x'-y') := by
  rw [residueCode_eq] at *
  convert dvd_sub hx hy using 1; ring

lemma residueCode_add {π x y x' y' : GaussianInt}
    (hx : residueCode π x = residueCode π x') (hy : residueCode π y = residueCode π y') :
    residueCode π (x+y) = residueCode π (x'+y') := by
  rw [residueCode_eq] at *
  convert dvd_add hx hy using 1; ring

lemma finite_gaussianResidue {π : GaussianInt} (hπ : π ≠ 0) :
    Finite (GaussianInt ⧸ multiples π) := by
  apply Nat.finite_of_card_ne_zero
  rw [multiples_index hπ]
  simpa only [Int.natAbs_ne_zero] using (GaussianInt.norm_pos.mpr hπ).ne'

lemma residueCode_range_card {π : GaussianInt} (hπ : π ≠ 0) :
    (Set.range (residueCode π)).Finite ∧ (Set.range (residueCode π)).ncard = π.norm.natAbs := by
  let := finite_gaussianResidue hπ
  let := Encodable.ofCountable (GaussianInt ⧸ multiples π)
  have hs : Function.Surjective (gaussianResidue π) := Submodule.Quotient.mk_surjective _
  have hr : Set.range (residueCode π) = Set.range
      (Encodable.encode : (GaussianInt ⧸ multiples π) → ℕ) := by
    change Set.range (Encodable.encode ∘ gaussianResidue π) = _
    rw [Set.range_comp,hs.range_eq,Set.image_univ]
  rw [hr]
  refine ⟨Set.finite_range _,?_⟩
  rw [Set.ncard_range_of_injective Encodable.encode_injective,multiples_index hπ]

end GaussianMoat

end OAI
