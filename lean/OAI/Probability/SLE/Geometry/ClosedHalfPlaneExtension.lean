import OAI.Probability.SLE.Geometry.ClosedComplexUnion

namespace OAI

/-! Extend a closed half-plane homeomorphism fixing its boundary by the
identity on the other half-plane. -/
noncomputable section
open Set Complex

namespace SLEExactGauge

theorem closedHalfPlane_extension
    (e : {z : ℂ // 0 ≤ z.im} ≃ₜ {z : ℂ // 0 ≤ z.im})
    (he : ∀ (z : {z : ℂ // 0 ≤ z.im}), z.val.im=0 → (e z:ℂ)=z) :
    ∃ F : ℂ ≃ₜ ℂ,
      (∀ (z : ℂ) (hz : 0 ≤ z.im), F z=(e ⟨z,hz⟩:ℂ)) ∧
      (∀ x : ℝ, F (x:ℂ)=(x:ℂ)) ∧
      MapsTo F {z : ℂ | 0 < z.im} {z : ℂ | 0 < z.im} := by
  classical
  let A : Set ℂ := {z | 0 ≤ z.im}
  let B : Set ℂ := {z | z.im ≤ 0}
  have hA : IsClosed A := isClosed_le continuous_const Complex.continuous_im
  have hB : IsClosed B := isClosed_le Complex.continuous_im continuous_const
  have hfix (z : A) (hz : (z:ℂ) ∈ B) : (e z:ℂ)=z :=
    he z (le_antisymm hz z.property)
  have hfixi (z : A) (hz : (z:ℂ) ∈ B) : (e.symm z:ℂ)=z := by
    have hh : e z=z := Subtype.ext (hfix z hz)
    have hh' := congrArg e.symm hh
    rw [e.symm_apply_apply] at hh'
    exact congrArg Subtype.val hh'.symm
  let E := closedComplexUnionHomeomorph hA hA hB e hfix hfixi
  have hU : A ∪ B=univ := by
    ext z
    exact iff_true_intro (le_total 0 z.im)
  let j : ℂ ≃ₜ ↥(A ∪ B) := (Homeomorph.Set.univ ℂ).symm.trans
    (Homeomorph.setCongr hU.symm)
  let F : ℂ ≃ₜ ℂ := (j.trans E).trans j.symm
  have hF (z : ℂ) (hz : 0 ≤ z.im) : F z=(e ⟨z,hz⟩:ℂ) := by
    change (if hx : z ∈ A then (e ⟨z,hx⟩:ℂ) else z)=_
    rw [dite_eq_left (show z ∈ A from hz)]
  have hFr (x : ℝ) : F (x:ℂ)=(x:ℂ) := by
    rw [hF _ (by simp)]
    exact he _ (by simp)
  refine ⟨F,hF,hFr,?_⟩
  intro z hz
  have hn : 0 ≤ (F z).im := by
    rw [hF z hz.le]
    exact (e ⟨z,hz.le⟩).property
  apply lt_of_le_of_ne hn
  intro hzero
  have hx : F z=((F z).re:ℂ) := Complex.ext rfl (by simpa using hzero.symm)
  have hsame : z=((F z).re:ℂ) := F.injective (hx.trans (hFr _).symm)
  have hz0 := congrArg Complex.im hsame
  simpa only [Complex.ofReal_im] using hz.ne' hz0

end SLEExactGauge

end

end OAI
