import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchingIntersection

namespace OAI

/-! Matching value-and-slope data joins the interior and outgoing physical solutions. -/

open Set Filter
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralPhysicalField_add (νp νm η : ℂ) (m : ℕ) (Q : ℂ)
    (r : ℝ) (Z W : E₄) :
    spectralPhysicalCircularField νp νm η m Q r (Z+W)=
      spectralPhysicalCircularField νp νm η m Q r Z+
        spectralPhysicalCircularField νp νm η m Q r W := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [spectralPhysicalCircularField,Prod.fst_add,Prod.snd_add]
  all_goals ring

theorem spectralPhysicalField_smul (νp νm η : ℂ) (m : ℕ) (Q a : ℂ)
    (r : ℝ) (Z : E₄) :
    spectralPhysicalCircularField νp νm η m Q r (a • Z)=
      a • spectralPhysicalCircularField νp νm η m Q r Z := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [spectralPhysicalCircularField,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  all_goals ring

theorem spectral_ode_join {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : ℝ → E) (V : ℝ → E → E) (R : ℝ) (hR : 0 < R)
    (hF : ∀ r ∈ Ioc 0 R, HasDerivAt F (V r (F r)) r)
    (hG : ∀ r, R ≤ r → HasDerivAt G (V r (G r)) r)
    (hmatch : F R=G R) :
    ∀ r, 0 < r → HasDerivAt (fun t => if t ≤ R then F t else G t)
      (V r (if r ≤ R then F r else G r)) r := by
  intro r hr
  rcases lt_trichotomy r R with hlt | heq | hgt
  · rw [ite_eq_left hlt.le]
    apply (hF r ⟨hr,hlt.le⟩).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hlt] with t ht
    exact ite_eq_left ht.le
  · subst r
    rw [ite_eq_left le_rfl]
    have hleft : HasDerivWithinAt (fun t => if t ≤ R then F t else G t)
        (V R (F R)) (Iic R) R := by
      apply (hF R ⟨hR,le_rfl⟩).hasDerivWithinAt.congr
      · intro t ht
        exact ite_eq_left ht
      · exact ite_eq_left le_rfl
    have hg := hG R le_rfl
    rw [← hmatch] at hg
    have hright : HasDerivWithinAt (fun t => if t ≤ R then F t else G t)
        (V R (F R)) (Ici R) R := by
      apply hg.hasDerivWithinAt.congr
      · intro t ht
        rcases (show R ≤ t from ht).eq_or_lt with rfl | ht
        · simpa only [ite_eq_left le_rfl] using hmatch
        · exact ite_eq_right ht.not_ge
      · simpa only [ite_eq_left le_rfl] using hmatch
    have h := hleft.union hright
    rw [Iic_union_Ici] at h
    exact h.hasDerivAt (by simp)
  · rw [ite_eq_right hgt.not_ge]
    apply (hG r hgt.le).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hgt] with t ht
    exact ite_eq_right ht.not_ge

end DefocusingNLS

end OAI
