import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.CartierExtraction

namespace OAI


                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}} [IsIntegral X]

lemma associated_power_step {R : Type*} [CommMonoid R] (f b c z : R) (j : ℕ)
    (h : Associated (f^j*b) c) (h' : Associated (f*c) z) :
    Associated (f^(j+1)*b) z := by
  have H := h.mul_left f
  rw [← mul_assoc,← pow_succ'] at H
  exact H.trans h'

theorem maximal_cartier_extraction (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L : LineBundle X) (d : ℕ) (hd : 0 < d) {σ : Type} [Fintype σ]
    (k : ℂ →+* Γ(X,⊤)) (s : σ → (O X ⟶ (L.pow d).sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → ℂ)
    (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (U : X.affineOpens) [Nonempty U.1]
    [Nonempty ((sectionIdeal k s hs v).subschemeι ⁻¹ᵁ U.1).toScheme]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hnu : ¬ IsUnit (affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s v)))
    (a : ℕ) (t : O X ⟶ (L.pow a).sheaf) (ht : t ≠ 0) :
    ∃ j n : ℕ, a = j*d+n ∧ ∃ q : O X ⟶ (L.pow n).sheaf, q ≠ 0 ∧
      pullbackSection (sectionIdeal k s hs v).subschemeι q ≠ 0 ∧
      Associated ((affineCoefficient U (localPowerFrame U.1 e d)
        (sectionCombination k s v))^j * affineCoefficient U (localPowerFrame U.1 e n) q)
        (affineCoefficient U (localPowerFrame U.1 e a) t) := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    by_cases hv : pullbackSection (sectionIdeal k s hs v).subschemeι t = 0
    · have hda : d ≤ a := by
        by_contra h
        exact small_power_restriction_ne_zero p L d k s hs v hne U e hnu a
          (by omega) t ht hv
      obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hda
      obtain ⟨q,hq,-⟩ := divide_by_power_section p L d n k s hs v hne t hv
      have hqn : q ≠ 0 := global_quotient_ne_zero _ t ht q hq
      obtain ⟨j,r,he,z,hz,hzv,hassoc⟩ := ih n (by omega) q hqn
      refine ⟨j+1,r,by rw [he]; ring,z,hz,hzv,?_⟩
      have ha := affineCoefficient_division L U e d n (sectionCombination k s v) q
      rw [hq] at ha
      exact associated_power_step _ _ _ _ j hassoc ha
    · exact ⟨0,a,by simp,t,ht,hv,by simpa only [pow_zero,one_mul] using (Associated.refl
        (affineCoefficient U (localPowerFrame U.1 e a) t))⟩
end
end MaximalSeshadri.Geometry

end



end OAI
