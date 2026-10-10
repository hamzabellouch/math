import OAI.Analysis.RelativeGeneration.OriginalTransport

namespace OAI

noncomputable section

/- Actual image inclusion, algebra equivalence, hypotheses, and relative generation. -/
namespace Generator.Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)
local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit
local notation "R" => traceFreeHilbertClosure hfactor hdiff hfinite hunit
local notation "σ" => traceFreeHilbertClosureTrace hfactor hdiff hfinite hunit
local notation "e" => traceFreeHilbertEquiv hfactor hdiff hfinite hunit

/-- The actual WOT-closed image of the original given subalgebra. -/
def traceFreeRelativeImage (P : StarSubalgebra ℂ (H →L[ℂ] H)) (hP : WOTClosed P) :
    VonNeumannAlgebra K :=
  vonNeumannOfWOTClosed ((P.comap M.toStarSubalgebra.subtype).map π)
    (traceFreeSubalgebraImage_wotClosed hfactor hdiff hfinite hunit P hP)

variable (P : StarSubalgebra ℂ (H →L[ℂ] H)) (hP : WOTClosed P)
local notation "N" => traceFreeRelativeImage hfactor hdiff hfinite hunit P hP

theorem traceFreeRelativeImage_le : N ≤ R := by
  rintro a ⟨b,hb,rfl⟩
  exact traceFreeHilbertAction_mem_closure hfactor hdiff hfinite hunit b

variable (hPM : P ≤ M.toStarSubalgebra)

def traceFreeRelativeImageHom : P →⋆ₐ[ℂ] (N).toStarSubalgebra :=
  ((π).comp (StarSubalgebra.inclusion hPM)).codRestrict (N).toStarSubalgebra
    (fun a => ⟨StarSubalgebra.inclusion hPM a,a.property,rfl⟩)

theorem traceFreeRelativeImageHom_bijective :
    Function.Bijective (traceFreeRelativeImageHom hfactor hdiff hfinite hunit P hP hPM) := by
  constructor
  · intro a b h
    apply Subtype.ext
    have he := traceFreeHilbertAction_injective hfactor hdiff hfinite hunit
      (congrArg Subtype.val h)
    exact congrArg (fun x : M.toStarSubalgebra => x.val) he
  · rintro ⟨b,c,hc,rfl⟩
    exact ⟨⟨c.val,hc⟩,rfl⟩

def traceFreeRelativeImageEquiv : P ≃⋆ₐ[ℂ] (N).toStarSubalgebra :=
  StarAlgEquiv.ofBijective (traceFreeRelativeImageHom hfactor hdiff hfinite hunit P hP hPM)
    (traceFreeRelativeImageHom_bijective hfactor hdiff hfinite hunit P hP hPM)

include hPM in
theorem traceFreeRelativeImage_isII1Factor (hII : IsII1Factor P) :
    IsII1Factor (N).toStarSubalgebra :=
  isII1Factor_of_starAlgEquiv
    (traceFreeRelativeImageEquiv hfactor hdiff hfinite hunit P hP hPM) hII
    (vonNeumann_wotClosed N)

theorem traceFreeRelativeImage_irreducible
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : P, StarSubalgebra.inclusion hPM a*c=c*StarSubalgebra.inclusion hPM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra)) :
    ∀ c : (R).toStarSubalgebra,
      (∀ a : (N).toStarSubalgebra,
        coordinateInclusion (traceFreeRelativeImage_le hfactor hdiff hfinite hunit P hP) a*c =
        c*coordinateInclusion (traceFreeRelativeImage_le hfactor hdiff hfinite hunit P hP) a) →
      ∃ z : ℂ,c=z • (1 : (R).toStarSubalgebra) := by
  intro c hc
  have hcomm (a : P) :
      StarSubalgebra.inclusion hPM a*(e).symm c=(e).symm c*StarSubalgebra.inclusion hPM a := by
    apply (e).injective
    rw [map_mul,map_mul]
    change (e) (StarSubalgebra.inclusion hPM a)*(e) ((e).symm c) =
      (e) ((e).symm c)*(e) (StarSubalgebra.inclusion hPM a)
    rw [StarAlgEquiv.apply_symm_apply]
    exact hc (traceFreeRelativeImageEquiv hfactor hdiff hfinite hunit P hP hPM a)
  obtain ⟨z,hz⟩ := hirr ((e).symm c) hcomm
  exact ⟨z,by simpa only [StarAlgEquiv.apply_symm_apply,map_smul,map_one] using congrArg (e) hz⟩

include hPM in
/-- Generation is transported both ways, using closed preimages and closed images. -/
theorem traceFreeRelativeGeneration_iff (u : M.toStarSubalgebra) :
    wstar ((P : Set (H →L[ℂ] H)) ∪ {u.val}) = M.toStarSubalgebra ↔
      wstar ((N : Set (K →L[ℂ] K)) ∪ {π u}) = (R).toStarSubalgebra := by
  constructor
  · intro hgen
    let Q := vonNeumannOfWOTClosed
      (wstar ((N : Set (K →L[ℂ] K)) ∪ {π u})) (wstar_closed _)
    have hQR : Q ≤ R := wstar_le (vonNeumann_wotClosed R) (by
      rintro a (ha|ha)
      · exact traceFreeRelativeImage_le hfactor hdiff hfinite hunit P hP ha
      · obtain rfl := Set.mem_singleton_iff.mp ha
        exact traceFreeHilbertAction_mem_closure hfactor hdiff hfinite hunit u)
    have hpre : M.toStarSubalgebra ≤ concretePreimage (e).toStarAlgHom Q.toStarSubalgebra := by
      apply le_trans (le_of_eq hgen.symm)
      apply wstar_le (traceFreeHilbert_preimage_wotClosed hfactor hdiff hfinite hunit Q hQR)
      rintro a (ha|ha)
      · apply (mem_concretePreimage (e).toStarAlgHom Q.toStarSubalgebra ⟨a,hPM ha⟩).mpr
        exact subset_wstar _ (Or.inl ⟨⟨a,hPM ha⟩,ha,rfl⟩)
      · obtain rfl := Set.mem_singleton_iff.mp ha
        exact (mem_concretePreimage (e).toStarAlgHom Q.toStarSubalgebra u).mpr
          (subset_wstar _ (Or.inr (Set.mem_singleton _)))
    apply le_antisymm (show Q.toStarSubalgebra ≤ (R).toStarSubalgebra from hQR)
    intro b hb
    let a := (e).symm ⟨b,hb⟩
    have ha := (mem_concretePreimage (e).toStarAlgHom Q.toStarSubalgebra a).mp (hpre a.property)
    change ((e) ((e).symm ⟨b,hb⟩)).val ∈ Q.toStarSubalgebra at ha
    simpa only [StarAlgEquiv.apply_symm_apply] using ha
  · intro hgen
    let A := wstar ((P : Set (H →L[ℂ] H)) ∪ {u.val})
    have hAM : A ≤ M.toStarSubalgebra := wstar_le (vonNeumann_wotClosed M) (by
      rintro a (ha|ha)
      · exact hPM ha
      · obtain rfl := Set.mem_singleton_iff.mp ha
        exact u.property)
    let B := (A.comap M.toStarSubalgebra.subtype).map π
    have hRB : (R).toStarSubalgebra ≤ B := by
      apply le_trans (le_of_eq hgen.symm)
      apply wstar_le (traceFreeSubalgebraImage_wotClosed hfactor hdiff hfinite hunit A
        (wstar_closed _))
      rintro a (ha|ha)
      · obtain ⟨b,hb,rfl⟩ := ha
        exact ⟨b,subset_wstar _ (Or.inl hb),rfl⟩
      · obtain rfl := Set.mem_singleton_iff.mp ha
        exact ⟨u,subset_wstar _ (Or.inr (Set.mem_singleton _)),rfl⟩
    apply le_antisymm hAM
    intro a ha
    obtain ⟨b,hb,he⟩ := hRB (traceFreeHilbertAction_mem_closure hfactor hdiff hfinite hunit ⟨a,ha⟩)
    have he' := traceFreeHilbertAction_injective hfactor hdiff hfinite hunit he
    change b.val ∈ A at hb
    rwa [he'] at hb

end Generator.Tracial

end

end OAI
