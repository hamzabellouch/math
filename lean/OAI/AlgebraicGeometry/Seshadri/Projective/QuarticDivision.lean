import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.GlobalQuartic
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorDivision

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}} [IsIntegral X]

theorem divide_by_doublePointQuartic (p : X ⟶ Spec (CommRingCat.of ℂ))
    (L M : LineBundle X) {σ : Type} [Fintype σ] (k : ℂ →+* Γ(X,⊤))
    (s : Option σ → (O X ⟶ L.sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : QuarticIndex σ → ℂ) (hne : sectionCombination k (doublePointQuartics s) v ≠ 0)
    (t : O X ⟶ ((L.pow 4).tensor M).sheaf)
    (ht : pullbackSection (doublePointQuarticIdeal k s hs v).subschemeι t = 0) :
    ∃! q : O X ⟶ M.sheaf,
      q ≫ sectionMultiply (L.pow 4) M (sectionCombination k (doublePointQuartics s) v) = t := by
  have hc : sectionCombination k (augmentedQuartics s) (fun j => j.elim 0 v) =
      sectionCombination k (doublePointQuartics s) v := by
    rw [sectionCombination_extend_zero]
    rfl
  have hn : sectionCombination k (augmentedQuartics s) (fun j => j.elim 0 v) ≠ 0 := by
    rwa [hc]
  have H := divide_by_generated_section (X := X) p (L.pow 4) M k (augmentedQuartics s)
    (augmentedQuartics_cover s hs) (fun j => j.elim 0 v) hn t ht
  exact (congrArg (fun globalSection : O X ⟶ (L.pow 4).sheaf =>
    ∃! q : O X ⟶ M.sheaf, q ≫ sectionMultiply (L.pow 4) M globalSection = t) hc).mp H

def quarticPowerProductIso (L : LineBundle X) (d n : ℕ) :
    moduleTensor X ((L.pow d).pow 4).sheaf (L.pow n).sheaf ≅
      (L.pow (d*4+n)).sheaf :=
  moduleTensorIso (linePowerMul L d 4) (Iso.refl _) ≪≫
    (linePowerAdd L (d*4) n).symm

theorem divide_by_doublePointQuartic_power (p : X ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle X) (d n : ℕ) {σ : Type} [Fintype σ] (k : ℂ →+* Γ(X,⊤))
    (s : Option σ → (O X ⟶ (L.pow d).sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : QuarticIndex σ → ℂ) (hne : sectionCombination k (doublePointQuartics s) v ≠ 0)
    (t : O X ⟶ (L.pow (d*4+n)).sheaf)
    (ht : pullbackSection (doublePointQuarticIdeal k s hs v).subschemeι t = 0) :
    ∃! q : O X ⟶ (L.pow n).sheaf,
      q ≫ sectionMultiply ((L.pow d).pow 4) (L.pow n)
        (sectionCombination k (doublePointQuartics s) v) ≫
        (quarticPowerProductIso L d n).hom = t := by
  let e : (((L.pow d).pow 4).tensor (L.pow n)).sheaf ≅
      (L.pow (d*4+n)).sheaf := quarticPowerProductIso L d n
  have hv : pullbackSection (doublePointQuarticIdeal k s hs v).subschemeι (t ≫ e.inv) = 0 := by
    unfold pullbackSection at ht ⊢
    rw [Functor.map_comp,← Category.assoc,ht,zero_comp]
  obtain ⟨q,hq,huniq⟩ := divide_by_doublePointQuartic p (L.pow d) (L.pow n)
    k s hs v hne (t ≫ e.inv) hv
  let multiplication : (L.pow n).sheaf ⟶ (((L.pow d).pow 4).tensor (L.pow n)).sheaf :=
    sectionMultiply ((L.pow d).pow 4) (L.pow n)
      (sectionCombination k (doublePointQuartics s) v)
  change q ≫ multiplication = t ≫ e.inv at hq
  refine ⟨q,?_,?_⟩
  · change q ≫ multiplication ≫ e.hom = t
    rw [← Category.assoc,hq,Category.assoc,e.inv_hom_id,Category.comp_id]
  · intro r hr
    apply huniq
    change r ≫ multiplication = t ≫ e.inv
    apply (cancel_mono e.hom).mp
    change r ≫ multiplication ≫ e.hom = t at hr
    simpa only [Category.assoc,e.inv_hom_id,Category.comp_id] using hr

omit [IsIntegral X] in
lemma doublePointQuartic_quotient_ne_zero (L : LineBundle X) (d n : ℕ)
    (τ : O X ⟶ ((L.pow d).pow 4).sheaf)
    (t : O X ⟶ (L.pow (d*4+n)).sheaf) (ht : t ≠ 0)
    (q : O X ⟶ (L.pow n).sheaf)
    (hq : q ≫ sectionMultiply ((L.pow d).pow 4) (L.pow n) τ ≫
        (quarticPowerProductIso L d n).hom = t) : q ≠ 0 := by
  apply global_quotient_ne_zero (X := X)
    (sectionMultiply ((L.pow d).pow 4) (L.pow n) τ ≫ (quarticPowerProductIso L d n).hom)
    t ht q
  exact hq

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
