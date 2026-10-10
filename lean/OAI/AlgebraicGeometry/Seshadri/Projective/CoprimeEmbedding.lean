import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.MixedEmbedding
import OAI.AlgebraicGeometry.Seshadri.Sheaves.AmpleFramedCover

namespace OAI


                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.TensorPure MaximalSeshadri.Projective

variable {X : Scheme.{0}} {K : Type} [CommRing K]

theorem LineBundle.coprime_projective_sections [IsIntegral X] [CompactSpace X]
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
    (L : LineBundle X) (hL : L.IsAmple) (a : ℕ) (ha : 0 < a) :
    ∃ b : ℕ, 0 < b ∧ Nat.Coprime a b ∧ ∃ σ : Type, ∃ _ : Fintype σ,
      ∃ s : σ → GlobalSections X (L.pow b).sheaf,
      ∃ hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤,
        IsClosedImmersion (sectionsMorphism
          (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs) := by
  classical
  obtain ⟨d,hd,had,ι,hi,s,hs,hsa,hsn,he⟩ := L.ample_framed_cover L hL a ha
  obtain ⟨n,hn,σ,hσ,t,ht,hc⟩ := (L.pow d).mixed_section_embedding p L s hs hsa hsn
    (fun i => Classical.choice (he i))
  let f : (((L.pow d).pow n).tensor L).sheaf ≅ (L.pow (d*n+1)).sheaf :=
    moduleTensorIso (linePowerMul L d n) (Iso.refl L.sheaf) ≪≫
      moduleTensorIso (Iso.refl _) (moduleTensorRightUnit L.sheaf).symm ≪≫
      (linePowerAdd L (d*n) 1).symm
  have ht' : (⨆ i, SectionOpens.isoOpen (t i ≫ f.hom)) = ⊤ := by
    exact (iSup_congr fun index => SectionOpens.isoOpen_postcomp (t index) f).trans ht
  have hcop : Nat.Coprime a (d*n+1) := by
    obtain ⟨q,rfl⟩ := had
    rw [Nat.mul_assoc,Nat.add_comm]
    exact (Nat.coprime_add_mul_left_right a 1 (q*n)).mpr (Nat.coprime_one_right a)
  refine ⟨d*n+1,by omega,hcop,σ,hσ,fun i => t i ≫ f.hom,ht',?_⟩
  exact (congrArg IsClosedImmersion (sectionsMorphism_transport
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) t ht f ht')).mpr hc

theorem Surface.coprime_embedding_option (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) (a : ℕ) (ha : 0 < a) :
    ∃ b : ℕ, 0 < b ∧ Nat.Coprime a b ∧ ∃ N : ℕ,
      ∃ s : Option (Fin N) → GlobalSections S.scheme (L.pow b).sheaf,
      ∃ hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤,
        IsClosedImmersion (sectionsMorphism
          (S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) s hs) := by
  classical
  obtain ⟨b,hb,hcop,σ,hσ,s,hs,hc⟩ := L.coprime_projective_sections S.structureMap hL a ha
  have hne : Nonempty σ := by
    obtain ⟨x⟩ := (inferInstance : Nonempty S.scheme)
    have hx : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := by rw [hs]; trivial
    obtain ⟨i,-⟩ := Opens.mem_iSup.mp hx
    exact ⟨i⟩
  have hpos : 0 < Fintype.card σ := Fintype.card_pos_iff.mpr hne
  obtain ⟨N,hN⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hpos)
  let e : Option (Fin N) ≃ σ := (finSuccEquiv N).symm.trans
    (((Fintype.equivFin σ).trans (finCongr hN)).symm)
  have ht : (⨆ i, SectionOpens.isoOpen (s (e i))) = ⊤ :=
    (e.iSup_comp (g := fun j => SectionOpens.isoOpen (s j))).trans hs
  exact ⟨b,hb,hcop,N,s ∘ e,ht,sectionsMorphism_reindex_closed _ s hs e ht⟩

end
end MaximalSeshadri.Geometry

end

end OAI
