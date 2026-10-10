import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.IndividualGridSplits
import OAI.GroupTheory.SimpleAmenable.CentralCovers.TemplateRelators
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.SupportedCellPatching

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section GridFormalPatching

theorem inner_action_iSup {G J : Type*} [Group G] (P : J → Subgroup G) (x y : G)
    (h : ∀ j, ∀ z ∈ P j, x*z*x⁻¹=y*z*y⁻¹) :
    ∀ z ∈ ⨆ j, P j, x*z*x⁻¹=y*z*y⁻¹ := by
  have hh : (⨆ j, P j) ≤ MonoidHom.eqLocus (MulAut.conj x).toMonoidHom
      (MulAut.conj y).toMonoidHom := by
    apply iSup_le
    intro j z hz
    exact h j z hz
  exact hh

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι D : Type*} [Finite ι] [Fintype D]
    {κ : Option ι → Type*} [∀ i, Finite (κ i)]
    {τ : D → Type*} [∀ d, Finite (τ d)]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem grid_formal_patching (hlarge : 25 ≤ m+1)
    (Q : (i : Option ι) → κ i → Fin 5 × (CutRing × CutRing))
    (h : ∀ i I, I.card≤15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (Q i))
    (U : Option ι → polygonAlgebra a) (W : D → polygonAlgebra a)
    (hU : ∀ i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (U i).val)
    (hW : ∀ i d, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (W d).val)
    (he : ∀ i d, B.fullGeometricSector (by omega) (Q i) (h i) (W d)=
      B.fullGeometricSector (by omega) (Q none) (h none) (W d))
    (hdisjoint : Pairwise fun d e => Disjoint (W d).val (W e).val)
    (hcover : ∀ x, ∃ d, x ∈ (W d).val)
    (f : (I : FiveAlphabet (Fin (m+1))) → Option ι → alternatingGroup I.val →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (hspec : ∀ I i, (B.gridInput (by omega) Q h U i).comp (universalMap (subtypeAlternatingHom I.val))=
      (f I i).comp (universalProjection (alternatingGroup I.val)))
    (T : (d : D) → τ d → Fin 5 × (CutRing × CutRing))
    (hT : ∀ d I, I.card≤15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (T d))
    (V : D → polygonAlgebra a) (R : D → ι → polygonAlgebra a)
    (hV : ∀ d, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (T d) j).val) (V d).val)
    (hR : ∀ d i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (T d) j).val) (R d i).val)
    (hcontrol : ∀ d i, SmallControlled B.c (B.gridPiece (by omega) Q h U W d i)
      (B.fullGeometricSector (by omega) (T d) (hT d) (V d)))
    (haction : ∀ d i (I : FiveAlphabet (Fin (m+1))) s j,
      ∀ x ∈ (B.gridPiece (by omega) Q h U W d j).range,
        B.gridInput (by omega) Q h U i (universalMap (subtypeAlternatingHom I.val) s)*x*
          (B.gridInput (by omega) Q h U i (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
        B.fullGeometricSector (by omega) (T d) (hT d) (marginFamily (R d) (V d) i)
          (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.fullGeometricSector (by omega) (T d) (hT d) (marginFamily (R d) (V d) i)
          (universalMap (subtypeAlternatingHom I.val) s))⁻¹) :
    HasCentralLaw (smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}))
      (smallFamilyEval f).rangeRestrict := by
  apply supported_cell_patching (B.gridInput (by omega) Q h U) f hspec
    (fun d => ⨆ j, (B.gridPiece (by omega) Q h U W d j).range) ?_ ?_
    (fun d i => B.fullGeometricSector (by omega) (T d) (hT d) (marginFamily (R d) (V d) i))
    ?_ ?_ (by simp only [Fintype.card_fin]; omega)
  · rw [copyFamilyEval_range]
    exact B.gridPieces_generate (by omega) Q h U W hU hW hdisjoint hcover
  · exact B.gridInputs_normalize (by omega) Q h U W (by omega) none hU hW he
  · intro d I i s
    apply inner_action_iSup
    intro j
    exact haction d i I s j
  · intro d S hS w hw hrel
    have hh : (⨆ j, (B.gridPiece (by omega) Q h U W d j).range) ≤
        Subgroup.centralizer ({copyFamilyEval
          (fun i => B.fullGeometricSector (by omega) (T d) (hT d) (marginFamily (R d) (V d) i))
          (smallFamilyStarWord w)} : Set _) := by
      apply iSup_le
      intro j x hx
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact (B.actual_template_word_controls hlarge (T d) (hT d) (R d) (V d)
        (hR d) (hV d) _ (B.gridPiece_supported (by omega) Q h U W hU hW d j)
        (hcontrol d j) S hS w hw hrel x hx).symm
    intro x hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hh hx)).symm

end InitialCoverSystem
end GridFormalPatching

section CoordinateGlobalActions
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in

theorem coordinateFamilyLaw_all (g : ∀ n, B.CoordinateWindowLaw n)
    (j : ι → Fin 2) (u : ι → CutRing × CutRing)
    (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I) :
    B.PrimitiveFamilyLaw I b hb (fun i => (coordinateTestIndex (j i),u i)) := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨n,q,hq⟩ := finite_coordinate_windows_container (fun _ : ι => 1)
    (fun i k => pointLabel (u i) k)
  apply B.coordinateFamilyLaw_of_window (n+1) (g (n+1)) q j u ?_ ?_ I b hb
  · intro i
    have hh := (hq i (j i)).1
    simpa only [pointLabel,pointCoordinate] using hh
  · intro i
    have hh := (hq i (j i)).2
    have hx : endpointLabel (if j i=0 then (u i).1 else (u i).2)=pointLabel (u i) (j i) := by
      rfl
    rw [hx]
    omega

theorem coordinate_charts_action (hlarge : 20 ≤ m+1)
    (g : ∀ n, B.CoordinateWindowLaw n)
    (j : ι → Fin 2) (u : ι → CutRing × CutRing)
    (j' : κ → Fin 2) (u' : κ → CutRing × CutRing)
    (V V' W : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (fun i => (coordinateTestIndex (j i),u i)) i).val) V.val)
    (hV' : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (fun i => (coordinateTestIndex (j' i),u' i)) i).val) V'.val)
    (n : ℕ) (q : Fin 2 → ℤ)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) W.val)
    (heq : V ⊓ W=V' ⊓ W)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (g n) q W))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)) :
    ∀ x ∈ f.range,
      B.fullGeometricSector (by omega) (fun i => (coordinateTestIndex (j i),u i))
        (fun I _ b hb => B.coordinateFamilyLaw_all g j u I b hb) V
        (universalMap (subtypeAlternatingHom I.val) s)*x*
      (B.fullGeometricSector (by omega) (fun i => (coordinateTestIndex (j i),u i))
        (fun I _ b hb => B.coordinateFamilyLaw_all g j u I b hb) V
        (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
      B.fullGeometricSector (by omega) (fun i => (coordinateTestIndex (j' i),u' i))
        (fun I _ b hb => B.coordinateFamilyLaw_all g j' u' I b hb) V'
        (universalMap (subtypeAlternatingHom I.val) s)*x*
      (B.fullGeometricSector (by omega) (fun i => (coordinateTestIndex (j' i),u' i))
        (fun I _ b hb => B.coordinateFamilyLaw_all g j' u' I b hb) V'
        (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  let J : Sum (Sum ι κ) (Fin 2 × Fin (n-1)) → Fin 2 := Sum.elim (Sum.elim j j') Prod.fst
  let Z : Sum (Sum ι κ) (Fin 2 × Fin (n-1)) → CutRing × CutRing :=
    Sum.elim (Sum.elim u u') (fun i => (coordinateWindowPrimitives n q i).2)
  let P := fun i => (coordinateTestIndex (J i),Z i)
  have h := fun I (_ : I.card≤15) b hb => B.coordinateFamilyLaw_all g J Z I b hb
  have h₀ := B.fullGeometricSector_subfamily (by omega) P _ (Sum.inl ∘ Sum.inl) rfl h
    (fun I _ b hb => B.coordinateFamilyLaw_all g j u I b hb) V hV
  have h₁ := B.fullGeometricSector_subfamily (by omega) P _ (Sum.inl ∘ Sum.inr) rfl h
    (fun I _ b hb => B.coordinateFamilyLaw_all g j' u' I b hb) V' hV'
  have h₂ := B.fullGeometricSector_subfamily (by omega) P (coordinateWindowPrimitives n q) Sum.inr rfl h
    (fun I _ b hb => g n I b hb q) W hW
  change SmallControlled B.c f (B.fullGeometricSector (by omega) (coordinateWindowPrimitives n q)
    (fun I _ b hb => g n I b hb q) W) at hc
  rw [h₂] at hc
  simp only [Function.comp_def,P,J,Z,Sum.elim_inl,Sum.elim_inr] at h₀ h₁
  rw [h₀,h₁]
  exact B.chart_action_transfer hlarge P h V V' W
    (fun x y he => hV x y (fun i => he (Sum.inl (Sum.inl i))))
    (fun x y he => hV' x y (fun i => he (Sum.inl (Sum.inr i))))
    (fun x y he => hW x y (fun i => he (Sum.inr i))) heq f hf hc I s

end InitialCoverSystem
end CoordinateGlobalActions

end SimpleAmenable
end
end

end OAI
