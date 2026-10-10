import OAI.CategoryTheory.Globular.OneSidedPresentation

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularPresheaf
noncomputable def liftSmallDiskIso (j : ℕ) : liftSmall.{v}.obj (disk.{0} j) ≅ disk.{v} j :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun x => ⟨x.down.down⟩
      invFun := fun x => ⟨⟨x.down⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) (by intros; rfl)
end GlobularPresheaf
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)

theorem hasFillers_of_iso {X Y : CutoffModels C q} (e : X ≅ Y)
    (hX : X.obj.underlying.HasFillers) : Y.obj.underlying.HasFillers := by
  apply hX.retract (underlyingMap e.inv.hom) (underlyingMap e.hom.hom)
  exact congrArg (fun z : Y ⟶ Y => underlyingMap z.hom) e.inv_hom_id

noncomputable def cylinderCriticalData (ε : Bool) :
    GlobularFrame.CriticalData (cylinderEndpoint hC q n ε) n ε where
  low j hj := by
    change IsIso ((cylinderNode hC q n j).endpoint ε)
    rw [cylinderNode_low hC q n hj]
    change IsIso (𝟙 _)
    infer_instance
  iso := eqToIso (congrArg CylinderNode.obj (cylinderNode_critical hC q n))
  endpoint := by
    change (cylinderNode hC q n n).endpoint ε ≫
      eqToHom (congrArg CylinderNode.obj (cylinderNode_critical hC q n)) = _
    have h (Z : CylinderNode (cutoffDiskFrame hC q) n)
        (hz : Z = CylinderNode.critical (cutoffDiskFrame hC q) n) :
        Z.endpoint ε ≫ eqToHom (congrArg CylinderNode.obj hz) =
          if ε then (cutoffDiskFrame hC q).diagram.target n else (cutoffDiskFrame hC q).diagram.source n := by
      subst Z
      exact Category.comp_id _
    exact h _ (cylinderNode_critical hC q n)

theorem cutoff_boundary_surjective_iff (X : CutoffModels C q) (j : ℕ) :
    Function.Surjective (X.obj.underlying.boundary j) ↔
      ∀ a : cutoffBoundary hC q j ⟶ X, ∃ b : cutoffDisk hC q j ⟶ X, cutoffI hC q j ≫ b = a := by
  let A := cutoffAdjunction hC q
  let R := boundaryRepresentation C j
  constructor
  · intro h a
    obtain ⟨x, hx⟩ := h (R.equiv X.obj (A.homEquiv _ X a))
    refine ⟨(A.homEquiv _ X).symm ((cellEquiv X.obj j).symm x), ?_⟩
    apply (A.homEquiv _ X).injective
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
    apply (R.equiv X.obj).injective
    change R.equiv X.obj (R.inclusion ≫ (cellEquiv X.obj j).symm x) = _
    simpa only [R.inclusion_boundary, Equiv.apply_symm_apply] using hx
  · intro h a
    obtain ⟨g, hg⟩ := h ((A.homEquiv _ X).symm ((R.equiv X.obj).symm a))
    refine ⟨cellEquiv X.obj j (A.homEquiv _ X g), ?_⟩
    have e := congrArg (A.homEquiv _ X) hg
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply] at e
    change R.inclusion ≫ A.homEquiv _ X g = _ at e
    rw [← R.inclusion_boundary, e, Equiv.apply_symm_apply]

variable [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)]
local instance smallColimits : HasColimitsOfSize.{0,v} (CutoffModels C q) :=
  hasColimitsOfSizeShrink.{0,v} (CutoffModels C q)

omit [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
theorem cutoffFrame_diskWhisker_hasFillers (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1))
    (j : ℕ) (ε : Bool) :
    ((cutoffDiskFrame hC q).realization.obj
      ((GlobularPresheaf.whiskering n ε).obj (GlobularPresheaf.disk.{v} j))).obj.underlying.HasFillers := by
  apply hasFillers_of_iso (q := q)
    ((cutoffDiskFrame hC q).realization.mapIso
      ((GlobularPresheaf.whiskering n ε).mapIso (GlobularPresheaf.liftSmallDiskIso j)))
  exact cutoffFrame_whisker_hasFillers hC q n hnq H (Shape.globe j) ε

theorem cylinderNode_high_hasFillers {j : ℕ} (hj : n < j) (hnq : n ≤ q)
    (ε : Bool)
    (hA : (GlobularFrame.oneSided (cylinderEndpoint hC q n ε) j).obj.underlying.HasFillers) :
    (cylinderNode hC q n j).obj.obj.underlying.HasFillers := by
  let i := GlobularFrame.oneSidedMap (cylinderEndpoint hC q n ε) j
  have hi := cylinderFrame_upper hC q n hj ε
  apply hA.of_low_bijective (underlyingMap i.hom) n
  · intro k hk
    exact upper_cofibration_low_bijective hC q (n+1) k (hk.trans hnq) (by omega) i hi
  · intro k hk
    rw [cutoff_boundary_surjective_iff hC q]
    apply (lifting_terminal_iff _ _).1
    exact cylinderNode_upper_fillers hC q n hj _
      (MorphismProperty.ofHoms.mk (⟨k,by omega⟩ : {k : ℕ // n+1 ≤ k}))

theorem cylinder_oneSided_contractible (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1)) :
    ∀ j, n < j → ∀ ε : Bool,
      Cofibrant hC q (GlobularFrame.oneSided (cylinderEndpoint hC q n ε) j) ∧
      (GlobularFrame.oneSided (cylinderEndpoint hC q n ε) j).obj.underlying.HasFillers ∧
      (sourceClass hC q (n+1)).rlp.llp (GlobularFrame.oneSidedMap (cylinderEndpoint hC q n ε) j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj ε
    cases j with
    | zero => omega
    | succ j =>
      let e := cylinderEndpoint hC q n ε
      let U := (cylinderCriticalData hC q n ε).whiskerPresentation (GlobularPresheaf.disk.{v} (j+1)).underlying
      let V := GlobularFrame.Presentation.oneSidedPresentation e j
      let f := V.comparison U (by omega)
      have hf : (sourceClass hC q (n+1)).rlp.llp f := by
        intro X Y p hp
        exact V.comparison_lifting U (by omega) p (fun k hk hk' =>
          (ih k (by omega) hk ε).2.2 p hp)
      have hU : Cofibrant hC q U.obj := cutoffFrame_cofibrant hC q _
      have hUF : U.obj.obj.underlying.HasFillers := cutoffFrame_diskWhisker_hasFillers hC q n hnq H (j+1) ε
      have hV : Cofibrant hC q V.obj := hU.of_cofibration f
        (boundaryClass_cofibration_le hC q 0 (n+1) (Nat.zero_le _) f
          (sourceClass_cofibration_le hC q (n+1) f hf))
      have hVF : V.obj.obj.underlying.HasFillers := H f hf hU hUF
      refine ⟨hV, hVF, ?_⟩
      exact upper_boundary_is_source hC q (n+1) H _
        (cylinderFrame_upper hC q n hj ε) hV hVF
        (cylinderNode_high_hasFillers hC q n hj hnq ε hVF)

end GlobularTheory.Model
end Grothendieck

end OAI
