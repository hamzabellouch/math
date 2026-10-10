import OAI.CategoryTheory.Globular.ReflectedCylinder

namespace OAI

universe u v w

namespace Grothendieck.GlobularTheory.Model
open CategoryTheory CategoryTheory.Limits

theorem exactBoundaryTest_of_cutoff_path {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) {X Y : CutoffModels C q} (i : X ⟶ Y)
    (hi : (sourceClass hC q r).rlp.llp i) (hX : Cofibrant hC q X)
    (z : Y ⟶ X) (hz : i ≫ z = 𝟙 X) (P : CutoffPathData hC q r Y) :
    GlobularSet.ExactBoundaryTest (underlyingMap i.hom) := by
  let := cutoff_hasLimits hC q
  obtain ⟨a, ha⟩ := hX P.p₀ P.lifts₀ i
  let u : X ⟶ Y := a ≫ P.p₁
  let := hi (prod.lift P.p₀ P.p₁) P.joint_rlp
  have sq : CommSq a i (prod.lift P.p₀ P.p₁) (prod.lift (𝟙 Y) (z ≫ u)) := by
    constructor
    apply prod.hom_ext
    · simpa only [Category.assoc, prod.lift_fst, Category.comp_id] using ha
    · simp only [Category.assoc, prod.lift_snd]
      rw [← Category.assoc i, hz, Category.id_comp]
  have hf₀ : sq.lift ≫ P.p₀ = 𝟙 Y := by
    have e := congrArg (· ≫ prod.fst) sq.fac_right
    simpa only [Category.assoc, prod.lift_fst] using e
  have hf₁ : sq.lift ≫ P.p₁ = z ≫ u := by
    have e := congrArg (· ≫ prod.snd) sq.fac_right
    simpa only [Category.assoc, prod.lift_snd] using e
  have hp₀ : GlobularSet.LiftsBoundaries (underlyingMap P.p₀.hom) := by
    intro k
    exact (hasLiftingProperty_I_iff k P.p₀.hom).1
      ((boundaryClass_rlp_iff hC q 0 P.p₀).1 P.lifts₀ k (Nat.zero_le k))
  have hp₁ : GlobularSet.LiftsBoundaries (underlyingMap P.p₁.hom) := by
    intro k
    exact (hasLiftingProperty_I_iff k P.p₁.hom).1
      ((boundaryClass_rlp_iff hC q 0 P.p₁).1 P.lifts₁ k (Nat.zero_le k))
  apply GlobularSet.ExactBoundaryTest.of_retract_factor
    (underlyingMap i.hom) (underlyingMap z.hom) (underlyingMap u.hom)
    (congrArg (fun t : X ⟶ X => underlyingMap t.hom) hz) _ (Y.obj.joined_refl hC)
  have hv := GlobularSet.exactBoundaryTest_endpoint_section
    (underlyingMap P.p₀.hom) (underlyingMap P.p₁.hom) (underlyingMap sq.lift.hom)
    hp₀ hp₁
    (fun k x => congrFun (congrArg (fun t => (underlyingMap t.hom).app k) hf₀) x)
    (Y.obj.joined_refl hC)
  have e := congrArg (fun t : Y ⟶ Y => underlyingMap t.hom) hf₁
  change GlobularSet.ExactBoundaryTest (underlyingMap (sq.lift ≫ P.p₁).hom) at hv
  rw [e] at hv
  exact hv

theorem sourceClass_cofibration_mono {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {r s : ℕ} (hrs : r ≤ s) :
    (sourceClass hC q s).rlp.llp ≤ (sourceClass hC q r).rlp.llp := by
  intro X Y i hi P Q p hp
  apply hi p
  rw [sourceClass_rlp_iff] at hp ⊢
  exact fun k hk => hp k (hrs.trans hk)

theorem expansionContraction_mono {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {r s : ℕ} (hrs : r ≤ s) (H : ExpansionContraction hC q r) :
    ExpansionContraction hC q s := by
  intro X Y i hi hX hXF
  exact H i (sourceClass_cofibration_mono hC q hrs i hi) hX hXF

theorem expansionContraction_all {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) : ExpansionContraction hC q r := by
  let := cutoff_hasColimits hC q
  let := cutoff_hasLimits hC q
  have hall : ∀ m r, q-r = m → ExpansionContraction hC q r := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro r hr
      by_cases hqr : q ≤ r
      · exact expansionContraction_mono hC q hqr (expansionContraction_top hC q)
      · have Hnext : ExpansionContraction hC q (r+1) := @ih (q-(r+1)) (by omega) (r+1) rfl
        exact expansionContraction_of_paths hC q r
          (fun Y => ⟨cylinderPathData hC q r (by omega) Hnext Y⟩)
  exact @hall (q-r) r rfl

theorem cutoff_elementary_exactBoundaryTest {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (hnq : n ≤ q) {X Y : C.Model} (hX : X.IsCellular)
    (a : disk C n ⟶ X) (i : X ⟶ Y) (b : disk C (n+1) ⟶ Y)
    (sq : IsPushout a (J C n) i b) :
    GlobularSet.ExactBoundaryTest (underlyingMap ((cutoffFunctor hC q).map i).hom) := by
  let := cutoff_hasColimits hC q
  let := cutoff_hasLimits hC q
  let F := cutoffFunctor hC q
  let : F.IsLeftAdjoint := (cutoffAdjunction hC q).isLeftAdjoint
  have hi : (sourceClass hC q n).rlp.llp (F.map i) := by
    apply MorphismProperty.of_isPushout (sq.map F)
    intro P Q p hp
    exact hp _ (MorphismProperty.ofHoms.mk (⟨n,le_rfl⟩ : {k : ℕ // n ≤ k}))
  obtain ⟨z,hz⟩ := elementary_pushout_retraction hC n a i b sq
  apply exactBoundaryTest_of_cutoff_path hC q n (F.map i) hi
    (isCellular_cutoff_cofibrant hC q hX) (F.map z)
  · exact (F.map_comp i z).symm.trans ((congrArg F.map hz).trans (F.map_id X))
  · exact cylinderPathData hC q n hnq (expansionContraction_all hC q (n+1)) (F.obj Y)

end Grothendieck.GlobularTheory.Model

end OAI
