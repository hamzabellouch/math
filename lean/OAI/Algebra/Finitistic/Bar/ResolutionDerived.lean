import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

namespace OAI
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
noncomputable section
namespace DerivedBar
variable {C E H : Type*} [Category* C] [Category* E] [Category* H]
variable (W : MorphismProperty C) (L : C ⥤ E) [L.IsLocalization W]
variable (R : C ⥤ C) (ε : R ⟶ 𝟭 C) (hε : ∀ X, W (ε.app X))
variable (F : C ⥤ H) (LF : E ⥤ H) (e : L ⋙ LF ≅ R ⋙ F)
variable (α : L ⋙ LF ⟶ F) (hα : α = e.hom ≫ whiskerRight ε F)
variable (hres : ∀ X, IsIso (α.app (R.obj X)))

include hε in
lemma resolution_map_isIso (X : C) : IsIso (L.map (ε.app X)) :=
  Localization.inverts L W _ (hε X)

/-- A candidate map into the resolved model, before descending the localization. -/
def resolutionLiftUp (G : E ⥤ H) (β : L ⋙ G ⟶ F) : L ⋙ G ⟶ L ⋙ LF := by
  have : IsIso (whiskerRight ε (L ⋙ G)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    have := resolution_map_isIso W L R ε hε X
    exact inferInstanceAs (IsIso (G.map (L.map (ε.app X))))
  exact inv (whiskerRight ε (L ⋙ G)) ≫ whiskerLeft R β ≫ e.inv

/-- Full faithfulness of precomposition by the localization descends that map. -/
def resolutionLift (G : E ⥤ H) (β : L ⋙ G ⟶ F) : G ⟶ LF :=
  (Localization.fullyFaithfulWhiskeringLeft L W H).preimage
    (resolutionLiftUp W L R ε hε F LF e G β)

lemma whisker_resolutionLift (G : E ⥤ H) (β : L ⋙ G ⟶ F) :
    whiskerLeft L (resolutionLift W L R ε hε F LF e G β) =
      resolutionLiftUp W L R ε hε F LF e G β :=
  (Localization.fullyFaithfulWhiskeringLeft L W H).map_preimage _

include hα in
lemma resolutionLift_fac (G : E ⥤ H) (β : L ⋙ G ⟶ F) :
    whiskerLeft L (resolutionLift W L R ε hε F LF e G β) ≫ α = β := by
  rw [whisker_resolutionLift, hα]
  ext X
  have := resolution_map_isIso W L R ε hε X
  simp only [resolutionLiftUp, NatTrans.comp_app, NatIso.isIso_inv_app, whiskerLeft_app,
    whiskerRight_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  change inv (G.map (L.map (ε.app X))) ≫ β.app (R.obj X) ≫ F.map (ε.app X) = β.app X
  rw [← β.naturality (ε.app X)]
  simp

include hres hε in
lemma resolutionLift_unique (G : E ⥤ H) (γ₁ γ₂ : G ⟶ LF)
    (h : whiskerLeft L γ₁ ≫ α = whiskerLeft L γ₂ ≫ α) : γ₁ = γ₂ := by
  apply Localization.natTrans_ext L W
  intro X
  have := resolution_map_isIso W L R ε hε X
  have := hres X
  have heq : γ₁.app (L.obj (R.obj X)) = γ₂.app (L.obj (R.obj X)) := by
    apply (cancel_mono (α.app (R.obj X))).mp
    exact congrArg (fun τ => τ.app (R.obj X)) h
  rw [← cancel_epi (G.map (L.map (ε.app X)))]
  have hn₁ := γ₁.naturality (L.map (ε.app X))
  have hn₂ := γ₂.naturality (L.map (ε.app X))
  dsimp only [Functor.id_obj] at hn₁ hn₂
  rw [heq] at hn₁
  exact hn₁.trans hn₂.symm

include hε hα hres in
/-- A functorial resolution computes the genuine left derived functor.
The criterion is a right Kan extension universal property; its hypotheses are
checked on the actual bar resolution in the application. -/
theorem isLeftDerivedFunctor_of_resolution : LF.IsLeftDerivedFunctor α W where
  isRightKanExtension := by
    refine ⟨⟨IsTerminal.ofUniqueHom (fun y =>
      CostructuredArrow.homMk (resolutionLift W L R ε hε F LF e y.left y.hom)
        (resolutionLift_fac W L R ε hε F LF e α hα y.left y.hom)) ?_⟩⟩
    intro y m
    apply CostructuredArrow.hom_ext
    apply resolutionLift_unique W L R ε hε F LF α hres y.left
    have hm : whiskerLeft L m.left ≫ α = y.hom := by simpa using m.w
    exact hm.trans (resolutionLift_fac W L R ε hε F LF e α hα y.left y.hom).symm
end DerivedBar

end

end OAI
