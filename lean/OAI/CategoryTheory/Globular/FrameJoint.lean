import OAI.CategoryTheory.Globular.FullCylinder

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] [HasPushouts K]
variable {D B : GlobularFrame K} (e : Bool → Hom D B)

noncomputable abbrev twoEnded (j : ℕ) := TwoEndpoints.obj (D.inc j) (fun ε => (e ε).bd j)
noncomputable def twoEndedMap (j : ℕ) : twoEnded e j ⟶ B.obj j :=
  TwoEndpoints.desc (D.inc j) (fun ε => (e ε).bd j) (B.inc j) (fun ε => (e ε).obj j)
    (fun ε => (e ε).inc j)

theorem twoEnded_lift {X Y : K} (p : X ⟶ Y) (j : ℕ)
    (h : HasLiftingProperty (twoEndedMap e j) p)
    (a : B.bd j ⟶ X) (d : Bool → (D.obj j ⟶ X))
    (hd : ∀ ε, (e ε).bd j ≫ a = D.inc j ≫ d ε)
    (y : B.obj j ⟶ Y) (ha : a ≫ p = B.inc j ≫ y)
    (hy : ∀ ε, d ε ≫ p = (e ε).obj j ≫ y) :
    ∃ l : B.obj j ⟶ X, B.inc j ≫ l = a ∧ (∀ ε, (e ε).obj j ≫ l = d ε) ∧ l ≫ p = y := by
  let t := TwoEndpoints.desc (D.inc j) (fun ε => (e ε).bd j) a d hd
  have sq : CommSq t (twoEndedMap e j) p y := by
    constructor
    apply TwoEndpoints.hom_ext
    · erw [← Category.assoc, TwoEndpoints.base_desc]
      erw [← Category.assoc, TwoEndpoints.base_desc]
      exact ha
    · intro ε
      erw [← Category.assoc, TwoEndpoints.endpoint_desc]
      erw [← Category.assoc, TwoEndpoints.endpoint_desc]
      exact hy ε
  let : sq.HasLift := h.sq_hasLift sq
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · have hh := congrArg (TwoEndpoints.base (D.inc j) (fun ε => (e ε).bd j) ≫ ·) sq.fac_left
    erw [← Category.assoc, TwoEndpoints.base_desc, TwoEndpoints.base_desc] at hh
    exact hh
  · intro ε
    have hh := congrArg (TwoEndpoints.endpoint (D.inc j) (fun ε => (e ε).bd j) ε ≫ ·) sq.fac_left
    erw [← Category.assoc, TwoEndpoints.endpoint_desc, TwoEndpoints.endpoint_desc] at hh
    exact hh

noncomputable abbrev jointSource (k : ℕ) :=
  TwoEndpoints.obj (D.diagram.source k) (fun ε => (e ε).obj k)
noncomputable def jointSourceMap (k : ℕ) : jointSource e k ⟶ B.obj (k+1) :=
  TwoEndpoints.desc (D.diagram.source k) (fun ε => (e ε).obj k)
    (B.diagram.source k) (fun ε => (e ε).obj (k+1))
    (fun ε => ((e ε).source_naturality k).symm)

omit [HasPushouts K] in
@[reassoc] theorem inc_source_eq_inc_target (B : GlobularFrame K) (k : ℕ) :
    B.inc k ≫ B.diagram.source k = B.inc k ≫ B.diagram.target k := by
  change B.inc k ≫ B.left k ≫ B.inc (k+1) = B.inc k ≫ B.right k ≫ B.inc (k+1)
  rw [← Category.assoc, (B.square k).w, Category.assoc]

theorem jointSource_lifting {X Y : K} (p : X ⟶ Y) (k : ℕ)
    (h₀ : HasLiftingProperty (twoEndedMap e k) p)
    (h₁ : HasLiftingProperty (twoEndedMap e (k+1)) p) :
    HasLiftingProperty (jointSourceMap e k) p := by
  constructor
  intro a y sq
  let u := TwoEndpoints.base (D.diagram.source k) (fun ε => (e ε).obj k) ≫ a
  let d (ε) := TwoEndpoints.endpoint (D.diagram.source k) (fun ε => (e ε).obj k) ε ≫ a
  have hd (ε) : (e ε).obj k ≫ u = D.diagram.source k ≫ d ε := by
    dsimp only [u,d]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ a) (TwoEndpoints.condition (D.diagram.source k)
        (fun ε => (e ε).obj k) ε)).trans (Category.assoc _ _ _))
  have hu : u ≫ p = B.diagram.source k ≫ y := by
    have h := congrArg (TwoEndpoints.base (D.diagram.source k) (fun ε => (e ε).obj k) ≫ ·) sq.w
    erw [← Category.assoc _ (jointSourceMap e k), TwoEndpoints.base_desc] at h
    exact (Category.assoc _ _ _).trans h
  have hyp (ε) : d ε ≫ p = (e ε).obj (k+1) ≫ y := by
    have h := congrArg (TwoEndpoints.endpoint (D.diagram.source k) (fun ε => (e ε).obj k) ε ≫ ·) sq.w
    erw [← Category.assoc _ (jointSourceMap e k), TwoEndpoints.endpoint_desc] at h
    exact (Category.assoc _ _ _).trans h
  have hbd (ε) : (e ε).bd k ≫ (B.inc k ≫ u) = D.inc k ≫ (D.diagram.target k ≫ d ε) := by
    erw [← Category.assoc, (e ε).inc, Category.assoc]
    exact (congrArg (D.inc k ≫ ·) (hd ε)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ d ε) (inc_source_eq_inc_target D k)).trans (Category.assoc _ _ _)))
  have hbyp : (B.inc k ≫ u) ≫ p = B.inc k ≫ B.diagram.target k ≫ y := by
    erw [Category.assoc, hu]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ y) (inc_source_eq_inc_target B k)).trans (Category.assoc _ _ _))
  have hdy (ε) : (D.diagram.target k ≫ d ε) ≫ p = (e ε).obj k ≫ B.diagram.target k ≫ y := by
    erw [Category.assoc, hyp]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ y) ((e ε).target_naturality k)).trans (Category.assoc _ _ _))
  obtain ⟨v,hv,he,hvp⟩ := twoEnded_lift e p k h₀ (B.inc k ≫ u)
    (fun ε => D.diagram.target k ≫ d ε) hbd (B.diagram.target k ≫ y) hbyp hdy
  let b := (B.square k).desc u v hv.symm
  have hbe (ε) : (e ε).bd (k+1) ≫ b = D.inc (k+1) ≫ d ε := by
    apply (D.square k).hom_ext
    · rw [← Category.assoc, (e ε).left, Category.assoc, IsPushout.inl_desc]
      exact (hd ε).trans (Category.assoc _ _ _)
    · rw [← Category.assoc, (e ε).right, Category.assoc, IsPushout.inr_desc]
      exact (he ε).trans (Category.assoc _ _ _)
  have hbp : b ≫ p = B.inc (k+1) ≫ y := by
    apply (B.square k).hom_ext
    · rw [← Category.assoc, IsPushout.inl_desc]
      exact hu.trans (Category.assoc _ _ _)
    · rw [← Category.assoc, IsPushout.inr_desc]
      exact hvp.trans (Category.assoc _ _ _)
  obtain ⟨l,hl,hel,hlp⟩ := twoEnded_lift e p (k+1) h₁ b d hbe y hbp hyp
  refine CommSq.HasLift.mk' ⟨l, ?_, hlp⟩
  apply TwoEndpoints.hom_ext
  · erw [← Category.assoc, TwoEndpoints.base_desc]
    change (B.left k ≫ B.inc (k+1)) ≫ l = u
    rw [Category.assoc, hl]
    exact (B.square k).inl_desc _ _ _
  · intro ε
    erw [← Category.assoc, TwoEndpoints.endpoint_desc]
    exact hel ε

end GlobularFrame
end Grothendieck

end OAI
