import OAI.CategoryTheory.Globular.CylinderJointUpper

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] [HasPushouts K]
variable {D B : GlobularFrame K}

theorem criticalJoint_retract (e : Bool → Hom D B) (n : ℕ)
    (i : B.obj n ≅ D.obj (n+1))
    (hs : (e false).obj n ≫ i.hom = D.diagram.source n)
    (ht : (e true).obj n ≫ i.hom = D.diagram.target n)
    (hb : (e false).bd n = (e true).bd n) [Epi ((e false).bd n)] :
    ∃ f : jointSource e n ⟶ oneSided (e false) (n+1),
      ∃ g : oneSided (e false) (n+1) ⟶ jointSource e n, f ≫ g = 𝟙 _ := by
  let aB := pushout.inl ((e false).bd (n+1)) (D.inc (n+1))
  let aD := pushout.inr ((e false).bd (n+1)) (D.inc (n+1))
  let c := TwoEndpoints.base (D.diagram.source n) (fun ε => (e ε).obj n)
  let d := TwoEndpoints.endpoint (D.diagram.source n) (fun ε => (e ε).obj n)
  let side (ε : Bool) := if ε then B.right n else B.left n
  have hc (ε) : D.diagram.source n ≫ d ε = (e ε).obj n ≫ c :=
    (TwoEndpoints.condition (D.diagram.source n) (fun ε => (e ε).obj n) ε).symm
  have hcommon : D.inc n ≫ (e false).obj n = D.inc n ≫ (e true).obj n := by
    rw [← (e false).inc, hb, (e true).inc]
  have hsi : D.diagram.source n ≫ i.inv = (e false).obj n := by
    apply (cancel_mono i.hom).1
    erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact hs.symm
  have hti : D.diagram.target n ≫ i.inv = (e true).obj n := by
    apply (cancel_mono i.hom).1
    erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact ht.symm
  have hpar : B.inc n ≫ i.hom ≫ d false = B.inc n ≫ i.hom ≫ d true := by
    apply (cancel_epi ((e false).bd n)).1
    have hx (ε) : (e false).bd n ≫ B.inc n ≫ i.hom ≫ d ε = D.inc n ≫ (e ε).obj n ≫ c := by
      erw [← Category.assoc, (e false).inc, Category.assoc]
      have hh : (e false).obj n ≫ i.hom ≫ d ε = (e ε).obj n ≫ c :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ d ε) hs).trans (hc ε))
      exact congrArg (D.inc n ≫ ·) hh
    exact (hx false).trans (((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ c) hcommon).trans (Category.assoc _ _ _))).trans (hx true).symm)
  let b := (B.square n).desc (i.hom ≫ d false) (i.hom ≫ d true) hpar
  have hbg : (e false).bd (n+1) ≫ b = D.inc (n+1) ≫ i.inv ≫ c := by
    apply (D.square n).hom_ext
    · erw [← Category.assoc, (e false).left, Category.assoc, IsPushout.inl_desc]
      erw [← Category.assoc, hs, hc false]
      have hh : D.diagram.source n ≫ i.inv ≫ c = (e false).obj n ≫ c :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ c) hsi)
      exact hh.symm.trans (Category.assoc _ _ _)
    · erw [← Category.assoc, (e false).right, Category.assoc, IsPushout.inr_desc]
      erw [← Category.assoc, hs, hc true]
      have hh : D.diagram.target n ≫ i.inv ≫ c = (e true).obj n ≫ c :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ c) hti)
      exact hh.symm.trans (Category.assoc _ _ _)
  let g := pushout.desc b (i.inv ≫ c) hbg
  have hgB : aB ≫ g = b := pushout.inl_desc _ _ _
  have hgD : aD ≫ g = i.inv ≫ c := pushout.inr_desc _ _ _
  have hfd (ε) : (e ε).obj n ≫ i.hom ≫ aD = D.diagram.source n ≫ i.inv ≫ side ε ≫ aB := by
    have hl : D.left n ≫ (e false).bd (n+1) ≫ aB = (e false).obj n ≫ B.left n ≫ aB := by
      erw [← Category.assoc, (e false).left, Category.assoc]
    have hr : D.right n ≫ (e false).bd (n+1) ≫ aB = (e false).obj n ≫ B.right n ≫ aB := by
      erw [← Category.assoc, (e false).right, Category.assoc]
    have hp : (e false).bd (n+1) ≫ aB = D.inc (n+1) ≫ aD := pushout.condition
    have hrhs (ε) : D.diagram.source n ≫ i.inv ≫ side ε ≫ aB = (e false).obj n ≫ side ε ≫ aB :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ side ε ≫ aB) hsi)
    cases ε
    · have hh : (e false).obj n ≫ i.hom ≫ aD = (e false).obj n ≫ B.left n ≫ aB :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ aD) hs).trans
          ((Category.assoc _ _ _).trans ((congrArg (D.left n ≫ ·) hp).symm.trans hl)))
      exact hh.trans (hrhs false).symm
    · have hh : (e true).obj n ≫ i.hom ≫ aD = (e false).obj n ≫ B.right n ≫ aB :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ aD) ht).trans
          ((Category.assoc _ _ _).trans ((congrArg (D.right n ≫ ·) hp).symm.trans hr)))
      exact hh.trans (hrhs true).symm
  let f := TwoEndpoints.desc (D.diagram.source n) (fun ε => (e ε).obj n)
    (i.hom ≫ aD) (fun ε => i.inv ≫ side ε ≫ aB) hfd
  refine ⟨f,g,?_⟩
  apply TwoEndpoints.hom_ext
  · erw [← Category.assoc, TwoEndpoints.base_desc, Category.assoc, hgD, Iso.hom_inv_id_assoc,
      Category.comp_id]
  · intro ε
    erw [← Category.assoc, TwoEndpoints.endpoint_desc, Category.assoc, Category.assoc, hgB]
    cases ε
    · change i.inv ≫ B.left n ≫ b = d false ≫ 𝟙 _
      erw [IsPushout.inl_desc, Iso.inv_hom_id_assoc, Category.comp_id]
    · change i.inv ≫ B.right n ≫ b = d true ≫ 𝟙 _
      erw [IsPushout.inr_desc, Iso.inv_hom_id_assoc, Category.comp_id]
end GlobularFrame
end Grothendieck

end OAI
