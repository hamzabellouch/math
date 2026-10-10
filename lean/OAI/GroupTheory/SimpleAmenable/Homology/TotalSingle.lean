import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ModelAssembly
import OAI.GroupTheory.SimpleAmenable.Homology.BiResolution

namespace OAI

section

open CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalHomotopy

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasCoproducts.{0} C]

noncomputable def equiv {K L : HomologicalComplex₂ C c c} (e : HomotopyEquiv K L) :
    HomotopyEquiv (K.total c) (L.total c) where
  hom := HomologicalComplex₂.total.map e.hom c
  inv := HomologicalComplex₂.total.map e.inv c
  homotopyHomInvId := by simpa using total e.homotopyHomInvId
  homotopyInvHomId := by simpa using total e.homotopyInvHomId

noncomputable abbrev single (K : ChainComplex C ℕ) : HomologicalComplex₂ C c c := (ChainComplex.single₀ (ChainComplex C ℕ)).obj K

noncomputable def singleIn (K : ChainComplex C ℕ) : K ⟶ (single K).total c where
  f n := (single K).ιTotal c 0 n n (by simp)
  comm' i j h := by
    change j+1=i at h
    subst i
    exact ι_d_leftZero (K := single K) j

noncomputable def singleOutF (K : ChainComplex C ℕ) (n : ℕ) :
    ((single K).total c).X n ⟶ K.X n :=
  (single K).totalDesc (fun p q hpq => if hp : p=0 then by
    subst p
    have hq : q=n := by simpa using hpq
    subst q
    exact 𝟙 _
    else 0)
@[reassoc, simp] lemma singleIn_out (K : ChainComplex C ℕ) (n : ℕ) :
    (singleIn K).f n ≫ singleOutF K n = 𝟙 _ := by
  dsimp only [singleIn, singleOutF]
  erw [ι_totalDesc]
  simp
@[reassoc, simp] lemma singleOut_in (K : ChainComplex C ℕ) (n : ℕ) :
    singleOutF K n ≫ (singleIn K).f n = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  simp only [←Category.assoc,singleOutF,ι_totalDesc]
  split_ifs with hp
  · subst p
    have : q=n := by simpa using hpq
    subst q
    dsimp only [singleIn]
    erw [Category.id_comp, Category.comp_id]
  · have hz : IsZero (((single K).X p).X q) := by
      exact ((eval C c q).map_isZero
        (isZero_single_obj_X c 0 K p hp))
    exact hz.eq_of_src _ _

instance singleIn_isIso (K : ChainComplex C ℕ) : IsIso (singleIn K) := by
  have (n : ℕ) : IsIso ((singleIn K).f n) :=
    ⟨⟨singleOutF K n, singleIn_out K n, singleOut_in K n⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components (singleIn K)

noncomputable def singleIso (K : ChainComplex C ℕ) : (single K).total c ≅ K :=
  (asIso (singleIn K)).symm

end TotalHomotopy

end

section

open CategoryTheory Limits SimplicialObject Simplicial Opposite AlgebraicTopology
open HomologicalComplex HomologicalComplex₂
namespace BiResolution

open DiagonalResolution SSet.Augmented.StandardSimplex
abbrev c := ComplexShape.down ℕ

noncomputable def pointAugmentation (d : D) : point d ⟶ (SimplicialObject.const A).obj Z where
  app q := Sigma.desc (fun _ : q.unop ⟶ d.2 => 𝟙 Z)
  naturality q q' f := by apply Sigma.hom_ext; intro g; simp [point]

noncomputable def pointAugmented (d : D) : SimplicialObject.Augmented A where
  left := point d
  right := Z
  hom := pointAugmentation d

noncomputable def pointExtra (d : D) : (pointAugmented d).ExtraDegeneracy where
  s' := Sigma.ι (fun _ : ⦋0⦌ ⟶ d.2 => Z) (zeroSimplex d.2)
  s n := Sigma.desc (fun f : ⦋n⦌ ⟶ d.2 => Sigma.ι (fun _ : ⦋n+1⦌ ⟶ d.2 => Z) (shift f))
  s'_comp_ε := by exact Sigma.ι_comp_desc _ _
  s₀_comp_δ₁ := by
    apply Sigma.hom_ext
    intro f
    dsimp only [pointAugmented,pointAugmentation,SimplicialObject.δ,point]
    simp only [Sigma.ι_comp_desc_assoc,Sigma.ι_comp_desc,Quiver.Hom.unop_op,shift_δ₁,Category.id_comp]
  s_comp_δ₀ n := by
    apply Sigma.hom_ext
    intro f
    dsimp only [pointAugmented,pointAugmentation,SimplicialObject.δ,point]
    simp only [Sigma.ι_comp_desc_assoc,Sigma.ι_comp_desc,Quiver.Hom.unop_op,shift_δ₀,Category.comp_id]
  s_comp_δ n i := by
    apply Sigma.hom_ext
    intro f
    dsimp only [pointAugmented,pointAugmentation,SimplicialObject.δ,point]
    simp only [Sigma.ι_comp_desc_assoc,Sigma.ι_comp_desc,Quiver.Hom.unop_op,shift_δ_succ]
  s_comp_σ n i := by
    apply Sigma.hom_ext
    intro f
    dsimp only [pointAugmented,pointAugmentation,SimplicialObject.σ,point]
    simp only [Sigma.ι_comp_desc_assoc,Sigma.ι_comp_desc,Quiver.Hom.unop_op,shift_σ_succ]

noncomputable def complexAt (d : D) : HomologicalComplex₂ A c c :=
  AlternatingFaceMapComplex.obj (chainsAt d ⋙ alternatingFaceMapComplex A)

noncomputable def complexAtIso (d : D) :
    (((alternatingFaceMapComplex A).mapHomologicalComplex c).obj
      (AlternatingFaceMapComplex.obj (chainsAt d))) ≅ complexAt d :=
  eqToIso (congrArg (fun F => F.obj (chainsAt d))
    (map_alternatingFaceMapComplex (alternatingFaceMapComplex A)))

noncomputable def complexAtEquiv (d : D) : HomotopyEquiv (complexAt d)
    (TotalHomotopy.single (AlternatingFaceMapComplex.obj (point d))) :=
  (HomotopyEquiv.ofIso (complexAtIso d).symm).trans
    (((alternatingFaceMapComplex A).mapHomotopyEquiv (extra d).homotopyEquiv).trans
      (HomotopyEquiv.ofIso ((HomologicalComplex.singleMapHomologicalComplex
        (alternatingFaceMapComplex A) c 0).app (point d))))

noncomputable def totalAtEquiv (d : D) : HomotopyEquiv ((complexAt d).total c)
    ((ChainComplex.single₀ A).obj Z) :=
  (TotalHomotopy.equiv (complexAtEquiv d)).trans
    ((HomotopyEquiv.ofIso (TotalHomotopy.singleIso _)).trans (pointExtra d).homotopyEquiv)

end BiResolution

end

open CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalFunctor

universe u v u' v'
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{0} C]
  {E : Type u'} [Category.{v'} E] [Preadditive E] [HasCoproducts.{0} E]
open TotalHomotopy
variable (F : C ⥤ E) [F.Additive]
noncomputable abbrev map₂ (K : HomologicalComplex₂ C c c) : HomologicalComplex₂ E c c :=
  ((F.mapHomologicalComplex c).mapHomologicalComplex c).obj K

noncomputable def comparisonF (K : HomologicalComplex₂ C c c) (n : ℕ) :
    ((map₂ F K).total c).X n ⟶ F.obj ((K.total c).X n) :=
  (map₂ F K).totalDesc (fun p q hpq => F.map (K.ιTotal c p q n hpq))

@[reassoc (attr := simp)] lemma ι_comparisonF (K : HomologicalComplex₂ C c c)
    (p q n : ℕ) (hpq : p+q=n) :
    (map₂ F K).ιTotal c p q n hpq ≫ comparisonF F K n = F.map (K.ιTotal c p q n hpq) := by
  apply ι_totalDesc

noncomputable def comparison (K : HomologicalComplex₂ C c c) :
    (map₂ F K).total c ⟶ (F.mapHomologicalComplex c).obj (K.total c) where
  f := comparisonF F K
  comm' i j h := by
    change j+1=i at h
    subst i
    apply total.hom_ext
    intro p q hpq
    change p+q=j+1 at hpq
    cases p with
    | zero =>
      have hq : q=j+1 := by omega
      subst q
      simp only [←Category.assoc,Functor.mapHomologicalComplex_obj_d]
      rw [ι_comparisonF,←F.map_comp,ι_d_leftZero,ι_d_leftZero,
        F.map_comp,Category.assoc,ι_comparisonF]
      rfl
    | succ p =>
      cases q with
      | zero =>
        have hp : p=j := by omega
        subst p
        simp only [←Category.assoc,Functor.mapHomologicalComplex_obj_d]
        rw [ι_comparisonF,←F.map_comp,ι_d_rightZero,ι_d_rightZero,
          F.map_comp,Category.assoc,ι_comparisonF]
        rfl
      | succ q =>
        have h : p+q+1=j := by omega
        simp only [←Category.assoc,Functor.mapHomologicalComplex_obj_d]
        rw [ι_comparisonF,←F.map_comp,ι_d_both p q j h,ι_d_both p q j h]
        simp only [F.map_add,F.map_units_smul,F.map_comp,Preadditive.add_comp,
          Linear.units_smul_comp,Category.assoc,ι_comparisonF]
        rfl

instance comparisonF_isIso [PreservesColimitsOfSize.{0,0} F]
    (K : HomologicalComplex₂ C c c) (n : ℕ) : IsIso (comparisonF F K n) := by
  change IsIso (sigmaComparison F (fun ij : {ij : ℕ×ℕ // ij.1+ij.2=n} => (K.X ij.1.1).X ij.1.2))
  infer_instance

instance comparison_isIso [PreservesColimitsOfSize.{0,0} F]
    (K : HomologicalComplex₂ C c c) : IsIso (comparison F K) := by
  have (n : ℕ) : IsIso ((comparison F K).f n) := comparisonF_isIso F K n
  exact HomologicalComplex.Hom.isIso_of_components _

noncomputable def iso [PreservesColimitsOfSize.{0,0} F] (K : HomologicalComplex₂ C c c) :
    (F.mapHomologicalComplex c).obj (K.total c) ≅ (map₂ F K).total c :=
  (asIso (comparison F K)).symm

end TotalFunctor

end OAI
