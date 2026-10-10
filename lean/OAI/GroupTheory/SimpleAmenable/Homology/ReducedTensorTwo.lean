import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.FreeChains
import OAI.GroupTheory.SimpleAmenable.Homology.ChainPositiveCokernel

namespace OAI

section
open CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂
namespace ChainComplex
open scoped _root_.ChainComplex

variable {R:Type} [CommRing R] (K:ChainComplex (ModuleCat.{0} R) ℕ)
noncomputable def positiveIsCokernel (n:ℕ) (hn:K.d (n+1) n=0) :
    IsColimit (CokernelCofork.ofπ (positiveπ K n hn) (d_positiveπ K n hn)) :=
  CokernelCofork.IsColimit.ofπ' _ _ (fun f hf=>⟨positiveDesc K n hn f hf,positiveπ_desc K n hn f hf⟩)
end ChainComplex
namespace ReducedTensorTwo

section
open FreeChains

variable (K L:ChainComplex A ℕ) (hK:IsZero (K.X 0)) (hL:IsZero (L.X 0))
noncomputable abbrev inc (p q n:ℕ) (h:p+q=n) : K.X p ⊗ L.X q ⟶ (K⊗L).X n :=
  ιMapBifunctor K L (curriedTensor A) c p q n h
include hK hL
lemma total_one_zero : IsZero ((K⊗L).X 1) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply total.hom_ext
  intro p q hpq
  change inc K L p q 1 hpq ≫ 𝟙 _ = inc K L p q 1 hpq ≫ 0
  have hpq':p+q=1:=hpq
  by_cases hp:p=0
  · subst p
    exact (Functor.map_isZero (tensorRight (L.X q)) hK).eq_of_src _ _
  · have hq:q=0:=by omega
    subst q
    exact (Functor.map_isZero (tensorLeft (K.X p)) hL).eq_of_src _ _
lemma d21_zero : (K⊗L).d 2 1=0 := (total_one_zero K L hK hL).eq_of_tgt _ _
lemma inc_epi : Epi (inc K L 1 1 2 rfl) where
  left_cancellation f g h := by
    apply total.hom_ext
    intro p q hpq
    change inc K L p q 2 hpq ≫ f=inc K L p q 2 hpq ≫ g
    have hpq':p+q=2:=hpq
    by_cases hp:p=0
    · subst p; exact (Functor.map_isZero (tensorRight (L.X q)) hK).eq_of_src _ _
    · by_cases hq:q=0
      · subst q; exact (Functor.map_isZero (tensorLeft (K.X p)) hL).eq_of_src _ _
      · have he:p=1:=by omega
        have he':q=1:=by omega
        subst p q
        exact h
noncomputable def raw : K.X 1⊗L.X 1 ⟶ (K⊗L).homology 2 :=
  inc K L 1 1 2 rfl ≫ ChainComplex.positiveπ (K⊗L) 1 (d21_zero K L hK hL)
lemma raw_epi : Epi (raw K L hK hL) := by
  have :=inc_epi K L hK hL
  dsimp only [raw]; infer_instance
omit hK in
lemma inc21_d : inc K L 2 1 3 rfl ≫ (K⊗L).d 3 2 =
    (K.d 2 1 ▷ L.X 1) ≫ inc K L 1 1 2 rfl := by
  change ιMapBifunctor K L (curriedTensor A) c _ _ _ _ ≫ (mapBifunctor K L (curriedTensor A) c).d 3 2 = _
  rw [mapBifunctor.d_eq,Preadditive.comp_add,mapBifunctor.ι_D₁,mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq K L (curriedTensor A) c (show c.Rel 2 1 from rfl) 1 2 rfl,
    mapBifunctor.d₂_eq K L (curriedTensor A) c 2 (show c.Rel 1 0 from rfl) 2 rfl]
  have h:L.d 1 0=0:=hL.eq_of_tgt _ _
  simp [h,ComplexShape.ε₁,ComplexShape.ε₂]
omit hL in
lemma inc12_d : inc K L 1 2 3 rfl ≫ (K⊗L).d 3 2 =
    -((K.X 1 ◁ L.d 2 1) ≫ inc K L 1 1 2 rfl) := by
  change ιMapBifunctor K L (curriedTensor A) c _ _ _ _ ≫ (mapBifunctor K L (curriedTensor A) c).d 3 2 = _
  rw [mapBifunctor.d_eq,Preadditive.comp_add,mapBifunctor.ι_D₁,mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq K L (curriedTensor A) c (show c.Rel 1 0 from rfl) 2 2 rfl,
    mapBifunctor.d₂_eq K L (curriedTensor A) c 1 (show c.Rel 2 1 from rfl) 2 rfl]
  have h:K.d 1 0=0:=hK.eq_of_tgt _ _
  simp [h,ComplexShape.ε₁,ComplexShape.ε₂]
lemma d_left_raw : (K.d 2 1 ▷ L.X 1) ≫ raw K L hK hL=0 := by
  rw [raw,←Category.assoc,←inc21_d K L hL,Category.assoc,ChainComplex.d_positiveπ,comp_zero]
lemma d_right_raw : (K.X 1 ◁ L.d 2 1) ≫ raw K L hK hL=0 := by
  have h:=congrArg (fun f=>f≫ChainComplex.positiveπ (K⊗L) 1 (d21_zero K L hK hL)) (inc12_d K L hK)
  simpa only [raw,Category.assoc,ChainComplex.d_positiveπ,comp_zero,Preadditive.neg_comp,neg_eq_zero] using h.symm
end

open FreeChains

variable (K L:ChainComplex A ℕ) (hK:IsZero (K.X 0)) (hL:IsZero (L.X 0))
noncomputable abbrev πK := ChainComplex.positiveπ K 0 (hK.eq_of_tgt (K.d 1 0) 0)
noncomputable abbrev πL := ChainComplex.positiveπ L 0 (hL.eq_of_tgt (L.d 1 0) 0)
noncomputable def leftColimit := isColimitCoforkMapOfIsColimit' (tensorRight (L.X 1))
  (ChainComplex.d_positiveπ K 0 (hK.eq_of_tgt (K.d 1 0) 0))
  (ChainComplex.positiveIsCokernel K 0 (hK.eq_of_tgt (K.d 1 0) 0))
noncomputable def leftDesc : K.homology 1⊗L.X 1 ⟶ (K⊗L).homology 2 :=
  (leftColimit K L hK).desc (CokernelCofork.ofπ (raw K L hK hL) (d_left_raw K L hK hL))
@[reassoc] lemma π_leftDesc : (πK K hK ▷ L.X 1) ≫ leftDesc K L hK hL=raw K L hK hL :=
  (leftColimit K L hK).fac _ WalkingParallelPair.one
lemma d_leftDesc : (K.homology 1 ◁ L.d 2 1) ≫ leftDesc K L hK hL=0 := by
  have : Epi (πK K hK ▷ L.X 2) := Cofork.IsColimit.epi
    (isColimitCoforkMapOfIsColimit' (tensorRight (L.X 2))
      (ChainComplex.d_positiveπ K 0 (hK.eq_of_tgt (K.d 1 0) 0))
      (ChainComplex.positiveIsCokernel K 0 (hK.eq_of_tgt (K.d 1 0) 0)))
  apply (cancel_epi (πK K hK ▷ L.X 2)).mp
  rw [comp_zero,←Category.assoc,←MonoidalCategory.whisker_exchange,Category.assoc,π_leftDesc,d_right_raw]
noncomputable def rightColimit := isColimitCoforkMapOfIsColimit' (tensorLeft (K.homology 1))
  (ChainComplex.d_positiveπ L 0 (hL.eq_of_tgt (L.d 1 0) 0))
  (ChainComplex.positiveIsCokernel L 0 (hL.eq_of_tgt (L.d 1 0) 0))
noncomputable def generator : K.homology 1⊗L.homology 1 ⟶ (K⊗L).homology 2 :=
  (rightColimit K L hL).desc (CokernelCofork.ofπ (leftDesc K L hK hL) (d_leftDesc K L hK hL))
@[reassoc] lemma π_generator : (πK K hK ⊗ₘ πL L hL) ≫ generator K L hK hL=raw K L hK hL := by
  rw [MonoidalCategory.tensorHom_def,Category.assoc]
  have h : (K.homology 1 ◁ πL L hL) ≫ generator K L hK hL=leftDesc K L hK hL :=
    (rightColimit K L hL).fac _ WalkingParallelPair.one
  rw [h,π_leftDesc]
lemma generator_epi : Epi (generator K L hK hL) := by
  have : Epi ((πK K hK ⊗ₘ πL L hL) ≫ generator K L hK hL):=by
    rw [π_generator]; exact raw_epi K L hK hL
  exact epi_of_epi (πK K hK ⊗ₘ πL L hL) _
end ReducedTensorTwo

end

open CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂
namespace ChainComplex
open scoped _root_.ChainComplex

variable {R:Type} [CommRing R] {K L:ChainComplex (ModuleCat.{0} R) ℕ}
@[reassoc] lemma positiveπ_natural (f:K⟶L) (n:ℕ) (hK:K.d (n+1) n=0) (hL:L.d (n+1) n=0) :
    positiveπ K n hK ≫ homologyMap f (n+1)=f.f (n+1) ≫ positiveπ L n hL := by
  apply (cancel_mono (L.homologyι (n+1))).mp
  simp only [positiveπ,Category.assoc,homologyι_naturality,isoHomologyι_inv_hom_id_assoc,
    isoHomologyι_inv_hom_id,Category.comp_id,p_opcyclesMap]
end ChainComplex
namespace ModuleCat
open scoped _root_.ModuleCat
lemma tensor_epi {R:Type} [CommRing R] {M N P Q:ModuleCat.{0} R} (f:M⟶N) (g:P⟶Q)
    [Epi f] [Epi g] : Epi (f⊗ₘg) := by
  apply (_root_.ModuleCat.epi_iff_surjective _).mpr
  exact TensorProduct.map_surjective ((_root_.ModuleCat.epi_iff_surjective f).mp inferInstance)
    ((_root_.ModuleCat.epi_iff_surjective g).mp inferInstance)
end ModuleCat
namespace ReducedTensorTwo
open FreeChains

variable {K L K' L':ChainComplex A ℕ} (f:K⟶K') (g:L⟶L')
variable (hK:IsZero (K.X 0)) (hL:IsZero (L.X 0)) (hK':IsZero (K'.X 0)) (hL':IsZero (L'.X 0))
@[reassoc] lemma inc_natural (p q n:ℕ) (h:p+q=n) :
    inc K L p q n h ≫ (f⊗ₘg).f n=(f.f p ⊗ₘg.f q) ≫ inc K' L' p q n h := by
  change ιMapBifunctor K L (curriedTensor A) c p q n h ≫
    (mapBifunctorMap f g (curriedTensor A) c).f n=_
  rw [ι_mapBifunctorMap]
  change (f.f p ▷ L.X q) ≫ (K'.X p ◁ g.f q) ≫ _ = _
  rw [←Category.assoc,←MonoidalCategory.tensorHom_def]
@[reassoc] lemma raw_natural : raw K L hK hL ≫ homologyMap (f⊗ₘg) 2=
    (f.f 1⊗ₘg.f 1) ≫ raw K' L' hK' hL' := by
  rw [raw,Category.assoc,ChainComplex.positiveπ_natural,←Category.assoc,inc_natural,Category.assoc]
  rfl
@[reassoc] lemma generator_natural : generator K L hK hL ≫ homologyMap (f⊗ₘg) 2=
    (homologyMap f 1⊗ₘhomologyMap g 1) ≫ generator K' L' hK' hL' := by
  have :=ModuleCat.tensor_epi (πK K hK) (πL L hL)
  apply (cancel_epi (πK K hK⊗ₘπL L hL)).mp
  rw [π_generator_assoc,raw_natural,←Category.assoc,tensorHom_comp_tensorHom]
  rw [ChainComplex.positiveπ_natural f 0 _ (hK'.eq_of_tgt _ _),
    ChainComplex.positiveπ_natural g 0 _ (hL'.eq_of_tgt _ _),←tensorHom_comp_tensorHom,
    Category.assoc,π_generator]
include hK hL hK' hL' in
lemma homology_epi [Epi (homologyMap f 1)] [Epi (homologyMap g 1)] :
    Epi (homologyMap (f⊗ₘg) 2) := by
  have :=ModuleCat.tensor_epi (homologyMap f 1) (homologyMap g 1)
  have :=generator_epi K' L' hK' hL'
  have : Epi (generator K L hK hL ≫ homologyMap (f⊗ₘg) 2):=by rw [generator_natural f g hK hL hK' hL']; infer_instance
  exact epi_of_epi (generator K L hK hL) _
end ReducedTensorTwo

end OAI
