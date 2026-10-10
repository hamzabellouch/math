import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorComplex

namespace OAI

noncomputable section

namespace ArExplicit.ExternalTensor

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

universe u

variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

abbrev inclusion (i j n : ℕ) (h : i+j=n) :
    moduleObject k A B (P.X i) (Q.X j) ⟶ (complex k A B P Q).X n :=
  ιMapBifunctor P Q (bifunctor k A B) (ComplexShape.down ℕ) i j n h

abbrev desc {N : ModuleCat.{u} (A ⊗[k] B)} {n : ℕ}
    (f : ∀ (i j : ℕ) (_ : i+j=n), moduleObject k A B (P.X i) (Q.X j) ⟶ N) :
    (complex k A B P Q).X n ⟶ N :=
  mapBifunctorDesc (K₁ := P) (K₂ := Q) (F := bifunctor k A B) (c := ComplexShape.down ℕ) f

@[simp] theorem inclusion_desc {N : ModuleCat.{u} (A ⊗[k] B)} {n : ℕ}
    (f : ∀ (i j : ℕ) (_ : i+j=n), moduleObject k A B (P.X i) (Q.X j) ⟶ N)
    (i j : ℕ) (h : i+j=n) :
    inclusion k A B P Q i j n h ≫ desc k A B P Q f = f i j h :=
  ι_mapBifunctorDesc (K₁ := P) (K₂ := Q) (F := bifunctor k A B)
    (c := ComplexShape.down ℕ) f i j h

theorem hom_ext {N : ModuleCat.{u} (A ⊗[k] B)} {n : ℕ}
    {f g : (complex k A B P Q).X n ⟶ N}
    (h : ∀ (i j : ℕ) (hij : i+j=n),
      inclusion k A B P Q i j n hij ≫ f = inclusion k A B P Q i j n hij ≫ g) : f=g :=
  mapBifunctor.hom_ext h

abbrev horizontal (i j n : ℕ) : moduleObject k A B (P.X i) (Q.X j) ⟶ (complex k A B P Q).X n :=
  mapBifunctor.d₁ P Q (bifunctor k A B) (ComplexShape.down ℕ) i j n

abbrev vertical (i j n : ℕ) : moduleObject k A B (P.X i) (Q.X j) ⟶ (complex k A B P Q).X n :=
  mapBifunctor.d₂ P Q (bifunctor k A B) (ComplexShape.down ℕ) i j n

theorem inclusion_d (i j n n' : ℕ) (h : i+j=n) :
    inclusion k A B P Q i j n h ≫ (complex k A B P Q).d n n' =
      horizontal k A B P Q i j n' + vertical k A B P Q i j n' := by
  change ιMapBifunctor P Q (bifunctor k A B) (ComplexShape.down ℕ) i j n h ≫
    (mapBifunctor P Q (bifunctor k A B) (ComplexShape.down ℕ)).d n n' =
    mapBifunctor.d₁ P Q (bifunctor k A B) (ComplexShape.down ℕ) i j n' +
    mapBifunctor.d₂ P Q (bifunctor k A B) (ComplexShape.down ℕ) i j n'
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]

theorem horizontal_succ (i j n : ℕ) (h : i+j=n) :
    horizontal k A B P Q (i+1) j n =
      mapHom k A B (P.d (i+1) i) (𝟙 (Q.X j)) ≫ inclusion k A B P Q i j n h := by
  dsimp only [horizontal]
  rw [mapBifunctor.d₁_eq P Q (bifunctor k A B) (ComplexShape.down ℕ) (by rfl) j n h]
  change (1 : ℤˣ) • _ = _
  exact one_smul _ _

theorem vertical_succ (i j n : ℕ) (h : i+j=n) :
    vertical k A B P Q i (j+1) n =
      (-1 : ℤˣ)^i • (mapHom k A B (𝟙 (P.X i)) (Q.d (j+1) j) ≫
        inclusion k A B P Q i j n h) := by
  dsimp only [vertical]
  rw [mapBifunctor.d₂_eq P Q (bifunctor k A B) (ComplexShape.down ℕ) i (by rfl) n h]
  rfl

theorem horizontal_zero (j n : ℕ) : horizontal k A B P Q 0 j n = 0 :=
  mapBifunctor.d₁_eq_zero P Q (bifunctor k A B) (ComplexShape.down ℕ) 0 j n (by
    change ¬ (ComplexShape.down ℕ).next 0 + 1 = 0
    omega)

theorem vertical_zero (i n : ℕ) : vertical k A B P Q i 0 n = 0 :=
  mapBifunctor.d₂_eq_zero P Q (bifunctor k A B) (ComplexShape.down ℕ) i 0 n (by
    change ¬ (ComplexShape.down ℕ).next 0 + 1 = 0
    omega)

theorem termDirectSumEquiv_inclusion (i j n : ℕ) (h : i+j=n) :
    (termDirectSumEquiv k A B P Q n).toLinearMap.comp
      (inclusion k A B P Q i j n h).hom =
      DFinsupp.lsingle (R := A ⊗[k] B) (M := fun p : Diagonal n => summands k A B P Q n p)
        ⟨(i,j),h⟩ := by
  exact congrArg (fun f => f.hom)
    (ModuleCat.ι_coprodIsoDirectSum_hom (summands k A B P Q n) ⟨(i,j),h⟩)

theorem inclusion_eq_directSum (i j n : ℕ) (h : i+j=n) :
    (inclusion k A B P Q i j n h).hom =
      (termDirectSumEquiv k A B P Q n).symm.toLinearMap.comp
        (DFinsupp.lsingle (R := A ⊗[k] B) (M := fun p : Diagonal n => summands k A B P Q n p)
          ⟨(i,j),h⟩) := by
  ext x
  apply (termDirectSumEquiv k A B P Q n).injective
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using
    LinearMap.congr_fun (termDirectSumEquiv_inclusion k A B P Q i j n h) x

end ArExplicit.ExternalTensor

end

end OAI
