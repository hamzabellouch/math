import OAI.Algebra.AuslanderReiten.HomComplex.FullHomProducts

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory
open CochainComplex CochainComplex.HomComplex

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
variable (Φ : C ⥤ D) [Φ.Additive] [Φ.Full] [Φ.Faithful]
variable (K L : CochainComplex C ℤ) (n : ℤ)

def fullHomCochainEquiv : Cochain K L n ≃+
    Cochain ((Φ.mapHomologicalComplex _).obj K) ((Φ.mapHomologicalComplex _).obj L) n where
  toFun x := x.map Φ
  invFun y := Cochain.mk fun p q hpq => Φ.preimage (y.v p q hpq)
  left_inv x := by
    apply Cochain.ext
    intro p q hpq
    exact Φ.preimage_map _
  right_inv y := by
    apply Cochain.ext
    intro p q hpq
    exact Φ.map_preimage _
  map_add' := fun x y => Cochain.map_add x y Φ

theorem fullHomCochainEquiv_differential (m : ℤ) (x : Cochain K L n) :
    δ n m (fullHomCochainEquiv Φ K L n x) = fullHomCochainEquiv Φ K L m (δ n m x) :=
  δ_map n m x Φ

def fullHomCocycleMap : Cocycle K L n →+
    Cocycle ((Φ.mapHomologicalComplex _).obj K) ((Φ.mapHomologicalComplex _).obj L) n where
  toFun x := Cocycle.mk (x.1.map Φ) (n + 1) rfl (by
    rw [δ_map, Cocycle.δ_eq_zero, Cochain.map_zero])
  map_zero' := by apply Cocycle.ext; exact Cochain.map_zero K L n Φ
  map_add' x y := by apply Cocycle.ext; exact Cochain.map_add x.1 y.1 Φ

theorem fullHomCocycleMap_bijective : Function.Bijective (fullHomCocycleMap Φ K L n) := by
  constructor
  · intro x y h
    apply Cocycle.ext
    apply (fullHomCochainEquiv Φ K L n).injective
    exact congrArg Subtype.val h
  · intro y
    let x := (fullHomCochainEquiv Φ K L n).symm y.1
    have hx : δ n (n + 1) x = 0 := by
      apply (fullHomCochainEquiv Φ K L (n + 1)).injective
      rw [← fullHomCochainEquiv_differential, map_zero]
      change δ n (n + 1) (fullHomCochainEquiv Φ K L n
        ((fullHomCochainEquiv Φ K L n).symm y.1)) = 0
      rw [AddEquiv.apply_symm_apply, Cocycle.δ_eq_zero]
    refine ⟨Cocycle.mk x (n + 1) rfl hx, ?_⟩
    apply Cocycle.ext
    exact (fullHomCochainEquiv Φ K L n).apply_symm_apply y.1

theorem fullHomCocycleMap_boundary (x : Cocycle K L n) :
    fullHomCocycleMap Φ K L n x ∈
      coboundaries ((Φ.mapHomologicalComplex _).obj K) ((Φ.mapHomologicalComplex _).obj L) n ↔
      x ∈ coboundaries K L n := by
  rw [mem_coboundaries_iff _ (n - 1) (by omega), mem_coboundaries_iff _ (n - 1) (by omega)]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(fullHomCochainEquiv Φ K L (n - 1)).symm y, ?_⟩
    apply (fullHomCochainEquiv Φ K L n).injective
    rw [← fullHomCochainEquiv_differential, AddEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨y, hy⟩
    refine ⟨y.map Φ, ?_⟩
    rw [δ_map, hy]
    rfl

def fullHomCohomologyMap : CohomologyClass K L n →+
    CohomologyClass ((Φ.mapHomologicalComplex _).obj K) ((Φ.mapHomologicalComplex _).obj L) n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom _ _ _).comp (fullHomCocycleMap Φ K L n)) (by
      intro x hx
      exact (CohomologyClass.mk_eq_zero_iff _).mpr
        ((fullHomCocycleMap_boundary Φ K L n x).mpr hx))

@[simp] theorem fullHomCohomologyMap_mk (x : Cocycle K L n) :
    fullHomCohomologyMap Φ K L n (CohomologyClass.mk x) =
      CohomologyClass.mk (fullHomCocycleMap Φ K L n x) := rfl

theorem fullHomCohomologyMap_bijective : Function.Bijective (fullHomCohomologyMap Φ K L n) := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective x
    exact (CohomologyClass.mk_eq_zero_iff y).mpr
      ((fullHomCocycleMap_boundary Φ K L n y).mp
        ((CohomologyClass.mk_eq_zero_iff _).mp hx))
  · intro y
    obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective y
    obtain ⟨x, rfl⟩ := (fullHomCocycleMap_bijective Φ K L n).surjective y
    exact ⟨CohomologyClass.mk x, rfl⟩

def fullHomCohomologyEquiv : CohomologyClass K L n ≃+
    CohomologyClass ((Φ.mapHomologicalComplex _).obj K) ((Φ.mapHomologicalComplex _).obj L) n :=
  AddEquiv.ofBijective (fullHomCohomologyMap Φ K L n) (fullHomCohomologyMap_bijective Φ K L n)

variable {K L n}

theorem fullHomCohomologyMap_product {M : CochainComplex C ℤ} {m : ℤ}
    (x : CohomologyClass K L n) (y : CohomologyClass L M m) :
    fullHomCohomologyMap Φ K M (n + m) (CompleteComparison.fullHomProduct x y) =
      CompleteComparison.fullHomProduct (fullHomCohomologyMap Φ K L n x)
        (fullHomCohomologyMap Φ L M m y) := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective y
  simp only [CompleteComparison.fullHomProduct_mk, fullHomCohomologyMap_mk]
  congr 1
  apply Cocycle.ext
  apply Cochain.map_comp
  rfl

end ArExplicit

end

end OAI
