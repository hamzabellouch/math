import OAI.Algebra.AuslanderReiten.HomComplex.FullHomProducts

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory CochainComplex.HomComplex

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]

structure FullHomEquivalence (K L : CochainComplex C ℤ) (K' L' : CochainComplex D ℤ) where
  cochain : ∀ n : ℤ, Cochain K L n ≃+ Cochain K' L' n
  differential : ∀ (n m : ℤ) (x : Cochain K L n), δ n m (cochain n x) = cochain m (δ n m x)

namespace FullHomEquivalence

variable {K L : CochainComplex C ℤ} {K' L' : CochainComplex D ℤ}
variable (e : FullHomEquivalence K L K' L') (n : ℤ)

def cocycle : Cocycle K L n →+ Cocycle K' L' n where
  toFun x := Cocycle.mk (e.cochain n x.1) (n+1) rfl (by
    rw [e.differential, Cocycle.δ_eq_zero, map_zero])
  map_zero' := by apply Cocycle.ext; exact (e.cochain n).map_zero
  map_add' x y := by apply Cocycle.ext; exact (e.cochain n).map_add x.1 y.1

theorem cocycle_bijective : Function.Bijective (e.cocycle n) := by
  constructor
  · intro x y h
    apply Cocycle.ext
    exact (e.cochain n).injective (congrArg Subtype.val h)
  · intro y
    let x := (e.cochain n).symm y.1
    have hx : δ n (n+1) x = 0 := by
      apply (e.cochain (n+1)).injective
      rw [← e.differential, map_zero]
      change δ n (n+1) (e.cochain n ((e.cochain n).symm y.1)) = 0
      rw [AddEquiv.apply_symm_apply, Cocycle.δ_eq_zero]
    refine ⟨Cocycle.mk x (n+1) rfl hx, ?_⟩
    apply Cocycle.ext
    exact (e.cochain n).apply_symm_apply y.1

theorem boundary_iff (x : Cocycle K L n) :
    e.cocycle n x ∈ coboundaries K' L' n ↔ x ∈ coboundaries K L n := by
  rw [mem_coboundaries_iff _ (n-1) (by omega), mem_coboundaries_iff _ (n-1) (by omega)]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(e.cochain (n-1)).symm y, ?_⟩
    apply (e.cochain n).injective
    rw [← e.differential, AddEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨y, hy⟩
    refine ⟨e.cochain (n-1) y, ?_⟩
    rw [e.differential, hy]
    rfl

def cohomologyMap : CohomologyClass K L n →+ CohomologyClass K' L' n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom _ _ _).comp (e.cocycle n)) (by
      intro x hx
      exact (CohomologyClass.mk_eq_zero_iff _).mpr ((e.boundary_iff n x).mpr hx))

@[simp] theorem cohomologyMap_mk (x : Cocycle K L n) :
    e.cohomologyMap n (CohomologyClass.mk x) = CohomologyClass.mk (e.cocycle n x) := rfl

theorem cohomologyMap_bijective : Function.Bijective (e.cohomologyMap n) := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective x
    exact (CohomologyClass.mk_eq_zero_iff y).mpr
      ((e.boundary_iff n y).mp ((CohomologyClass.mk_eq_zero_iff _).mp hx))
  · intro y
    obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective y
    obtain ⟨x, rfl⟩ := (e.cocycle_bijective n).2 y
    exact ⟨CohomologyClass.mk x, rfl⟩

def cohomology : CohomologyClass K L n ≃+ CohomologyClass K' L' n :=
  AddEquiv.ofBijective (e.cohomologyMap n) (e.cohomologyMap_bijective n)

end FullHomEquivalence
end ArExplicit

end

end OAI
