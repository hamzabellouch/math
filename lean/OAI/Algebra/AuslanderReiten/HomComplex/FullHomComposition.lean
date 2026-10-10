import OAI.Algebra.AuslanderReiten.HomComplex.FullHomProducts

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory
open CochainComplex CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Preadditive C]
variable {F G K : CochainComplex C ℤ} (φ : F ⟶ G) (n : ℤ)

def fullHomPrecompCocycle : Cocycle G K n →+ Cocycle F K n where
  toFun x := x.precomp φ
  map_zero' := by apply Cocycle.ext; simp
  map_add' x y := by apply Cocycle.ext; simp

def fullHomPostcompCocycle : Cocycle K F n →+ Cocycle K G n where
  toFun x := x.postcomp φ
  map_zero' := by apply Cocycle.ext; simp
  map_add' x y := by apply Cocycle.ext; simp

def fullHomPrecomp : CohomologyClass G K n →+ CohomologyClass F K n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom _ _ _).comp (fullHomPrecompCocycle φ n)) (by
      intro x hx
      apply (CohomologyClass.mk_eq_zero_iff _).mpr
      obtain ⟨m, hm, y, hy⟩ := hx
      refine ⟨m, hm, (Cochain.ofHom φ).comp y (zero_add m), ?_⟩
      simpa [fullHomPrecompCocycle] using congrArg (fun z => (Cochain.ofHom φ).comp z (zero_add n)) hy)

def fullHomPostcomp : CohomologyClass K F n →+ CohomologyClass K G n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom _ _ _).comp (fullHomPostcompCocycle φ n)) (by
      intro x hx
      apply (CohomologyClass.mk_eq_zero_iff _).mpr
      obtain ⟨m, hm, y, hy⟩ := hx
      refine ⟨m, hm, y.comp (Cochain.ofHom φ) (add_zero m), ?_⟩
      simpa [fullHomPostcompCocycle] using congrArg (fun z => z.comp (Cochain.ofHom φ) (add_zero n)) hy)

@[simp] theorem fullHomPrecomp_mk (x : Cocycle G K n) :
    fullHomPrecomp φ n (CohomologyClass.mk x) = CohomologyClass.mk (x.precomp φ) := rfl

@[simp] theorem fullHomPostcomp_mk (x : Cocycle K F n) :
    fullHomPostcomp φ n (CohomologyClass.mk x) = CohomologyClass.mk (x.postcomp φ) := rfl

end ArExplicit

end

end OAI
