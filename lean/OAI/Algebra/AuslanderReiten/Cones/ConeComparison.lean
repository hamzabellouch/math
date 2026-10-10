import OAI.Algebra.AuslanderReiten.Cones.ConeEnd
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomComposition

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Preadditive C]
variable {F G : CochainComplex C ℤ} (φ : F ⟶ G) (n : ℤ)

def coneComparisonCochain : (Cochain G G n × Cochain F F n) →ₗ[ℤ] Cochain F G n where
  toFun x := x.2.comp (Cochain.ofHom φ) (add_zero n) +
    (n + 1).negOnePow • (Cochain.ofHom φ).comp x.1 (zero_add n)
  map_add' x y := by simp [smul_add]; abel
  map_smul' r x := by simp [smul_add, smul_comm r (n + 1).negOnePow]

def coneDiagonalDifferential (m : ℤ) :
    (Cochain G G n × Cochain F F n) →ₗ[ℤ] (Cochain G G m × Cochain F F m) where
  toFun x := (δ n m x.1, -(δ n m x.2))
  map_add' x y := by ext <;> simp [add_comm]
  map_smul' r x := by ext <;> simp

@[simp] theorem coneComparisonCochain_apply (a : Cochain G G n) (b : Cochain F F n) :
    coneComparisonCochain φ n (a, b) = b.comp (Cochain.ofHom φ) (add_zero n) +
      (n + 1).negOnePow • (Cochain.ofHom φ).comp a (zero_add n) := rfl

theorem coneComparison_differential (m : ℤ) (hm : n + 1 = m)
    (x : Cochain G G n × Cochain F F n) :
    coneComparisonCochain φ m (coneDiagonalDifferential n m x) =
      -(δ n m (coneComparisonCochain φ n x)) := by
  subst m
  simp [coneComparisonCochain, coneDiagonalDifferential, Int.negOnePow_succ]
  abel

def coneComparison :
    (CohomologyClass G G n × CohomologyClass F F n) →+ CohomologyClass F G n where
  toFun x := fullHomPostcomp φ n x.2 + (n + 1).negOnePow • fullHomPrecomp φ n x.1
  map_zero' := by simp
  map_add' x y := by simp [smul_add]; abel

theorem coneComparison_mk (a : Cocycle G G n) (b : Cocycle F F n) :
    coneComparison φ n (CohomologyClass.mk a, CohomologyClass.mk b) =
      CohomologyClass.mk (b.postcomp φ + (n + 1).negOnePow • a.precomp φ) := by
  change CohomologyClass.mk (b.postcomp φ) +
      (n + 1).negOnePow • CohomologyClass.mk (a.precomp φ) = _
  rw [CohomologyClass.mk_add]
  congr 1

end ArExplicit

end

end OAI
