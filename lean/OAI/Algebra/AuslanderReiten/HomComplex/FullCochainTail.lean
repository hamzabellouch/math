import OAI.Algebra.AuslanderReiten.Resolutions.NatResolutionCochain
import OAI.Algebra.AuslanderReiten.HomComplex.PositiveFullHomExt
import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionProductCompatibility

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (K L : CochainComplex (ModuleCat.{u} R) ℤ)

def tailTermIso (n : ℕ) :
    (nonnegativeTail (chainOfCochain K)).X n ≅ K.X (-(n : ℤ)) :=
  K.extendXIso negIndexEmbedding (by change -(-(n : ℤ))=(n : ℤ); omega)

theorem tailTerm_d (i j : ℕ) (h : j+1=i) :
    (nonnegativeTail (chainOfCochain K)).d i j =
      (tailTermIso K i).hom ≫ K.d (-(i : ℤ)) (-(j : ℤ)) ≫ (tailTermIso K j).inv := by
  subst i
  rw [nonnegativeTail_d]
  exact K.extend_d_eq negIndexEmbedding
    (show negIndexEmbedding.f (-((j+1 : ℕ) : ℤ))=((j+1 : ℕ) : ℤ) by
      change -(-((j+1 : ℕ) : ℤ))=((j+1 : ℕ) : ℤ); omega)
    (show negIndexEmbedding.f (-(j : ℤ))=(j : ℤ) by change -(-(j : ℤ))=(j : ℤ); omega)

def cochainTailMap (r : ℕ) (x : Cochain K L (r : ℤ)) (n : ℕ) :
    (nonnegativeTail (chainOfCochain K)).X (r+n) ⟶
      (nonnegativeTail (chainOfCochain L)).X n :=
  (tailTermIso K (r+n)).hom ≫ x.v (-((r+n : ℕ) : ℤ)) (-(n : ℤ)) (by omega) ≫
    (tailTermIso L n).inv

include k in
theorem cochainTailMap_comm (r : ℕ) (x : Cocycle K L (r : ℤ)) (n : ℕ) :
    cochainTailMap K L r x.val (n+1) ≫ (nonnegativeTail (chainOfCochain L)).d (n+1) n =
      (nonnegativeTail (chainOfCochain K)).d (r+(n+1)) (r+n) ≫ cochainTailMap K L r x.val n := by
  let i : ℤ := -((r+(n+1) : ℕ) : ℤ)
  let j : ℤ := -(n : ℤ)
  have hx := congrArg (fun z : Cochain K L ((r : ℤ)+1) => z.v i j (by dsimp [i,j]; omega))
    (show δ (r : ℤ) ((r : ℤ)+1) x.val=0 by simp)
  rw [δ_v _ _ rfl _ _ _ (by dsimp [i,j]; omega)
    (-((n+1 : ℕ) : ℤ)) (-((r+n : ℕ) : ℤ)) (by dsimp [i,j]; omega) (by dsimp [i,j]; omega),
    ResolutionProducts.intUnit_smul_charTwo (k := k), Cochain.zero_v] at hx
  let a := x.val.v i (-((n+1 : ℕ) : ℤ)) (by dsimp [i]; omega) ≫
    L.d (-((n+1 : ℕ) : ℤ)) j
  let b := K.d i (-((r+n : ℕ) : ℤ)) ≫
    x.val.v (-((r+n : ℕ) : ℤ)) j (by dsimp [j]; omega)
  have hab : a=b := by
    have hb : b+b=0 := by
      rw [← two_smul k b, show (2 : k)=0 from CharP.cast_eq_zero k 2, zero_smul]
    exact (eq_neg_of_add_eq_zero_left hx).trans (eq_neg_iff_add_eq_zero.mpr hb).symm
  rw [tailTerm_d L _ _ rfl, tailTerm_d K _ _ (by omega)]
  simp only [cochainTailMap, Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun z => (tailTermIso K (r+(n+1))).hom ≫ z ≫ (tailTermIso L n).inv) hab

variable (hK : TotallyAcyclicComplex (chainOfCochain K))
variable (hL : ExactProjectiveComplex (chainOfCochain L))

def restrictedCocycle (r : ℕ) (x : Cocycle K L (r : ℤ)) :
    Cocycle (completeExtResolution hK).cochainComplex
      (completeCokernelResolution (chainOfCochain L) hL.projective hL.exactAt).cochainComplex (r : ℤ) :=
  ResolutionProducts.natComparisonCocycle (k := k) (completeExtResolution hK)
    (completeCokernelResolution (chainOfCochain L) hL.projective hL.exactAt) r
    (cochainTailMap K L r x.val) (cochainTailMap_comm (k := k) K L r x)

end ArExplicit.CompleteComparison

end

end OAI
