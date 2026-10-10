import OAI.NumberTheory.Ostmann.Arithmetic.ResidueHaar

namespace OAI

noncomputable section
namespace Ostmann.Characters.BinaryHaar
universe u

@[reducible] def Leaves (G:Type u) : ℕ → Type u
  | 0 => G
  | k+1 => Leaves G k × Leaves G k

@[reducible] def Splits (G:Type u) : ℕ → Type u
  | 0 => PUnit
  | k+1 => G × (Splits G k × Splits G k)

@[reducible] instance leavesFintype {G:Type*} [Fintype G] (k:ℕ) : Fintype (Leaves G k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype G)
  | succ k ih => exact @instFintypeProd _ _ ih ih

@[reducible] instance splitsFintype {G:Type*} [Fintype G] (k:ℕ) : Fintype (Splits G k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ k ih => exact @instFintypeProd _ _ inferInstance (@instFintypeProd _ _ ih ih)

def decoratedSplit {G C D:Type*} [Group G] :
    (G×C)×(G×D) ≃ G×(G×(C×D)) where
  toFun z := (z.1.1*z.2.1,(z.1.1,(z.1.2,z.2.2)))
  invFun z := ((z.2.1,z.2.2.1),(z.2.1⁻¹*z.1,z.2.2.2))
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp

def expose {G:Type*} [Group G] : (k:ℕ) → Leaves G k ≃ G×Splits G k
  | 0 =>
    { toFun := fun x => (x,PUnit.unit)
      invFun := Prod.fst
      left_inv := fun _ => rfl
      right_inv := fun x => by cases x; rfl }
  | k+1 => (Equiv.prodCongr (expose (G:=G) k) (expose (G:=G) k)).trans decoratedSplit

def product {G:Type*} [Group G] : {k:ℕ} → Leaves G k → G
  | 0,x => x
  | k+1,x => product (k:=k) x.1 * product (k:=k) x.2

@[simp] theorem expose_first {G:Type*} [Group G] (k:ℕ) (x:Leaves G k) :
    (expose (G:=G) k x).1=product x := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg₂ (·*·) (ih x.1) (ih x.2)

def fixedProductEquiv {G:Type*} [Group G] (k:ℕ) (t:G) :
    {x:Leaves G k // product x=t} ≃ Splits G k where
  toFun x := (expose (G:=G) k x.val).2
  invFun c := ⟨(expose (G:=G) k).symm (t,c), by
    rw [← expose_first, Equiv.apply_symm_apply]⟩
  left_inv x := by
    apply Subtype.ext
    apply (expose (G:=G) k).injective
    rw [Equiv.apply_symm_apply]
    apply Prod.ext
    · exact x.property.symm.trans (expose_first (G:=G) k x.val).symm
    · rfl
  right_inv c := by simp

theorem expose_average {G:Type*} [Group G] [Fintype G] (k:ℕ)
    (F:G×Splits G k→ℂ) :
    Arithmetic.ResidueHaar.average (fun x:Leaves G k => F (expose (G:=G) k x)) =
      Arithmetic.ResidueHaar.average F :=
  Arithmetic.ResidueHaar.average_equiv (expose (G:=G) k) F

theorem fixedProduct_card {G:Type*} [Group G] [Fintype G] (k:ℕ) (t:G) :
    Nat.card {x:Leaves G k // product x=t}=Nat.card (Splits G k) :=
  Nat.card_congr (fixedProductEquiv k t)

end Ostmann.Characters.BinaryHaar

end

end OAI
