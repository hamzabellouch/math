import Mathlib.Data.ZMod.Units
import OAI.NumberTheory.Ostmann.Characters.TemplateCharacterTransportCore
import OAI.NumberTheory.Ostmann.Characters.TemplatePhaseProducts

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template

def primeRowUnits {ι:Type*} [DecidableEq ι] (p:ι→ℕ)
    (hc:Pairwise (fun i j => (p i).Coprime (p j))) (i j:ι) : (ZMod (p i))ˣ :=
  if h:j=i then 1 else ZMod.unitOfCoprime (p j) (hc h)

@[simp] theorem primeRowUnits_self {ι:Type*} [DecidableEq ι] (p:ι→ℕ)
    (hc:Pairwise (fun i j => (p i).Coprime (p j))) (i:ι) :
    primeRowUnits p hc i i=1 := by simp [primeRowUnits]

@[simp] theorem primeRowUnits_coe {ι:Type*} [DecidableEq ι] (p:ι→ℕ)
    (hc:Pairwise (fun i j => (p i).Coprime (p j))) (i j:ι) (h:j≠i) :
    (primeRowUnits p hc i j:ZMod (p i))=(p j:ZMod (p i)) := by
  simp [primeRowUnits,h]

theorem primeRowUnits_character_row {ι:Type*} [Fintype ι] [DecidableEq ι]
    (p:ι→ℕ) (hc:Pairwise (fun i j => (p i).Coprime (p j)))
    (i:ι) (χ:MulChar (ZMod (p i)) ℂ) (B:ι→ℤ) (hB:B i=0) :
    ((rowProduct B (fun j => χ.toUnitHom (primeRowUnits p hc i j)):ℂˣ):ℂ) =
      ∏j:ι,χ (p j)^B j := by
  classical
  unfold rowProduct
  rw [Units.coe_prod]
  apply Finset.prod_congr rfl
  intro j _
  by_cases h:j=i
  · subst j
    simp [hB]
  · simp [Units.val_zpow_eq_zpow_val,primeRowUnits_coe p hc i j h]

theorem primeRowUnits_product {ι:Type*} [DecidableEq ι]
    (p:ι→ℕ) (hc:Pairwise (fun i j => (p i).Coprime (p j))) (i:ι)
    (S:Finset ι) (hi:i∉S) :
    (((∏j∈S,primeRowUnits p hc i j):(ZMod (p i))ˣ):ZMod (p i)) = ((∏j∈S,p j):ℕ) := by
  rw [Units.coe_prod,Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro j hj
  exact primeRowUnits_coe p hc i j (fun h => hi (h ▸ hj))

end Ostmann.Characters.Template

end

end OAI
