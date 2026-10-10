import OAI.Algebra.OddKaplansky.SectorRectangles

namespace OAI

universe portUniverse1

section
namespace OddKaplansky.SectorStabilizer
noncomputable section
open scoped Classical BigOperators
variable {G : Type portUniverse1} [Group G] (M : ℕ)
def stabilizer (a : G → ZMod M) : Subgroup G where
  carrier := {g | ∀ x, a (g*x)=a x}
  one_mem' x := by simp
  mul_mem' hg hh x := by rw [mul_assoc,hg,hh]
  inv_mem' {g} hg x := by have h := hg (g⁻¹*x); simpa only [mul_inv_cancel_left] using h.symm
variable (p : ℕ) [sectionInstance55 : NeZero p] [sectionInstance56 : NeZero M]
abbrev Point := Multiplicative (Fin 3 → ZMod p)
abbrev H := RegularWreathProduct (Multiplicative (ZMod M)) (Point p)
instance : Fintype (H M p) := Fintype.ofFinite _
def baseHom : (Point p → Multiplicative (ZMod M)) →* H M p where
  toFun a := ⟨a,1⟩
  map_one' := rfl
  map_mul' a b := by ext x <;> simp
lemma base_pow
    (M : Nat)
    (p : Nat)
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) p]
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (a : Point p → Multiplicative (ZMod M)) : a^M=1 := by
  funext x
  apply Multiplicative.toAdd.injective
  simp
lemma pow_of_right (g : H M p) (h : g.right=1) : g^M=1 := by
  have hg : g=baseHom M p g.left := by ext <;> simp [baseHom,h]
  rw [hg,← map_pow,base_pow,map_one]
variable (a : H M p → ZMod M) (ha : ∑ g, a g = 1)
def toPoint : stabilizer M a →* Point p := RegularWreathProduct.rightHom.comp (stabilizer M a).subtype
include ha in
lemma toPoint_kernel (g : stabilizer M a) (hg : toPoint M p a g = 1) : g=1 := by
  apply Subtype.ext
  exact CosetCoordinates.eq_one_of_power_and_sum M a ha g g.property (pow_of_right M p g hg)
include ha in
lemma toPoint_injective : Function.Injective (toPoint M p a) := by
  intro x y h
  have hxy : toPoint M p a (x*y⁻¹)=1 := by rw [map_mul,map_inv,h,mul_inv_cancel]
  exact mul_inv_eq_one.mp (toPoint_kernel M p a ha _ hxy)
include ha in
lemma commutative (x y : stabilizer M a) : x*y=y*x := by
  apply toPoint_injective M p a ha
  rw [map_mul,map_mul,mul_comm]
@[instance_reducible]
def commGroup (ha : ∑ g, a g=1) : CommGroup (stabilizer M a) :=
  { (inferInstance : Group (stabilizer M a)) with mul_comm := commutative M p a ha }
include ha in
lemma exponent (x : stabilizer M a) : x^p=1 := by
  apply toPoint_injective M p a ha
  rw [map_pow,map_one]
  apply Multiplicative.toAdd.injective
  funext i
  simp
end
end OddKaplansky.SectorStabilizer

end

end OAI
