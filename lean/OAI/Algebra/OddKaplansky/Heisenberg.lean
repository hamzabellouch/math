import OAI.Algebra.OddKaplansky.SquareCertificate

namespace OAI

section
namespace OddKaplansky.Heisenberg
noncomputable section
open scoped Classical BigOperators
variable (M q : ℕ)
abbrev Z := Fin q → Fourier.C M
def dot (y x : Z M q) : Fourier.C M := Multiplicative.ofAdd (∑ j, (y j).toAdd * (x j).toAdd)
lemma dot_one_left (x : Z M q) : dot M q 1 x=1 := by simp [dot]
lemma dot_one_right (y : Z M q) : dot M q y 1=1 := by simp [dot]
lemma dot_mul_left (y t x : Z M q) : dot M q (y*t) x = dot M q y x * dot M q t x := by
  apply Multiplicative.toAdd.injective
  simp [dot,add_mul,Finset.sum_add_distrib]
lemma dot_mul_right (y x s : Z M q) : dot M q y (x*s) = dot M q y x * dot M q y s := by
  apply Multiplicative.toAdd.injective
  simp [dot,mul_add,Finset.sum_add_distrib]
lemma dot_inv_left (y x : Z M q) : dot M q y⁻¹ x = (dot M q y x)⁻¹ := by
  apply Multiplicative.toAdd.injective
  simp [dot,Finset.sum_neg_distrib]
lemma dot_inv_right (y x : Z M q) : dot M q y x⁻¹ = (dot M q y x)⁻¹ := by
  apply Multiplicative.toAdd.injective
  simp [dot,Finset.sum_neg_distrib]
lemma dot_symm (y x : Z M q) : dot M q y x=dot M q x y := by simp [dot,mul_comm]
structure GroupData where
  x : Z M q
  y : Z M q
  k : Fourier.C M
@[ext] lemma GroupData.ext {a b : GroupData M q} (hx : a.x=b.x) (hy : a.y=b.y) (hk : a.k=b.k) : a=b := by
  cases a; cases b; simp_all
instance : One (GroupData M q) := ⟨⟨1,1,1⟩⟩
instance : Mul (GroupData M q) := ⟨fun a b => ⟨a.x*b.x,a.y*b.y,a.k*b.k*dot M q a.y b.x⟩⟩
instance : Inv (GroupData M q) := ⟨fun a => ⟨a.x⁻¹,a.y⁻¹,a.k⁻¹*dot M q a.y a.x⟩⟩
@[simp] lemma one_x : (1 : GroupData M q).x=1 := rfl
@[simp] lemma one_y : (1 : GroupData M q).y=1 := rfl
@[simp] lemma one_k : (1 : GroupData M q).k=1 := rfl
@[simp] lemma mul_x (a b : GroupData M q) : (a*b).x=a.x*b.x := rfl
@[simp] lemma mul_y (a b : GroupData M q) : (a*b).y=a.y*b.y := rfl
@[simp] lemma mul_k (a b : GroupData M q) : (a*b).k=a.k*b.k*dot M q a.y b.x := rfl
@[simp] lemma inv_x (a : GroupData M q) : a⁻¹.x=a.x⁻¹ := rfl
@[simp] lemma inv_y (a : GroupData M q) : a⁻¹.y=a.y⁻¹ := rfl
@[simp] lemma inv_k (a : GroupData M q) : a⁻¹.k=a.k⁻¹*dot M q a.y a.x := rfl
instance : Group (GroupData M q) where
  mul_assoc a b c := by ext <;> simp only [mul_x,mul_y,mul_k,dot_mul_left,dot_mul_right,mul_assoc]; ac_rfl
  one_mul a := by ext <;> simp [dot_one_left]
  mul_one a := by ext <;> simp [dot_one_right]
  inv_mul_cancel a := by ext <;> simp [dot_inv_left,mul_comm]
def coordinates : GroupData M q ≃ Z M q × Z M q × Fourier.C M where
  toFun a := (a.x,a.y,a.k)
  invFun a := ⟨a.1,a.2.1,a.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
instance [NeZero M] : Fintype (GroupData M q) := Fintype.ofEquiv _ (coordinates M q).symm
lemma card [NeZero M] : Fintype.card (GroupData M q)=M*(M^q)^2 := by
  rw [Fintype.card_congr (coordinates M q)]
  simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_multiplicative,ZMod.card]
  ring
def central : Fourier.C M →* GroupData M q where
  toFun k := ⟨1,1,k⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp [dot_one_left]
def X : Z M q →* GroupData M q where
  toFun x := ⟨x,1,1⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp [dot_one_left]
def Y : Z M q →* GroupData M q where
  toFun y := ⟨1,y,1⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp [dot_one_right]
lemma central_injective : Function.Injective (central M q) := fun _ _ he => congrArg GroupData.k he
lemma central_commute (c : Fourier.C M) (g : GroupData M q) : Commute (central M q c) g := by
  change central M q c*g=g*central M q c
  ext <;> simp [central,dot_one_left,dot_one_right,mul_comm]
lemma YX (y x : Z M q) : Y M q y * X M q x = central M q (dot M q y x) * (X M q x * Y M q y) := by
  ext <;> simp [central,X,Y,dot_one_left,dot_one_right]
lemma normal (g : GroupData M q) : g=central M q g.k * (X M q g.x * Y M q g.y) := by
  ext <;> simp [central,X,Y,dot_one_left,dot_one_right]
end
end OddKaplansky.Heisenberg

end

end OAI
