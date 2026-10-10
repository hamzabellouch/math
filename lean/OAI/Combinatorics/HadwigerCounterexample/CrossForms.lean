import OAI.Combinatorics.HadwigerCounterexample.NominalSpaces

namespace OAI

/-! # Cross Forms -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

def flipZ (p : Shape) (z : Place p) : Place p := (z.1,!z.2)
@[simp] theorem flipZ_flip (z : Place p) : flipZ p (flipZ p z)=z := by cases z; simp [flipZ]

abbrev Cross (p : Shape) (n : ℕ) := Place p → Mat (JointIdx p n) (JointIdx p n)
def reciprocal (p : Shape) {n} (M : Cross p n) : Cross p n := fun z => (M (flipZ p z))ᵀ
@[simp] theorem reciprocal_twice (M : Cross p n) : reciprocal p (reciprocal p M)=M := by
  funext i; simp [reciprocal]

def actual (p : Shape) {n N} (x y : UnitType p n N) : Cross p n :=
  fun z => (images x z)ᵀ * images y (flipZ p z)

@[simp] theorem reciprocal_actual (x y : UnitType p n N) :
    reciprocal p (actual p x y)=actual p y x := by
  funext z; simp only [reciprocal,actual,transpose_mul,flipZ_flip,transpose_transpose]

/-- two abstract cross sets agree at every row coming from these frozen
directions. Also apply this notion reciprocally to check columns. -/
def rowAgree (q : Plan p n) (A B : Cross p n) :=
  ∀ z, ∀ x∈ q z,∀ y, evmat (A z) x y=evmat (B z) x y

/-- The flag on an orientation of A. Test all entries on the table spaces
with column in the B pins. Test the other entries by the reciprocal flag.
Together these are §5 admissibility (when units are in the pin leaves). -/
def tableFlag (a b : Pin p n N) (M : Cross p n) (x : UnitType p n N) :=
  ∀ z,∀ v∈tabSpace a.sp z,∀ w∈b.sp (flipZ p z),
    evmat (M z) v w=dotProduct (images x z *ᵥ v) (b.target (flipZ p z) *ᵥ w)

private theorem ev_gram {I J W : Type} [Fintype I] [Fintype J] [Fintype W]
    (P : Mat W I) (Q : Mat W J) (v : Vec I) (w : Vec J) :
    evmat (Pᵀ*Q) v w = dotProduct (P *ᵥ v) (Q *ᵥ w) := by
  rw [evmat,← Matrix.mulVec_mulVec,dotProduct_transpose_mulVec,dotProduct_comm]

theorem flag_actual {a b : Pin p n N} (x y : UnitType p n N) (h : b.agree y) :
    tableFlag a b (actual p x y) x := by
  intro z v hv w hw
  rw [actual,ev_gram,h _ _ hw]

def channelOut (p : Shape) {n} (M : Cross p n) (j : Bool) (z : Place p) :
    Mat (Chan p) (JointIdx p n) := (M z * IH p n j)ᵀ

/-- small table injecting condition, at this role. Row directions are in
a.sp and wholly in the indicated primal block; output is viewed modulo
*hPin at the same sign*, not the sign of the tested columns. -/
def tableInj (a b : Plan p n) (M : Cross p n) :=
  ∀ (z : Place p) (i j : Bool) (v : Ray p n), (IP p n i)*ᵥv ∈ a z →
    channelOut p M j z *ᵥ (IP p n i *ᵥ v) ∈ hPin b z j → v=0

/-- Contraction on x, computed in full table coordinates; at the small
table only its restriction to C_i is initially meaningful. -/
def contract (p : Shape) {n} (M : Cross p n) (i j : Bool) :
    Profile p n →ₗ[F] F where
  toFun x := ∑ e : Comp p.g, mpair
    ((channelOut p M j (e,true))ᵀ * channelOut p M j (e,false))
    (liftM (IP p n i) (IP p n i) (x e))
  map_add' x y := by simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]
  map_smul' a x := by simp only [Pi.smul_apply,map_smul,RingHom.id_apply,
    smul_eq_mul, Finset.mul_sum]

theorem contract_actual (x y : UnitType p n N) (i j : Bool) :
    contract p (actual p x y) i j = (ufun (onSide y j)) ∘ₗ (Uembed (onSide x i)) := by
  let A := onSide x i
  let B := onSide y j
  have he (z : Place p) : actual p x y z * IH p n j = (images x z)ᵀ *
      channel (takeSign (B z.1) !z.2) := by rw [actual,Matrix.mul_assoc,images_ih]; rfl
  apply LinearMap.ext
  intro w
  change ∑ e : Comp p.g, _ = ∑ e : Comp p.g, _
  refine Finset.sum_congr rfl fun e _ => ?_

  let P := images x (e,true)
  let Q := images x (e,false)
  let Y := channel (B e).2
  let X := channel (B e).1
  have hm : (channelOut p (actual p x y) j (e,true))ᵀ * channelOut p (actual p x y) j (e,false) =
      liftM Pᵀ Qᵀ (Y*Xᵀ) := by
    unfold channelOut
    rw [he,he]
    simp only [transpose_mul,transpose_transpose,liftM_def]
    change (Pᵀ * Y)*(Xᵀ*Q)=_
    simp only [Matrix.mul_assoc]
  change mpair _ _ = mpair (Y*Xᵀ) (liftM (primary (A e).1) (primary (A e).2) (w e))
  rw [hm, ← mpair_liftM P Q,liftM_comp]
  have hP : P * IP p n i = primary (A e).1 := images_ip x (e,true) _
  have hQ : Q * IP p n i = primary (A e).2 := images_ip x (e,false) _
  rw [hP,hQ]

def innerP (p : Shape) {n N} (x : UnitType p n N) (i : Bool) :=
  ufun (onSide x (!i)) ∘ₗ Uembed (onSide x i)

end HadwigerCounterexample

end

end OAI
