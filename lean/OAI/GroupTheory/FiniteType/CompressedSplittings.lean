import Mathlib
import OAI.GroupTheory.FiniteType.RingExchange

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace CompressedSplittings
section
variable {R : Type*} [Ring R] (φ : R →ₙ+* R)

structure Idempotent where
  val : R
  idem : val*val=val
  commute : ∀ x, Commute val (φ x)

namespace Idempotent
@[ext] lemma ext {E F : Idempotent φ} (h : E.val=F.val) : E=F := by
  cases E; cases F; cases h; rfl

variable {φ}

def coefficient (E : Idempotent φ) : R →ₙ+* R where
  toFun x := φ x*E.val
  map_zero' := by simp
  map_add' x y := by simp [add_mul]
  map_mul' x y := by
    change φ (x*y)*E.val=(φ x*E.val)*(φ y*E.val)
    rw [map_mul,mul_assoc,mul_assoc,← mul_assoc E.val (φ y),E.commute y |>.eq,
      mul_assoc (φ y), E.idem]

def units (E : Idempotent φ) : Rˣ →* Rˣ := NonunitalCompression.units E.coefficient

@[simp] lemma units_val (E : Idempotent φ) (u : Rˣ) :
    (E.units u).val=1+φ (u.val-1)*E.val := rfl

lemma units_mul (E F Q : Idempotent φ) (hQ : Q.val=E.val+F.val)
    (hEF : E.val*F.val=0) (u : Rˣ) : Q.units u=E.units u*F.units u := by
  apply Units.ext
  have hc : (φ (u.val-1)*E.val)*(φ (u.val-1)*F.val)=0 := by
    rw [mul_assoc,← mul_assoc E.val, E.commute (u.val-1) |>.eq,
      mul_assoc (φ (u.val-1)),hEF,mul_zero,mul_zero]
  simp only [Units.val_mul,units_val,hQ,mul_add]
  simp only [add_mul,one_mul,mul_one,hc,add_zero]
  abel

lemma units_conjugate (E F : Idempotent φ) (c : Rˣ)
    (hc : ∀ x, Commute c.val (φ x)) (hEF : c.val*E.val*c.inv=F.val) (u : Rˣ) :
    c*E.units u*c⁻¹=F.units u := by
  apply Units.ext
  change c.val*(1+φ (u.val-1)*E.val)*c.inv=1+φ (u.val-1)*F.val
  have he : c.val*(φ (u.val-1)*E.val)*c.inv=φ (u.val-1)*(c.val*E.val*c.inv) := by
    rw [← mul_assoc c.val (φ (u.val-1)),hc (u.val-1) |>.eq]
    simp [mul_assoc]
  rw [mul_add,mul_one,add_mul,c.val_inv,he,hEF]

end Idempotent

def full : Idempotent φ where
  val := φ 1
  idem := by rw [← map_mul,one_mul]
  commute x := by change φ 1*φ x=φ x*φ 1; rw [← map_mul,← map_mul,one_mul,mul_one]

lemma full_units (u : Rˣ) : (full φ).units u=NonunitalCompression.units φ u := by
  apply Units.ext
  change 1+φ (u.val-1)*φ 1=1+φ (u.val-1)
  rw [← map_mul,mul_one]

theorem swindle {A : Type*} [Group A] (q : Rˣ →* A)
    (hq : ∀ u v : Rˣ, q (u*v*u⁻¹)=q v)
    (P E₀ E₁ E₀₀ E₀₁ : Idempotent φ)
    (hsplit : P.val=E₀.val+E₁.val) (hsubsplit : E₀.val=E₀₀.val+E₀₁.val)
    (hcross : E₀.val*E₁.val=0) (hsubcross : E₀₀.val*E₀₁.val=0)
    (c₀ c₀₀ c₀₁ : Rˣ)
    (hc₀ : ∀ x, Commute c₀.val (φ x))
    (hc₀₀ : ∀ x, Commute c₀₀.val (φ x))
    (hc₀₁ : ∀ x, Commute c₀₁.val (φ x))
    (hconj₀ : c₀.val*E₀.val*c₀.inv=E₁.val)
    (hconj₀₀ : c₀₀.val*E₀₀.val*c₀₀.inv=E₁.val)
    (hconj₀₁ : c₀₁.val*E₀₁.val*c₀₁.inv=E₁.val) (u : Rˣ) : q (P.units u)=1 := by
  have h₀ : q (E₀.units u)=q (E₁.units u) := by
    rw [← E₀.units_conjugate E₁ c₀ hc₀ hconj₀ u,hq]
  have h₀₀ : q (E₀₀.units u)=q (E₁.units u) := by
    rw [← E₀₀.units_conjugate E₁ c₀₀ hc₀₀ hconj₀₀ u,hq]
  have h₀₁ : q (E₀₁.units u)=q (E₁.units u) := by
    rw [← E₀₁.units_conjugate E₁ c₀₁ hc₀₁ hconj₀₁ u,hq]
  have heq : q (E₁.units u)=q (E₁.units u)*q (E₁.units u) := by
    calc q (E₁.units u)=q (E₀.units u) := h₀.symm
         _ = q (E₀₀.units u)*q (E₀₁.units u) := by
           rw [Idempotent.units_mul E₀₀ E₀₁ E₀ hsubsplit hsubcross,map_mul]
         _ = _ := by rw [h₀₀,h₀₁]
  have h₁ : q (E₁.units u)=1 := mul_left_cancel (heq.symm.trans (mul_one _).symm)
  rw [Idempotent.units_mul E₀ E₁ P hsplit hcross,map_mul,h₀,h₁,one_mul]

end

variable {R : Type*} [Ring R] (φ : R →ₙ+* R)

namespace BinaryData
variable {φ} (D : BinaryData φ)
@[simp] lemma ds_same (i : Fin 2) : D.d i*D.s i=φ 1 := by simp [D.ds]
lemma ds_cross (i j : Fin 2) (h : i≠j) : D.d i*D.s j=0 := by simp [D.ds,h]

def projection (i : Fin 2) : Idempotent φ where
  val := D.s i*D.d i
  idem := by rw [mul_assoc,← mul_assoc (D.d i),D.ds_same,D.d_left]
  commute x := (D.s_commute i x).mul_left (D.d_commute i x)

lemma dd_ss (i j : Fin 2) : (D.d j*D.d i)*(D.s i*D.s j)=φ 1 := by
  rw [mul_assoc,← mul_assoc (D.d i),D.ds_same,← mul_assoc,D.d_right,D.ds_same]

def doubleProjection (i j : Fin 2) : Idempotent φ where
  val := (D.s i*D.s j)*(D.d j*D.d i)
  idem := by
    rw [mul_assoc,← mul_assoc (D.d j*D.d i),D.dd_ss,
      ← mul_assoc (φ 1),D.d_left]
  commute x := ((D.s_commute i x).mul_left (D.s_commute j x)).mul_left
    ((D.d_commute j x).mul_left (D.d_commute i x))

lemma split : (full φ).val=(D.projection 0).val+(D.projection 1).val := D.partition.symm

lemma subsplit : (D.projection 0).val=(D.doubleProjection 0 0).val+(D.doubleProjection 0 1).val := by
  change D.s 0*D.d 0=(D.s 0*D.s 0)*(D.d 0*D.d 0)+(D.s 0*D.s 1)*(D.d 1*D.d 0)
  calc D.s 0*D.d 0=D.s 0*φ 1*D.d 0 := by rw [D.s_right]
       _ = D.s 0*(D.s 0*D.d 0+D.s 1*D.d 1)*D.d 0 := by rw [D.partition]
       _ = _ := by noncomm_ring

lemma cross : (D.projection 0).val*(D.projection 1).val=0 := by
  change (D.s 0*D.d 0)*(D.s 1*D.d 1)=0
  rw [mul_assoc,← mul_assoc (D.d 0),D.ds_cross 0 1 (by decide),zero_mul,mul_zero]

lemma subcross : (D.doubleProjection 0 0).val*(D.doubleProjection 0 1).val=0 := by
  have hd : (D.d 0*D.d 0)*(D.s 0*D.s 1)=0 := by
    calc (D.d 0*D.d 0)*(D.s 0*D.s 1)
        = D.d 0*(D.d 0*D.s 0)*D.s 1 := by simp only [mul_assoc]
      _ = 0 := by rw [D.ds_same,D.d_right,D.ds_cross 0 1 (by decide)]
  change ((D.s 0*D.s 0)*(D.d 0*D.d 0))*((D.s 0*D.s 1)*(D.d 1*D.d 0))=0
  rw [mul_assoc,← mul_assoc (D.d 0*D.d 0),hd,zero_mul,mul_zero]

def firstExchange : RingExchange.Data R :=
  RingExchange.ofPairs (φ 1) (D.s 0) (D.d 0) (D.s 1) (D.d 1)
    (D.d_left 0) (D.d_left 1) (D.ds_same 0) (D.ds_same 1)
    (D.ds_cross 0 1 (by decide)) (D.ds_cross 1 0 (by decide))

def secondExchange (j : Fin 2) : RingExchange.Data R :=
  RingExchange.ofPairs (φ 1) (D.s 0*D.s j) (D.d j*D.d 0) (D.s 1) (D.d 1)
    (by rw [← mul_assoc,D.d_left]) (D.d_left 1) (D.dd_ss 0 j) (D.ds_same 1)
    (by rw [mul_assoc,D.ds_cross 0 1 (by decide),mul_zero])
    (by rw [← mul_assoc,D.ds_cross 1 0 (by decide),zero_mul])

lemma firstExchange_commutes (x : R) : Commute D.firstExchange.unit.val (φ x) := by
  apply RingExchange.Data.commutes
  · exact (D.s_commute 0 x).mul_left (D.d_commute 0 x)
  · exact (D.s_commute 1 x).mul_left (D.d_commute 1 x)
  · exact (D.s_commute 1 x).mul_left (D.d_commute 0 x)
  · exact (D.s_commute 0 x).mul_left (D.d_commute 1 x)

lemma secondExchange_commutes (i : Fin 2) (x : R) :
    Commute (D.secondExchange i).unit.val (φ x) := by
  apply RingExchange.Data.commutes
  · exact ((D.s_commute 0 x).mul_left (D.s_commute i x)).mul_left
      ((D.d_commute i x).mul_left (D.d_commute 0 x))
  · exact (D.s_commute 1 x).mul_left (D.d_commute 1 x)
  · exact (D.s_commute 1 x).mul_left ((D.d_commute i x).mul_left (D.d_commute 0 x))
  · exact ((D.s_commute 0 x).mul_left (D.s_commute i x)).mul_left (D.d_commute 1 x)

theorem annihilates (D : BinaryData φ) {A : Type*} [Group A] (q : Rˣ →* A)
    (hq : ∀ u v : Rˣ, q (u*v*u⁻¹)=q v) (u : Rˣ) :
    q (NonunitalCompression.units φ u)=1 := by
  rw [← full_units]
  exact swindle φ q hq (full φ) (D.projection 0) (D.projection 1)
    (D.doubleProjection 0 0) (D.doubleProjection 0 1) D.split D.subsplit D.cross D.subcross
    D.firstExchange.unit (D.secondExchange 0).unit (D.secondExchange 1).unit
    D.firstExchange_commutes (D.secondExchange_commutes 0) (D.secondExchange_commutes 1)
    D.firstExchange.conjugates (D.secondExchange 0).conjugates (D.secondExchange 1).conjugates u

end BinaryData
end CompressedSplittings

namespace CompressedSplittings.Idempotent
variable {R : Type*} [Ring R] {φ : R →ₙ+* R}

lemma coefficient_left (E : Idempotent φ) (a : R) :
    E.val*E.coefficient a=E.coefficient a := by
  change E.val*(φ a*E.val)=φ a*E.val
  rw [← mul_assoc,E.commute a |>.eq,mul_assoc,E.idem]

lemma coefficient_right (E : Idempotent φ) (a : R) :
    E.coefficient a*E.val=E.coefficient a := by
  change (φ a*E.val)*E.val=φ a*E.val
  rw [mul_assoc,E.idem]

lemma coefficient_orthogonal (E F : Idempotent φ) (hEF : E.val*F.val=0) (a b : R) :
    E.coefficient a * F.coefficient b=0 := by
  change (φ a*E.val)*(φ b*F.val)=0
  rw [mul_assoc,← mul_assoc E.val,E.commute b |>.eq,mul_assoc (φ b),hEF,mul_zero,mul_zero]

lemma coefficient_conjugate (E F : Idempotent φ) (u : Rˣ)
    (hc : ∀ x, Commute u.val (φ x)) (hEF : u.val*E.val*u.inv=F.val) (a : R) :
    F.coefficient a=u.val*E.coefficient a*u.inv := by
  change φ a*F.val=u.val*(φ a*E.val)*u.inv
  rw [← mul_assoc u.val (φ a),hc a |>.eq]
  simp only [mul_assoc,← hEF]

lemma steinberg_split {n : Type*} (hthree : ∀ i j : n, i≠j → ∃ k, i≠k ∧ j≠k)
    (P E F : Idempotent φ) (hP : P.val=E.val+F.val)
    (hEF : E.val*F.val=0) (hFE : F.val*E.val=0) (w : Steinberg.Group n R) :
    Steinberg.map P.coefficient w=Steinberg.map E.coefficient w*Steinberg.map F.coefficient w := by
  have he : P.coefficient = Steinberg.orthogonalSum E.coefficient F.coefficient
      (E.coefficient_orthogonal F hEF) (F.coefficient_orthogonal E hFE) := by
    ext a
    change φ a*P.val=φ a*E.val+φ a*F.val
    rw [hP,mul_add]
  rw [he,Steinberg.map_orthogonalSum hthree]

end CompressedSplittings.Idempotent

end

end OAI
