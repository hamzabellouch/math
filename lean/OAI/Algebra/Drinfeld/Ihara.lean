import OAI.Algebra.Drinfeld.Reduction

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section
namespace WordGrading
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]

theorem homogeneous_lie {wt : α → ℕ} {r s : ℕ} {p q : A R α}
    (hp : p∈homogeneous wt r) (hq : q∈homogeneous wt s) : ⁅p,q⁆∈homogeneous wt (r+s) := by
  change p*q-q*p∈_
  exact (homogeneous wt _).sub_mem (homogeneous_mul hp hq) (by simpa only [Nat.add_comm] using homogeneous_mul hq hp)

theorem above_lie {wt : α → ℕ} {r s : ℕ} {p q : A R α}
    (hp : p∈above wt r) (hq : q∈above wt s) : ⁅p,q⁆∈above wt (r+s) := by
  change p*q-q*p∈_
  exact (above wt _).sub_mem (above_mul hp hq) (by simpa only [Nat.add_comm] using above_mul hq hp)

theorem piece_of_difference_high {wt : α → ℕ} {n : ℕ} {p q : A R α}
    (hq : q∈homogeneous wt n) (hd : p-q∈above wt (n+1)) : piece wt n p=q := by
  have h := piece_zero_of_above hd (Nat.lt_succ_self n)
  rw [map_sub,piece_homogeneous hq,ite_eq_left rfl] at h
  exact sub_eq_zero.mp h

theorem leading_lie {wt : α → ℕ} {r s : ℕ} {p q : A R α}
    (hp : p∈above wt r) (hq : q∈above wt s) :
    piece wt (r+s) ⁅p,q⁆=⁅piece wt r p,piece wt s q⁆ := by
  apply piece_of_difference_high (homogeneous_lie (piece_mem wt r p) (piece_mem wt s q))
  have h1 := above_lie (subtract_piece_above hp) hq
  have h2 := above_lie (homogeneous_above (piece_mem wt r p)) (subtract_piece_above hq)
  have he : ⁅p,q⁆-⁅piece wt r p,piece wt s q⁆=⁅p-piece wt r p,q⁆+⁅piece wt r p,q-piece wt s q⁆ := by
    simp only [sub_lie,lie_sub]; abel
  rw [he]
  exact (above wt (r+s+1)).add_mem (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1)
    (by simpa only [Nat.add_assoc] using h2)

theorem leading_deriv {wt : α → ℕ} {c n : ℕ} {f g : α → A R α}
    (hf : ∀ a,f a∈above wt (wt a+c)) (hg : ∀ a,g a∈homogeneous wt (wt a+c))
    (hd : ∀ a,f a-g a∈above wt (wt a+c+1)) {p : A R α} (hp : p∈above wt n) :
    piece wt (n+c) (deriv f p)=deriv g (piece wt n p) := by
  apply piece_of_difference_high (deriv_homogeneous hg (piece_mem wt n p))
  have h1 := deriv_above hf (subtract_piece_above hp)
  have h2 := deriv_above (c:=c+1) (f:=fun a => f a-g a)
    (by intro a; simpa only [Nat.add_assoc] using hd a) (homogeneous_above (piece_mem wt n p))
  rw [deriv_sub] at h2
  have he : deriv f p-deriv g (piece wt n p)=deriv f (p-piece wt n p)+
      (deriv f (piece wt n p)-deriv g (piece wt n p)) := by rw [map_sub]; abel
  rw [he]
  exact (above wt (n+c+1)).add_mem (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1)
    (by simpa only [Nat.add_assoc] using h2)

end WordGrading
namespace IharaLeading
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open RowTwo RowKernel ExactPentagon ResidualKernel
attribute [local instance] LieRing.ofAssociativeRing
abbrev K := ZMod 2
local notation "S" => A K Slot
local notation "B" => (atom Slot.B : S)
local notation "C" => (atom Slot.C : S)

def action (p : S) : Slot → S
  | .A => 0 | .B => ⁅B,p⁆ | .C => ⁅C,p⁆+⁅B,deriv delta p⁆
def lowAction (q : S) : Slot → S
  | .A => 0 | .B => ⁅B,q⁆ | .C => ⁅C,q⁆+⁅B,deriv low q⁆

theorem delta_above {p : S} {r : ℕ} (hp : p∈above bCount r) : deriv delta p∈above bCount (r-1) := by
  rw [delta_split]
  apply (above bCount (r-1)).add_mem
  · exact deriv_lowers_above bCount 1 low low_degree hp
  · exact space_mono (by intro w hw; omega) (deriv_above (fun a => homogeneous_above (high_degree a)) hp)

theorem action_above {p : S} {r : ℕ} (hr : 0<r) (hp : p∈above bCount r) (a : Slot) :
    action p a∈above bCount (bCount a+r) := by
  have hb : B∈above bCount 1 := homogeneous_above (word_mem (FreeMonoid.of Slot.B) rfl)
  have hc : C∈above bCount 0 := homogeneous_above (word_mem (FreeMonoid.of Slot.C) rfl)
  cases a with
  | A => exact Submodule.zero_mem _
  | «B» => exact above_lie hb hp
  | «C» =>
    apply (above bCount (0+r)).add_mem (above_lie hc hp)
    convert above_lie hb (delta_above hp) using 1
    congr 1
    omega

theorem lowAction_homogeneous {q : S} {r : ℕ} (hr : 0<r)
    (hq : q∈homogeneous bCount r) (a : Slot) : lowAction q a∈homogeneous bCount (bCount a+r) := by
  have hb : B∈homogeneous bCount 1 := word_mem (FreeMonoid.of Slot.B) rfl
  have hc : C∈homogeneous bCount 0 := word_mem (FreeMonoid.of Slot.C) rfl
  cases a with
  | A => exact Submodule.zero_mem _
  | «B» => exact homogeneous_lie hb hq
  | «C» =>
    apply (homogeneous bCount (0+r)).add_mem (homogeneous_lie hc hq)
    convert homogeneous_lie hb (lower_homogeneous (deriv_lower bCount 1 low low_degree hq)) using 1
    congr 1
    omega

theorem delta_low_difference {p q : S} {r : ℕ} (hp : p∈above bCount r)
    (hd : p-q∈above bCount (r+1)) : deriv delta p-deriv low q∈above bCount r := by
  have hl := deriv_lowers_above bCount 1 low low_degree hd
  have hh := deriv_above (fun a => homogeneous_above (high_degree a)) hp
  rw [delta_split]
  have he : deriv low p+deriv high p-deriv low q=deriv low (p-q)+deriv high p := by rw [map_sub]; abel
  rw [he]
  exact (above bCount r).add_mem (by simpa using hl) (space_mono (by intro w hw; omega) hh)

theorem action_difference {p q : S} {r : ℕ} (hp : p∈above bCount r)
    (hd : p-q∈above bCount (r+1)) (a : Slot) : action p a-lowAction q a∈above bCount (bCount a+r+1) := by
  have hb : B∈above bCount 1 := homogeneous_above (word_mem (FreeMonoid.of Slot.B) rfl)
  have hc : C∈above bCount 0 := homogeneous_above (word_mem (FreeMonoid.of Slot.C) rfl)
  cases a with
  | A => simp only [action,lowAction,sub_self]; exact Submodule.zero_mem _
  | «B» =>
    change ⁅B,p⁆-⁅B,q⁆∈_
    rw [←lie_sub]
    simpa only [Nat.add_assoc,bCount,ite_true] using above_lie hb hd
  | «C» =>
    have he : action p Slot.C-lowAction q Slot.C=⁅C,p-q⁆+⁅B,deriv delta p-deriv low q⁆ := by
      simp only [action,lowAction,lie_sub]; abel
    rw [he]
    exact (above bCount (0+r+1)).add_mem (by simpa only [Nat.add_assoc] using above_lie hc hd)
      (by simpa only [Nat.add_comm,Nat.zero_add] using above_lie hb (delta_low_difference hp hd))

theorem leading_action {p q : S} {r s : ℕ} (hr : 0<r)
    (hp : p∈above bCount r) (hq : q∈above bCount s) :
    piece bCount (r+s) (deriv (action p) q)=deriv (lowAction (piece bCount r p)) (piece bCount s q) := by
  rw [Nat.add_comm r s]
  exact leading_deriv (action_above hr hp) (lowAction_homogeneous hr (piece_mem bCount r p))
    (action_difference hp (subtract_piece_above hp)) hq

end IharaLeading

namespace AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α β : Type*} [CommRing R]

theorem deriv_naturality (F : A R α →ₐ[R] A R β) (f : α → A R α) (g : β → A R β)
    (h : ∀ a,F (f a)=deriv g (F (atom a))) (p : A R α) : F (deriv f p)=deriv g (F p) := by
  induction p using QuadraticAlphabet.algebra_induction with
  | h1 => simp
  | ha a => rw [deriv_atom,h a]
  | hadd p q hp hq => simp only [map_add,hp,hq]
  | hs c p hp => simp only [map_smul,hp]
  | hm p q hp hq => rw [deriv_mul,map_add,map_mul,map_mul,hp,hq,map_mul,deriv_mul]

theorem deriv_inner_right (p q : A R α) : deriv (fun a => ⁅(atom a : A R α),p⁆) q=⁅q,p⁆ := by
  induction q using QuadraticAlphabet.algebra_induction with
  | h1 => simp [Ring.lie_def]
  | ha a => exact deriv_atom _ _
  | hadd q r hq hr => simp only [map_add,add_lie,hq,hr]
  | hs c q hq => simp only [map_smul,smul_lie,hq]
  | hm q r hq hr => rw [deriv_mul,hq,hr]; simp only [Ring.lie_def]; noncomm_ring

end AssociativeElimination
namespace IharaLeading
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open RowTwo RowKernel ExactPentagon ResidualKernel
attribute [local instance] LieRing.ofAssociativeRing
local notation "S" => A K Slot
local notation "E" => (OreShift.eraseShift (0 : A K Bool))

theorem erase_low (p : S) : E (deriv low p)=OreShift.D (E p) := by
  apply deriv_naturality E low (fun b => if b then OreShift.C else 0) ?_
  intro a
  cases a <;> simp [low,OreShift.eraseShift,OreShift.C,OreShift.B]

theorem erase_lowAction_inner {p : S} (hp : OreShift.D (E p)=0) (q : S) :
    E (deriv (lowAction p) q)=⁅E q,E p⁆ := by
  rw [←deriv_inner_right]
  apply deriv_naturality E (lowAction p) (fun b => ⁅atom b,E p⁆) ?_
  intro a
  cases a with
  | A => simp [lowAction,OreShift.eraseShift]
  | C =>
    change E (⁅(atom Slot.C : S),p⁆+⁅(atom Slot.B : S),deriv low p⁆)=_
    rw [map_add,EvenIndex.map_lie,EvenIndex.map_lie,erase_low,hp,lie_zero,add_zero]
    simp [OreShift.eraseShift,OreShift.C]
  | B =>
    change E ⁅(atom Slot.B : S),p⁆=_
    rw [EvenIndex.map_lie]
    simp [OreShift.eraseShift,OreShift.B]

def ihara (p q : S) : S := deriv (action p) q-deriv (action q) p+⁅p,q⁆

theorem ihara_above {p q : S} {r s : ℕ} (hr : 0<r) (hs : 0<s)
    (hp : p∈above bCount r) (hq : q∈above bCount s) : ihara p q∈above bCount (r+s) := by
  apply (above bCount (r+s)).add_mem
  · apply (above bCount (r+s)).sub_mem
    · simpa only [Nat.add_comm] using deriv_above (action_above hr hp) hq
    · exact deriv_above (action_above hs hq) hp
  · exact above_lie hp hq

theorem leading_ihara {p q : S} {r s : ℕ} (hr : 0<r) (hs : 0<s)
    (hp : p∈above bCount r) (hq : q∈above bCount s)
    (hDp : OreShift.D (E (piece bCount r p))=0) (hDq : OreShift.D (E (piece bCount s q))=0) :
    E (piece bCount (r+s) (ihara p q))=⁅E (piece bCount r p),E (piece bCount s q)⁆ := by
  simp only [ihara,map_add,map_sub]
  rw [leading_action hr hp hq,show r+s=s+r from Nat.add_comm r s,leading_action hs hq hp]
  rw [show s+r=r+s from Nat.add_comm s r,leading_lie hp hq]
  rw [erase_lowAction_inner hDp,erase_lowAction_inner hDq,EvenIndex.map_lie]
  rw [sub_add_cancel,←lie_skew]
  exact TwoModule.neg_eq _

theorem actual_leading_ihara {ψ φ : FreeLieAlgebra K Bool} {p q : FreeLieAlgebra K Slot} {n m r s : ℕ}
    (hn : 1<n) (hm : 1 < m) (hψ : embed ψ∈homogeneous (fun _ => 1) n)
    (hφ : embed φ∈homogeneous (fun _ => 1) m)
    (hp : under p=embed ψ) (hq : under q=embed φ)
    (hψa : BaseChangeEquations.antisymmetry ψ=0) (hφa : BaseChangeEquations.antisymmetry φ=0)
    (hr : 0<r) (hs : 0<s) (hpr : embed p∈above bCount r) (hqs : embed q∈above bCount s) :
    ihara (embed p) (embed q)∈above bCount (r+s) ∧
    E (piece bCount (r+s) (ihara (embed p) (embed q)))=⁅embed (ImageBound.leading r p),embed (ImageBound.leading s q)⁆ := by
  refine ⟨ihara_above hr hs hpr hqs,?_⟩
  simp only [ImageBound.embed_leading]
  have hDp := ImageBound.leading_D_zero hn hψ hp hψa hpr
  have hDq := ImageBound.leading_D_zero hm hφ hq hφa hqs
  rw [ImageBound.embed_leading] at hDp hDq
  exact leading_ihara hr hs hpr hqs hDp hDq

end IharaLeading

namespace GenericIhara
open AssociativeElimination UniversalEmbedding
attribute [local instance] LieRing.ofAssociativeRing
variable {R : Type*} [CommRing R]

def D (p : FreeLieAlgebra R Bool) : LieDerivation R (FreeLieAlgebra R Bool) (FreeLieAlgebra R Bool) :=
  FreeDerivations.extend (fun b => if b then ⁅FreeLieAlgebra.of R true,p⁆ else 0)
def ihara (p q : FreeLieAlgebra R Bool) := D p q-D q p+⁅p,q⁆
def assocD (p : A R Bool) : A R Bool →ₗ[R] A R Bool :=
  deriv (fun b => if b then ⁅(atom true : A R Bool),p⁆ else 0)
def assocIhara (p q : A R Bool) := assocD p q-assocD q p+⁅p,q⁆

theorem embed_D (p q : FreeLieAlgebra R Bool) : embed (D p q)=assocD (embed p) (embed q) := by
  rw [←AssociativeDerivations.extend_embed]
  congr 1
  unfold AssociativeDerivations.extend assocD
  congr 1
  funext b
  cases b <;> simp [D]

theorem embed_ihara (p q : FreeLieAlgebra R Bool) : embed (ihara p q)=assocIhara (embed p) (embed q) := by
  simp only [ihara,assocIhara,map_add,map_sub,LieHom.map_lie,embed_D]

theorem rational_D (p q : L) : D p q=DeligneDrinfeld.D p q := by
  have h : D p=derivation p := by
    apply derivation_ext
    · change D p x=DeligneDrinfeld.D p x
      rw [D_x]
      simp [D,x]
    · change D p y=DeligneDrinfeld.D p y
      rw [D_y]
      simp [D,y]
  exact LieDerivation.congr_fun h q

theorem rational_ihara (p q : L) : ihara p q=DeligneDrinfeld.ihara p q := by
  simp only [ihara,DeligneDrinfeld.ihara,rational_D]

end GenericIhara
namespace IharaLeading
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open RowTwo RowKernel ExactPentagon ResidualKernel
attribute [local instance] LieRing.ofAssociativeRing
local notation "S" => A K Slot
local notation "Q" => A K Bool

theorem quad_action (p q : S) : quad (deriv (action p) q)=GenericIhara.assocD (quad p) (quad q) := by
  apply deriv_naturality quad (action p) (fun b => if b then ⁅(atom true : Q),quad p⁆ else 0) ?_
  intro a
  cases a with
  | A =>
    simp only [action,map_zero,quad,lift_atom,AssociativeElimination.deriv_mul,deriv_atom,
      Bool.false_eq_true,ite_false,zero_mul,mul_zero,add_zero]
  | C =>
    simp only [action,map_add,EvenIndex.map_lie,quad_delta]
    simp only [quad,lift_atom,map_sub,AssociativeElimination.deriv_mul,deriv_atom,
      ite_true,Bool.false_eq_true,ite_false,Ring.lie_def,zero_mul,mul_zero,zero_add,add_zero]
    noncomm_ring
  | B => simp [action,quad,EvenIndex.map_lie]

theorem quad_ihara (p q : S) : quad (ihara p q)=GenericIhara.assocIhara (quad p) (quad q) := by
  simp only [ihara,GenericIhara.assocIhara,map_add,map_sub,EvenIndex.map_lie,quad_action]

def deltaLie : LieDerivation K (FreeLieAlgebra K Slot) (FreeLieAlgebra K Slot) :=
  FreeDerivations.extend (fun (a : Slot) => match a with
    | .A => 0 | .B => FreeLieAlgebra.of K Slot.C
    | .C => ⁅FreeLieAlgebra.of K Slot.A,FreeLieAlgebra.of K Slot.B⁆)

theorem embed_deltaLie (p : FreeLieAlgebra K Slot) : embed (deltaLie p)=deriv delta (embed p) := by
  have h : (fun a => embed (deltaLie (FreeLieAlgebra.of K a)))=delta := by
    funext a
    cases a <;> simp [deltaLie,delta,low,high,Ring.lie_def]
  rw [←AssociativeDerivations.extend_embed]
  change deriv (fun a => embed (deltaLie (FreeLieAlgebra.of K a))) (embed p)=_
  rw [h]

def actionLie (p : FreeLieAlgebra K Slot) : LieDerivation K (FreeLieAlgebra K Slot) (FreeLieAlgebra K Slot) :=
  FreeDerivations.extend (fun (a : Slot) => match a with
    | .A => 0 | .B => ⁅FreeLieAlgebra.of K Slot.B,p⁆
    | .C => ⁅FreeLieAlgebra.of K Slot.C,p⁆+⁅FreeLieAlgebra.of K Slot.B,deltaLie p⁆)

theorem embed_actionLie (p q : FreeLieAlgebra K Slot) :
    embed (actionLie p q)=deriv (action (embed p)) (embed q) := by
  have h : (fun a => embed (actionLie p (FreeLieAlgebra.of K a)))=action (embed p) := by
    funext a
    cases a <;> simp [actionLie,action,embed_deltaLie]
  rw [←AssociativeDerivations.extend_embed]
  change deriv (fun a => embed (actionLie p (FreeLieAlgebra.of K a))) (embed q)=_
  rw [h]

def iharaLie (p q : FreeLieAlgebra K Slot) := actionLie p q-actionLie q p+⁅p,q⁆

theorem embed_iharaLie (p q : FreeLieAlgebra K Slot) : embed (iharaLie p q)=ihara (embed p) (embed q) := by
  simp only [iharaLie,ihara,map_add,map_sub,LieHom.map_lie,embed_actionLie]

theorem actual_ihara_representation {ψ φ : FreeLieAlgebra K Bool} {p q : FreeLieAlgebra K Slot}
    (hp : under p=embed ψ) (hq : under q=embed φ) : under (iharaLie p q)=embed (GenericIhara.ihara ψ φ) := by
  change quad (embed (iharaLie p q))=_
  rw [embed_iharaLie,quad_ihara,GenericIhara.embed_ihara]
  rw [show quad (embed p)=embed ψ from hp,show quad (embed q)=embed φ from hq]

end IharaLeading

namespace GenericIhara

section
open AssociativeElimination UniversalEmbedding WordGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R : Type*} [CommRing R]

def depth : Bool → ℕ := fun b => if b then 1 else 0

theorem assocD_above {p q : A R Bool} {r s : ℕ} (hp : p∈above depth r) (hq : q∈above depth s) :
    assocD p q∈above depth (s+r) := by
  apply deriv_above (c:=r) (f:=fun b => if b then ⁅(atom true : A R Bool),p⁆ else 0) ?_ hq
  intro b
  cases b with
  | false => exact Submodule.zero_mem _
  | true =>
    exact above_lie (homogeneous_above (word_mem (FreeMonoid.of true) (degree_of depth true))) hp

theorem assocIhara_above {p q : A R Bool} {r s : ℕ} (hp : p∈above depth r) (hq : q∈above depth s) :
    assocIhara p q∈above depth (r+s) := by
  apply (above depth (r+s)).add_mem ?_ (above_lie hp hq)
  apply (above depth (r+s)).sub_mem
  · simpa only [Nat.add_comm] using assocD_above hp hq
  · exact assocD_above hq hp

theorem ihara_above {p q : FreeLieAlgebra R Bool} {r s : ℕ}
    (hp : embed p∈above depth r) (hq : embed q∈above depth s) :
    embed (ihara p q)∈above depth (r+s) := by
  rw [embed_ihara]
  exact assocIhara_above hp hq

theorem assocD_homogeneous {wt : Bool → ℕ} {p q : A R Bool} {n m : ℕ}
    (hp : p∈homogeneous wt n) (hq : q∈homogeneous wt m) :
    assocD p q∈homogeneous wt (m+n) := by
  apply deriv_homogeneous (c:=n) (f:=fun b => if b then ⁅(atom true : A R Bool),p⁆ else 0) ?_ hq
  intro b
  cases b with
  | false => exact Submodule.zero_mem _
  | true => exact homogeneous_lie (word_mem (FreeMonoid.of true) (degree_of wt true)) hp

theorem ihara_homogeneous {wt : Bool → ℕ} {p q : FreeLieAlgebra R Bool} {n m : ℕ}
    (hp : embed p∈homogeneous wt n) (hq : embed q∈homogeneous wt m) :
    embed (ihara p q)∈homogeneous wt (n+m) := by
  rw [embed_ihara]
  apply (homogeneous wt (n+m)).add_mem ?_ (homogeneous_lie hp hq)
  apply (homogeneous wt (n+m)).sub_mem
  · simpa only [Nat.add_comm] using assocD_homogeneous hp hq
  · exact assocD_homogeneous hq hp

end

open LieAlgebra
variable {R : Type*} [CommRing R]
local notation "FL" => FreeLieAlgebra R Bool
local notation "Der" => LieDerivation R FL FL

@[simp] theorem D_zero : D (0 : FL)=0 := by
  apply FreeDerivations.ext
  intro b
  cases b <;> simp [D]

@[simp] theorem D_add (p q : FL) : D (p+q)=D p+D q := by
  apply FreeDerivations.ext
  intro b
  cases b <;> simp [D,lie_add]

@[simp] theorem D_smul (c : R) (p : FL) : D (c • p)=c • D p := by
  apply FreeDerivations.ext
  intro b
  cases b <;> simp [D,lie_smul]

def Dlinear : FL →ₗ[R] Der where
  toFun := D
  map_add' := D_add
  map_smul' := D_smul

@[simp] theorem D_of_false (p : FL) : D p (FreeLieAlgebra.of R false)=0 := by simp [D]
@[simp] theorem D_of_true (p : FL) : D p (FreeLieAlgebra.of R true)=⁅FreeLieAlgebra.of R true,p⁆ := by simp [D]

theorem D_ihara (p q : FL) : D (ihara p q)=⁅D p,D q⁆ := by
  apply FreeDerivations.ext
  intro b
  cases b with
  | false => simp
  | true =>
    simp only [D_of_true,LieDerivation.lie_apply,LieDerivation.apply_lie_eq_add]
    simp only [ihara,lie_add,lie_sub]
    rw [leibniz_lie,←lie_skew p ⁅FreeLieAlgebra.of R true,q⁆]
    abel

abbrev Ambient (R : Type*) [CommRing R] :=
  SemiDirectSum (FreeLieAlgebra R Bool) (LieDerivation R (FreeLieAlgebra R Bool) (FreeLieAlgebra R Bool)) LieHom.id

def graph : LieSubalgebra R (Ambient R) where
  carrier := {p | p.right=D p.left}
  zero_mem' := D_zero.symm
  add_mem' := by
    intro p q hp hq
    change p.right+q.right=D (p.left+q.left)
    rw [D_add,hp,hq]
  smul_mem' := by
    intro c p hp
    change c • p.right=D (c • p.left)
    rw [D_smul,hp]
  lie_mem' := by
    intro p q hp hq
    change ⁅p.right,q.right⁆=D (⁅p.left,q.left⁆+p.right q.left-q.right p.left)
    rw [hp,hq,←D_ihara]
    congr 1
    unfold ihara
    abel

abbrev Algebra (R : Type*) [CommRing R] := graph (R:=R)

def erase : Algebra R ≃ₗ[R] FL where
  toFun p := p.val.left
  invFun p := ⟨⟨p,D p⟩,rfl⟩
  left_inv p := by
    apply Subtype.ext
    change (⟨p.val.left,D p.val.left⟩ : Ambient R)=p.val
    apply SemiDirectSum.ext
    · rfl
    · exact p.property.symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem erase_lie (p q : Algebra R) : erase ⁅p,q⁆=ihara (erase p) (erase q) := by
  change ⁅p.val.left,q.val.left⁆+p.val.right q.val.left-q.val.right p.val.left=_
  rw [p.property,q.property]
  change ⁅p.val.left,q.val.left⁆+D p.val.left q.val.left-D q.val.left p.val.left =
    D p.val.left q.val.left-D q.val.left p.val.left+⁅p.val.left,q.val.left⁆
  abel

variable {α : Type*}

def lift (f : α → FL) : FreeLieAlgebra R α →ₗ⁅R⁆ Algebra R :=
  FreeLieAlgebra.lift R (fun a => erase.symm (f a))

def evalIhara (f : α → FL) : FreeLieAlgebra R α →ₗ[R] FL := erase.toLinearMap.comp (lift f).toLinearMap

@[simp] theorem evalIhara_of (f : α → FL) (a : α) : evalIhara f (FreeLieAlgebra.of R a)=f a := by
  simp [evalIhara,lift]

theorem evalIhara_lie (f : α → FL) (p q : FreeLieAlgebra R α) :
    evalIhara f ⁅p,q⁆=ihara (evalIhara f p) (evalIhara f q) := by
  change erase (lift f ⁅p,q⁆)=_
  rw [LieHom.map_lie,erase_lie]
  rfl

end GenericIhara

namespace LatticeDimension
open scoped TensorProduct
variable {ι : Type*}

def cast : (ι → ℤ) →ₗ[ℤ] (ι → ℚ) where
  toFun u i := u i
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp] theorem cast_apply (u : ι → ℤ) (i : ι) : cast u i=(u i : ℚ) := rfl

def lattice (E : Submodule ℚ (ι → ℚ)) : Submodule ℤ (ι → ℤ) :=
  (E.restrictScalars ℤ).comap cast

@[simp] theorem mem_lattice (E : Submodule ℚ (ι → ℚ)) (u : ι → ℤ) :
    u∈lattice E ↔ cast u∈E := Iff.rfl

theorem saturated (E : Submodule ℚ (ι → ℚ)) {k : ℤ} (hk : k≠0) {u : ι → ℤ}
    (hu : k • u∈lattice E) : u∈lattice E := by
  have h : (k : ℚ) • cast u∈E := by
    change cast (k • u)∈E at hu
    rw [map_smul] at hu
    simpa only [Int.cast_smul_eq_zsmul] using hu
  exact (E.smul_mem_iff (by exact_mod_cast hk)).mp h

instance quotient_torsionFree (E : Submodule ℚ (ι → ℚ)) :
    Module.IsTorsionFree ℤ ((ι → ℤ) ⧸ lattice E) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro k u h
  by_cases hk : k=0
  · exact Or.inl hk
  right
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    apply (Submodule.Quotient.mk_eq_zero (lattice E)).mpr
    apply saturated E hk
    exact (Submodule.Quotient.mk_eq_zero (lattice E)).mp h

variable [Fintype ι]

theorem exists_retraction (E : Submodule ℚ (ι → ℚ)) :
    ∃ p : (ι → ℤ) →ₗ[ℤ] lattice E,p.comp (lattice E).subtype=LinearMap.id := by
  obtain ⟨s,hs⟩ := (lattice E).mkQ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (lattice E).mkQ_surjective)
  let p : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) := LinearMap.id-s.comp (lattice E).mkQ
  have hp (u : ι → ℤ) : p u∈lattice E := by
    apply (Submodule.Quotient.mk_eq_zero (lattice E)).mp
    change (lattice E).mkQ (p u)=0
    dsimp [p]
    have he := LinearMap.congr_fun hs ((lattice E).mkQ u)
    simpa using sub_eq_zero.mpr he.symm
  refine ⟨p.codRestrict (lattice E) hp,?_⟩
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  have hu0 : (lattice E).mkQ u.val=0 := (Submodule.Quotient.mk_eq_zero _).mpr u.property
  change u.val-s ((lattice E).mkQ u.val)=u.val
  rw [hu0,map_zero,sub_zero]

variable (F : Type*) [Field F]

def scalarMap (E : Submodule ℚ (ι → ℚ)) : F ⊗[ℤ] lattice E →ₗ[F] (ι → F) :=
  (TensorProduct.piScalarRightHom ℤ F F ι).comp ((lattice E).subtype.baseChange F)

omit [Fintype ι] in
@[simp] theorem scalarMap_tmul (E : Submodule ℚ (ι → ℚ)) (r : F) (u : lattice E) :
    scalarMap F E (r ⊗ₜ u)=fun i => (u.val i : F)*r := by
  ext i
  simp [scalarMap]

theorem scalarMap_injective (E : Submodule ℚ (ι → ℚ)) : Function.Injective (scalarMap F E) := by
  classical
  obtain ⟨p,hp⟩ := exists_retraction E
  have hleft : (p.baseChange F).comp ((lattice E).subtype.baseChange F)=LinearMap.id := by
    rw [←LinearMap.baseChange_comp,hp,LinearMap.baseChange_id]
  have hi : Function.Injective ((lattice E).subtype.baseChange F) := by
    apply Function.LeftInverse.injective (f:=((lattice E).subtype.baseChange F)) (g:=p.baseChange F)
    intro u
    exact LinearMap.congr_fun hleft u
  exact (TensorProduct.piScalarRight ℤ F F ι).injective.comp hi

def reduction (E : Submodule ℚ (ι → ℚ)) : Submodule F (ι → F) :=
  (scalarMap F E).range

theorem rational_range (E : Submodule ℚ (ι → ℚ)) : reduction ℚ E=E := by
  apply le_antisymm
  · rintro v ⟨u,rfl⟩
    induction u using TensorProduct.inductionOn with

    | tmul r u =>
      have he : scalarMap ℚ E (r ⊗ₜ u)=r • cast u.val := by ext; simp [mul_comm]
      rw [he]
      exact E.smul_mem r u.property
    | add u v hu hv => simpa using E.add_mem hu hv
  · intro v hv
    obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) v
    choose u hu using hd
    have hcast : cast u=(d.val : ℚ) • v := by
      ext i
      simpa using hu i
    have huE : u∈lattice E := by
      rw [mem_lattice,hcast]
      exact E.smul_mem _ hv
    refine ⟨(d.val : ℚ)⁻¹ ⊗ₜ (⟨u,huE⟩ : lattice E),?_⟩
    have hd0 : (d.val : ℚ)≠0 := by exact_mod_cast nonZeroDivisors.ne_zero d.property
    ext i
    rw [scalarMap_tmul]
    have hi := congrFun hcast i
    dsimp at hi ⊢
    rw [hi]
    field_simp

theorem finrank_reduction (E : Submodule ℚ (ι → ℚ)) :
    Module.finrank F (reduction F E)=Module.finrank ℚ E := by
  have hF := (LinearEquiv.ofInjective (scalarMap F E) (scalarMap_injective F E)).finrank_eq
  have hQ := (LinearEquiv.ofInjective (scalarMap ℚ E) (scalarMap_injective ℚ E)).finrank_eq
  rw [Module.finrank_baseChange] at hF hQ
  change _=Module.finrank ℚ (reduction ℚ E) at hQ
  rw [rational_range] at hQ
  exact hF.symm.trans hQ

end LatticeDimension

namespace LieDimension
open AssociativeElimination UniversalEmbedding WordGrading
open scoped TensorProduct
attribute [local instance] LieRing.ofAssociativeRing
variable {α : Type*}
variable (R : Type*) [CommRing R] (wt : α → ℕ) (n : ℕ)

abbrev Words := {w : FreeMonoid α // degree wt w=n}

def toWords : LieGrading.homogeneousLie (R:=R) wt n →ₗ[R] homogeneous (R:=R) wt n :=
  ((embed (R:=R) (α:=α)).toLinearMap.comp (LieGrading.homogeneousLie wt n).subtype).codRestrict
    (homogeneous wt n) (fun p => LieGrading.homogeneousLie_embed p.property)

def coordinates : LieGrading.homogeneousLie (R:=R) wt n →ₗ[R] (Words wt n → R) :=
  (WordCoordinates.coordinates (fun w => degree wt w=n)).comp (toWords R wt n)

@[simp] theorem coordinates_apply (p : LieGrading.homogeneousLie (R:=R) wt n) (w : Words wt n) :
    coordinates R wt n p w=(embed p.val).coeff w.val := rfl

theorem coordinates_injective : Function.Injective (coordinates R wt n) := by
  intro p q h
  have he := WordCoordinates.coordinates_injective (fun w => degree wt w=n) h
  apply Subtype.ext
  apply UniversalEmbedding.injective
  exact congrArg Subtype.val he

def image : Submodule R (Words wt n → R) := (coordinates R wt n).range

variable {R wt n}

theorem words_space {P : FreeMonoid α → Prop} {p : A ℤ α} (hp : p∈space P) :
    IntegralBaseChange.words (S:=R) p∈space P := by
  apply mem_space
  intro w hw
  rw [IntegralBaseChange.words_coeff] at hw
  apply mem_space_iff.mp hp w
  intro h
  exact hw (by rw [h,Int.cast_zero])

theorem words_space_reflect {P : FreeMonoid α → Prop} {p : A ℤ α}
    (hp : IntegralBaseChange.words (S:=ℚ) p∈space P) : p∈space P := by
  apply mem_space
  intro w hw
  apply mem_space_iff.mp hp w
  rw [IntegralBaseChange.words_coeff]
  exact_mod_cast hw

def castHom (p : LieGrading.homogeneousLie (R:=ℤ) wt n) : LieGrading.homogeneousLie (R:=R) wt n :=
  ⟨IntegralBaseChange.lie p.val,LieGrading.homogeneous_iff.mpr (by
    rw [IntegralBaseChange.embed_lie]
    exact words_space (LieGrading.homogeneousLie_embed p.property))⟩

@[simp] theorem coordinates_castHom (p : LieGrading.homogeneousLie (R:=ℤ) wt n) (w : Words wt n) :
    coordinates R wt n (castHom p) w=(coordinates ℤ wt n p w : R) := by
  simp [castHom,IntegralBaseChange.embed_lie]

theorem lattice_image (wt : α → ℕ) (n : ℕ) :
    LatticeDimension.lattice (image ℚ wt n)=image ℤ wt n := by
  apply le_antisymm
  · rintro u ⟨p,hp⟩
    have hpint : embed p.val∈IntegralWords.lattice := by
      apply IntegralWords.integral_of_coeff
      intro w
      by_cases hw : degree wt w=n
      · refine ⟨u ⟨w,hw⟩,?_⟩
        exact congrFun hp ⟨w,hw⟩
      · exact ⟨0,(coeff_support (LieGrading.homogeneousLie_embed p.property) w hw).trans (Int.cast_zero).symm⟩
    obtain ⟨q,hq⟩ := IntegralBaseChange.lift_integral hpint
    have hqm : q∈LieGrading.homogeneousLie wt n := by
      apply LieGrading.homogeneous_iff.mpr
      apply words_space_reflect
      rw [←IntegralBaseChange.embed_lie,hq]
      exact LieGrading.homogeneousLie_embed p.property
    refine ⟨⟨q,hqm⟩,?_⟩
    ext w
    apply Int.cast_injective (α:=ℚ)
    change ((embed q).coeff w.val : ℚ)=_
    rw [←IntegralBaseChange.words_coeff,←IntegralBaseChange.embed_lie,hq]
    exact congrFun hp w
  · rintro u ⟨p,rfl⟩
    refine ⟨castHom (R:=ℚ) p,?_⟩
    ext w
    exact coordinates_castHom p w

theorem cast_eval (t : UniversalEmbedding.Tree α) : IntegralBaseChange.lie (t.eval (R:=ℤ))=t.eval (R:=R) := by
  induction t with
  | leaf a => simp [Tree.eval]
  | node t u ht hu => simp [Tree.eval,ht,hu]

variable (F : Type*) [Field F] (wt : α → ℕ) (n : ℕ) [Fintype (Words wt n)]

omit [Fintype (Words wt n)] in
theorem reduction_image : LatticeDimension.reduction F (image ℚ wt n)=image F wt n := by
  apply le_antisymm
  · rintro v ⟨u,rfl⟩
    induction u using TensorProduct.inductionOn with

    | tmul c u =>
      have hup : u.val∈image ℤ wt n := by
        rw [←lattice_image]
        exact u.property
      obtain ⟨p,hp⟩ := hup
      have he : LatticeDimension.scalarMap F (image ℚ wt n) (c ⊗ₜ u)=
          c • coordinates F wt n (castHom p) := by
        ext w
        rw [LatticeDimension.scalarMap_tmul]
        simp only [Pi.smul_apply,smul_eq_mul,coordinates_castHom]
        rw [←congrFun hp w,mul_comm]
      rw [he]
      exact (image F wt n).smul_mem c ⟨castHom p,rfl⟩
    | add u v hu hv => simpa using (image F wt n).add_mem hu hv
  · rintro v ⟨p,rfl⟩
    have hgen : ∀ q : FreeLieAlgebra F α,q∈LieGrading.homogeneousLie wt n →
        ∀ hq,coordinates F wt n ⟨q,hq⟩∈LatticeDimension.reduction F (image ℚ wt n) := by
      intro q hq
      induction hq using Submodule.span_induction with
      | mem q hq =>
        obtain ⟨t,ht,rfl⟩ := hq
        intro hm
        let pZ : LieGrading.homogeneousLie (R:=ℤ) wt n := ⟨t.eval,Submodule.subset_span ⟨t,ht,rfl⟩⟩
        have hpZ : coordinates ℤ wt n pZ∈LatticeDimension.lattice (image ℚ wt n) := by
          rw [lattice_image]
          exact ⟨pZ,rfl⟩
        refine ⟨(1 : F) ⊗ₜ (⟨coordinates ℤ wt n pZ,hpZ⟩ : LatticeDimension.lattice (image ℚ wt n)),?_⟩
        ext w
        rw [LatticeDimension.scalarMap_tmul]
        change ((embed (t.eval (R:=ℤ))).coeff w.val : F)*1=(embed (t.eval (R:=F))).coeff w.val
        rw [mul_one]
        rw [←IntegralBaseChange.words_coeff,←IntegralBaseChange.embed_lie,cast_eval]
      | zero => intro hm; change coordinates F wt n 0∈_; simp
      | add q r hq hr hi hj =>
        intro hm
        change coordinates F wt n (⟨q,hq⟩+⟨r,hr⟩)∈_
        rw [map_add]
        exact (LatticeDimension.reduction F (image ℚ wt n)).add_mem (hi hq) (hj hr)
      | smul c q hq hi =>
        intro hm
        change coordinates F wt n (c • ⟨q,hq⟩)∈_
        rw [map_smul]
        exact (LatticeDimension.reduction F (image ℚ wt n)).smul_mem c (hi hq)
    exact hgen p.val p.property p.property

instance homogeneous_finite : Module.Finite F (LieGrading.homogeneousLie (R:=F) wt n) :=
  Module.Finite.of_injective (coordinates F wt n) (coordinates_injective F wt n)

theorem finrank_homogeneous :
    Module.finrank F (LieGrading.homogeneousLie (R:=F) wt n)=
      Module.finrank ℚ (LieGrading.homogeneousLie (R:=ℚ) wt n) := by
  have hF := (LinearEquiv.ofInjective (coordinates F wt n) (coordinates_injective F wt n)).finrank_eq
  have hQ := (LinearEquiv.ofInjective (coordinates ℚ wt n) (coordinates_injective ℚ wt n)).finrank_eq
  have h := LatticeDimension.finrank_reduction F (image ℚ wt n)
  rw [reduction_image] at h
  exact hF.trans (h.trans hQ.symm)

end LieDimension

namespace LieGrading
open AssociativeElimination UniversalEmbedding WordGrading
variable {R α : Type*} [CommRing R]

@[simp] theorem piece_add (wt : α → ℕ) (n : ℕ) (p q : FreeLieAlgebra R α) :
    piece wt n (p+q)=piece wt n p+piece wt n q := by
  apply UniversalEmbedding.injective
  simp only [embed_piece,map_add]

@[simp] theorem piece_smul (wt : α → ℕ) (n : ℕ) (c : R) (p : FreeLieAlgebra R α) :
    piece wt n (c • p)=c • piece wt n p := by
  apply UniversalEmbedding.injective
  simp only [embed_piece,map_smul]

def projection (wt : α → ℕ) (n : ℕ) : FreeLieAlgebra R α →ₗ[R] FreeLieAlgebra R α where
  toFun := piece wt n
  map_add' := piece_add wt n
  map_smul' := piece_smul wt n

theorem piece_homogeneous {wt : α → ℕ} {m : ℕ} {p : FreeLieAlgebra R α}
    (hp : p∈homogeneousLie wt m) (n : ℕ) : piece wt n p=if m=n then p else 0 := by
  apply UniversalEmbedding.injective
  rw [embed_piece,WordGrading.piece_homogeneous (homogeneousLie_embed hp)]
  split_ifs <;> simp

def biPiece (wa wb : α → ℕ) (n r : ℕ) : Submodule R (FreeLieAlgebra R α) :=
  homogeneousLie wa n ⊓ homogeneousLie wb r

def components (wa wb : α → ℕ) (n m : ℕ) :
    homogeneousLie (R:=R) wa n →ₗ[R] ((r : Fin (m+1)) → biPiece (R:=R) wa wb n r.val) where
  toFun p r := ⟨piece wb r.val p.val,⟨homogeneous_iff.mpr (by
      rw [embed_piece]; exact project_preserves (homogeneousLie_embed p.property)),
      (piece_spec wb r.val p.val).1⟩⟩
  map_add' p q := by ext r; exact piece_add wb r.val p.val q.val
  map_smul' c p := by ext r; exact piece_smul wb r.val c p.val

def assemble (wa wb : α → ℕ) (n m : ℕ) :
    ((r : Fin (m+1)) → biPiece (R:=R) wa wb n r.val) →ₗ[R] homogeneousLie (R:=R) wa n where
  toFun q := ⟨∑ r,(q r).val,Submodule.sum_mem _ (fun r _ => (q r).property.1)⟩
  map_add' p q := by ext; simp only [Pi.add_apply,Submodule.coe_add,Finset.sum_add_distrib]
  map_smul' c p := by ext; simp only [Pi.smul_apply,Submodule.coe_smul,Finset.smul_sum,RingHom.id_apply]

theorem components_assemble (wa wb : α → ℕ) (n m : ℕ)
    (q : (r : Fin (m+1)) → biPiece (R:=R) wa wb n r.val) :
    components wa wb n m (assemble wa wb n m q)=q := by
  classical
  funext r
  apply Subtype.ext
  change projection wb r.val (∑ s,(q s).val)=(q r).val
  rw [map_sum]
  simp only [projection,LinearMap.coe_mk,AddHom.coe_mk]
  simp_rw [piece_homogeneous (q _).property.2]
  simp [Fin.val_inj]

theorem assemble_components (wa wb : α → ℕ) (n m : ℕ)
    (hbound : ∀ w : FreeMonoid α, degree wa w = n → degree wb w ≤ m)
    (p : homogeneousLie (R:=R) wa n) :
    assemble wa wb n m (components wa wb n m p)=p := by
  classical
  apply Subtype.ext
  apply UniversalEmbedding.injective
  change embed (∑ r : Fin (m+1),piece wb r.val p.val)=embed p.val
  rw [map_sum]
  simp_rw [embed_piece]
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  change (∑ r : Fin (m+1), WordGrading.piece wb r.val (embed p.val)).coeff w=(embed p.val).coeff w
  simp only [MonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,WordGrading.piece,project_coeff]
  by_cases hw : degree wa w=n
  · have hb := hbound w hw
    exact Finset.sum_eq_single (⟨degree wb w,by omega⟩ : Fin (m+1))
      (by intro r _ hr; rw [ite_eq_right (by intro h; apply hr; exact Fin.ext h.symm)])
      (by simp) |>.trans (ite_eq_left rfl)
  · have hz := coeff_support (homogeneousLie_embed p.property) w hw
    simp [hz]

def decomposition (wa wb : α → ℕ) (n m : ℕ)
    (hbound : ∀ w : FreeMonoid α, degree wa w = n → degree wb w ≤ m) :
    homogeneousLie (R:=R) wa n ≃ₗ[R] ((r : Fin (m+1)) → biPiece (R:=R) wa wb n r.val) :=
  LinearEquiv.ofLinearMap (components wa wb n m) (assemble wa wb n m)
    (LinearMap.ext (components_assemble wa wb n m))
    (LinearMap.ext (assemble_components wa wb n m hbound))

variable (F : Type*) [Field F]

theorem finrank_decomposition (wa wb : α → ℕ) (n m : ℕ)
    (hbound : ∀ w : FreeMonoid α, degree wa w = n → degree wb w ≤ m)
    [Module.Finite F (homogeneousLie (R:=F) wa n)] :
    Module.finrank F (homogeneousLie (R:=F) wa n)=
      ∑ r : Fin (m+1),Module.finrank F (biPiece (R:=F) wa wb n r.val) := by
  let (r : Fin (m+1)) : Module.Finite F (biPiece (R:=F) wa wb n r.val) :=
    Module.Finite.of_injective (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)
  rw [(decomposition (R:=F) wa wb n m hbound).finrank_eq,Module.finrank_pi_fintype]

end LieGrading
end

namespace FiltrationDimension
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
variable {T : ℕ → Type*} [∀ r,AddCommGroup (T r)] [∀ r,Module K (T r)] [∀ r,Module.Finite K (T r)]

theorem step (F : ℕ → Submodule K V) (r : ℕ) (f : F r →ₗ[K] T r)
    (hk : ∀ p : F r,f p=0 → p.val∈F (r+1)) :
    Module.finrank K (F r)≤Module.finrank K (T r)+Module.finrank K (F (r+1)) := by
  let g : f.ker →ₗ[K] F (r+1) :=
    { toFun := fun p => ⟨p.val.val,hk p.val p.property⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hi : Function.Injective g := by
    intro p q h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun p : F (r+1) => p.val) h
  have hker := LinearMap.finrank_le_finrank_of_injective hi
  have hrange := Submodule.finrank_le f.range
  have := f.finrank_range_add_finrank_ker
  omega

theorem telescoping (F : ℕ → Submodule K V) (f : (r : ℕ) → F r →ₗ[K] T r)
    (hk : ∀ r (p : F r),f r p=0 → p.val∈F (r+1)) (N : ℕ) :
    Module.finrank K (F 0)≤(∑ r∈Finset.range N,Module.finrank K (T r))+Module.finrank K (F N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs := step F N (f N) (hk N)
    rw [Finset.sum_range_succ]
    omega

theorem bound (F : ℕ → Submodule K V) (f : (r : ℕ) → F r →ₗ[K] T r)
    (hk : ∀ r (p : F r),f r p=0 → p.val∈F (r+1)) (N : ℕ)
    (hN : F N=⊥) : Module.finrank K (F 0)≤∑ r∈Finset.range N,Module.finrank K (T r) := by
  have h := telescoping F f hk N
  rw [hN,finrank_bot,add_zero] at h
  exact h

omit [∀ r,Module.Finite K (T r)] in
theorem range_step (F : ℕ → Submodule K V) (r : ℕ) (f : F r →ₗ[K] T r)
    (hk : ∀ p : F r,f p=0 → p.val∈F (r+1)) :
    Module.finrank K (F r)≤Module.finrank K f.range+Module.finrank K (F (r+1)) := by
  let g : f.ker →ₗ[K] F (r+1) :=
    { toFun := fun p => ⟨p.val.val,hk p.val p.property⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hi : Function.Injective g := by
    intro p q h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun p : F (r+1) => p.val) h
  have hker := LinearMap.finrank_le_finrank_of_injective hi
  have := f.finrank_range_add_finrank_ker
  omega

theorem surjective_of_equality (F : ℕ → Submodule K V)
    (f : (r : ℕ) → F r →ₗ[K] T r)
    (hk : ∀ r (p : F r),f r p=0 → p.val∈F (r+1)) (N : ℕ)
    (hN : F N=⊥)
    (he : Module.finrank K (F 0)=∑ r∈Finset.range N,Module.finrank K (T r))
    (r : ℕ) (hr : r<N) : Function.Surjective (f r) := by
  let a := fun i => (∑ j∈Finset.range i,Module.finrank K (T j))+Module.finrank K (F i)
  have ha : Monotone a := by
    apply monotone_nat_of_le_succ
    intro i
    have hi := step F i (f i) (hk i)
    dsimp [a]
    rw [Finset.sum_range_succ]
    omega
  have hends : a 0=a N := by
    simp only [a,Finset.range_zero,Finset.sum_empty,zero_add]
    rw [hN,finrank_bot,add_zero]
    exact he
  have hstep : a r=a (r+1) := by
    apply le_antisymm (ha (by omega))
    exact (ha (by omega : r+1≤N)).trans (hends.symm.le.trans (ha (Nat.zero_le r)))
  have hs := range_step F r (f r) (hk r)
  have hle := Submodule.finrank_le (f r).range
  have heq : Module.finrank K (f r).range=Module.finrank K (T r) := by
    dsimp [a] at hstep
    rw [Finset.sum_range_succ] at hstep
    omega
  exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq heq)
end FiltrationDimension

section
namespace BaseChangeEquations
variable {R : Type*} [CommRing R]

def antisymmetryMap : FreeLieAlgebra R Bool →ₗ[R] FreeLieAlgebra R Bool :=
  LinearMap.id+(eval y x).toLinearMap

def specialMap : FreeLieAlgebra R Bool →ₗ[R] FreeLieAlgebra R Bool :=
  (LieAlgebra.ad R _ x).comp (eval y x).toLinearMap+
    (LieAlgebra.ad R _ (-x-y)).comp (eval y (-x-y)).toLinearMap

def pentagonMap : FreeLieAlgebra R Bool →ₗ[R] GenericBraid.T R (Fin 4) :=
  let t := GenericBraid.t (R:=R)
  (eval (t 0 1) (t 1 2+t 1 3)).toLinearMap+(eval (t 0 2+t 1 2) (t 2 3)).toLinearMap-
    (eval (t 1 2) (t 2 3)).toLinearMap-(eval (t 0 1+t 0 2) (t 1 3+t 2 3)).toLinearMap-
    (eval (t 0 1) (t 1 2)).toLinearMap

@[simp] theorem antisymmetryMap_apply (p : FreeLieAlgebra R Bool) : antisymmetryMap p=antisymmetry p := rfl
@[simp] theorem specialMap_apply (p : FreeLieAlgebra R Bool) : specialMap p=special p := rfl
@[simp] theorem pentagonMap_apply (p : FreeLieAlgebra R Bool) : pentagonMap p=pentagon p := rfl

end BaseChangeEquations
namespace ReducedDimension
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open RowTwo RowKernel ExactPentagon ImageBound
attribute [local instance] LieRing.ofAssociativeRing
abbrev K := ZMod 2

instance finite_boolWords (n : ℕ) : Fintype (LieDimension.Words (fun _ : Bool => 1) n) :=
  (WordCoordinates.finite_degree_finite_alphabet (fun _ : Bool => 1) (by simp) n).fintype

instance finite_oddWords (n : ℕ) : Fintype (LieDimension.Words oddWeight n) := by
  apply Set.Finite.fintype
  apply WordCoordinates.finite_degree oddWeight (by intro a; simp [oddWeight]) n
  apply (Set.finite_Iic n).subset
  intro a ha
  change a≤n
  change oddWeight a≤n at ha
  unfold oddWeight at ha
  omega

def solutions (n : ℕ) : Submodule K (FreeLieAlgebra K Bool) :=
  LieGrading.homogeneousLie (fun _ => 1) n ⊓ BaseChangeEquations.antisymmetryMap.ker ⊓
    BaseChangeEquations.specialMap.ker ⊓ BaseChangeEquations.pentagonMap.ker

theorem solutions_hom {n : ℕ} (p : solutions n) :
    p.val∈LieGrading.homogeneousLie (fun _ => 1) n := p.property.1.1.1

theorem solutions_anti {n : ℕ} (p : solutions n) : BaseChangeEquations.antisymmetry p.val=0 := p.property.1.1.2

theorem solutions_special {n : ℕ} (p : solutions n) : BaseChangeEquations.special p.val=0 := p.property.1.2

theorem solutions_pentagon {n : ℕ} (p : solutions n) : BaseChangeEquations.pentagon p.val=0 := p.property.2

instance finite_solutions (n : ℕ) : Module.Finite K (solutions n) :=
  Module.Finite.of_injective (Submodule.inclusion (inf_le_left.trans (inf_le_left.trans inf_le_left)))
    (Submodule.inclusion_injective _)

def representation (n : ℕ) (hn : 1<n) (p : solutions n) : FreeLieAlgebra K Slot :=
  (QuadraticLeading.representation hn (LieGrading.homogeneousLie_embed (solutions_hom p))).choose

theorem representation_under (n : ℕ) (hn : 1<n) (p : solutions n) :
    under (representation n hn p)=embed p.val :=
  (QuadraticLeading.representation hn (LieGrading.homogeneousLie_embed (solutions_hom p))).choose_spec.1

def representationMap (n : ℕ) (hn : 1<n) : solutions n →ₗ[K] FreeLieAlgebra K Slot where
  toFun := representation n hn
  map_add' p q := by
    apply under_injective
    rw [map_add,representation_under,representation_under,representation_under]
    simp only [Submodule.coe_add,map_add]
  map_smul' c p := by
    apply under_injective
    rw [map_smul,representation_under,representation_under]
    simp only [Submodule.coe_smul,map_smul,RingHom.id_apply]

theorem representation_injective (n : ℕ) (hn : 1<n) : Function.Injective (representationMap n hn) := by
  intro p q h
  apply Subtype.ext
  apply UniversalEmbedding.injective
  exact (representation_under n hn p).symm.trans ((congrArg under h).trans (representation_under n hn q))

def filtration (n : ℕ) (hn : 1<n) (r : ℕ) : Submodule K (solutions n) :=
  (above bCount r).comap (embed.toLinearMap.comp (representationMap n hn))

def oddPiece (n r : ℕ) : Submodule K (FreeLieAlgebra K ℕ) :=
  LieGrading.biPiece oddWeight (fun _ => 1) n r

instance finite_oddPiece (n r : ℕ) : Module.Finite K (oddPiece n r) :=
  Module.Finite.of_injective (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)

def inclusion (n r : ℕ) : oddPiece n r →ₗ[K] A K Bool :=
  positiveInput.toLinearMap.comp (embed.toLinearMap.comp (oddPiece n r).subtype)

theorem inclusion_injective (n r : ℕ) : Function.Injective (inclusion n r) :=
  positiveInput_injective.comp (UniversalEmbedding.injective.comp Subtype.val_injective)

def leadingMap (n : ℕ) (hn : 1<n) (r : ℕ) : filtration n hn r →ₗ[K] A K Bool :=
  (embed.toLinearMap.comp (eraseLie.toLinearMap.comp (LieGrading.projection bCount r))).comp
    ((representationMap n hn).comp (filtration n hn r).subtype)

theorem leadingMap_apply (n : ℕ) (hn : 1<n) (r : ℕ) (p : filtration n hn r) :
    leadingMap n hn r p=embed (leading r (representation n hn p.val)) := rfl

theorem leading_in_range (n : ℕ) (hn : 2<n) (r : ℕ) (p : filtration n (by omega) r) :
    leadingMap n (by omega) r p∈(inclusion n r).range := by
  obtain ⟨q,hq,hw,hr⟩ := actual_image hn (LieGrading.homogeneousLie_embed (solutions_hom p.val))
    (representation_under n (by omega) p.val) p.val.property.1.1.2 p.property
  exact ⟨⟨q,LieGrading.homogeneous_iff.mpr hw,LieGrading.homogeneous_iff.mpr hr⟩,hq⟩

def gradedMap (n : ℕ) (hn : 2<n) (r : ℕ) : filtration n (by omega) r →ₗ[K] oddPiece n r :=
  (LinearEquiv.ofInjective (inclusion n r) (inclusion_injective n r)).symm.toLinearMap.comp
    ((leadingMap n (by omega) r).codRestrict _ (leading_in_range n hn r))

theorem gradedMap_spec (n : ℕ) (hn : 2<n) (r : ℕ) (p : filtration n (by omega) r) :
    inclusion n r (gradedMap n hn r p)=leadingMap n (by omega) r p := by
  have h := (LinearEquiv.ofInjective (inclusion n r) (inclusion_injective n r)).apply_symm_apply
    ⟨leadingMap n (by omega) r p,leading_in_range n hn r p⟩
  exact congrArg Subtype.val h

def restore : FreeLieAlgebra K Bool →ₗ⁅K⁆ FreeLieAlgebra K Slot :=
  FreeLieAlgebra.lift K (fun b => if b then FreeLieAlgebra.of K Slot.B else FreeLieAlgebra.of K Slot.C)

theorem restore_erase (p : FreeLieAlgebra K Slot) :
    restore (eraseLie p)=LetterRetraction.lie (fun a => a≠Slot.A) p := by
  have he : restore.comp eraseLie=LetterRetraction.lie (fun a => a≠Slot.A) := by
    apply FreeLieAlgebra.hom_ext
    intro a
    cases a <;> simp [restore,eraseLie,LetterRetraction.lie]
  exact LieHom.congr_fun he p

theorem graded_kernel (n : ℕ) (hn : 2<n) (r : ℕ) (p : filtration n (by omega) r)
    (hz : gradedMap n hn r p=0) : p.val∈filtration n (by omega) (r+1) := by
  have he : leading r (representation n (by omega) p.val)=0 := by
    apply UniversalEmbedding.injective
    rw [map_zero,←leadingMap_apply,←gradedMap_spec n hn r p,hz,map_zero]
  have hret : LetterRetraction.lie (fun a => a≠Slot.A)
      (LieGrading.piece bCount r (representation n (by omega) p.val))=0 := by
    rw [←restore_erase]
    change restore (leading r (representation n (by omega) p.val))=0
    rw [he,map_zero]
  have hproj := ProjectionKernel.leading_projection_kernel hn (representation_under n (by omega) p.val)
    (representation_weight (LieGrading.homogeneousLie_embed (solutions_hom p.val))
      (representation_under n (by omega) p.val)) p.property
    (solutions_anti p.val) (solutions_special p.val) (solutions_pentagon p.val) hret
  have hs := subtract_piece_above p.property
  change embed (representation n (by omega) p.val)-
    WordGrading.piece bCount r (embed (representation n (by omega) p.val))∈above bCount (r+1) at hs
  rw [←LieGrading.embed_piece,hproj,map_zero,sub_zero] at hs
  exact hs

theorem filtration_zero (n : ℕ) (hn : 1<n) : filtration n hn 0=⊤ := by
  apply top_unique
  intro p hp
  apply mem_space
  intro w hw
  exact Nat.zero_le _

theorem filtration_terminal (n : ℕ) (hn : 1<n) : filtration n hn (n+1)=⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro p hp
  apply representation_injective n hn
  rw [map_zero]
  apply UniversalEmbedding.injective
  rw [map_zero]
  have hw := representation_weight (LieGrading.homogeneousLie_embed (solutions_hom p))
    (representation_under n hn p)
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  change (embed (representation n hn p)).coeff w=0
  by_contra hc
  have h1 := mem_space_iff.mp hw w hc
  have h2 := mem_space_iff.mp hp w hc
  have h3 := weight_count w
  omega

theorem odd_length_bound (n : ℕ) (w : FreeMonoid ℕ) (hw : degree oddWeight w=n) :
    degree (fun _ => 1) w≤n := by
  calc
    _=w.toList.length := by simp [degree]
    _≤degree oddWeight w := WordCoordinates.length_le_degree oddWeight (by intro a; simp [oddWeight]) w
    _=n := hw

theorem finrank_bound (n : ℕ) (hn : 2<n) :
    Module.finrank K (solutions n)≤Module.finrank K (LieGrading.homogeneousLie (R:=K) oddWeight n) := by
  have h := FiltrationDimension.bound (filtration n (by omega)) (gradedMap n hn)
    (graded_kernel n hn) (n+1) (filtration_terminal n (by omega))
  rw [filtration_zero,finrank_top] at h
  rw [LieGrading.finrank_decomposition K oddWeight (fun _ => 1) n n (odd_length_bound n)]
  change Module.finrank K (solutions n)≤∑ r : Fin (n+1),Module.finrank K (oddPiece n r.val)
  rw [Fin.sum_univ_eq_sum_range (fun r => Module.finrank K (oddPiece n r)) (n+1)]
  exact h

theorem rational_finrank_bound (n : ℕ) (hn : 2<n) :
    Module.finrank K (solutions n)≤Module.finrank ℚ (LieGrading.homogeneousLie (R:=ℚ) oddWeight n) := by
  rw [←LieDimension.finrank_homogeneous K oddWeight n]
  exact finrank_bound n hn

end ReducedDimension

open AssociativeElimination UniversalEmbedding WordGrading
open scoped TensorProduct

namespace LieGrading
variable {α : Type*} {wt : α → ℕ}

theorem weightedWord_tree {n : ℕ} {p : FreeLieAlgebra ℚ α} (hp : WeightedWord wt n p) :
    ∃ t : UniversalEmbedding.Tree α,treeDegree wt t=n ∧ t.eval=p := by
  induction hp with
  | generator a => exact ⟨.leaf a,rfl,rfl⟩
  | bracket hp hq hi hj =>
    obtain ⟨t,ht,rfl⟩ := hi
    obtain ⟨u,hu,rfl⟩ := hj
    exact ⟨.node t u,by simp only [treeDegree_node,ht,hu],rfl⟩

theorem tree_weightedWord (t : UniversalEmbedding.Tree α) : WeightedWord wt (treeDegree wt t) t.eval := by
  induction t with
  | leaf a => exact .generator a
  | node t u ht hu => simpa only [treeDegree_node,UniversalEmbedding.Tree.eval] using WeightedWord.bracket ht hu

theorem weightPiece_eq (wt : α → ℕ) (n : ℕ) : weightPiece wt n=homogeneousLie (R:=ℚ) wt n := by
  unfold weightPiece homogeneousLie
  congr 1
  ext p
  constructor
  · exact weightedWord_tree
  · rintro ⟨t,ht,rfl⟩
    rw [←ht]
    exact tree_weightedWord t

end LieGrading
namespace RationalBound
open ReducedDimension
abbrev wt : Bool → ℕ := fun _ => 1
abbrev Words (n : ℕ) := LieDimension.Words wt n

def toHom (n : ℕ) : Wn n →ₗ[ℚ] LieGrading.homogeneousLie (R:=ℚ) wt n :=
  (Wn n).subtype.codRestrict _ (fun p => by
    rw [←LieGrading.weightPiece_eq]
    exact p.property.2)

def coordinates (n : ℕ) : Wn n →ₗ[ℚ] (Words n → ℚ) :=
  (LieDimension.coordinates ℚ wt n).comp (toHom n)

theorem coordinates_injective (n : ℕ) : Function.Injective (coordinates n) := by
  intro p q h
  apply Subtype.ext
  exact congrArg (fun z : LieGrading.homogeneousLie (R:=ℚ) wt n => z.val) (LieDimension.coordinates_injective ℚ wt n h)

instance finite_Wn (n : ℕ) : Module.Finite ℚ (Wn n) :=
  Module.Finite.of_injective (coordinates n) (coordinates_injective n)

def image (n : ℕ) : Submodule ℚ (Words n → ℚ) := (coordinates n).range

def reducedCoordinates (n : ℕ) : solutions n →ₗ[K] (Words n → K) :=
  (LieDimension.coordinates K wt n).comp ((solutions n).subtype.codRestrict _ solutions_hom)

theorem reducedCoordinates_injective (n : ℕ) : Function.Injective (reducedCoordinates n) := by
  intro p q h
  apply Subtype.ext
  exact congrArg (fun z : LieGrading.homogeneousLie (R:=K) wt n => z.val) (LieDimension.coordinates_injective K wt n h)

def reducedImage (n : ℕ) : Submodule K (Words n → K) := (reducedCoordinates n).range

theorem lattice_lift (n : ℕ) (u : LatticeDimension.lattice (image n)) :
    ∃ q : LieGrading.homogeneousLie (R:=ℤ) wt n,
      LieDimension.coordinates ℤ wt n q=u.val ∧ (LieDimension.castHom (R:=ℚ) q).val∈W := by
  obtain ⟨p,hp⟩ := u.property
  have hfull : u.val∈LatticeDimension.lattice (LieDimension.image ℚ wt n) := by
    exact ⟨toHom n p,hp⟩
  rw [LieDimension.lattice_image] at hfull
  obtain ⟨q,hq⟩ := hfull
  refine ⟨q,hq,?_⟩
  have he : LieDimension.castHom (R:=ℚ) q=toHom n p := by
    apply LieDimension.coordinates_injective ℚ wt n
    ext w
    rw [LieDimension.coordinates_castHom]
    change ((LieDimension.coordinates ℤ wt n q) w : ℚ)=coordinates n p w
    rw [hq,congrFun hp w]
    rfl
  rw [he]
  exact p.property.1

def reduceLattice (n : ℕ) (hn : 2<n) (q : LieGrading.homogeneousLie (R:=ℤ) wt n)
    (hq : (LieDimension.castHom (R:=ℚ) q).val∈W) : solutions n := by
  have hw : (IntegralBaseChange.lie q.val : L)∈Ln n := by
    change (IntegralBaseChange.lie q.val : L)∈weightPiece wt n
    rw [LieGrading.weightPiece_eq]
    exact (LieDimension.castHom (R:=ℚ) q).property
  have hE := BaseChangeEquations.reduce (S:=K) q.val hq
  have hS := BaseChangeEquations.reduce_special (S:=K) q.val hq hw hn
  exact ⟨(LieDimension.castHom (R:=K) q).val,
    ⟨⟨⟨(LieDimension.castHom (R:=K) q).property,hE.1⟩,hS⟩,hE.2.2⟩⟩

theorem reduction_le (n : ℕ) (hn : 2<n) :
    LatticeDimension.reduction K (image n)≤reducedImage n := by
  rintro v ⟨u,rfl⟩
  induction u using TensorProduct.inductionOn with

  | tmul c u =>
    obtain ⟨q,hq,hW⟩ := lattice_lift n u
    have he : LatticeDimension.scalarMap K (image n) (c ⊗ₜ u)=
        c • reducedCoordinates n (reduceLattice n hn q hW) := by
      ext w
      rw [LatticeDimension.scalarMap_tmul]
      change (u.val w : K)*c=c*(embed (IntegralBaseChange.lie (S:=K) q.val)).coeff w.val
      rw [IntegralBaseChange.embed_lie,IntegralBaseChange.words_coeff]
      have hh := congrFun hq w
      change (embed q.val).coeff w.val=u.val w at hh
      rw [hh,mul_comm]
    rw [he]
    exact (reducedImage n).smul_mem c ⟨reduceLattice n hn q hW,rfl⟩
  | add u v hu hv => simpa using (reducedImage n).add_mem hu hv

theorem finrank_Wn_le (n : ℕ) (hn : 2<n) :
    Module.finrank ℚ (Wn n)≤Module.finrank ℚ (Fn n) := by
  have h0 := (LinearEquiv.ofInjective (coordinates n) (coordinates_injective n)).finrank_eq
  have h1 := LatticeDimension.finrank_reduction K (image n)
  have h2 := Submodule.finrank_mono (reduction_le n hn)
  have h3 := (LinearEquiv.ofInjective (reducedCoordinates n) (reducedCoordinates_injective n)).finrank_eq
  have h4 := rational_finrank_bound n hn
  rw [←LieGrading.weightPiece_eq] at h4
  change Module.finrank ℚ (Wn n)=Module.finrank ℚ (image n) at h0
  change Module.finrank K (solutions n)=Module.finrank K (reducedImage n) at h3
  change Module.finrank ℚ (Wn n)≤Module.finrank ℚ (weightPiece DeligneDrinfeld.oddWeight n)
  omega

end RationalBound
end

namespace LowWeight
open LieGrading UniversalEmbedding

theorem treeDegree_pos {α : Type*} {wt : α → ℕ} (hw : ∀ a,0<wt a) (u : UniversalEmbedding.Tree α) :
    0<treeDegree wt u := by
  induction u with
  | leaf a => simpa using hw a
  | node u v hu hv => simp only [treeDegree_node]; omega

theorem tree_degree_one {α : Type*} (u : UniversalEmbedding.Tree α) (hu : treeDegree (fun _ => 1) u=1) :
    ∃ a,u=.leaf a := by
  cases u with
  | leaf a => exact ⟨a,rfl⟩
  | node u v =>
    have h1 := treeDegree_pos (fun _ : α => Nat.zero_lt_one) u
    have h2 := treeDegree_pos (fun _ : α => Nat.zero_lt_one) v
    simp only [treeDegree_node] at hu
    omega

theorem weight_zero {α : Type*} {wt : α → ℕ} (hw : ∀ a,0<wt a) :
    weightPiece wt 0=⊥ := by
  rw [weightPiece_eq]
  apply le_antisymm ?_ bot_le
  apply Submodule.span_le.mpr
  rintro p ⟨u,hu,rfl⟩
  have h := treeDegree_pos hw u
  omega

theorem weight_one_form {p : L} (hp : p∈Ln 1) : ∃ a b : ℚ,p=a • x+b • y := by
  simp only [Ln,weightPiece_eq] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u,hu,rfl⟩ := hp
    obtain ⟨a,rfl⟩ := tree_degree_one u hu
    cases a
    · exact ⟨1,0,by simp [Tree.eval,x]⟩
    · exact ⟨0,1,by simp [Tree.eval,y]⟩
  | zero => exact ⟨0,0,by simp⟩
  | add p q _ _ hp hq =>
    obtain ⟨a,b,rfl⟩ := hp
    obtain ⟨c,d,rfl⟩ := hq
    exact ⟨a+c,b+d,by simp only [add_smul]; abel⟩
  | smul c p _ hp =>
    obtain ⟨a,b,rfl⟩ := hp
    exact ⟨c*a,c*b,by simp only [smul_add,mul_smul]⟩

attribute [local instance] LieRing.ofAssociativeRing

def edgeValue (a b i j : Fin 4) : ℚ :=
  if (i=a ∧ j=b) ∨ (i=b ∧ j=a) then 1 else 0

def detector (a b : Fin 4) (hab : a≠b) : T4 →ₗ⁅ℚ⁆ ℚ :=
  T4Universal.lift (edgeValue a b)
    (by intros; simp only [edgeValue]; congr 1; apply propext; tauto)
    (by
      intro i
      simp only [edgeValue]
      split_ifs with h
      · rcases h with h|h
        · exact (hab (h.1.symm.trans h.2)).elim
        · exact (hab (h.2.symm.trans h.1)).elim
      · rfl)
    (by intros; simp only [LieRing.of_associative_ring_bracket,mul_comm,sub_self])
    (by intros; simp only [LieRing.of_associative_ring_bracket,mul_comm,sub_self])

@[simp] theorem detector_t (a b : Fin 4) (hab : a≠b) (i j : Fin 4) :
    detector a b hab (t i j)=edgeValue a b i j := T4Universal.lift_t _ _ _ _ _ _ _

theorem weight_one_zero {p : L} (hp : p∈Wn 1) : p=0 := by
  obtain ⟨a,b,rfl⟩ := weight_one_form hp.2
  have h := hp.1.2.2
  simp only [eval,map_add,map_smul,FreeLieAlgebra.lift_of_apply,x,y,Bool.false_eq_true,↓reduceIte] at h
  have h1 := congrArg (detector 0 1 (by decide)) h
  have h2 := congrArg (detector 2 3 (by decide)) h
  norm_num [map_add,map_smul,edgeValue,Fin.ext_iff] at h1 h2
  have ha : a=0 := by linarith
  have hb : b=0 := by linarith
  simp [ha,hb]

def cyclic : L →ₗ[ℚ] L := LinearMap.id+(eval y (-x-y)).toLinearMap+(eval (-x-y) x).toLinearMap

theorem cyclic_weight_two {p : L} (hp : p∈Ln 2) : cyclic p=(3 : ℚ) • p := by
  simp only [Ln,weightPiece_eq] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u,hu,rfl⟩ := hp
    cases u with
    | leaf a => simp at hu
    | node u v =>
      have h1 := treeDegree_pos (fun _ : Bool => Nat.zero_lt_one) u
      have h2 := treeDegree_pos (fun _ : Bool => Nat.zero_lt_one) v
      simp only [treeDegree_node] at hu
      obtain ⟨a,rfl⟩ := tree_degree_one u (by omega)
      obtain ⟨b,rfl⟩ := tree_degree_one v (by omega)
      cases a <;> cases b <;>
        simp [Tree.eval,cyclic,eval,x,y,lie_sub,sub_lie,lie_skew,show (3 : ℚ)=(1+1+1) by norm_num,add_smul]
  | zero => simp
  | add p q _ _ hp hq => simp only [map_add,hp,hq,smul_add]
  | smul c p _ hp => simp only [map_smul,hp,smul_smul,mul_comm]

theorem weight_two_zero {p : L} (hp : p∈Wn 2) : p=0 := by
  have hc : cyclic p=0 := hp.1.2.1
  rw [cyclic_weight_two hp.2] at hc
  exact (smul_eq_zero.mp hc).resolve_left (by norm_num)

theorem Wn_eq_bot {n : ℕ} (hn : n≤2) : Wn n=⊥ := by
  apply le_antisymm ?_ bot_le
  intro p hp
  change p=0
  interval_cases n
  · have h : Ln 0=⊥ := weight_zero (fun _ => by decide)
    have hz := hp.2
    rw [h] at hz
    exact hz
  · exact weight_one_zero hp
  · exact weight_two_zero hp

end LowWeight

end DeligneDrinfeld

end

end OAI
