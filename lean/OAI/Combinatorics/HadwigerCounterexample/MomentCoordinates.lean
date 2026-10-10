import OAI.Combinatorics.HadwigerCounterexample.ComponentIndices
import OAI.Combinatorics.HadwigerCounterexample.BinaryMatrices
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Option

namespace OAI

/-! # Moment Coordinates -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Finset

/-- Construction parameters that affect dimensions (except n,N). j = selector degree;
r = number of ordered tester pairs in a tester. J, h mix and channel indices. -/
structure Shape where
  g : ℕ
  b : ℕ
  j : ℕ
  J : ℕ
  r : ℕ
  h : ℕ

abbrev Block (g : ℕ) := (Tag g × Tag g) ⊕ Fin 3
namespace Block
variable {g : ℕ}
abbrev O (d t : Tag g) : Block g := .inl (d,t)
abbrev S : Block g := .inr 0
abbrev sharp : Block g := .inr 1
abbrev Z : Block g := .inr 2
end Block

abbrev BaseIdx (g n : ℕ) := Block g × Fin n
abbrev Base (g n : ℕ) := Vec (BaseIdx g n)
abbrev AIdx (g n : ℕ) := Option (BaseIdx g n)
abbrev Label (b : ℕ) := Vec (Fin b)
abbrev SelIdx (b j : ℕ) := { m : Finset (Fin b) // m.card ≤ j }
abbrev Row (p : Shape) (n : ℕ) := SelIdx p.b p.j × AIdx p.g n
abbrev Ray (p : Shape) (n : ℕ) := Vec (Row p n)
abbrev Moment (p : Shape) (n : ℕ) := Mat (Row p n) (Row p n)

theorem card_baseIdx (g n : ℕ) : Fintype.card (BaseIdx g n) = (g*g+3)*n := by
  simp [BaseIdx,Block,Tag]

def psize (p : Shape) := Fintype.card (SelIdx p.b p.j)
theorem card_row (p : Shape) (n : ℕ) :
    Fintype.card (Row p n) = psize p * (1 + (p.g*p.g+3)*n) := by
  simp [Row,AIdx,psize,add_comm]

def emptySel {b j} : SelIdx b j := ⟨∅,by simp⟩
def selV {b} (j) (s : Label b) : Vec (SelIdx b j) := fun x => ∏ i ∈ x.val, s i
def baseV {g n} (z : Base g n) : Vec (AIdx g n) := Option.elim' 1 z

variable (p : Shape)
variable {n : ℕ}

/-- Embedding of the affine coordinate space at a fixed label. -/
def putLab (n : ℕ) (s : Label p.b) : Vec (AIdx p.g n) →ₗ[F] Ray p n where
  toFun z r := selV p.j s r.1 * z r.2
  map_add' z w := by ext; simp only [Pi.add_apply,mul_add]
  map_smul' b z := by ext; simp only [Pi.smul_apply,RingHom.id_apply,smul_eq_mul]; ring

def point (s : Label p.b) (z : Base p.g n) : Ray p n := putLab p n s (baseV z)
def mom (s : Label p.b) (z : Base p.g n) : Moment p n := vecMulVec (point p s z) (point p s z)

theorem point_base_eval (s : Label p.b) (z : Base p.g n) (r : AIdx p.g n) :
    point p s z (emptySel,r) = baseV z r := by simp [point,putLab,selV,emptySel]

theorem point_ne_zero (s : Label p.b) (z : Base p.g n) : point p s z ≠ 0 := by
  intro h
  have := point_base_eval p s z none
  rw [h] at this
  simp [baseV] at this

def Wspace (n : ℕ) : Space (Moment p n) :=
  Submodule.span F {m | ∃ s z, m = mom p s z}

/-- O-blocks disallowed at l are set to zero. -/
def allows {g n} (l : Tag g) (z : Base g n) :=
  ∀ d t : Tag g, ¬ allowed d l → ∀ i : Fin n, z (Block.O d t,i) = 0

def shared {g n} (z : Base g n) :=
  ∀ d t : Tag g, ∀ i : Fin n, z (Block.O d t,i) = 0

def Wtag (n : ℕ) (l : Tag p.g) : Space (Moment p n) :=
  Submodule.span F {m | ∃ s z, allows l z ∧ m = mom p s z}

def Wstar (n : ℕ) : Space (Moment p n) :=
  Submodule.span F {m | ∃ s z, shared z ∧ m = mom p s z}

variable {p}

theorem Wstar_le_tag (l : Tag p.g) : Wstar p n ≤ Wtag p n l :=
  Submodule.span_mono (by rintro m ⟨s,z,h,rfl⟩; exact ⟨s,z,fun d t _ => h d t,rfl⟩)
theorem Wtag_le (l : Tag p.g) : Wtag p n l ≤ Wspace p n :=
  Submodule.span_mono (by rintro m ⟨s,z,h,rfl⟩; exact ⟨s,z,rfl⟩)

theorem Wspace_sym {m : Moment p n} (h : m ∈ Wspace p n) : mᵀ = m := by
  unfold Wspace at h
  induction h using Submodule.span_induction with
  | mem m hm => obtain ⟨s,z,rfl⟩ := hm; rw [mom,transpose_vecMulVec]
  | zero => simp
  | add x y _ _ hx hy => rw [transpose_add,hx,hy]
  | smul b x _ hx => rw [transpose_smul,hx]

/-- Cut profiles in the direct sum over unordered components. -/
abbrev Profile (p : Shape) (n : ℕ) := Comp p.g → Moment p n
def cut (p : Shape) (n : ℕ) : (Tag p.g → Moment p n) →ₗ[F] Profile p n where
  toFun w e := w e.val.1 + w e.val.2
  map_add' w w' := by
    funext e
    simp only [Pi.add_apply]
    ac_rfl
  map_smul' b w := by funext; simp only [Pi.smul_apply, RingHom.id_apply, smul_add]

def Xspace (p : Shape) (n : ℕ) : Space (Profile p n) :=
  (Submodule.pi Set.univ (fun l => Wtag p n l)).map (cut p n)

theorem mem_X {x : Profile p n} :
    x ∈ Xspace p n ↔ ∃ w : Tag p.g → Moment p n, (∀ l, w l ∈ Wtag p n l) ∧ cut p n w = x :=
  Submodule.mem_map.trans (by simp [Submodule.mem_pi])

/-- For complete generality this returns zero on pairs with equal tags. -/
def getPair (p : Shape) (n : ℕ) (l d : Tag p.g) : Profile p n →ₗ[F] Moment p n :=
  if h : l ≠ d then LinearMap.proj (edge l d h) else 0

theorem getPair_edge (l d : Tag p.g) (h : l ≠ d) (x : Profile p n) :
    getPair p n l d x = x (edge l d h) := by rw [getPair,dite_eq_left h]; rfl

theorem getPair_cut (w : Tag p.g → Moment p n) (l d : Tag p.g) :
    getPair p n l d (cut p n w) = w l + w d := by
  by_cases h : l = d
  · subst l; rw [getPair,dite_eq_right, LinearMap.zero_apply,char_two]; simp
  · rw [getPair_edge _ _ h]
    change w _ + w _ = _
    rcases lt_or_gt_of_ne h with e|e
    · rw [edge_eq e]
    · rw [edge_symm,edge_eq e,add_comm]

/-- Single star atoms as profiles in ambient coordinates. -/
def atom (p : Shape) (l : Tag p.g) (s : Label p.b) (z : Base p.g n) : Profile p n :=
  cut p n (Pi.single l (mom p s z))

theorem atom_mem {l} {z : Base p.g n} (s : Label p.b) (h : allows l z) :
    atom p l s z ∈ Xspace p n := by
  rw [mem_X]
  refine ⟨Pi.single l (mom p s z),fun i => ?_,rfl⟩
  by_cases e : l = i
  · subst i
    rw [Pi.single_eq_same]
    exact Submodule.subset_span ⟨s,z,h,rfl⟩
  · simp [Pi.single_eq_of_ne (Ne.symm e)]

theorem atom_def (l : Tag p.g) (s : Label p.b) (z : Base p.g n) (e) :
    atom p l s z e = if inc e l then mom p s z else 0 := by
  change (Pi.single l (mom p s z) : Tag p.g → Moment p n) e.val.1 +
    (Pi.single l (mom p s z) : Tag p.g → Moment p n) e.val.2 = _
  by_cases h : e.val.1 = l
  · have h' : e.val.2 ≠ l := h ▸ e.property.ne.symm
    rw [Pi.single_eq_of_ne h',ite_eq_left (show inc e l from Or.inl h)]
    rw [h, Pi.single_eq_same,add_zero]
  by_cases h' : e.val.2 = l
  · rw [Pi.single_eq_of_ne h,ite_eq_left (show inc e l from Or.inr h'),h',Pi.single_eq_same,zero_add]
  rw [Pi.single_eq_of_ne h,Pi.single_eq_of_ne h',add_zero,ite_eq_right (by simp [inc,h,h'])]

end HadwigerCounterexample

end

end OAI
