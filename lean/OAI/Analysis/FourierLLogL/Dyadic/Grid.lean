import OAI.Analysis.FourierLLogL.Fourier.Affine
/-! # The finite spatial model -/

open MeasureTheory Filter Set Function
open scoped ENNReal BigOperators Topology Real

namespace OAI

namespace FourierLLogL.Dyadic
open Period
noncomputable section

abbrev Grid (M : ℕ) := ZMod (2^M)

def pos {M : ℕ} (x : Grid M) : ℝ := x.val * side M

def chi {M : ℕ} (n x : Grid M) : ℂ := ZMod.stdAddChar (n*x)

lemma chi_cast {M : ℕ} (n : ℤ) (x : Grid M) : chi (n:Grid M) x = phase n (pos x) := by
  unfold chi
  have heq : (n:Grid M)*x = ((n*(x.val:ℤ):ℤ):Grid M) := by
    rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [heq, ZMod.stdAddChar_coe, phase, pos, side]
  congr 1
  push_cast
  simp only [div_eq_mul_inv, ← inv_pow]; ring

lemma norm_chi {M : ℕ} (n x : Grid M) : ‖chi n x‖ = 1 := by
  unfold chi
  simp [ZMod.stdAddChar_apply]

/-- Uniform probability average. -/
def expU {E : Type*} [SMul ℝ E] [AddCommMonoid E] {M : ℕ} (f : Grid M → E) :=
  side M • ∑ y, f y

@[ext] structure Node where
  lev : ℕ
  ix : ℕ
  deriving DecidableEq

namespace Node

def root : Node := ⟨0,0⟩

def valid (p : Node) : Prop := p.ix < 2^p.lev

def len (p : Node) := side p.lev

def a (p : Node) : ℝ := p.ix * p.len

def cells (p : Node) := box p.a p.len

theorem len_pos (p : Node) : 0 < p.len := side_pos _

lemma cells_sub {p : Node} (hp : p.valid) : p.cells ⊆ unitInt := by
  simpa [lft, unitInt, cells, a, len, box] using cell_in_top 0 zero_lt_one hp

lemma cells_dis {n k l : ℕ} (h : k ≠ l) :
    Disjoint (cells ⟨n,k⟩) (cells ⟨n,l⟩) := by
  rw [Set.disjoint_left]
  intro x hx hy
  apply h
  apply cell_unique 0 1 zero_lt_one n (x:=x)
  all_goals simpa only [lft,one_mul,zero_add]


def L (p : Node) : Node := ⟨p.lev+1,p.ix*2⟩
def R (p : Node) : Node := ⟨p.lev+1,p.ix*2+1⟩

lemma len_L (p : Node) : p.L.len = p.len/2 := side_succ _
lemma len_R (p : Node) : p.R.len = p.len/2 := side_succ _

lemma a_L (p : Node) : p.L.a = p.a := by
  unfold a
  rw [len_L]
  dsimp only [L]
  push_cast; ring

lemma a_R (p : Node) : p.R.a = p.a+p.len/2 := by
  unfold a
  rw [len_R]
  dsimp only [R]
  push_cast; ring

lemma cells_L (p : Node) : p.L.cells = Ico p.a (p.a+p.len/2) := by rw [cells, len_L, a_L, box]
lemma cells_R (p : Node) : p.R.cells = Ico (p.a+p.len/2) (p.a+p.len) := by
  rw [cells,len_R,a_R,box]
  ring_nf

lemma cells_split (p : Node) : p.cells = p.L.cells ∪ p.R.cells := by
  rw [cells_L,cells_R,Ico_union_Ico_eq_Ico (by linarith [p.len_pos]) (by linarith [p.len_pos])]
  rfl

lemma valid_L (p : Node) : p.L.valid ↔ p.valid := by
  unfold L valid; simp; omega
lemma valid_R (p : Node) : p.R.valid ↔ p.valid := by
  unfold R valid; simp; omega

def block (p : Node) (M : ℕ) := (pos : Grid M → ℝ) ⁻¹' p.cells

def avg (p : Node) {M : ℕ} {E : Type*} [AddCommMonoid E] [SMul ℝ E] (f : Grid M → E) :=
  p.len⁻¹ • expU ((p.block M).indicator f)

def normarg (p : Node) (x : ℝ) : ℝ := (x-p.a) / p.len

def Hi (p : Node) (x : ℝ) : ℝ := haarH (p.normarg x)
def Gi (p : Node) (x : ℝ) : ℝ := haarG (p.normarg x)

lemma arg_mem (p : Node) (x : ℝ) : p.normarg x ∈ unitInt ↔ x ∈ p.cells :=
  norm_mem_box p.len_pos

lemma argL_eq (p : Node) (x : ℝ) : p.L.normarg x = 2*p.normarg x := by
  rw [normarg, a_L,len_L,normarg]
  ring
lemma argR_eq (p : Node) (x : ℝ) : p.R.normarg x = 2*p.normarg x - 1 := by
  rw [normarg, a_R,len_R,normarg]
  have H := p.len_pos
  field_simp; ring

lemma Gi_eq (p : Node) (x : ℝ) : p.Gi x = p.L.Hi x - p.R.Hi x := by
  rw [Hi,Hi, argL_eq, argR_eq]; rfl

lemma Hi_L (p : Node) {x : ℝ} (hx : x ∈ p.L.cells) : p.Hi x = 1 := by
  rw [← arg_mem, argL_eq] at hx
  apply H_of_left
  constructor <;> linarith [hx.1,hx.2]

lemma Hi_R (p : Node) {x : ℝ} (hx : x ∈ p.R.cells) : p.Hi x = -1 := by
  rw [← arg_mem, argR_eq] at hx
  apply H_of_right
  constructor <;> linarith [hx.1,hx.2]

lemma Hi_out (p : Node) {x : ℝ} (hx : x ∉ p.cells) : p.Hi x = 0 := by
  rw [← arg_mem] at hx
  exact H_outside hx

lemma Gi_out (p : Node) {x : ℝ} (hx : x ∉ p.cells) : p.Gi x = 0 := by
  rw [← arg_mem] at hx
  exact G_outside hx

end Node

open Node

def vertex {M : ℕ} (x : Grid M) : Node := ⟨M,x.val⟩

def atom {M : ℕ} (x : Grid M) := (vertex x).cells

lemma pos_mem {M : ℕ} (x : Grid M) : pos x ∈ atom x :=
  ⟨le_refl (pos x), lt_add_of_pos_right (pos x) (side_pos M)⟩

lemma atom_sub {M : ℕ} (x : Grid M) : atom x ⊆ unitInt :=
  cells_sub (ZMod.val_lt _)

lemma atom_disjoint {M : ℕ} : Pairwise (fun x y : Grid M => Disjoint (atom x) (atom y)) := by
  intro x y h
  apply cells_dis
  intro he
  have H := congrArg (fun n : ℕ => (n:Grid M)) he
  exact h (by simpa using H)

lemma atom_measurable {M : ℕ} (x : Grid M) : MeasurableSet (atom x) := measurableSet_Ico

lemma atom_volume {M : ℕ} (x : Grid M) : volume (atom x) = ENNReal.ofReal (side M) := by
  change volume (Ico (pos x) (pos x+side M)) = _
  simp

lemma atom_partition (M : ℕ) : unitInt = ⋃ x : Grid M, atom x := by
  apply Subset.antisymm _ (iUnion_subset atom_sub)
  intro x hx
  obtain ⟨p,hp,hi,hxp⟩ :
      ∃ p : Node, p.valid ∧ p.lev = M ∧ x ∈ p.cells := by
    induction M with
    | zero =>
      refine ⟨root,by simp [valid,root], rfl, ?_⟩
      simpa [root,cells,box, len,side,a,unitInt] using hx
    | succ M ih =>
      obtain ⟨p,hv,hM,hx⟩ := ih
      rw [cells_split] at hx
      exact hx.elim (fun h => ⟨p.L,p.valid_L.mpr hv,congrArg Nat.succ hM,h⟩)
        (fun h => ⟨p.R,p.valid_R.mpr hv,congrArg Nat.succ hM,h⟩)
  refine mem_iUnion.mpr ⟨(p.ix:Grid M),?_⟩
  obtain ⟨n,k⟩ := p
  cases hi
  change x ∈ cells ⟨_, ((k:Grid _).val)⟩
  rwa [ZMod.val_natCast_of_lt hp]

/-- Every atom fully inside/out of a coarser dyadic cell. -/
lemma coarse_const {p q : Node} (h : p.lev ≤ q.lev) {x y : ℝ}
    (hx : x ∈ q.cells) (hy : y ∈ q.cells) : x ∈ p.cells ↔ y ∈ p.cells := by
  suffices HH : ∀ n : ℕ, ∀ q : Node, q.lev = p.lev+n →
      x ∈ q.cells → y ∈ q.cells → (x ∈ p.cells ↔ y ∈ p.cells) by
    exact HH (q.lev - p.lev) q (by omega) hx hy
  intro n
  induction n with
  | zero =>
    rintro ⟨l,k⟩ hl hx hy
    obtain ⟨m,r⟩ := p
    simp only [Nat.add_zero] at hl
    subst l
    by_cases H : r = k
    · subst r; exact iff_of_true hx hy
    · have Hd := Set.disjoint_left.mp (cells_dis (n:=m) H)
      exact iff_of_false (fun hh => Hd hh hx) (fun hh => Hd hh hy)
  | succ n ih =>
    rintro ⟨l,k⟩ hl hx hy
    let r : Node := ⟨p.lev+n,k/2⟩
    have hs : cells ⟨l,k⟩ ⊆ r.cells := by
      have heq : (⟨l,k⟩:Node) = r.L ∨ (⟨l,k⟩:Node) = r.R := by
        simp only [r,L,R,Node.mk.injEq]
        change l = p.lev+(n+1) at hl
        omega
      rw [cells_split r]
      exact heq.elim (fun e => e ▸ subset_union_left) (fun e => e ▸ subset_union_right)
    exact ih r rfl (hs hx) (hs hy)

lemma atom_iff_coarse {M : ℕ} (p : Node) (h : p.lev ≤ M) {y : Grid M} {x : ℝ}
    (hx : x ∈ atom y) : x ∈ p.cells ↔ y ∈ p.block M :=
  coarse_const (q:=vertex y) h hx (pos_mem y)

lemma Hi_const {p q : Node} (h : p.lev+1 ≤ q.lev) {x y : ℝ} (hx : x ∈ q.cells)
    (hy : y ∈ q.cells) : p.Hi x = p.Hi y := by
  by_cases hp : x ∈ p.cells
  · rw [cells_split] at hp
    exact hp.elim (fun hh => (p.Hi_L hh).trans
        (p.Hi_L ((coarse_const (p:=p.L) h hx hy).mp hh)).symm)
      (fun hh => (p.Hi_R hh).trans (p.Hi_R ((coarse_const (p:=p.R) h hx hy).mp hh)).symm)
  · rw [p.Hi_out hp, p.Hi_out (mt (coarse_const (p:=p) (by omega) hy hx).mp hp)]

lemma Gi_const {p q : Node} (h : p.lev+2 ≤ q.lev) {x y : ℝ} (hx : x ∈ q.cells)
    (hy : y ∈ q.cells) : p.Gi x = p.Gi y := by
  rw [Gi_eq,Gi_eq, Hi_const (p:=p.L) h hx hy, Hi_const (p:=p.R) h hx hy]

def FinJump {M : ℕ} (p : Node) (F : Grid M → ℂ) (x : Grid M) :=
  p.Gi (pos x) • p.avg (fun y => p.Hi (pos y) • F y)

def FinShift {M : ℕ} (J : ℕ) (F : Grid M → ℂ) (x : Grid M) :=
  ∑ n ∈ Finset.range J, ∑ k ∈ Finset.range (2^n), FinJump ⟨n,k⟩ F x

def finMod {M : ℕ} (ρ : Grid M → ℝ) (u : Grid M) (x : Grid M) :=
  (ρ x : ℂ)*chi u x

def finGood {M : ℕ} (D : ℝ) (J : ℕ) (ρ : Grid M → ℝ) (x : Grid M) :=
  ∀ p : Node, p.valid → p.lev < J → x ∈ p.block M → p.avg ρ ≤ D

/-- Finite cut statement; asks for an L¹ majorant restricted to points where density steps stay
below threshold. There is no dependence on a frequency or depth cutoff in the constant. -/
def GridBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ j : ℕ in atTop, ∀ J : ℕ, ∀ᶠ M : ℕ in atTop,
    ∀ (ρ : Grid M → ℝ), (∀ x, 0 ≤ ρ x) → expU ρ ≤ 2 →
      (∀ x, ρ x ≤ Real.exp ((2:ℝ)^j)) →
    ∃ W : Grid M → ℝ, (∀ x, 0 ≤ W x) ∧ expU W ≤ C*(2:ℝ)^j ∧
      ∀ x : Grid M, finGood (((j:ℝ)+1)^3) J ρ x →
        ∀ u : Grid M, ‖FinShift J (finMod ρ u) x‖ ≤ W x

end
end FourierLLogL.Dyadic

end OAI
