import OAI.Combinatorics.HoneycombChords.PhysicalTiles

namespace OAI

/-!
# Finite honeycomb raster contractions

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition
open scoped BigOperators

abbrev Cell (W H : ℕ) := Fin W × Fin H
/-- Horizontal wires run west/east; vertical wires run south/north. The
extra endpoint in each coordinate is literal, not periodic boundary data. -/
abbrev GridWire (W H : ℕ) := (Fin (W+1) × Fin H) ⊕ (Fin W × Fin (H+1))
abbrev FullWire (W H : ℕ) := GridWire W H ⊕ Cell W H

def network (W H : ℕ) : TileNetwork (GridWire W H) (Cell W H) where
  west t := .inl (t.1.castSucc,t.2)
  east t := .inl (t.1.succ,t.2)
  south t := .inr (t.1,t.2.castSucc)
  north t := .inr (t.1,t.2.succ)

def wireEmbedding {W H : ℕ} : FullWire W H → Wire
  | .inl (.inl (i,j)) => (i.val,j.val,2)
  | .inl (.inr (i,j)) => (i.val,j.val,1)
  | .inr (i,j) => (i.val,j.val,0)

lemma wireEmbedding_injective (W H : ℕ) :
    Function.Injective (wireEmbedding (W:=W) (H:=H)) := by
  intro x y h
  cases x with
  | inl x => cases x with
    | inl x => cases y with
      | inl y => cases y with
        | inl y => simpa [wireEmbedding,Prod.ext_iff,Fin.ext_iff] using h
        | inr y => simp [wireEmbedding] at h
      | inr y => simp [wireEmbedding] at h
    | inr x => cases y with
      | inl y => cases y with
        | inl y => simp [wireEmbedding] at h
        | inr y => simpa [wireEmbedding,Prod.ext_iff,Fin.ext_iff] using h
      | inr y => simp [wireEmbedding] at h
  | inr x => cases y with
    | inl y => cases y <;> simp [wireEmbedding] at h
    | inr y => simpa [wireEmbedding,Prod.ext_iff,Fin.ext_iff] using h

noncomputable def spins {W H : ℕ} (σ : GridWire W H → Fin 3)
    (μ : Cell W H → Fin 3) : Wire → Fin 3 :=
  Function.extend wireEmbedding (Sum.elim σ μ) (fun _ => 1)

lemma spins_wire {W H : ℕ} (σ : GridWire W H → Fin 3) (μ : Cell W H → Fin 3)
    (w : FullWire W H) : spins σ μ (wireEmbedding w)=Sum.elim σ μ w := by
  exact (wireEmbedding_injective W H).extend_apply _ _ _

def cellCenter {W H : ℕ} (t : Cell W H) (b : Bool) : Center :=
  (t.1.val,t.2.val,b)

lemma cellCenter_injective (W H : ℕ) :
    Function.Injective (fun p : Cell W H × Bool => cellCenter p.1 p.2) := by
  intro x y h
  rcases x with ⟨⟨i,j⟩,b⟩
  rcases y with ⟨⟨i',j'⟩,b'⟩
  simpa [cellCenter,Prod.ext_iff,Fin.ext_iff,and_assoc] using h

noncomputable def domain (W H : ℕ) : Finset Center :=
  Finset.univ.image (fun p : Cell W H × Bool => cellCenter p.1 p.2)

lemma up_wires {W H : ℕ} (t : Cell W H) :
    incidentWire (cellCenter t true) 0 = wireEmbedding (.inr t) ∧
    incidentWire (cellCenter t true) 1 = wireEmbedding (.inl ((network W H).south t)) ∧
    incidentWire (cellCenter t true) 2 = wireEmbedding (.inl ((network W H).west t)) := by
  simp [incidentWire,cellCenter,wireEmbedding,network]

lemma down_wires {W H : ℕ} (t : Cell W H) :
    incidentWire (cellCenter t false) 0 = wireEmbedding (.inr t) ∧
    incidentWire (cellCenter t false) 1 = wireEmbedding (.inl ((network W H).north t)) ∧
    incidentWire (cellCenter t false) 2 = wireEmbedding (.inl ((network W H).east t)) := by
  simp [incidentWire,cellCenter,wireEmbedding,network,Nat.cast_add]

lemma up_centerTensor {W H : ℕ} (σ : GridWire W H → Fin 3) (μ : Cell W H → Fin 3)
    (t : Cell W H) : centerTensor (spins σ μ) (cellCenter t true) =
      upTensor (σ ((network W H).west t)) (σ ((network W H).south t)) (μ t) := by
  change upTensor _ _ _ = _
  rw [(up_wires t).1,(up_wires t).2.1,(up_wires t).2.2]
  simp only [spins_wire,Sum.elim_inl,Sum.elim_inr]

lemma down_centerTensor {W H : ℕ} (σ : GridWire W H → Fin 3) (μ : Cell W H → Fin 3)
    (t : Cell W H) : centerTensor (spins σ μ) (cellCenter t false) =
      downTensor (σ ((network W H).east t)) (σ ((network W H).north t)) (μ t) := by
  change downTensor _ _ _ = _
  rw [(down_wires t).1,(down_wires t).2.1,(down_wires t).2.2]
  simp only [spins_wire,Sum.elim_inl,Sum.elim_inr]

/-- Product of actual visited-center tensors on the literal rectangle. -/
lemma center_product_eq {W H : ℕ} (σ : GridWire W H → Fin 3) (μ : Cell W H → Fin 3) :
    centerProduct (domain W H) (spins σ μ) =
      ∏ t : Cell W H, upTensor (σ ((network W H).west t)) (σ ((network W H).south t)) (μ t) *
        downTensor (σ ((network W H).east t)) (σ ((network W H).north t)) (μ t) := by
  classical
  rw [centerProduct,domain,Finset.prod_image (fun x _ y _ h => cellCenter_injective W H h)]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro t ht
  simp only [Fintype.prod_bool,up_centerTensor,down_centerTensor]

/-- The source finite physical network contracts precisely to the actual
center tensors on the rectangle, with every internal middle wire summed. -/
theorem grid_physical_eq_centers (W H : ℕ) (σ : GridWire W H → Fin 3) :
    (network W H).physical σ = ∑ μ : Cell W H → Fin 3,
      centerProduct (domain W H) (spins σ μ) := by
  rw [physical_network_center_expansion]
  apply Finset.sum_congr rfl
  intro μ hμ
  exact (center_product_eq σ μ).symm

end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition
open scoped BigOperators Matrix

lemma sum_vectors_cons {α : Type*} [Fintype α] {n : ℕ}
    (F : (Fin (n+1) → α) → ℂ) :
    (∑ τ, F τ) = ∑ a : α, ∑ τ : Fin n → α, F (Fin.cons (α:=fun _=>α) a τ) := by
  rw [←(Fin.consEquiv (fun _ : Fin (n+1) => α)).sum_comp F,Fintype.sum_prod_type]
  rfl

/-- A finite matrix path expansion, used only for the actual physical
column kernels below. All intermediate states are summed once. -/
noncomputable def matrixPath {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (K : Fin n → Matrix α α ℂ) (a b : α) : ℂ :=
  ∑ τ : Fin n → α, if (Fin.cons (α:=fun _=>α) a τ) (Fin.last n)=b then
    ∏ j : Fin n, K j ((Fin.cons (α:=fun _=>α) a τ) j.castSucc) (τ j) else 0

lemma matrixPath_zero {α : Type*} [Fintype α] [DecidableEq α]
    (K : Fin 0 → Matrix α α ℂ) (a b : α) :
    matrixPath K a b = if a=b then 1 else 0 := by
  simp [matrixPath]

lemma matrixPath_succ {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (K : Fin (n+1) → Matrix α α ℂ) (a b : α) :
    matrixPath K a b = ∑ c, K 0 a c * matrixPath (fun j => K j.succ) c b := by
  unfold matrixPath
  rw [sum_vectors_cons]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ hτ
  have hl : (Fin.cons (α:=fun _=>α) a (Fin.cons (α:=fun _=>α) c τ)) (Fin.last (n+1)) =
      (Fin.cons (α:=fun _=>α) c τ) (Fin.last n) := rfl
  rw [hl]
  split_ifs with hb
  · rw [Fin.prod_univ_succ]
    congr 1
  · simp

theorem matrixPath_eq_prod {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (K : Fin n → Matrix α α ℂ) (a b : α) :
    matrixPath K a b = (List.ofFn K).prod a b := by
  induction n generalizing a b with
  | zero => simp [matrixPath_zero,Matrix.one_apply]
  | succ n ih =>
    rw [matrixPath_succ,List.ofFn_succ,List.prod_cons,Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro c hc
    rw [ih]

abbrev Column (H : ℕ) := Fin H → Fin 3

noncomputable def columnProduct {H : ℕ} (west east vertical : Column H) (north : Fin 3) : ℂ :=
  ∏ j : Fin H, Planar.sourceR (kappa:ℂ) (kappa^2:ℂ) (kappa^2:ℂ) (kappa^2:ℂ) 0
    ((Fin.snoc (α:=fun _=>Fin 3) vertical north) j.succ,west j) (vertical j,east j)

noncomputable def columnKernel (H : ℕ) (south north : Fin 3) : Matrix (Column H) (Column H) ℂ :=
  fun west east => ∑ vertical : Column H,
    if (Fin.snoc (α:=fun _=>Fin 3) vertical north) 0=south then
      columnProduct west east vertical north else 0

/-- Literal grid spins after fixing the west and north outer boundaries.
The remaining horizontal and vertical wires are genuine independent
coordinates, not redundant copies at the centers. -/
def spinsFromColumns {W H : ℕ} (west : Column H) (north : Fin W → Fin 3)
    (horizontal : Fin W → Column H) (vertical : Fin W → Column H) : GridWire W H → Fin 3
  | .inl (i,j) => (Fin.cons (α:=fun _=>Column H) west horizontal) i j
  | .inr (i,j) => (Fin.snoc (α:=fun _=>Fin 3) (vertical i) (north i)) j

lemma physical_columns {W H : ℕ} (west : Column H) (north : Fin W → Fin 3)
    (horizontal vertical : Fin W → Column H) :
    (network W H).physical (spinsFromColumns west north horizontal vertical) =
      ∏ i : Fin W, columnProduct ((Fin.cons (α:=fun _=>Column H) west horizontal) i.castSucc)
        (horizontal i) (vertical i) (north i) := by
  unfold TileNetwork.physical columnProduct
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  simp [network,spinsFromColumns]

/-- Actual finite grid tensor with all four boundary spin lists prescribed.
West and north are built into the parametrization; east and south are
imposed by their exact indicator, before performing any orientation sum. -/
noncomputable def prescribedPartition (W H : ℕ) (west east : Column H)
    (south north : Fin W → Fin 3) : ℂ :=
  ∑ horizontal : Fin W → Column H, ∑ vertical : Fin W → Column H,
    if (Fin.cons (α:=fun _=>Column H) west horizontal) (Fin.last W)=east ∧
        (∀ i, (Fin.snoc (α:=fun _=>Fin 3) (vertical i) (north i)) 0=south i) then
      (network W H).physical (spinsFromColumns west north horizontal vertical) else 0

lemma prescribedPartition_eq_matrixPath (W H : ℕ) (west east : Column H)
    (south north : Fin W → Fin 3) :
    prescribedPartition W H west east south north =
      matrixPath (fun i => columnKernel H (south i) (north i)) west east := by
  classical
  unfold prescribedPartition matrixPath
  apply Finset.sum_congr rfl
  intro horizontal hhorizontal
  by_cases he : (Fin.cons (α:=fun _=>Column H) west horizontal) (Fin.last W)=east
  · simp only [he,true_and,ite_true]
    simp_rw [physical_columns]
    unfold columnKernel
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro vertical hvertical
    rw [Fintype.prod_ite_zero]
    split_ifs <;> rfl
  · simp [he]

/-- The exact full finite rectangle contraction is the product of its
physical column matrices. Together with `grid_physical_eq_centers` this
connects the transfer ordering to the literal center tensors. -/
theorem prescribedPartition_eq_transfer (W H : ℕ) (west east : Column H)
    (south north : Fin W → Fin 3) :
    prescribedPartition W H west east south north =
      (List.ofFn (fun i => columnKernel H (south i) (north i))).prod west east := by
  rw [prescribedPartition_eq_matrixPath,matrixPath_eq_prod]

/-- The parametrization has exactly the actual spin assignments with the
west/north walls fixed; no geometric configurations are dropped. -/
def HasWestNorth {W H : ℕ} (west : Column H) (north : Fin W → Fin 3)
    (σ : GridWire W H → Fin 3) : Prop :=
  (∀ j, σ (.inl (0,j))=west j) ∧ (∀ i, σ (.inr (i,Fin.last H))=north i)

lemma spinsFromColumns_boundary {W H : ℕ} (west : Column H) (north : Fin W → Fin 3)
    (horizontal vertical : Fin W → Column H) :
    HasWestNorth west north (spinsFromColumns west north horizontal vertical) := by
  constructor <;> intro i <;> simp [spinsFromColumns]

def gridSpinsEquiv {W H : ℕ} (west : Column H) (north : Fin W → Fin 3) :
    ((Fin W → Column H) × (Fin W → Column H)) ≃
      {σ : GridWire W H → Fin 3 // HasWestNorth west north σ} where
  toFun p := ⟨spinsFromColumns west north p.1 p.2,
    spinsFromColumns_boundary west north p.1 p.2⟩
  invFun σ := (fun i j => σ.val (.inl (i.succ,j)),
    fun i j => σ.val (.inr (i,j.castSucc)))
  left_inv p := by
    rcases p with ⟨horizontal,vertical⟩
    ext i j <;> simp [spinsFromColumns]
  right_inv σ := by
    apply Subtype.ext
    funext wire
    cases wire with
    | inl p =>
      rcases p with ⟨i,j⟩
      cases i using Fin.cases with
      | zero => simpa [spinsFromColumns] using (σ.property.1 j).symm
      | succ i => simp [spinsFromColumns]
    | inr p =>
      rcases p with ⟨i,j⟩
      cases j using Fin.lastCases with
      | last => simpa [spinsFromColumns] using (σ.property.2 i).symm
      | cast j => simp [spinsFromColumns]

noncomputable instance fixedGridSpinsFintype {W H : ℕ} (west : Column H) (north : Fin W → Fin 3) :
    Fintype {σ : GridWire W H → Fin 3 // HasWestNorth west north σ} :=
  Fintype.ofEquiv ((Fin W → Column H) × (Fin W → Column H)) (gridSpinsEquiv west north)

/-- Exact literal finite-network expression for the prescribed partition. -/
theorem prescribedPartition_eq_grid_sum (W H : ℕ) (west east : Column H)
    (south north : Fin W → Fin 3) :
    prescribedPartition W H west east south north =
      ∑ σ : {σ : GridWire W H → Fin 3 // HasWestNorth west north σ},
        if (∀ j, σ.val (.inl (Fin.last W,j))=east j) ∧
            (∀ i, σ.val (.inr (i,0))=south i) then
          (network W H).physical σ.val else 0 := by
  classical
  rw [←(gridSpinsEquiv west north).sum_comp]
  rw [Fintype.sum_prod_type]
  unfold prescribedPartition
  apply Finset.sum_congr rfl
  intro horizontal hh
  apply Finset.sum_congr rfl
  intro vertical hv
  change (if (Fin.cons (α:=fun _=>Column H) west horizontal) (Fin.last W)=east ∧
      (∀ i, (Fin.snoc (α:=fun _=>Fin 3) (vertical i) (north i)) 0=south i) then
      (network W H).physical (spinsFromColumns west north horizontal vertical) else 0) =
    (if (∀ j, (Fin.cons (α:=fun _=>Column H) west horizontal) (Fin.last W) j=east j) ∧
      (∀ i, (Fin.snoc (α:=fun _=>Fin 3) (vertical i) (north i)) 0=south i) then
      (network W H).physical (spinsFromColumns west north horizontal vertical) else 0)
  congr 1
  exact propext (and_congr funext_iff Iff.rfl)

end CriticalHoneycomb.Transfer.RasterGrid

end OAI
