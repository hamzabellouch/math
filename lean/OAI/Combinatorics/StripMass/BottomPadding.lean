import Mathlib
import OAI.Combinatorics.StripMass.PairingDiagrams

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open Finset
theorem realizes_padBottom_iff {n : ℕ} (p q : Pairing n) (t : Configuration n) :
    Realizes p.padBottom q.padBottom t.padBottom ↔ Realizes p q t := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; simpa using h.west i.succ
    · intro i; simpa using h.east i.succ
    · intro i hi hocc
      have hg := h.glued 0 i.succ (by simpa using hi)
      exact Tile.vacant_not_occupied 3 (hg.mpr hocc)
    · intro i hi
      exact h.north i.succ (by change i.val+1+1 = n+1; omega)
    · intro i j hij
      exact h.glued i.succ j.succ (by simpa using hij)
    · intro v w hvw
      obtain ⟨j,hj,hr⟩ := h.no_loop _ _ ((wiring_padBottom_iff p t v w).2 hvw)
      induction j using Fin.cases with
      | zero => exact (q.padBottom_not_occupied_zero hj).elim
      | succ j =>
          exact ⟨j,(q.padBottom_occupied_succ j).1 hj, (reach_padBottom_iff p t v (j,2)).1 hr⟩
    · intro i j hij
      exact (q.padBottom_adj_succ i j).symm.trans <|
        (h.output i.succ j.succ (fun h' => hij (Fin.succ_injective n h'))).trans
          (reach_padBottom_iff p t (i,2) (j,2))
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => simp
      | succ i => simpa using h.west i
    · intro i
      induction i using Fin.cases with
      | zero => simp
      | succ i => simpa using h.east i
    · intro i hi
      have : i = 0 := Fin.ext hi
      subst i; simp
    · intro i hi
      induction i using Fin.cases with
      | zero => simp
      | succ i => exact h.north i (by change i.val+1+1 = n+1 at hi; omega)
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
          induction j using Fin.cases with
          | zero => simp only [Fin.val_zero] at hij; omega
          | succ j =>
              have hj : j.val = 0 := by simpa using hij.symm
              simp [h.south j hj]
      | succ i =>
          induction j using Fin.cases with
          | zero => simp only [Fin.val_zero, Fin.val_succ] at hij; omega
          | succ j => exact h.glued i j (by simpa using hij)
    · rintro ⟨i,a⟩ ⟨j,b⟩ hij
      induction i using Fin.cases with
      | zero => exact (wiring_padBottom_zero p t a _ hij).elim
      | succ i =>
          induction j using Fin.cases with
          | zero => exact (wiring_padBottom_zero_right p t _ b hij).elim
          | succ j =>
              obtain ⟨k,hk,hr⟩ := h.no_loop _ _ ((wiring_padBottom_iff p t (i,a) (j,b)).1 hij)
              exact ⟨k.succ,(q.padBottom_occupied_succ k).2 hk,
                (reach_padBottom_iff p t (i,a) (k,2)).2 hr⟩
    · intro i j hij
      induction i using Fin.cases with
      | zero => simp [hij.symm]
      | succ i =>
          induction j using Fin.cases with
          | zero => simp
          | succ j =>
              exact (Pairing.padBottom_adj_succ q i j).trans <|
                (h.output i j (fun h' => hij (congrArg Fin.succ h'))).trans
                  (reach_padBottom_iff p t (i,2) (j,2)).symm

theorem Tile.vacant_of_three (t : Tile) (h₀ : ¬ t.Occupied 0)
    (h₁ : ¬ t.Occupied 1) (h₂ : ¬ t.Occupied 2) : t = .vacant := by
  cases t <;> simp_all [Tile.Occupied, Tile.Adj, Tile.edges]

theorem Realizes.bottom_vacant {n : ℕ} {p q : Pairing n} {t : Configuration (n+1)}
    (h : Realizes p.padBottom q.padBottom t) : t 0 = .vacant :=
  Tile.vacant_of_three _ (h.south 0 rfl)
    (fun hc => p.padBottom_not_occupied_zero ((h.west 0).mp hc))
    (fun hc => q.padBottom_not_occupied_zero ((h.east 0).mp hc))

theorem realizes_cons_bottom_iff {n : ℕ} (p q : Pairing n)
    (a : Tile) (t : Configuration n) :
    Realizes p.padBottom q.padBottom (Fin.cons a t) ↔
      a = .vacant ∧ Realizes p q t := by
  constructor
  · intro h
    have ha : a = .vacant := h.bottom_vacant
    subst a
    exact ⟨rfl, (realizes_padBottom_iff p q t).mp h⟩
  · rintro ⟨rfl, h⟩
    exact (realizes_padBottom_iff p q t).mpr h

 
theorem column_padBottom {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin (n+1) → Weights 𝕜) (p q : Pairing n) :
    column w q.padBottom p.padBottom = column (fun i => w i.succ) q p := by
  classical
  unfold column
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Tile))
    (fun tt : Tile × Configuration n =>
      if Realizes p.padBottom q.padBottom (Fin.cons tt.1 tt.2)
      then ∏ i : Fin (n+1), (w i).tile ((Fin.cons tt.1 tt.2 : Configuration (n+1)) i) else 0)
    _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [realizes_cons_bottom_iff]
  rw [Finset.sum_eq_single Tile.vacant]
  · apply Finset.sum_congr rfl
    intro t _
    simp [Fin.prod_univ_succ, Weights.tile]
  · intro a ha hav
    simp [hav]
  · simp

theorem Tile.identity_zero_of_south_vacant_east_occupied
    {𝕜 : Type*} [Zero 𝕜] [One 𝕜] (a : Tile) (hs : ¬a.Occupied 0)
    (he : a.Occupied 2) : (identityWeights : Weights 𝕜).tile a = 0 := by
  cases a <;> simp_all [Tile.Occupied, Tile.Adj, Tile.edges,
    identityWeights, Weights.tile]

theorem Tile.deletion_zero_of_south_vacant_west_occupied
    {𝕜 : Type*} [Zero 𝕜] [One 𝕜] (a : Tile) (hs : ¬a.Occupied 0)
    (hw : a.Occupied 1) : (deletionWeights : Weights 𝕜).tile a = 0 := by
  cases a <;> simp_all [Tile.Occupied, Tile.Adj, Tile.edges,
    deletionWeights, Weights.tile]

 
theorem column_identity_bottom_row {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin (n+1) → Weights 𝕜) (hw : w 0 = identityWeights)
    (p q : Pairing (n+1)) (hq : q.Occupied 0) : column w q p = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro t ht
  split_ifs with h
  · apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (n+1)))
    rw [hw]
    exact Tile.identity_zero_of_south_vacant_east_occupied _
      (h.south 0 rfl) ((h.east 0).mpr hq)
  · rfl

 
theorem column_deletion_bottom_col {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin (n+1) → Weights 𝕜) (hw : w 0 = deletionWeights)
    (p q : Pairing (n+1)) (hp : p.Occupied 0) : column w q p = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro t ht
  split_ifs with h
  · apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (n+1)))
    rw [hw]
    exact Tile.deletion_zero_of_south_vacant_west_occupied _
      (h.south 0 rfl) ((h.west 0).mpr hp)
  · rfl

namespace Pairing

def nonemptyPadBottom {n : ℕ} (p : NonemptyPairing n) : NonemptyPairing (n+1) :=
  ⟨p.val.padBottom, fun h => p.property ((padBottom_eq_empty _).mp h)⟩

def nonemptyBottomVacantEquiv (n : ℕ) :
    NonemptyPairing n ≃ {p : NonemptyPairing (n+1) // ¬p.val.Occupied 0} where
  toFun p := ⟨nonemptyPadBottom p, p.val.padBottom_not_occupied_zero⟩
  invFun p := ⟨p.val.val.restrict (Fin.succOrderEmb n), by
    intro he
    have hp := padBottom_restrict p.val.val p.property
    rw [he, padBottom_empty] at hp
    exact p.val.property hp.symm⟩
  left_inv p := Subtype.ext (restrict_map _ _)
  right_inv p := Subtype.ext (Subtype.ext (padBottom_restrict _ p.property))

abbrev BottomOccupiedNonempty (n : ℕ) :=
  {p : NonemptyPairing (n+1) // ¬¬p.val.Occupied 0}

def nonemptyBottomSplit (n : ℕ) :
    NonemptyPairing n ⊕ BottomOccupiedNonempty n ≃ NonemptyPairing (n+1) := by
  classical
  exact (Equiv.sumCongr (nonemptyBottomVacantEquiv n) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun p : NonemptyPairing (n+1) => ¬p.val.Occupied 0))

@[simp] theorem nonemptyBottomSplit_inl {n : ℕ} (p : NonemptyPairing n) :
    nonemptyBottomSplit n (.inl p) = nonemptyPadBottom p := rfl

@[simp] theorem nonemptyBottomSplit_inr {n : ℕ} (p : BottomOccupiedNonempty n) :
    nonemptyBottomSplit n (.inr p) = p.val := rfl

end Pairing

 
theorem det_one_sub_zero_rows {𝕜 α β : Type*} [CommRing 𝕜]
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (M : Matrix (α ⊕ β) (α ⊕ β) 𝕜)
    (h : ∀ i j, M (.inr i) j = 0) :
    (1-M).det = (1-M.toBlocks₁₁).det := by
  have hm : 1-M = Matrix.fromBlocks (1-M.toBlocks₁₁) (-M.toBlocks₁₂) 0 1 := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.one_apply, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂, h]
  rw [hm, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

 
theorem det_one_sub_zero_cols {𝕜 α β : Type*} [CommRing 𝕜]
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (M : Matrix (α ⊕ β) (α ⊕ β) 𝕜)
    (h : ∀ i j, M i (.inr j) = 0) :
    (1-M).det = (1-M.toBlocks₁₁).det := by
  have hm : 1-M = Matrix.fromBlocks (1-M.toBlocks₁₁) 0 (-M.toBlocks₂₁) 1 := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.one_apply, Matrix.toBlocks₁₁,
      Matrix.toBlocks₂₁, h]
  rw [hm, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]

 
theorem det_flat_bottom {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin (n+1) → Weights 𝕜)
    (hw : w 0 = identityWeights ∨ w 0 = deletionWeights) :
    (1-restrictedColumn w).det = (1-restrictedColumn (fun i => w i.succ)).det := by
  classical
  let e := Pairing.nonemptyBottomSplit n
  let M := (restrictedColumn w).submatrix e e
  have hblock : M.toBlocks₁₁ = restrictedColumn (fun i => w i.succ) := by
    ext q p
    exact column_padBottom w p.val q.val
  have hdet : (1-restrictedColumn w).det = (1-M).det := by
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    simp only [Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_one_equiv]
    rfl
  rw [hdet]
  rcases hw with hi | hd
  · rw [det_one_sub_zero_rows M, hblock]
    intro q p
    exact column_identity_bottom_row w hi (e p).val q.val.val (not_not.mp q.property)
  · rw [det_one_sub_zero_cols M, hblock]
    intro q p
    exact column_deletion_bottom_col w hd p.val.val (e q).val (not_not.mp p.property)

namespace Pairing

 
def padTop {n : ℕ} (p : Pairing n) : Pairing (n+1) := p.map Fin.castSuccOrderEmb

@[simp] theorem padTop_adj_castSucc {n : ℕ} (p : Pairing n) (i j : Fin n) :
    p.padTop.Adj i.castSucc j.castSucc ↔ p.Adj i j := map_adj_image _ _ _ _

@[simp] theorem padTop_not_adj_last {n : ℕ} (p : Pairing n) (j : Fin (n+1)) :
    ¬ p.padTop.Adj (Fin.last n) j := by
  classical
  simp [padTop, map, Adj, Finset.mem_map, Fin.castSuccOrderEmb]

@[simp] theorem padTop_not_adj_last' {n : ℕ} (p : Pairing n) (j : Fin (n+1)) :
    ¬ p.padTop.Adj j (Fin.last n) := by
  classical
  simp [padTop, map, Adj, Finset.mem_map, Fin.castSuccOrderEmb]

@[simp] theorem padTop_not_occupied_last {n : ℕ} (p : Pairing n) :
    ¬ p.padTop.Occupied (Fin.last n) := by simp [Occupied]

@[simp] theorem padTop_occupied_castSucc {n : ℕ} (p : Pairing n) (i : Fin n) :
    p.padTop.Occupied i.castSucc ↔ p.Occupied i := by
  simp only [Occupied, Fin.exists_iff_castSucc, padTop_adj_castSucc,
    padTop_not_adj_last', false_or]

@[simp] theorem padTop_empty {n : ℕ} : (empty n).padTop = empty (n+1) := by
  classical
  apply Subtype.ext
  simp [padTop, map, empty]

@[simp] theorem padTop_eq_empty {n : ℕ} (p : Pairing n) :
    p.padTop = empty (n+1) ↔ p = empty n := by
  simp only [eq_empty_iff, Fin.forall_iff_castSucc, padTop_not_occupied_last,
    padTop_occupied_castSucc, not_false_eq_true, true_and]

theorem padTop_restrict {n : ℕ} (p : Pairing (n+1)) (hp : ¬p.Occupied (Fin.last n)) :
    (p.restrict Fin.castSuccOrderEmb).padTop = p := by
  classical
  apply Subtype.ext
  ext e
  rcases e with ⟨i,j⟩
  induction i using Fin.lastCases with
  | last =>
      have hm : (Fin.last n,j) ∉ p.val := fun h => hp ⟨j, Or.inl h⟩
      simp [padTop, map, Finset.mem_map, Fin.castSuccOrderEmb, hm]
  | cast i =>
      induction j using Fin.lastCases with
      | last =>
          have hm : (i.castSucc,Fin.last n) ∉ p.val := fun h => hp ⟨i.castSucc, Or.inr h⟩
          simp [padTop, map, Finset.mem_map, Fin.castSuccOrderEmb, hm]
      | cast j => simp [padTop, map, restrict, Finset.mem_map, Fin.castSuccOrderEmb]

end Pairing

namespace Configuration

def padTop {n : ℕ} (t : Configuration n) : Configuration (n+1) := Fin.snoc t .vacant

@[simp] theorem padTop_last {n : ℕ} (t : Configuration n) :
    t.padTop (Fin.last n) = .vacant := Fin.snoc_last _ _
@[simp] theorem padTop_castSucc {n : ℕ} (t : Configuration n) (i : Fin n) :
    t.padTop i.castSucc = t i := Fin.snoc_castSucc _ _ _

end Configuration

def vertexCastSucc {n : ℕ} (v : Vertex n) : Vertex (n+1) := (v.1.castSucc,v.2)

theorem vertexCastSucc_injective {n : ℕ} : Function.Injective (@vertexCastSucc n) := by
  intro v w h
  apply Prod.ext
  · exact Fin.castSucc_injective n (congrArg (fun v : Vertex (n+1) => v.1) h)
  · exact congrArg (fun v : Vertex (n+1) => v.2) h

 
theorem wiring_padTop_last {n : ℕ} (p : Pairing n) (t : Configuration n)
    (ht : ∀ i, i.val+1=n → ¬(t i).Occupied 3)
    (a : Fin 4) (w : Vertex (n+1)) :
    ¬Wiring p.padTop t.padTop (Fin.last n,a) w := by
  intro h
  rcases h with ⟨hw,hh⟩ | hh | ⟨_,_,hv,_⟩ | ⟨_,_,hv,ho⟩
  · simp at hh
  · exact p.padTop_not_adj_last w.1 hh.2.2
  · have hw := w.1.isLt
    change n+1 = w.1.val at hv
    omega
  · rcases w with ⟨j,b⟩
    induction j using Fin.lastCases with
    | last => simp at ho
    | cast j => exact ht j hv (by simpa using ho)

theorem wiring_padTop_last_right {n : ℕ} (p : Pairing n) (t : Configuration n)
    (ht : ∀ i, i.val+1=n → ¬(t i).Occupied 3)
    (v : Vertex (n+1)) (b : Fin 4) :
    ¬Wiring p.padTop t.padTop v (Fin.last n,b) :=
  fun h => wiring_padTop_last p t ht b v (wiring_symm h)

@[simp] theorem wiring_padTop_iff {n : ℕ} (p : Pairing n) (t : Configuration n)
    (v w : Vertex n) :
    Wiring p.padTop t.padTop (vertexCastSucc v) (vertexCastSucc w) ↔ Wiring p t v w := by
  simp [Wiring, vertexCastSucc]

theorem reach_padTop_image {n : ℕ} (p : Pairing n) (t : Configuration n)
    (ht : ∀ i, i.val+1=n → ¬(t i).Occupied 3)
    {v : Vertex n} {w : Vertex (n+1)} (h : Reach p.padTop t.padTop (vertexCastSucc v) w) :
    ∃ z, w = vertexCastSucc z ∧ Reach p t v z := by
  induction h with
  | refl => exact ⟨v,rfl,Relation.ReflTransGen.refl⟩
  | @tail w z _ hwz ih =>
    obtain ⟨w',rfl,hw'⟩ := ih
    rcases z with ⟨j,b⟩
    induction j using Fin.lastCases with
    | last => exact (wiring_padTop_last_right p t ht _ b hwz).elim
    | cast j =>
      exact ⟨(j,b),rfl,hw'.tail ((wiring_padTop_iff p t _ _).1 hwz)⟩

theorem reach_padTop_iff {n : ℕ} (p : Pairing n) (t : Configuration n)
    (ht : ∀ i, i.val+1=n → ¬(t i).Occupied 3) (v w : Vertex n) :
    Reach p.padTop t.padTop (vertexCastSucc v) (vertexCastSucc w) ↔ Reach p t v w := by
  constructor
  · intro h
    obtain ⟨z,hz,hz'⟩ := reach_padTop_image p t ht h
    have := vertexCastSucc_injective hz
    simpa only [this] using hz'
  · exact Relation.ReflTransGen.lift vertexCastSucc
      (fun a b h => (wiring_padTop_iff p t a b).2 h) _ _

theorem reach_padTop_last_iff {n : ℕ} (p : Pairing n) (t : Configuration n)
    (ht : ∀ i, i.val+1=n → ¬(t i).Occupied 3) (a : Fin 4) (w : Vertex (n+1)) :
    Reach p.padTop t.padTop (Fin.last n,a) w ↔ w = (Fin.last n,a) :=
  Relation.reflTransGen_iff_eq (wiring_padTop_last p t ht a)

theorem reach_padTop_last_right_iff {n : ℕ} (p : Pairing n) (t : Configuration n)
    (ht : ∀ i, i.val+1=n → ¬(t i).Occupied 3) (v : Vertex (n+1)) (b : Fin 4) :
    Reach p.padTop t.padTop v (Fin.last n,b) ↔ v = (Fin.last n,b) := by
  constructor
  · intro h
    exact (reach_padTop_last_iff p t ht b v).1 (reach_symm h)
  · rintro rfl; exact Relation.ReflTransGen.refl

 
end
end CriticalStrip.Diagram

end OAI
