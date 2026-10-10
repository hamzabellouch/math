import Mathlib
import OAI.Combinatorics.StripMass.BottomPadding

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open Finset
theorem realizes_padTop_iff {n : ℕ} (p q : Pairing n) (t : Configuration n) :
    Realizes p.padTop q.padTop t.padTop ↔ Realizes p q t := by
  constructor
  · intro h
    have ht : ∀ i, i.val+1=n → ¬(t i).Occupied 3 := by
      intro i hi ho
      have hg := h.glued i.castSucc (Fin.last n) hi
      exact Tile.vacant_not_occupied 0 (by simpa using hg.mp (by simpa using ho))
    refine ⟨?_, ?_, ?_, ht, ?_, ?_, ?_⟩
    · intro i; simpa using h.west i.castSucc
    · intro i; simpa using h.east i.castSucc
    · intro i hi
      simpa using h.south i.castSucc hi
    · intro i j hij
      simpa using h.glued i.castSucc j.castSucc hij
    · intro v w hvw
      obtain ⟨j,hj,hr⟩ := h.no_loop _ _ ((wiring_padTop_iff p t v w).2 hvw)
      induction j using Fin.lastCases with
      | last => exact (q.padTop_not_occupied_last hj).elim
      | cast j =>
          exact ⟨j,(q.padTop_occupied_castSucc j).1 hj,
            (reach_padTop_iff p t ht v (j,2)).1 hr⟩
    · intro i j hij
      exact (q.padTop_adj_castSucc i j).symm.trans <|
        (h.output i.castSucc j.castSucc (fun h' => hij (Fin.castSucc_injective n h'))).trans
          (reach_padTop_iff p t ht (i,2) (j,2))
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa using h.west i
    · intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa using h.east i
    · intro i hi
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa using h.south i hi
    · intro i hi
      have he : i = Fin.last n := Fin.ext (by change i.val = n; change i.val+1=n+1 at hi; omega)
      subst i; simp
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
          have hj := j.isLt
          change n+1=j.val at hij
          omega
      | cast i =>
          induction j using Fin.lastCases with
          | last => simp [h.north i hij]
          | cast j => simpa using h.glued i j hij
    · rintro ⟨i,a⟩ ⟨j,b⟩ hij
      induction i using Fin.lastCases with
      | last => exact (wiring_padTop_last p t h.north a _ hij).elim
      | cast i =>
          induction j using Fin.lastCases with
          | last => exact (wiring_padTop_last_right p t h.north _ b hij).elim
          | cast j =>
              obtain ⟨k,hk,hr⟩ := h.no_loop _ _ ((wiring_padTop_iff p t (i,a) (j,b)).1 hij)
              exact ⟨k.castSucc,(q.padTop_occupied_castSucc k).2 hk,
                (reach_padTop_iff p t h.north (i,a) (k,2)).2 hr⟩
    · intro i j hij
      induction i using Fin.lastCases with
      | last => simp [reach_padTop_last_iff p t h.north, hij.symm]
      | cast i =>
          induction j using Fin.lastCases with
          | last => simp [reach_padTop_last_right_iff p t h.north]
          | cast j =>
              exact (Pairing.padTop_adj_castSucc q i j).trans <|
                (h.output i j (fun h' => hij (congrArg Fin.castSucc h'))).trans
                  (reach_padTop_iff p t h.north (i,2) (j,2)).symm

theorem Tile.vacant_of_three_top (t : Tile) (h₃ : ¬ t.Occupied 3)
    (h₁ : ¬ t.Occupied 1) (h₂ : ¬ t.Occupied 2) : t = .vacant := by
  cases t <;> simp_all [Tile.Occupied, Tile.Adj, Tile.edges]

theorem Realizes.top_vacant {n : ℕ} {p q : Pairing n} {t : Configuration (n+1)}
    (h : Realizes p.padTop q.padTop t) : t (Fin.last n) = .vacant :=
  Tile.vacant_of_three_top _ (h.north (Fin.last n) rfl)
    (fun hc => p.padTop_not_occupied_last ((h.west (Fin.last n)).mp hc))
    (fun hc => q.padTop_not_occupied_last ((h.east (Fin.last n)).mp hc))

theorem realizes_snoc_top_iff {n : ℕ} (p q : Pairing n)
    (a : Tile) (t : Configuration n) :
    Realizes p.padTop q.padTop (Fin.snoc t a) ↔
      a = .vacant ∧ Realizes p q t := by
  constructor
  · intro h
    have ha : a = .vacant := by simpa using h.top_vacant
    subst a
    exact ⟨rfl, (realizes_padTop_iff p q t).mp h⟩
  · rintro ⟨rfl, h⟩
    exact (realizes_padTop_iff p q t).mpr h

theorem column_padTop {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin (n+1) → Weights 𝕜) (p q : Pairing n) :
    column w q.padTop p.padTop = column (fun i => w i.castSucc) q p := by
  classical
  unfold column
  rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n+1) => Tile))
    (fun tt : Tile × Configuration n =>
      if Realizes p.padTop q.padTop (Fin.snoc tt.2 tt.1)
      then ∏ i : Fin (n+1), (w i).tile ((Fin.snoc tt.2 tt.1 : Configuration (n+1)) i) else 0)
    _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [realizes_snoc_top_iff]
  rw [Finset.sum_eq_single Tile.vacant]
  · apply Finset.sum_congr rfl
    intro t _
    simp [Fin.prod_univ_castSucc, Weights.tile]
  · intro a ha hav
    simp [hav]
  · simp

 
theorem Tile.deletion_zero_of_north_vacant_east_occupied
    {𝕜 : Type*} [Zero 𝕜] [One 𝕜] (a : Tile) (hn : ¬a.Occupied 3)
    (he : a.Occupied 2) : (deletionWeights : Weights 𝕜).tile a = 0 := by
  cases a <;> simp_all [Tile.Occupied, Tile.Adj, Tile.edges,
    deletionWeights, Weights.tile]

theorem Tile.identity_zero_of_north_vacant_west_occupied
    {𝕜 : Type*} [Zero 𝕜] [One 𝕜] (a : Tile) (hn : ¬a.Occupied 3)
    (hw : a.Occupied 1) : (identityWeights : Weights 𝕜).tile a = 0 := by
  cases a <;> simp_all [Tile.Occupied, Tile.Adj, Tile.edges,
    identityWeights, Weights.tile]

theorem column_deletion_top_row {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin (n+1) → Weights 𝕜) (hw : w (Fin.last n) = deletionWeights)
    (p q : Pairing (n+1)) (hq : q.Occupied (Fin.last n)) : column w q p = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro t ht
  split_ifs with h
  · apply Finset.prod_eq_zero (Finset.mem_univ (Fin.last n))
    rw [hw]
    exact Tile.deletion_zero_of_north_vacant_east_occupied _
      (h.north (Fin.last n) rfl) ((h.east (Fin.last n)).mpr hq)
  · rfl

theorem column_identity_top_col {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin (n+1) → Weights 𝕜) (hw : w (Fin.last n) = identityWeights)
    (p q : Pairing (n+1)) (hp : p.Occupied (Fin.last n)) : column w q p = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro t ht
  split_ifs with h
  · apply Finset.prod_eq_zero (Finset.mem_univ (Fin.last n))
    rw [hw]
    exact Tile.identity_zero_of_north_vacant_west_occupied _
      (h.north (Fin.last n) rfl) ((h.west (Fin.last n)).mpr hp)
  · rfl

namespace Pairing

def nonemptyPadTop {n : ℕ} (p : NonemptyPairing n) : NonemptyPairing (n+1) :=
  ⟨p.val.padTop, fun h => p.property ((padTop_eq_empty _).mp h)⟩

def nonemptyTopVacantEquiv (n : ℕ) :
    NonemptyPairing n ≃ {p : NonemptyPairing (n+1) // ¬p.val.Occupied (Fin.last n)} where
  toFun p := ⟨nonemptyPadTop p, p.val.padTop_not_occupied_last⟩
  invFun p := ⟨p.val.val.restrict Fin.castSuccOrderEmb, by
    intro he
    have hp := padTop_restrict p.val.val p.property
    rw [he, padTop_empty] at hp
    exact p.val.property hp.symm⟩
  left_inv p := Subtype.ext (restrict_map _ _)
  right_inv p := Subtype.ext (Subtype.ext (padTop_restrict _ p.property))

abbrev TopOccupiedNonempty (n : ℕ) :=
  {p : NonemptyPairing (n+1) // ¬¬p.val.Occupied (Fin.last n)}

def nonemptyTopSplit (n : ℕ) :
    NonemptyPairing n ⊕ TopOccupiedNonempty n ≃ NonemptyPairing (n+1) := by
  classical
  exact (Equiv.sumCongr (nonemptyTopVacantEquiv n) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun p : NonemptyPairing (n+1) => ¬p.val.Occupied (Fin.last n)))

@[simp] theorem nonemptyTopSplit_inl {n : ℕ} (p : NonemptyPairing n) :
    nonemptyTopSplit n (.inl p) = nonemptyPadTop p := rfl

@[simp] theorem nonemptyTopSplit_inr {n : ℕ} (p : TopOccupiedNonempty n) :
    nonemptyTopSplit n (.inr p) = p.val := rfl

end Pairing

 
theorem det_flat_top {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin (n+1) → Weights 𝕜)
    (hw : w (Fin.last n) = identityWeights ∨ w (Fin.last n) = deletionWeights) :
    (1-restrictedColumn w).det = (1-restrictedColumn (fun i => w i.castSucc)).det := by
  classical
  let e := Pairing.nonemptyTopSplit n
  let M := (restrictedColumn w).submatrix e e
  have hblock : M.toBlocks₁₁ = restrictedColumn (fun i => w i.castSucc) := by
    ext q p
    exact column_padTop w p.val q.val
  have hdet : (1-restrictedColumn w).det = (1-M).det := by
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    simp only [Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_one_equiv]
    rfl
  rw [hdet]
  rcases hw with hi | hd
  · rw [det_one_sub_zero_cols M, hblock]
    intro q p
    exact column_identity_top_col w hi p.val.val (e q).val (not_not.mp p.property)
  · rw [det_one_sub_zero_rows M, hblock]
    intro q p
    exact column_deletion_top_row w hd (e p).val q.val.val (not_not.mp q.property)

 
theorem Pairing.eq_empty_of_le_one {n : ℕ} (hn : n ≤ 1) (p : Pairing n) :
    p = empty n := by
  apply Subtype.ext
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have hlt := p.property.1 e he
  have hi := e.1.isLt
  have hj := e.2.isLt
  change e.1.val < e.2.val at hlt
  omega

theorem det_column_le_one {𝕜 : Type*} [CommRing 𝕜] {n : ℕ} (hn : n ≤ 1)
    (w : Fin n → Weights 𝕜) : (1-restrictedColumn w).det = 1 := by
  let : IsEmpty (NonemptyPairing n) := ⟨fun p => p.property (p.val.eq_empty_of_le_one hn)⟩
  exact Matrix.det_isEmpty

def Weights.IsFlat {𝕜 : Type*} [Zero 𝕜] [One 𝕜] (w : Weights 𝕜) : Prop :=
  w = identityWeights ∨ w = deletionWeights

 

theorem det_one_nonflat {𝕜 : Type*} [CommRing 𝕜] (n : ℕ)
    (w : Fin n → Weights 𝕜)
    (hw : ∀ i j, ¬(w i).IsFlat → ¬(w j).IsFlat → i = j) :
    (1-restrictedColumn w).det = 1 := by
  classical
  induction n with
  | zero => exact det_column_le_one (by omega) w
  | succ n ih =>
      by_cases hn : n = 0
      · subst n; exact det_column_le_one (by omega) w
      by_cases hb : (w 0).IsFlat
      · rw [det_flat_bottom w hb]
        apply ih
        intro i j hi hj
        exact Fin.succ_injective n (hw i.succ j.succ hi hj)
      · have ht : (w (Fin.last n)).IsFlat := by
          by_contra ht
          have he := congrArg Fin.val (hw 0 (Fin.last n) hb ht)
          exact hn (by simpa using he.symm)
        rw [det_flat_top w ht]
        apply ih
        intro i j hi hj
        exact Fin.castSucc_injective n (hw i.castSucc j.castSucc hi hj)

theorem vacuumRegular_one_nonflat {𝕜 : Type*} [Field 𝕜] {n : ℕ}
    (w : Fin n → Weights 𝕜) (r : Fin n)
    (hw : ∀ i, i ≠ r → (w i).IsFlat) : VacuumRegular w := by
  unfold VacuumRegular
  rw [det_one_nonflat n w]
  · exact one_ne_zero
  · intro i j hi hj
    have hir : i = r := by by_contra h; exact hi (hw i h)
    have hjr : j = r := by by_contra h; exact hj (hw j h)
    exact hir.trans hjr.symm

theorem inlinePrivate0_sin_two_lambda : Real.sin (2*lambda) = Real.cos (2*lambda) := by
  rw [← Real.sin_pi_div_two_sub]
  congr 1
  unfold lambda
  ring

theorem inlinePrivate0_sin_two_lambda_pos : 0 < Real.sin (2*lambda) := by
  apply Real.sin_pos_of_pos_of_lt_pi <;> unfold lambda <;> linarith [Real.pi_pos]

theorem inlinePrivate0_sin_three_lambda_pos : 0 < Real.sin (3*lambda) := by
  apply Real.sin_pos_of_pos_of_lt_pi <;> unfold lambda <;> linarith [Real.pi_pos]

 
theorem physicalWeights_zero : physicalWeights 0 = identityWeights := by
  have hs₂ := ne_of_gt inlinePrivate0_sin_two_lambda_pos
  have hs₃ := ne_of_gt inlinePrivate0_sin_three_lambda_pos
  have hd := inlinePrivate0_sin_two_lambda
  unfold physicalWeights identityWeights L
  simp only [add_zero, sub_zero, Real.sin_zero, mul_zero, zero_mul, zero_div]
  congr 1
  · rw [← hd]; exact div_self (mul_ne_zero hs₂ hs₃)
  · rw [mul_comm]; exact div_self (mul_ne_zero hs₂ hs₃)

 
theorem physicalWeights_three_lambda : physicalWeights (3*lambda) = deletionWeights := by
  have hs₂ := ne_of_gt inlinePrivate0_sin_two_lambda_pos
  have hs₃ := ne_of_gt inlinePrivate0_sin_three_lambda_pos
  have h₅ : Real.sin (2*lambda+3*lambda) = Real.sin (3*lambda) := by
    have harg : 2*lambda+3*lambda = Real.pi-3*lambda := by unfold lambda; ring
    rw [harg, Real.sin_pi_sub]
  have h₆ : Real.sin (3*lambda+3*lambda) = Real.sin (2*lambda) := by
    have harg : 3*lambda+3*lambda = Real.pi-2*lambda := by unfold lambda; ring
    rw [harg, Real.sin_pi_sub]
  unfold physicalWeights deletionWeights L
  simp only [sub_self, Real.sin_zero, mul_zero, zero_mul, zero_div, h₅, h₆]
  congr 1
  · rw [← inlinePrivate0_sin_two_lambda, mul_comm]; exact div_self (mul_ne_zero hs₃ hs₂)
  · have harg : 3*lambda-lambda = 2*lambda := by ring
    rw [harg, mul_comm]; exact div_self (mul_ne_zero hs₃ hs₂)

 

theorem physical_simultaneous_regular {n : ℕ} (u : Fin n → ℝ) (r : Fin n)
    (hu : ∀ i, i ≠ r → u i = 0 ∨ u i = 3*lambda) :
    (1-restrictedColumn (fun i => physicalWeights (3*lambda-u i))).det = 1 := by
  apply det_one_nonflat
  have hf : ∀ i, i ≠ r → (physicalWeights (3*lambda-u i)).IsFlat := by
    intro i hi
    rcases hu i hi with hz | ht
    · rw [hz, sub_zero, physicalWeights_three_lambda]
      exact Or.inr rfl
    · rw [ht, sub_self, physicalWeights_zero]
      exact Or.inl rfl
  intro i j hi hj
  have hir : i = r := by by_contra h; exact hi (hf i h)
  have hjr : j = r := by by_contra h; exact hj (hf j h)
  exact hir.trans hjr.symm

def attachEmpty {𝕜 : Type*} [One 𝕜] {n : ℕ}
    (v : NonemptyPairing n → 𝕜) : Pairing n → 𝕜 := by
  classical
  exact fun p => if h : p = empty n then 1 else v ⟨p,h⟩

@[simp] theorem attachEmpty_empty {𝕜 : Type*} [One 𝕜] {n : ℕ}
    (v : NonemptyPairing n → 𝕜) : attachEmpty v (empty n) = 1 := by
  simp [attachEmpty]

@[simp] theorem attachEmpty_nonempty {𝕜 : Type*} [One 𝕜] {n : ℕ}
    (v : NonemptyPairing n → 𝕜) (p : NonemptyPairing n) : attachEmpty v p.val = v p := by
  simp [attachEmpty, p.property]

def injectionColumn {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin n → Weights 𝕜) : NonemptyPairing n → 𝕜 := fun p => column w p.val (empty n)

 
def normalizedVacuum {𝕜 : Type*} [Field 𝕜] {n : ℕ}
    (w : Fin n → Weights 𝕜) : Pairing n → 𝕜 :=
  attachEmpty ((1-restrictedColumn w)⁻¹.mulVec (injectionColumn w))

def IsNormalizedStationary {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin n → Weights 𝕜) (v : Pairing n → 𝕜) : Prop :=
  v (empty n) = 1 ∧ (column w).mulVec v = v

theorem column_mulVec_empty {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin n → Weights 𝕜) (v : Pairing n → 𝕜) :
    (column w).mulVec v (empty n) = v (empty n) := by
  classical
  simp [Matrix.mulVec, dotProduct, column_empty_row]

theorem column_mulVec_nonempty {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin n → Weights 𝕜) (v : Pairing n → 𝕜) (p : NonemptyPairing n) :
    (column w).mulVec v p.val = injectionColumn w p * v (empty n) +
      (restrictedColumn w).mulVec (fun q => v q.val) p := by
  classical
  exact Fintype.sum_eq_add_sum_subtype_ne _ (empty n)

theorem normalizedVacuum_stationary {𝕜 : Type*} [Field 𝕜] {n : ℕ}
    (w : Fin n → Weights 𝕜) (hw : VacuumRegular w) :
    IsNormalizedStationary w (normalizedVacuum w) := by
  classical
  let Q := restrictedColumn w
  let v := injectionColumn w
  let P := (1-Q)⁻¹.mulVec v
  have hsolve : P-Q.mulVec P = v := by
    suffices hs : (1-Q).mulVec P = v by simpa [Matrix.sub_mulVec] using hs
    change (1-Q).mulVec ((1-Q)⁻¹.mulVec v) = v
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hw),
      Matrix.one_mulVec]
  refine ⟨attachEmpty_empty _, ?_⟩
  funext p
  by_cases hp : p = empty n
  · subst p; exact column_mulVec_empty w _
  · let p' : NonemptyPairing n := ⟨p,hp⟩
    change (column w).mulVec (attachEmpty P) p'.val = attachEmpty P p'.val
    rw [column_mulVec_nonempty]
    simp only [attachEmpty_empty, mul_one, attachEmpty_nonempty]
    have he := congrFun hsolve p'
    change P p' - Q.mulVec P p' = v p' at he
    exact eq_sub_iff_add_eq.mp he.symm

theorem normalizedVacuum_unique {𝕜 : Type*} [Field 𝕜] {n : ℕ}
    (w : Fin n → Weights 𝕜) (hw : VacuumRegular w)
    (v : Pairing n → 𝕜) (hv : IsNormalizedStationary w v) :
    v = normalizedVacuum w := by
  classical
  let x : NonemptyPairing n → 𝕜 := fun p => v p.val
  let Q := restrictedColumn w
  have heq : (1-Q).mulVec x = injectionColumn w := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    funext p
    have hp := congrFun hv.2 p.val
    rw [column_mulVec_nonempty, hv.1, mul_one] at hp
    change x p - Q.mulVec x p = injectionColumn w p
    exact (eq_sub_iff_add_eq.mpr (hp.trans (by rfl))).symm
  have hx : x = (1-Q)⁻¹.mulVec (injectionColumn w) := by
    rw [← heq, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hw), Matrix.one_mulVec]
  funext p
  by_cases hp : p = empty n
  · subst p; simpa [normalizedVacuum] using hv.1
  · let p' : NonemptyPairing n := ⟨p,hp⟩
    change x p' = attachEmpty ((1-Q)⁻¹.mulVec (injectionColumn w)) p'.val
    rw [attachEmpty_nonempty]
    exact congrFun hx p'

end

noncomputable section
 

def rawColumn {R : Type*} [CommRing R] {n : ℕ} (w : Fin n → Tile → R) :
    Matrix (Pairing n) (Pairing n) R := by
  classical
  exact fun q p => ∑ t : Configuration n,
    if Realizes p q t then ∏ i, w i (t i) else 0

end
end CriticalStrip.Diagram

end OAI
