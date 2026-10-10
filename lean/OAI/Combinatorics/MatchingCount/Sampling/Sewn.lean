import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.Components

namespace OAI

namespace MatchingFPRAS.Transport

section
variable {V E : Type*} [DecidableEq V] [DecidableEq E]
variable {inc : E → V → Prop}
namespace IndexedCycle.Corners

variable {c : IndexedCycle inc} (k : c.Corners)

lemma embeddedPair_outside [Fintype V] (M N : PM inc) (hU : ∀ i, c.edgeAt i ∈ M.val ∪ N.val)
    (chord : Fin 4 → E)
    (hc : ∀ i v, inc (chord i) v ↔
      v = (k.side i).vertex 0 ∨ v = (k.side i).vertex (k.side i).length)
    (flags : Fin 64) :
    (k.embeddedPair M N hU chord hc flags).outsideFirst = M.val \ c.edgeSet := by
  classical
  change M.val \ (k.cellPaths chord hc).orientation
    (decide (k.a₀ % 2 = if c.edgeAt 0 ∈ M.val then 0 else 1)) = _
  rw [k.cell_orientation_parity]
  have hp := c.inter_edgeSet_parity M.property N.property hU
  have he : (if decide (k.a₀ % 2 = if c.edgeAt 0 ∈ M.val then 0 else 1)
      then k.a₀ % 2 else 1-k.a₀ % 2) = (if c.edgeAt 0 ∈ M.val then 0 else 1) := by
    by_cases hz : c.edgeAt 0 ∈ M.val <;> simp only [hz,ite_true,ite_false]
    all_goals split_ifs <;> simp_all
  rw [he,← hp]
  ext e
  simp

end IndexedCycle.Corners

namespace CellPaths

variable (c : CellPaths inc)

lemma through_subset_contextOne (b : Bool) (X Y : Fin 4)
    (hX : sideBit X = b) (hY : sideBit Y = b) (hne : X ≠ Y)
    (hinc : ∀ e, ∃ v, inc e v) :
    (c.side X).through ⊆ c.contextOne b Y := by
  have hd := (c.side X).through_matching.disjoint_edges (c.side Y).through_matching hinc
    (c.same_bit_spans X Y hne (hX.trans hY.symm))
  intro e he
  exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
    ⟨c.through_subset_orientation b X hX he,fun hy => Finset.disjoint_left.mp hd he hy⟩)

lemma contextOne_self (b : Bool) (i : Fin 4) (hi : sideBit i = b)
    (he : (c.side i).closed (c.chord i) = (c.side i).through) :
    c.contextOne b i = c.orientation b := by
  rw [contextOne,he,Finset.sdiff_union_of_subset (c.through_subset_orientation b i hi)]

lemma contextError_short_left (R : Finset E) (f : Finset E → ℝ) (b : Bool)
    (X Y : Fin 4) (hX : sideBit X = b) (hY : sideBit Y = b) (hne : X ≠ Y)
    (hinc : ∀ e, ∃ v, inc e v)
    (he : (c.side X).closed (c.chord X) = (c.side X).through) :
    c.contextError R f b X Y = 0 := by
  rw [contextError,he,Finset.sdiff_union_of_subset
    (c.through_subset_contextOne b X Y hX hY hne hinc),c.contextOne_self b X hX he]
  ring

lemma contextError_short_right (R : Finset E) (f : Finset E → ℝ) (b : Bool)
    (X Y : Fin 4) (hY : sideBit Y = b)
    (he : (c.side Y).closed (c.chord Y) = (c.side Y).through) :
    c.contextError R f b X Y = 0 := by
  rw [contextError,c.contextOne_self b Y hY he]
  simp only [contextOne,sub_self]

lemma contextError_derivative (R : Finset E) (f : Finset E → ℝ) (b : Bool)
    (X Y : Fin 4) (hdis : Disjoint R (c.side X).through) :
    c.contextError R f b X Y =
    (f (R ∪ c.contextOne b Y) -
      f (((R ∪ c.contextOne b Y) \ (c.side X).through) ∪ (c.side X).closed (c.chord X))) -
    (f (R ∪ c.orientation b) -
      f (((R ∪ c.orientation b) \ (c.side X).through) ∪ (c.side X).closed (c.chord X))) := by
  have h (S : Finset E) :
      ((R ∪ S) \ (c.side X).through) ∪ (c.side X).closed (c.chord X) =
        R ∪ ((S \ (c.side X).through) ∪ (c.side X).closed (c.chord X)) := by
    have hr : R \ (c.side X).through = R := by
      ext e
      simp only [Finset.mem_sdiff]
      exact ⟨And.left,fun he => ⟨he,fun hn => Finset.disjoint_left.mp hdis he hn⟩⟩
    rw [Finset.union_sdiff_distrib,hr,Finset.union_assoc]
  rw [h,h]
  rfl

end CellPaths

end

section

variable {V E : Type*}

variable {inc : E → V → Prop}

namespace IndexedCycle

variable (c : IndexedCycle inc)

lemma edgeAt_injective_range {i j : ℕ} (hi : i < c.size) (hj : j < c.size)
    (he : c.edgeAt i = c.edgeAt j) : i = j := by
  have hf := c.four_le
  have h₀ := (c.edgeAt_incidence j (c.vertexAt i)).mp
    (he ▸ (c.edgeAt_incidence i _).mpr (Or.inl rfl))
  have h₁ := (c.edgeAt_incidence j (c.vertexAt (i+1))).mp
    (he ▸ (c.edgeAt_incidence i _).mpr (Or.inr rfl))
  have hv : ∀ a b, c.vertexAt a = c.vertexAt b → a % c.size = b % c.size := by
    intro a b h
    exact congrArg Fin.val (c.simple h)
  rcases h₀ with h₀ | h₀
  · have hh := hv _ _ h₀
    simpa only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hh
  · have hh₀ := hv _ _ h₀
    rcases h₁ with h₁ | h₁ <;> have hh₁ := hv _ _ h₁ <;>
      rw [Nat.mod_eq_of_lt hi, mod_of_lt_twice (by omega)] at hh₀ <;>
      rw [mod_of_lt_twice (by omega)] at hh₁
    · rw [Nat.mod_eq_of_lt hj] at hh₁
      split_ifs at hh₀ hh₁ <;> omega
    · rw [mod_of_lt_twice (by omega)] at hh₁
      split_ifs at hh₀ hh₁ <;> omega

lemma edgeAt_eq_iff {a x y : ℕ} (ha : a < c.size)
    (hx : a ≤ x ∧ x < a+c.size) (hy : a ≤ y ∧ y < a+c.size) :
    c.edgeAt x = c.edgeAt y ↔ x = y := by
  constructor
  · intro he
    have hh := c.edgeAt_injective_range
      (Nat.mod_lt x (by have := c.four_le; omega))
      (Nat.mod_lt y (by have := c.four_le; omega))
      (by simpa only [c.edgeAt_mod] using he)
    rw [mod_of_lt_twice (by omega), mod_of_lt_twice (by omega)] at hh
    split_ifs at hh <;> omega
  · exact congrArg c.edgeAt

variable [DecidableEq E]

lemma intervalPattern_disjoint {x y z : ℕ} (hx : x < c.size)
    (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ x+c.size) (a b : ℕ) :
    Disjoint (c.intervalPattern x y a) (c.intervalPattern y z b) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨i,hi,hj,_,he⟩ := (c.mem_intervalPattern e _ _ _).mp he
  obtain ⟨j,hk,hl,_,hf⟩ := (c.mem_intervalPattern e _ _ _).mp hf
  have hh := (c.edgeAt_eq_iff hx ⟨hi,by omega⟩ ⟨by omega,by omega⟩).mp (he.trans hf.symm)
  omega

lemma parity_sdiff_interval {x y : ℕ} (hx : x < c.size)
    (hxy : x ≤ y) (hy : y ≤ x+c.size) (a : ℕ) :
    c.parityPattern a \ c.intervalPattern x y a = c.intervalPattern y (x+c.size) a := by
  have hu := c.intervalPattern_union hxy hy a
  rw [c.rotatedPattern (by omega) a] at hu
  rw [← hu]
  have hd := c.intervalPattern_disjoint hx hxy hy (by omega) a a
  ext e
  simp only [Finset.mem_sdiff, Finset.mem_union]
  have hh : ¬ (e ∈ c.intervalPattern x y a ∧ e ∈ c.intervalPattern y (x+c.size) a) := by
    rintro ⟨h,h'⟩
    exact Finset.disjoint_left.mp hd h h'
  tauto

def sewn (x y : ℕ) (e : E) : Finset E :=
  (c.intervalPattern x y (1-x%2) ∪ c.intervalPattern y (x+c.size) (x%2)) ∪ {e}

lemma forward_conversion {x y : ℕ} (hx : x < c.size) (hxy : x < y)
    (hy : y < c.size) (ho : (y-x)%2=1) (e : E) :
    (c.parityPattern (x%2) \ (c.arc x (y-x) hx (by omega) (by omega) ho).through) ∪
      (c.arc x (y-x) hx (by omega) (by omega) ho).closed e = c.sewn x y e := by
  rw [OddPath.closed, c.arc_through, c.arc_interior]
  have he : x+(y-x)=y := by omega
  rw [he, c.parity_sdiff_interval hx (by omega) (by omega)]
  unfold sewn
  ext z
  simp only [Finset.mem_union]
  tauto

lemma complementary_conversion {x y : ℕ} (_hx : x < c.size) (hxy : x < y)
    (hy : y < c.size) (ho : (y-x)%2=1) (e : E) :
    (c.parityPattern (y%2) \
      (c.arc y (c.size+x-y) hy (by omega) (by omega) (by have := c.even; omega)).through) ∪
      (c.arc y (c.size+x-y) hy (by omega) (by omega) (by have := c.even; omega)).closed e =
      c.sewn x y e := by
  have hev := c.even
  have hp : y%2=1-x%2 := by omega
  have hp' : 1-y%2=x%2 := by omega
  have he : y+(c.size+x-y)=x+c.size := by omega
  rw [OddPath.closed, c.arc_through, c.arc_interior, he,
    c.parity_sdiff_interval hy (by omega) (by omega)]
  have hshift : c.intervalPattern (x+c.size) (y+c.size) (y%2) =
      c.intervalPattern x y (y%2) := c.intervalPattern_periodic _
  rw [hshift, hp', hp]
  unfold sewn
  ext z
  simp only [Finset.mem_union]
  tauto

lemma edgeAt_mem_parity (i : ℕ) : c.edgeAt i ∈ c.parityPattern (i%2) := by
  rw [parityPattern, c.mem_intervalPattern]
  have hdiv : 2 ∣ c.size := Nat.dvd_of_mod_eq_zero c.even
  exact ⟨i%c.size,by omega,Nat.mod_lt _ (by have := c.four_le; omega),
    Nat.mod_mod_of_dvd i hdiv,c.edgeAt_mod i⟩

lemma short_through (x : ℕ) (hx : x < c.size) :
    (c.arc x 1 hx (by omega) (by have := c.four_le; omega) (by omega)).through =
      {c.edgeAt x} := by
  norm_num [OddPath.through, pathPattern, arc]
  rw [show ({i ∈ ({0} : Finset ℕ) | i % 2 = 0}) = {0} by decide]
  simp

lemma short_closed (x : ℕ) (hx : x < c.size) :
    (c.arc x 1 hx (by omega) (by have := c.four_le; omega) (by omega)).closed (c.edgeAt x) =
      {c.edgeAt x} := by
  simp [OddPath.closed, OddPath.interior, pathPattern, arc]

lemma sewn_short (x : ℕ) (hx : x+1 < c.size) :
    c.sewn x (x+1) (c.edgeAt x) = c.parityPattern (x%2) := by
  have hh := c.forward_conversion (x := x) (y := x+1) (by omega) (by omega) hx (by omega) (c.edgeAt x)
  have ord : x+1-x=1 := by omega
  simp only [ord] at hh
  rw [c.short_through, c.short_closed] at hh
  rw [← hh]
  have hm : {c.edgeAt x} ⊆ c.parityPattern (x%2) := by
    simpa only [Finset.singleton_subset_iff] using c.edgeAt_mem_parity x
  exact Finset.sdiff_union_of_subset hm

lemma sewn_root : c.sewn 0 (c.size-1) (c.edgeAt (c.size-1)) = c.parityPattern 1 := by
  have hf := c.four_le
  have hev := c.even
  have hh := c.complementary_conversion (x := 0) (y := c.size-1) (by omega) (by omega)
    (by omega) (by omega) (c.edgeAt (c.size-1))
  have he : c.size+0-(c.size-1)=1 := by omega
  have hp : (c.size-1)%2=1 := by omega
  simp only [he, hp] at hh
  rw [c.short_through, c.short_closed] at hh
  rw [← hh]
  have hm : {c.edgeAt (c.size-1)} ⊆ c.parityPattern 1 := by
    simpa only [Finset.singleton_subset_iff, hp] using c.edgeAt_mem_parity (c.size-1)
  exact Finset.sdiff_union_of_subset hm

end IndexedCycle

end

variable {V E : Type*} [DecidableEq E]

variable {inc : E → V → Prop}

namespace IndexedCycle

variable (c : IndexedCycle inc)

def signedGain (R : Finset E) (f : Finset E → ℝ) (x y : ℕ) (e : E) : ℝ :=
  if x%2=0 then f (R ∪ c.parityPattern 0) - f (R ∪ c.sewn x y e)
  else f (R ∪ c.sewn x y e) - f (R ∪ c.parityPattern 1)

lemma signedGain_short (R : Finset E) (f : Finset E → ℝ) (x : ℕ) (hx : x+1<c.size) :
    c.signedGain R f x (x+1) (c.edgeAt x) = 0 := by
  unfold signedGain
  rw [c.sewn_short x hx]
  split_ifs with h
  · simp [h]
  · have hh : x%2=1 := by omega
    simp [hh]

lemma signedGain_root (R : Finset E) (f : Finset E → ℝ) :
    c.signedGain R f 0 (c.size-1) (c.edgeAt (c.size-1)) =
      f (R ∪ c.parityPattern 0) - f (R ∪ c.parityPattern 1) := by
  simp [signedGain, c.sewn_root]

namespace Corners

variable {c} (k : c.Corners)

def cornerSewn (chord : Fin 4 → E) : Fin 4 → Finset E :=
  ![c.sewn k.a₀ k.a₁ (chord 0), c.sewn k.a₁ k.a₂ (chord 1),
    c.sewn k.a₂ k.a₃ (chord 2), c.sewn k.a₀ k.a₃ (chord 3)]

variable [DecidableEq V]

lemma context_eq_sewn (chord : Fin 4 → E)
    (hc : ∀ i v, inc (chord i) v ↔
      v = (k.side i).vertex 0 ∨ v = (k.side i).vertex (k.side i).length)
    (i : Fin 4) :
    (k.cellPaths chord hc).contextOne (CellPaths.sideBit i) i = k.cornerSewn chord i := by
  have eh := k.cell_orientation_parity chord hc (CellPaths.sideBit i)
  rw [← k.parity_start i] at eh
  change ((k.cellPaths chord hc).orientation (CellPaths.sideBit i) \ (k.side i).through) ∪
    (k.side i).closed (chord i) = _
  rw [eh]
  have h₀ := k.lt₀
  have h₁ := k.lt₁
  have h₂ := k.lt₂
  have h₃ := k.lt₃
  fin_cases i
  · exact c.forward_conversion (by omega) h₀ (by omega) k.odd₀ _
  · exact c.forward_conversion (by omega) h₁ (by omega) k.odd₁ _
  · exact c.forward_conversion (by omega) h₂ h₃ k.odd₂ _
  · exact c.complementary_conversion (by omega) (by omega) h₃
      (by have := k.odd₀; have := k.odd₁; have := k.odd₂; omega) _

def signedLocalTerm (chord : Fin 4 → E)
    (hc : ∀ i v, inc (chord i) v ↔
      v = (k.side i).vertex 0 ∨ v = (k.side i).vertex (k.side i).length)
    (R : Finset E) (f : Finset E → ℝ) : ℝ :=
  let P := k.cellPaths chord hc
  let t := (f (R ∪ P.switched true) - f (R ∪ P.switched false)) +
    P.contextError R f true 2 0 - P.contextError R f false 3 1
  if k.a₀%2=0 then t else -t

theorem signed_cell_recurrence (chord : Fin 4 → E)
    (hc : ∀ i v, inc (chord i) v ↔
      v = (k.side i).vertex 0 ∨ v = (k.side i).vertex (k.side i).length)
    (R : Finset E) (f : Finset E → ℝ) (hinc : ∀ e, ∃ v, inc e v) :
    c.signedGain R f k.a₀ k.a₃ (chord 3) =
      k.signedLocalTerm chord hc R f +
      c.signedGain R f k.a₀ k.a₁ (chord 0) +
      c.signedGain R f k.a₁ k.a₂ (chord 1) +
      c.signedGain R f k.a₂ k.a₃ (chord 2) := by
  have hh := (k.cellPaths chord hc).single_cell_identity R f hinc
  have hc₀ := k.context_eq_sewn chord hc 0
  have hc₁ := k.context_eq_sewn chord hc 1
  have hc₂ := k.context_eq_sewn chord hc 2
  have hc₃ := k.context_eq_sewn chord hc 3
  norm_num [CellPaths.sideBit, Fin.isValue, cornerSewn, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] at hc₀ hc₁ hc₂ hc₃
  change (k.cellPaths chord hc).contextOne true 2 = c.sewn k.a₂ k.a₃ (chord 2) at hc₂
  change (k.cellPaths chord hc).contextOne false 3 = c.sewn k.a₀ k.a₃ (chord 3) at hc₃
  unfold CellPaths.canonicalGain at hh
  rw [hc₀, hc₁, hc₂, hc₃, k.cell_orientation_parity chord hc true,
    k.cell_orientation_parity chord hc false] at hh
  simp only [ite_true, Bool.false_eq_true, ite_false] at hh
  have ho₀ := k.odd₀
  have ho₁ := k.odd₁
  have hl₀ := k.lt₀
  have hl₁ := k.lt₁
  by_cases h : k.a₀%2=0
  · have h₁ : k.a₁%2=1 := by omega
    have h₂ : k.a₂%2=0 := by omega
    simp only [signedGain, signedLocalTerm, h, h₁, h₂,
      Nat.one_ne_zero, Nat.sub_zero, ite_true, ite_false] at hh ⊢
    linarith
  · have h₀ : k.a₀%2=1 := by omega
    have h₁ : k.a₁%2=0 := by omega
    have h₂ : k.a₂%2=1 := by omega
    simp only [signedGain, signedLocalTerm, h₀, h₁, h₂,
      Nat.one_ne_zero, Nat.sub_self, ite_true, ite_false] at hh ⊢
    linarith

end Corners

end IndexedCycle

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Cells.CycleData.Subdivision

variable {L : Type*} [DecidableEq L] {G : SimpleGraph L} {m : ℕ} {C : CycleData G m} {x y : ℕ}

lemma signed_cancellation_bounded (Q : Subdivision C x y)
    (gain : ℕ → ℕ → ℝ) (localTerm : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hshort : ∀ x, x + 1 < m → gain x (x+1)=0)
    (hcell : ∀ x p q y, C.Cell x p q y → y < m →
      gain x y = localTerm x p q y + gain x p + gain p q + gain q y)
    (hy : y < m) : gain x y = Q.sumCells localTerm := by
  induction Q with
  | edge h => simpa only [h, sumCells] using hshort _ (by omega)
  | node cell Q₁ Q₂ Q₃ h₁ h₂ h₃ =>
    have hpq := cell.middle_pos
    have hqy := cell.third_pos
    simpa only [sumCells, h₁ (by omega), h₂ (by omega), h₃ hy]
      using hcell _ _ _ _ cell hy

end MatchingFPRAS.Cells.CycleData.Subdivision

end OAI
