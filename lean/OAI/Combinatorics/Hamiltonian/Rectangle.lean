import OAI.Combinatorics.Hamiltonian.BranchPartition

namespace OAI

/-! Rectangular primal and dual networks and finite lattice containment. -/

namespace Barnette.RectangularDual
noncomputable section

abbrev Vertex (n m : ℕ) := Fin (n + 1) × Fin (m + 1)
abbrev Edge (n m : ℕ) := (Fin n × Fin (m + 1)) ⊕ (Fin (n + 1) × Fin m)
abbrev Face (n m : ℕ) := Option (Fin n × Fin m)

def primal (n m : ℕ) : Network (Vertex n m) (Edge n m) where
  tail := Sum.elim (fun e => (e.1.castSucc, e.2)) (fun e => (e.1, e.2.castSucc))
  head := Sum.elim (fun e => (e.1.succ, e.2)) (fun e => (e.1, e.2.succ))

def lower {n : ℕ} : Fin (n + 1) → Option (Fin n) := Fin.cases none some
def upper {n : ℕ} : Fin (n + 1) → Option (Fin n) := Fin.lastCases none some

def dual (n m : ℕ) : Network (Face n m) (Edge n m) where
  tail := Sum.elim
    (fun e => (lower e.2).map (fun j => (e.1, j)))
    (fun e => (upper e.1).map (fun i => (i, e.2)))
  head := Sum.elim
    (fun e => (upper e.2).map (fun j => (e.1, j)))
    (fun e => (lower e.1).map (fun i => (i, e.2)))

def lowerValue {n : ℕ} (f : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.cases 0 f
def upperValue {n : ℕ} (f : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.lastCases 0 f

def stepCoeff {n : ℕ} (v : Fin (n + 1)) (e : Fin n) : ℝ :=
  (if e.succ = v then 1 else 0) - (if e.castSucc = v then 1 else 0)

lemma sum_succ {n : ℕ} (f : Fin n → ℝ) (v : Fin (n + 1)) :
    (∑ i, if i.succ = v then f i else 0) = lowerValue f v := by
  induction v using Fin.cases with
  | zero => simp [lowerValue]
  | succ v => simp [lowerValue]

lemma sum_castSucc {n : ℕ} (f : Fin n → ℝ) (v : Fin (n + 1)) :
    (∑ i, if i.castSucc = v then f i else 0) = upperValue f v := by
  induction v using Fin.lastCases with
  | last => simp [upperValue, Fin.castSucc_ne_last]
  | cast v => simp [upperValue]

lemma sum_stepCoeff {n : ℕ} (f : Fin n → ℝ) (v : Fin (n + 1)) :
    (∑ i, stepCoeff v i * f i) = lowerValue f v - upperValue f v := by
  simp only [stepCoeff, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib, sum_succ, sum_castSucc]

lemma lower_eval {n : ℕ} (f : Fin n → ℝ) (v : Fin (n + 1)) :
    (lower v).elim 0 f = lowerValue f v := by
  induction v using Fin.cases <;> simp [lower, lowerValue]

lemma upper_eval {n : ℕ} (f : Fin n → ℝ) (v : Fin (n + 1)) :
    (upper v).elim 0 f = upperValue f v := by
  induction v using Fin.lastCases <;> simp [upper, upperValue]

def potential {n m : ℕ} (f : Fin n × Fin m → ℝ) : Face n m → ℝ :=
  fun z => z.elim 0 f

lemma eval_map {A B : Type*} (g : B → ℝ) (f : A → B) (z : Option A) :
    (z.map f).elim 0 g = z.elim 0 (g ∘ f) := by cases z <;> rfl

lemma dual_horizontal {n m : ℕ} (f : Fin n × Fin m → ℝ)
    (i : Fin n) (j : Fin (m + 1)) :
    (dual n m).gradient (potential f) (.inl (i, j)) =
      -∑ q, stepCoeff j q * f (i, q) := by
  change ((upper j).map _).elim 0 f - ((lower j).map _).elim 0 f = _
  rw [eval_map, eval_map, upper_eval, lower_eval, sum_stepCoeff]
  dsimp only [Function.comp_def]
  ring

lemma dual_vertical {n m : ℕ} (f : Fin n × Fin m → ℝ)
    (i : Fin (n + 1)) (j : Fin m) :
    (dual n m).gradient (potential f) (.inr (i, j)) =
      ∑ p, stepCoeff i p * f (p, j) := by
  change ((lower i).map _).elim 0 f - ((upper i).map _).elim 0 f = _
  rw [eval_map, eval_map, upper_eval, lower_eval, sum_stepCoeff]
  rfl

lemma boundary_formula {n m : ℕ} (x : Edge n m → ℝ) (i : Fin (n + 1))
    (j : Fin (m + 1)) :
    (primal n m).boundary x (i, j) =
      (∑ p, stepCoeff i p * x (.inl (p, j))) +
      (∑ q, stepCoeff j q * x (.inr (i, q))) := by
  classical
  rw [Network.boundary_apply, Fintype.sum_sum_type]
  simp only [primal, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq,
    Fintype.sum_prod_type, stepCoeff, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib, ite_and]
  simp

lemma orthogonal_potential (n m : ℕ) (f : Fin n × Fin m → ℝ) :
    (primal n m).boundary ((dual n m).gradient (potential f)) = 0 := by
  ext ⟨i, j⟩
  rw [boundary_formula]
  simp only [dual_horizontal, dual_vertical, mul_neg, Finset.sum_neg_distrib,
    Finset.mul_sum]
  rw [Finset.sum_comm (f := fun q p => stepCoeff j q * (stepCoeff i p * f (p, q)))]
  have he : (∑ p, ∑ q, stepCoeff j q * (stepCoeff i p * f (p, q))) =
      ∑ p, ∑ q, stepCoeff i p * (stepCoeff j q * f (p, q)) := by
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [he]
  exact neg_add_cancel _

lemma orthogonal (n m : ℕ) (f : Face n m → ℝ) :
    (primal n m).boundary ((dual n m).gradient f) = 0 := by
  let g : Fin n × Fin m → ℝ := fun t => f (some t) - f none
  have hf : f = potential g + (fun _ => f none) := by
    ext z
    cases z <;> simp [potential, g]
  rw [hf, map_add, Network.gradient_const, add_zero]
  exact orthogonal_potential n m g

lemma horizontal_adj {n m : ℕ} (i : Fin n) (j : Fin (m + 1)) :
    (primal n m).graph.Adj (i.castSucc, j) (i.succ, j) := by
  refine ⟨?_, .inl (i, j), Or.inl ⟨rfl, rfl⟩⟩
  intro h
  have hh := congrArg (fun z : Vertex n m => z.1.val) h
  simp only [Fin.val_castSucc, Fin.val_succ] at hh
  omega

lemma vertical_adj {n m : ℕ} (i : Fin (n + 1)) (j : Fin m) :
    (primal n m).graph.Adj (i, j.castSucc) (i, j.succ) := by
  refine ⟨?_, .inr (i, j), Or.inl ⟨rfl, rfl⟩⟩
  intro h
  have hh := congrArg (fun z : Vertex n m => z.2.val) h
  simp only [Fin.val_castSucc, Fin.val_succ] at hh
  omega

lemma primal_connected (n m : ℕ) : (primal n m).graph.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨(0, 0), ?_⟩
  rintro ⟨i, j⟩
  have hv : (primal n m).graph.Reachable (0, 0) (0, j) := by
    induction j using Fin.induction with
    | zero => exact .rfl
    | succ j ih => exact ih.trans (vertical_adj (0 : Fin (n + 1)) j).reachable
  have hh : (primal n m).graph.Reachable (0, j) (i, j) := by
    induction i using Fin.induction with
    | zero => exact .rfl
    | succ i ih => exact ih.trans (horizontal_adj i j).reachable
  exact hv.trans hh

lemma dual_connected (n m : ℕ) : (dual n m).graph.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨none, ?_⟩
  intro z
  cases z with
  | none => exact .rfl
  | some z =>
    obtain ⟨i, j⟩ := z
    cases n with
    | zero => exact isEmptyElim i
    | succ n =>
      induction i using Fin.induction with
      | zero =>
        have h := ((dual (n + 1) m).edge_reachable (.inr (0, j))).symm
        have hu : upper (0 : Fin (n + 2)) = some (0 : Fin (n + 1)) := by
          change upper (0 : Fin (n + 1)).castSucc = _
          exact Fin.lastCases_castSucc _
        simpa only [dual, Sum.elim_inr, lower, Fin.cases_zero, hu,
          Option.map_none, Option.map_some] using h
      | succ i ih =>
        have h := ((dual (n + 1) m).edge_reachable (.inr (i.succ.castSucc, j))).symm
        have hl : lower i.succ.castSucc = some i.castSucc := by
          have he : i.succ.castSucc = i.castSucc.succ := by ext; rfl
          rw [he]
          simp [lower]
        have hu : upper i.succ.castSucc = some i.succ := Fin.lastCases_castSucc _
        exact ih.trans (by
          simpa only [dual, Sum.elim_inr, hl, hu, Option.map_some] using h)

theorem grid_duality (n m : ℕ) : (primal n m).Duality (dual n m) := by
  apply Network.duality_of_orth_card (primal n m) (dual n m)
    (primal_connected n m) (dual_connected n m)
  · simp only [Vertex, Face, Edge, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_option, Fintype.card_sum]
    ring
  · exact orthogonal n m

end
end Barnette.RectangularDual

namespace Barnette.MinorModel
noncomputable section
open scoped Classical
variable {V W U : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
  {J : SimpleGraph U} [Fintype U]

def pullHost (M : MinorModel G H) (f : J ↪g H)
    (hf : ∀ v, M.branch v ⊆ Set.range f) : MinorModel G J where
  branch v := f ⁻¹' M.branch v
  branch_finite _ := Set.toFinite _
  branch_connected v := by
    let g : {x // f x ∈ M.branch v} → M.branch v := fun x => ⟨f x.val, x.property⟩
    have hg : Function.Bijective g := by
      refine ⟨?_, ?_⟩
      · intro x y hxy
        apply Subtype.ext
        exact f.injective (congrArg Subtype.val hxy)
      · intro y
        obtain ⟨x, hx⟩ := hf v y.property
        refine ⟨⟨x, hx ▸ y.property⟩, ?_⟩
        exact Subtype.ext hx
    let e : J.induce (f ⁻¹' M.branch v) ≃g H.induce (M.branch v) :=
      { toEquiv := Equiv.ofBijective g hg
        map_rel_iff' := by intro x y; exact f.map_rel_iff }
    exact e.connected_iff.mpr (M.branch_connected v)
  branches_disjoint v w hvw := (M.branches_disjoint v w hvw).preimage f
  adjacency v w h := by
    obtain ⟨a, ha, b, hb, hab⟩ := M.adjacency v w h
    obtain ⟨a', rfl⟩ := hf v ha
    obtain ⟨b', rfl⟩ := hf w hb
    exact ⟨a', ha, b', hb, f.map_rel_iff.mp hab⟩
end
end Barnette.MinorModel

namespace Barnette.RectangularDual
noncomputable section
open scoped Classical

lemma primal_adj_iff {n m : ℕ} (p q : Vertex n m) :
    (primal n m).graph.Adj p q ↔
      ((p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val) ∧ p.2 = q.2) ∨
      ((p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val) ∧ p.1 = q.1) := by
  constructor
  · rintro ⟨_, e, he⟩
    rcases e with ⟨i, j⟩ | ⟨i, j⟩ <;>
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [primal]
  · have hx (a b : Vertex n m) (h : a.1.val + 1 = b.1.val) (hj : a.2 = b.2) :
        (primal n m).graph.Adj a b := by
      have hi : a.1.val < n := by have := b.1.isLt; omega
      refine ⟨?_, .inl (⟨a.1.val, hi⟩, a.2), Or.inl ⟨?_, ?_⟩⟩
      · intro he; have hh := congrArg (fun x : Vertex n m => x.1.val) he; omega
      · apply Prod.ext <;> rfl
      · apply Prod.ext
        · apply Fin.ext; exact h
        · exact hj
    have hy (a b : Vertex n m) (h : a.2.val + 1 = b.2.val) (hi : a.1 = b.1) :
        (primal n m).graph.Adj a b := by
      have hj : a.2.val < m := by have := b.2.isLt; omega
      refine ⟨?_, .inr (a.1, ⟨a.2.val, hj⟩), Or.inl ⟨?_, ?_⟩⟩
      · intro he; have hh := congrArg (fun x : Vertex n m => x.2.val) he; omega
      · apply Prod.ext <;> rfl
      · apply Prod.ext
        · exact hi
        · apply Fin.ext; exact h
    rintro (⟨h | h, hj⟩ | ⟨h | h, hi⟩)
    · exact hx p q h hj
    · exact (hx q p h hj.symm).symm
    · exact hy p q h hi
    · exact (hy q p h hi.symm).symm

def latticePoint (r : ℕ) (p : Vertex (2 * r) (2 * r)) : ℤ × ℤ :=
  ((p.1.val : ℤ) - r, (p.2.val : ℤ) - r)

lemma latticePoint_injective (r : ℕ) : Function.Injective (latticePoint r) := by
  intro p q h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp [latticePoint] at h₁ h₂
  apply Prod.ext <;> apply Fin.ext <;> omega

def latticeEmbedding (r : ℕ) : (primal (2 * r) (2 * r)).graph ↪g SquareGrid.graph where
  toFun := latticePoint r
  inj' := latticePoint_injective r
  map_rel_iff' := by
    intro p q
    rw [primal_adj_iff]
    change SquareGrid.graph.Adj (latticePoint r p) (latticePoint r q) ↔ _
    simp only [SquareGrid.graph, latticePoint, Fin.ext_iff]
    omega

lemma bounded_mem_range (r : ℕ) (z : ℤ × ℤ)
    (h₁ : z.1.natAbs ≤ r) (h₂ : z.2.natAbs ≤ r) :
    z ∈ Set.range (latticeEmbedding r) := by
  have ha : z.1 ≤ (z.1.natAbs : ℤ) := Int.le_natAbs
  have hb : -z.1 ≤ (z.1.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -z.1))
  have hc : z.2 ≤ (z.2.natAbs : ℤ) := Int.le_natAbs
  have hd : -z.2 ≤ (z.2.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -z.2))
  refine ⟨(⟨(z.1 + r).toNat, ?_⟩, ⟨(z.2 + r).toNat, ?_⟩), ?_⟩
  · omega
  · omega
  · apply Prod.ext <;> dsimp [latticeEmbedding, latticePoint] <;> omega

lemma finite_subset_box (s : Set (ℤ × ℤ)) (hs : s.Finite) :
    ∃ r : ℕ, s ⊆ Set.range (latticeEmbedding r) := by
  let r := ∑ z ∈ hs.toFinset, (z.1.natAbs + z.2.natAbs)
  refine ⟨r, ?_⟩
  intro z hz
  have hle : z.1.natAbs + z.2.natAbs ≤ r :=
    Finset.single_le_sum (f := fun z : ℤ × ℤ => z.1.natAbs + z.2.natAbs)
      (fun _ _ => Nat.zero_le _) (hs.mem_toFinset.mpr hz)
  exact bounded_mem_range r z (by omega) (by omega)

theorem lattice_minor_in_rectangle {V : Type*} [Fintype V] {G : SimpleGraph V}
    (M : MinorModel G SquareGrid.graph) :
    ∃ r : ℕ, Nonempty (MinorModel G (primal (2 * r) (2 * r)).graph) := by
  let s := ⋃ v, M.branch v
  have hs : s.Finite := Set.finite_iUnion M.branch_finite
  obtain ⟨r, hr⟩ := finite_subset_box s hs
  refine ⟨r, ⟨M.pullHost (latticeEmbedding r) ?_⟩⟩
  intro v z hz
  exact hr (Set.mem_iUnion.mpr ⟨v, hz⟩)

end
end Barnette.RectangularDual

end OAI
