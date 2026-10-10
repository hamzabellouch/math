import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import OAI.Computability.BinPacking.Packing.LocalJobCounts
import OAI.Computability.BinPacking.Packing.PackingCoordinates

namespace OAI

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

private theorem up_indicator_add (g : GlobalSpecies D.graph) :
    (if g = .up true then 1 else 0) + (if g = .up false then 1 else 0) =
      match g with | .up _ => 1 | _ => 0 := by
  cases g with
  | up b => cases b <;> rfl
  | um b => rfl
  | edge e b => rfl

private theorem um_indicator_add (g : GlobalSpecies D.graph) :
    (if g = .um true then 1 else 0) + (if g = .um false then 1 else 0) =
      match g with | .um _ => 1 | _ => 0 := by
  cases g with
  | up b => rfl
  | um b => cases b <;> rfl
  | edge e b => rfl

private theorem root_copy_indicator_sum (T : UniformTree) (d : ℕ) :
    (∑ node : T.Node, ∑ _j : Fin d, if node = T.root then (1 : ℕ) else 0) = d := by
  classical
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Nat.cast_id]

theorem stateGlobalSpecies_up_true_count (v : D.Vertex) (selected : Bool) :
    (Finset.univ.filter (fun b : D.LocalBin v =>
      D.stateGlobalSpecies selected b = .up true)).card =
        if selected then D.d else 0 := by
  classical
  cases selected <;>
    simp [-Finset.sum_boole, Finset.card_filter, LocalBin, MBase, TreeRow,
      Fintype.sum_sum_type, Fintype.sum_prod_type, stateGlobalSpecies,
      stateMainGlobalSpecies]
  exact root_copy_indicator_sum D.plus D.d

theorem stateGlobalSpecies_um_true_count (v : D.Vertex) (selected : Bool) :
    (Finset.univ.filter (fun b : D.LocalBin v =>
      D.stateGlobalSpecies selected b = .um true)).card =
        if selected then 0 else D.d := by
  classical
  cases selected <;>
    simp [-Finset.sum_boole, Finset.card_filter, LocalBin, MBase, TreeRow,
      Fintype.sum_sum_type, Fintype.sum_prod_type, stateGlobalSpecies,
      stateMainGlobalSpecies]
  exact root_copy_indicator_sum D.minus D.d

theorem stateGlobalSpecies_up_total (v : D.Vertex) (selected : Bool) :
    (Finset.univ.filter (fun b : D.LocalBin v =>
      D.stateGlobalSpecies selected b = .up true)).card +
      (Finset.univ.filter (fun b : D.LocalBin v =>
        D.stateGlobalSpecies selected b = .up false)).card = D.tPlus + D.J v := by
  classical
  simp only [Finset.card_filter, ← Finset.sum_add_distrib, D.up_indicator_add]
  simp [LocalBin, MBase, TreeRow, Fintype.sum_sum_type,
    stateGlobalSpecies, stateMainGlobalSpecies, D.card_jobCopy, tPlus,
    Nat.mul_comm, Nat.add_assoc]

theorem stateGlobalSpecies_um_total (v : D.Vertex) (selected : Bool) :
    (Finset.univ.filter (fun b : D.LocalBin v =>
      D.stateGlobalSpecies selected b = .um true)).card +
      (Finset.univ.filter (fun b : D.LocalBin v =>
        D.stateGlobalSpecies selected b = .um false)).card = D.tMinus := by
  classical
  simp only [Finset.card_filter, ← Finset.sum_add_distrib, D.um_indicator_add]
  simp [LocalBin, MBase, TreeRow, Fintype.sum_sum_type,
    stateGlobalSpecies, stateMainGlobalSpecies, tMinus, Nat.mul_comm]

theorem stateGlobalSpecies_up_false_count (v : D.Vertex) (selected : Bool) :
    (Finset.univ.filter (fun b : D.LocalBin v =>
      D.stateGlobalSpecies selected b = .up false)).card =
        D.tPlus + D.J v - (if selected then D.d else 0) := by
  have h := D.stateGlobalSpecies_up_total v selected
  rw [D.stateGlobalSpecies_up_true_count] at h
  omega

theorem stateGlobalSpecies_um_false_count (v : D.Vertex) (selected : Bool) :
    (Finset.univ.filter (fun b : D.LocalBin v =>
      D.stateGlobalSpecies selected b = .um false)).card =
        D.tMinus - (if selected then 0 else D.d) := by
  have h := D.stateGlobalSpecies_um_total v selected
  rw [D.stateGlobalSpecies_um_true_count] at h
  omega

theorem stateGlobalSpecies_edge_count (v : D.Vertex) (selected : Bool)
    (e : D.Edge) (permit : Bool) :
    (Finset.univ.filter (fun b : D.LocalBin v =>
      D.stateGlobalSpecies selected b = .edge e permit)).card =
        if permit = !selected ∧ (D.graph.left e = v ∨ D.graph.right e = v)
        then D.d * D.R else 0 := by
  classical
  simp only [Finset.card_filter, Fintype.sum_sum_type]
  by_cases hp : permit = !selected
  · subst permit
    simpa [-Finset.sum_boole, Finset.card_filter, stateGlobalSpecies, stateMainGlobalSpecies,
      Fintype.sum_prod_type] using D.card_jobCopy_edge v e
  · have hp' : (!selected) ≠ permit := Ne.symm hp
    simp [-Finset.sum_boole, stateGlobalSpecies, stateMainGlobalSpecies, hp, hp']

theorem stateGlobalSpecies_count (v : D.Vertex) (selected : Bool)
    (g : GlobalSpecies D.graph) :
    (Finset.univ.filter (fun b : D.LocalBin v => D.stateGlobalSpecies selected b = g)).card =
      match g with
      | .up true => if selected then D.d else 0
      | .up false => D.tPlus + D.J v - (if selected then D.d else 0)
      | .um true => if selected then 0 else D.d
      | .um false => D.tMinus - (if selected then 0 else D.d)
      | .edge e permit =>
          if permit = !selected ∧ (D.graph.left e = v ∨ D.graph.right e = v)
          then D.d * D.R else 0 := by
  cases g with
  | up b =>
      cases b
      · exact D.stateGlobalSpecies_up_false_count v selected
      · exact D.stateGlobalSpecies_up_true_count v selected
  | um b =>
      cases b
      · exact D.stateGlobalSpecies_um_false_count v selected
      · exact D.stateGlobalSpecies_um_true_count v selected
  | edge e permit => exact D.stateGlobalSpecies_edge_count v selected e permit

theorem stateFlagSpecies_count (v : D.Vertex) (f : FlagSpecies) :
    (Finset.univ.filter (fun b : D.LocalBin v => D.stateFlagSpecies b = f)).card =
      match f with | .tree => D.t | .main => D.J v | .edge => D.J v := by
  classical
  simp only [Finset.card_filter, Fintype.sum_sum_type]
  cases f <;> simp [stateFlagSpecies, D.card_jobCopy, t, tPlus, tMinus,
    Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

private def allGlobalRequests (g : GlobalSpecies D.graph) : ℕ :=
  ∑ v : D.Vertex, ∑ selected : Bool,
    (Finset.univ.filter (fun b : D.LocalBin v => D.stateGlobalSpecies selected b = g)).card

private theorem allGlobalRequests_up_true : D.allGlobalRequests (.up true) = D.graph.n * D.d := by
  classical
  simp [allGlobalRequests, D.stateGlobalSpecies_up_true_count]

private theorem allGlobalRequests_um_true : D.allGlobalRequests (.um true) = D.graph.n * D.d := by
  classical
  simp [allGlobalRequests, D.stateGlobalSpecies_um_true_count]

private theorem allGlobalRequests_up_total :
    D.allGlobalRequests (.up true) + D.allGlobalRequests (.up false) = 2 * D.plusSlots := by
  classical
  calc
    _ = ∑ v : D.Vertex, ∑ selected : Bool,
        ((Finset.univ.filter (fun b : D.LocalBin v =>
          D.stateGlobalSpecies selected b = .up true)).card +
          (Finset.univ.filter (fun b : D.LocalBin v =>
            D.stateGlobalSpecies selected b = .up false)).card) := by
        simp only [allGlobalRequests, Finset.sum_add_distrib]
    _ = ∑ v : D.Vertex, ∑ _selected : Bool, (D.tPlus + D.J v) := by
        simp_rw [D.stateGlobalSpecies_up_total]
    _ = _ := by simp [plusSlots, Finset.sum_add_distrib, two_mul]

private theorem allGlobalRequests_um_total :
    D.allGlobalRequests (.um true) + D.allGlobalRequests (.um false) = 2 * D.minusSlots := by
  classical
  calc
    _ = ∑ v : D.Vertex, ∑ selected : Bool,
        ((Finset.univ.filter (fun b : D.LocalBin v =>
          D.stateGlobalSpecies selected b = .um true)).card +
          (Finset.univ.filter (fun b : D.LocalBin v =>
            D.stateGlobalSpecies selected b = .um false)).card) := by
        simp only [allGlobalRequests, Finset.sum_add_distrib]
    _ = ∑ v : D.Vertex, ∑ _selected : Bool, D.tMinus := by
        simp_rw [D.stateGlobalSpecies_um_total]
    _ = _ := by simp [minusSlots, two_mul, Nat.mul_add]

private theorem allGlobalRequests_edge (e : D.Edge) (permit : Bool) :
    D.allGlobalRequests (.edge e permit) = 2 * D.d * D.R := by
  classical
  have hpair (v : D.Vertex) :
      (Finset.univ.filter (fun b : D.LocalBin v =>
        D.stateGlobalSpecies true b = .edge e permit)).card +
        (Finset.univ.filter (fun b : D.LocalBin v =>
          D.stateGlobalSpecies false b = .edge e permit)).card =
        (Finset.univ.filter (fun j : D.JobCopy v => (D.jobPosition j).1 = e)).card := by
    cases permit <;> simp [D.stateGlobalSpecies_edge_count, D.card_jobCopy_edge]
  unfold allGlobalRequests
  simp only [Fintype.sum_bool, hpair]
  exact D.sum_card_jobCopy_edge e

private theorem allGlobalRequests_eq_twice_stock (hn : D.graph.n = 2 * D.k)
    (g : GlobalSpecies D.graph) : D.allGlobalRequests g = 2 * D.globalStock g := by
  have hk : D.k ≤ D.graph.n := by omega
  have hdiff : D.graph.n - D.k = D.k := by omega
  have hup : D.allGlobalRequests (.up true) = 2 * (D.d * D.k) := by
    rw [D.allGlobalRequests_up_true, hn]
    ring
  have hum : D.allGlobalRequests (.um true) = 2 * (D.d * (D.graph.n - D.k)) := by
    rw [D.allGlobalRequests_um_true, hdiff, hn]
    ring
  cases g with
  | up b =>
      cases b
      · have ht := D.allGlobalRequests_up_total
        have hs := D.unitPlus_le_stock hk
        rw [hup] at ht
        dsimp [globalStock]
        omega
      · exact hup
  | um b =>
      cases b
      · have ht := D.allGlobalRequests_um_total
        have hs := D.unitMinus_le_stock
        rw [hum] at ht
        dsimp [globalStock]
        omega
      · exact hum
  | edge e permit =>
      simpa [globalStock, Nat.mul_assoc] using D.allGlobalRequests_edge e permit

theorem doubled_stateGlobalSpecies_count (hn : D.graph.n = 2 * D.k)
    (g : GlobalSpecies D.graph) :
    (Finset.univ.filter (fun q : (Σ v : D.Vertex, Bool × D.LocalBin v) =>
      D.stateGlobalSpecies q.2.1 q.2.2 = g)).card = 2 * D.globalStock g := by
  classical
  have hsum :
      (Finset.univ.filter (fun q : (Σ v : D.Vertex, Bool × D.LocalBin v) =>
        D.stateGlobalSpecies q.2.1 q.2.2 = g)).card = D.allGlobalRequests g := by
    simp only [Finset.card_filter, Fintype.sum_sigma, Fintype.sum_prod_type,
      allGlobalRequests]
  rw [hsum]
  exact D.allGlobalRequests_eq_twice_stock hn g

theorem doubled_stateFlagSpecies_count (f : FlagSpecies) :
    (Finset.univ.filter (fun q : (Σ v : D.Vertex, Bool × D.LocalBin v) =>
      D.stateFlagSpecies q.2.2 = f)).card = 2 * D.flagStock f := by
  classical
  have hsum :
      (Finset.univ.filter (fun q : (Σ v : D.Vertex, Bool × D.LocalBin v) =>
        D.stateFlagSpecies q.2.2 = f)).card =
        ∑ v : D.Vertex, ∑ _selected : Bool,
          (Finset.univ.filter (fun b : D.LocalBin v => D.stateFlagSpecies b = f)).card := by
    simp only [Finset.card_filter, Fintype.sum_sigma, Fintype.sum_prod_type]
  rw [hsum]
  cases f <;>
    simp [D.stateFlagSpecies_count, flagStock, treeFlags,
      jobFlags, Finset.sum_add_distrib, two_mul, Nat.mul_add]

end BinPackingGap.InventoryData

namespace BinPackingGap

namespace GraphInput

theorem IsCover.mono {G : GraphInput} {C C' : Finset G.Vertex}
    (h : G.IsCover C) (hsub : C ⊆ C') : G.IsCover C' := by
  intro e he
  exact (h e he).imp (fun hx => hsub hx) (fun hx => hsub hx)

theorem CoverAtMost.exists_exact {G : GraphInput} {k : ℕ}
    (hk : k ≤ G.n) (h : G.CoverAtMost k) :
    ∃ C : Finset G.Vertex, G.IsCover C ∧ C.card = k := by
  classical
  obtain ⟨C, hC, hcard⟩ := h
  obtain ⟨C', hsub, _, heq⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ C) hcard (by simpa using hk)
  exact ⟨C', hC.mono hsub, heq⟩

theorem IsCover.endpoints {G : GraphInput} {C : Finset G.Vertex}
    (h : G.IsCover C) (e : G.Edge) : G.left e ∈ C ∨ G.right e ∈ C :=
  h _ (List.getElem_mem e.isLt)

end GraphInput

namespace InventoryData

variable (D : InventoryData)

def coverSelected (C : Finset D.Vertex) (v : D.Vertex) : Bool := decide (v ∈ C)

def permitLeft (C : Finset D.Vertex) (e : D.Edge) : Bool :=
  !D.coverSelected C (D.graph.left e) || D.coverSelected C (D.graph.right e)

def integralPermit (C : Finset D.Vertex) (e : D.Edge) (slot : Fin 2) : Bool :=
  if slot = 0 then D.permitLeft C e else !D.permitLeft C e

@[simp] theorem integralPermit_zero (C : Finset D.Vertex) (e : D.Edge) :
    D.integralPermit C e 0 = D.permitLeft C e := by simp [integralPermit]

@[simp] theorem integralPermit_one (C : Finset D.Vertex) (e : D.Edge) :
    D.integralPermit C e 1 = !D.permitLeft C e := by simp [integralPermit]

theorem integralPermit_of_unselected (C : Finset D.Vertex)
    (hC : D.graph.IsCover C) (e : D.Edge) (slot : Fin 2)
    (hnot : D.coverSelected C (D.graph.endpoint e slot) = false) :
    D.integralPermit C e slot = true := by
  have hends := hC.endpoints e
  have hs : slot = 0 ∨ slot = 1 := by omega
  rcases hs with rfl | rfl <;>
    by_cases hl : D.graph.left e ∈ C <;>
    by_cases hr : D.graph.right e ∈ C <;>
    simp_all [integralPermit, permitLeft, coverSelected, GraphInput.endpoint]

def integralGlobalSpecies (C : Finset D.Vertex) : D.PhysicalBins → GlobalSpecies D.graph
  | ⟨v, .inl b⟩ => D.stateMainGlobalSpecies (D.coverSelected C v) b
  | ⟨_, .inr j⟩ => .edge j.1.1.val.1 (D.integralPermit C j.1.1.val.1 j.1.1.val.2)

def integralFlagSpecies : D.PhysicalBins → FlagSpecies :=
  fun b => D.stateFlagSpecies b.2

theorem integral_edge_permit_of_unselected (C : Finset D.Vertex)
    (hC : D.graph.IsCover C) {v : D.Vertex} (j : D.JobCopy v)
    (hv : D.coverSelected C v = false) :
    D.integralPermit C j.1.1.val.1 j.1.1.val.2 = true := by
  apply D.integralPermit_of_unselected C hC
  simpa only [j.1.1.property] using hv

end InventoryData

end BinPackingGap

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

private theorem integral_up_count_eq_sum (C : Finset D.Vertex) (one : Bool) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralGlobalSpecies C b = .up one)).card =
      ∑ v : D.Vertex, (Finset.univ.filter (fun b : D.LocalBin v =>
        D.stateGlobalSpecies (D.coverSelected C v) b = .up one)).card := by
  classical
  simp only [Finset.card_filter, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro b _
  rcases b with b | j
  · rfl
  · simp [integralGlobalSpecies, stateGlobalSpecies]

private theorem integral_um_count_eq_sum (C : Finset D.Vertex) (one : Bool) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralGlobalSpecies C b = .um one)).card =
      ∑ v : D.Vertex, (Finset.univ.filter (fun b : D.LocalBin v =>
        D.stateGlobalSpecies (D.coverSelected C v) b = .um one)).card := by
  classical
  simp only [Finset.card_filter, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro b _
  rcases b with b | j
  · rfl
  · simp [integralGlobalSpecies, stateGlobalSpecies]

private theorem sum_coverSelected (C : Finset D.Vertex) :
    (∑ v : D.Vertex, if D.coverSelected C v then D.d else 0) = D.d * C.card := by
  classical
  simp [coverSelected, Nat.mul_comm]

private theorem sum_coverUnselected (C : Finset D.Vertex) :
    (∑ v : D.Vertex, if D.coverSelected C v then 0 else D.d) =
      D.d * (D.graph.n - C.card) := by
  classical
  calc
    _ = ∑ v : D.Vertex, if v ∈ Cᶜ then D.d else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v ∈ C <;> simp [coverSelected, hv]
    _ = D.d * (Cᶜ).card := by
      rw [Fintype.sum_ite_mem]
      simp [Nat.mul_comm]
    _ = _ := by simp [Finset.card_compl]

private theorem integral_up_true_count (C : Finset D.Vertex) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralGlobalSpecies C b = .up true)).card = D.d * C.card := by
  rw [D.integral_up_count_eq_sum]
  simp_rw [D.stateGlobalSpecies_up_true_count]
  exact D.sum_coverSelected C

private theorem integral_um_true_count (C : Finset D.Vertex) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralGlobalSpecies C b = .um true)).card =
      D.d * (D.graph.n - C.card) := by
  rw [D.integral_um_count_eq_sum]
  simp_rw [D.stateGlobalSpecies_um_true_count]
  exact D.sum_coverUnselected C

private theorem integral_up_total (C : Finset D.Vertex) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralGlobalSpecies C b = .up true)).card +
      (Finset.univ.filter (fun b : D.PhysicalBins =>
        D.integralGlobalSpecies C b = .up false)).card = D.plusSlots := by
  rw [D.integral_up_count_eq_sum, D.integral_up_count_eq_sum,
    ← Finset.sum_add_distrib]
  simp_rw [D.stateGlobalSpecies_up_total]
  rfl

private theorem integral_um_total (C : Finset D.Vertex) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralGlobalSpecies C b = .um true)).card +
      (Finset.univ.filter (fun b : D.PhysicalBins =>
        D.integralGlobalSpecies C b = .um false)).card = D.minusSlots := by
  rw [D.integral_um_count_eq_sum, D.integral_um_count_eq_sum,
    ← Finset.sum_add_distrib]
  simp_rw [D.stateGlobalSpecies_um_total]
  simp [minusSlots]

theorem card_integralEdgeJobs (C : Finset D.Vertex) (e : D.Edge) (permit : Bool) :
    (Finset.univ.filter (fun j : Σ v : D.Vertex, D.JobCopy v =>
      GlobalSpecies.edge (G := D.graph) j.2.1.1.val.1
        (D.integralPermit C j.2.1.1.val.1 j.2.1.1.val.2) =
      GlobalSpecies.edge e permit)).card = D.d * D.R := by
  classical
  let chosen : Fin 2 := if permit = D.permitLeft C e then 0 else 1
  have hslot (slot : Fin 2) :
      D.integralPermit C e slot = permit ↔ slot = chosen := by
    have hs : slot = 0 ∨ slot = 1 := by omega
    rcases hs with rfl | rfl <;>
      cases hp : D.permitLeft C e <;> cases permit <;>
      simp [chosen, hp]
  have hedge (e' : D.Edge) (slot : Fin 2) :
      GlobalSpecies.edge (G := D.graph) e' (D.integralPermit C e' slot) =
        GlobalSpecies.edge e permit ↔ (e', slot) = (e, chosen) := by
    rw [GlobalSpecies.edge.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨he, hp⟩
      subst e'
      exact ⟨rfl, (hslot slot).mp hp⟩
    · rintro ⟨he, hs⟩
      subst e'
      exact ⟨rfl, (hslot slot).mpr hs⟩
  calc
    _ = ((({(e, chosen)} : Finset (D.Edge × Fin 2)) ×ˢ
          (Finset.univ : Finset (Fin D.R))) ×ˢ
          (Finset.univ : Finset (Fin D.d))).card := by
      apply Finset.card_equiv D.allJobEquiv
      intro j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_product, Finset.mem_singleton, and_true]
      exact hedge j.2.1.1.val.1 j.2.1.1.val.2
    _ = D.d * D.R := by simp [Nat.mul_comm]

theorem card_integralGlobalSpecies (C : Finset D.Vertex) (hC : C.card = D.k)
    (s : GlobalSpecies D.graph) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralGlobalSpecies C b = s)).card = D.globalStock s := by
  classical
  cases s with
  | up one =>
      cases one
      · have ht := D.integral_up_total C
        have hu := D.integral_up_true_count C
        rw [hC] at hu
        dsimp [globalStock]
        omega
      · simpa [globalStock, hC] using D.integral_up_true_count C
  | um one =>
      cases one
      · have ht := D.integral_um_total C
        have hu := D.integral_um_true_count C
        rw [hC] at hu
        dsimp [globalStock]
        omega
      · simpa [globalStock, hC] using D.integral_um_true_count C
  | edge e permit =>
      rw [Finset.card_filter, Fintype.sum_sigma]
      have hj := D.card_integralEdgeJobs C e permit
      rw [Finset.card_filter, Fintype.sum_sigma] at hj
      refine Eq.trans ?_ hj
      apply Finset.sum_congr rfl
      intro vertex _
      have hmain (base : D.MBase vertex) :
          D.stateMainGlobalSpecies (D.coverSelected C vertex) base ≠ .edge e permit := by
        rcases base with (⟨node, copy⟩ | (⟨node, copy⟩ | zero)) | job <;>
          simp [stateMainGlobalSpecies]
      rw [Fintype.sum_sum_type]
      simp only [integralGlobalSpecies, hmain, ite_false, Finset.sum_const_zero, zero_add]
      rfl

theorem card_integralFlagSpecies (f : FlagSpecies) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralFlagSpecies b = f)).card = D.flagStock f := by
  classical
  have hsum :
      (Finset.univ.filter (fun b : D.PhysicalBins =>
        D.integralFlagSpecies b = f)).card =
        ∑ v : D.Vertex, (Finset.univ.filter (fun b : D.LocalBin v =>
          D.stateFlagSpecies b = f)).card := by
    rw [Finset.card_filter]
    simp only [Finset.card_filter, Fintype.sum_sigma, integralFlagSpecies]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro b _
    rfl
  rw [hsum]
  cases f <;> simp [D.stateFlagSpecies_count, flagStock, treeFlags, jobFlags]

end BinPackingGap.InventoryData

end OAI
