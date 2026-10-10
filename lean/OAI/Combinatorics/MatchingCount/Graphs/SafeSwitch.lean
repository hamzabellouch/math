import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.Through

namespace OAI

namespace MatchingFPRAS.Transport.IndexedCycle

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

variable {inc : E → V → Prop}

omit [Fintype V] [DecidableEq V] in
lemma parityPattern_subset_edgeSet (c : IndexedCycle inc) (a : ℕ) : c.parityPattern a ⊆ c.edgeSet := by
  intro e he
  obtain ⟨i,_,hi,_,rfl⟩ := (c.mem_intervalPattern e 0 c.size a).mp he
  exact c.edgeAt_mem_edgeSet i

end MatchingFPRAS.Transport.IndexedCycle

namespace MatchingFPRAS.Transport.CellDemands

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

namespace Demand

variable (d : Demand hbags hG)

omit [Fintype L] in
lemma outside_disjoint_through (i : Fin 4) : Disjoint d.outside (d.paths.side i).through := by
  have hp := d.corners.cell_orientation_parity d.paths.chord d.paths.chord_incidence (CellPaths.sideBit i)
  have hsub : (d.paths.side i).through ⊆ d.cycle.edgeSet := by
    apply Finset.Subset.trans (d.paths.through_subset_orientation (CellPaths.sideBit i) i rfl)
    exact hp ▸ d.cycle.parityPattern_subset_edgeSet _
  exact Finset.disjoint_left.mpr fun _ he hi => (Finset.mem_sdiff.mp he).2 (hsub hi)

omit [Fintype L] in
lemma short_error_zero (f : Finset (BagEdge bags) → ℝ) (b : Bool)
    (hh : ¬ ∀ i : Fin 4, CellPaths.sideBit i = b → (d.paths.side i).length ≠ 1) :
    d.paths.contextError d.outside f b (if b then 2 else 3) (if b then 0 else 1) = 0 := by
  classical
  push Not at hh
  obtain ⟨i,hib,hil⟩ := hh
  have he := d.cycle.cellShort_pattern hbags d.cell d.last_lt i hil
  cases b <;> fin_cases i <;> simp_all [CellPaths.sideBit]
  · exact d.paths.contextError_short_right d.outside f false 3 1 (by decide) he
  · exact d.paths.contextError_short_left d.outside f false 3 1 (by decide) (by decide)
      (by decide) BagEdge.exists_incident he
  · exact d.paths.contextError_short_right d.outside f true 2 0 (by decide) he
  · exact d.paths.contextError_short_left d.outside f true 2 0 (by decide) (by decide)
      (by decide) BagEdge.exists_incident he

end Demand

namespace ErrorDemand

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

variable (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi)

variable (f g : Finset (BagEdge bags) → ℝ)

variable (e : ErrorDemand hbags hG)

lemma literal_error :
    e.demand.paths.contextError e.demand.outside f e.bit e.X e.Y =
      PatternCode.firstDerivative f e.pattern
        (e.choice height hheight hstep D hD w hw lo hi hlo hlohi true).first -
      PatternCode.firstDerivative f e.pattern
        (e.choice height hheight hstep D hD w hw lo hi hlo hlohi false).first := by
  simp only [PatternCode.firstDerivative,
    (e.choice_spec height hheight hstep D hD w hw lo hi hlo hlohi true).1,
    (e.choice_spec height hheight hstep D hD w hw lo hi hlo hlohi false).1,
    Bool.false_eq_true,ite_false,ite_true]
  exact e.demand.paths.contextError_derivative e.demand.outside f e.bit e.X e.Y
    (e.demand.outside_disjoint_through e.X)

include hheight hstep hD hw hlohi

theorem error_load_bound (M : PM (BagEdge.Incident (bags := bags))) :
    let wt := fun e => max lo (min hi (w e))
    let π := gibbsLaw wt (fun _ => lt_of_lt_of_le hlo (le_max_left _ _)) M
    (∑ e : ErrorDemand hbags hG, π.weight e.demand.1.1 * π.weight e.demand.1.2 *
      (e.demand.paths.contextError e.demand.outside f e.bit e.X e.Y)^2) ≤
    4 * ((1000*D)^4 * Fintype.card (DemandTag (V := V) (E := BagEdge bags))) *
      MatchingFPRAS.PairEnergy.swapSum π PatternCode.throughStates PatternCode.closedStates
        (PatternCode.firstDerivative f) (PatternCode.secondDerivative g) := by
  classical
  dsimp only
  let wt := fun e => max lo (min hi (w e))
  let π := gibbsLaw wt (fun _ => lt_of_lt_of_le hlo (le_max_left _ _)) M
  let ρ := fun e : ErrorDemand hbags hG => π.weight e.demand.1.1 * π.weight e.demand.1.2
  let enc := fun j (e : ErrorDemand hbags hG) => e.choice height hheight hstep D hD w hw lo hi hlo hlohi j
  have h := MatchingFPRAS.PairEnergy.error_demand_load π PatternCode.throughStates
    PatternCode.closedStates (PatternCode.firstDerivative f) (PatternCode.secondDerivative g)
    ρ pattern (fun e => (enc false e).first) (fun e => (enc true e).first)
    ((1000*D)^4 * Fintype.card (DemandTag (V := V) (E := BagEdge bags)))
    (fun e => mul_nonneg (π.nonneg _) (π.nonneg _)) (by positivity)
    (fun e => e.choice_through height hheight hstep D hD w hw lo hi hlo hlohi false)
    (fun e => e.choice_through height hheight hstep D hD w hw lo hi hlo hlohi true)
    (context_load height hheight hstep D hD w hw lo hi hlo hlohi M false)
    (context_load height hheight hstep D hD w hw lo hi hlo hlohi M true)
  convert h using 1
  apply Finset.sum_congr rfl
  intro e _
  rw [e.literal_error height hheight hstep D hD w hw lo hi hlo hlohi f]

end ErrorDemand

end MatchingFPRAS.Transport.CellDemands

namespace MatchingFPRAS.Transport.PatternCode

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

variable (π : MatchingFPRAS.PairEnergy.Law (PM inc)) (f g : Finset E → ℝ)

omit [DecidableEq V] in
lemma statewise_swap_bound (A B : PM inc) :
    (∑ x : PatternCode inc, if x.through ⊆ A.val ∧ x.closed ⊆ B.val then
      (firstDerivative f x A - secondDerivative g x B)^2 else 0) ≤
    ∑ S ∈ components (inc := inc) (A.val ∪ B.val),
      ((f A.val + g B.val) - (f (exchange A.val B.val S) + g (exchange B.val A.val S)))^2 := by
  have h := activated_sum_le A.property B.property f g
  convert h using 1
  apply Finset.sum_congr rfl
  intro x _
  split_ifs with hx
  · rw [Finset.sdiff_union_of_subset hx.1,Finset.sdiff_union_of_subset hx.2]
    rfl
  · rfl

omit [DecidableEq V] in
theorem weighted_swap_bound :
    MatchingFPRAS.PairEnergy.swapSum π throughStates closedStates
      (firstDerivative f) (secondDerivative g) ≤
    ∑ A : PM inc, ∑ B : PM inc, π.weight A * π.weight B *
      ∑ S ∈ components (inc := inc) (A.val ∪ B.val),
        ((f A.val + g B.val) - (f (exchange A.val B.val S) + g (exchange B.val A.val S)))^2 := by
  classical
  let cost := fun (x : PatternCode inc) (A B : PM inc) =>
    if x.through ⊆ A.val ∧ x.closed ⊆ B.val then
      (firstDerivative f x A - secondDerivative g x B)^2 else 0
  have hsum : MatchingFPRAS.PairEnergy.swapSum π throughStates closedStates
      (firstDerivative f) (secondDerivative g) =
      ∑ A : PM inc, ∑ B : PM inc, π.weight A * π.weight B * ∑ x : PatternCode inc, cost x A B := by
    unfold MatchingFPRAS.PairEnergy.swapSum
    calc
      _ = ∑ x : PatternCode inc, ∑ A : PM inc, ∑ B : PM inc,
          π.weight A * π.weight B * cost x A B := by
        apply Finset.sum_congr rfl
        intro x _
        simp only [throughStates,closedStates,Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro A _
        by_cases ht : x.through ⊆ A.val
        · simp only [ht,ite_true]
          apply Finset.sum_congr rfl
          intro B _
          by_cases hc : x.closed ⊆ B.val <;> simp [cost,ht,hc]
        · simp [cost,ht]
      _ = ∑ A : PM inc, ∑ B : PM inc, ∑ x : PatternCode inc,
          π.weight A * π.weight B * cost x A B := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro A _
        rw [Finset.sum_comm]
      _ = _ := by simp only [Finset.mul_sum]
  rw [hsum]
  apply Finset.sum_le_sum
  intro A _
  apply Finset.sum_le_sum
  intro B _
  exact mul_le_mul_of_nonneg_left (statewise_swap_bound f g A B)
    (mul_nonneg (π.nonneg A) (π.nonneg B))

end MatchingFPRAS.Transport.PatternCode

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

def SafeSwitch (w : E → ℝ) (K : ℝ) (A B : PM inc) : Prop :=
  ∃ (v : Fin 4 → V) (e : Fin 4 → E) (R : Finset E),
    Function.Injective v ∧
    (∀ i x, inc (e i) x ↔ x = v i ∨ x = v (i+1)) ∧
    A.val = R ∪ {e 0,e 2} ∧ B.val = R ∪ {e 1,e 3} ∧
    (∀ i j, w (e i) ≤ K * w (e j))

noncomputable def safeDestinations (w : E → ℝ) (K : ℝ) (A : PM inc) : Finset (PM inc) := by
  classical
  exact Finset.univ.filter (SafeSwitch w K A)

namespace CellPaths

variable (c : CellPaths inc)

def commonInterior : Finset E := assemble fun i => (c.side i).interior

omit [Fintype V] [Fintype E] in
lemma switched_true_common : c.switched true = c.commonInterior ∪ {c.chord 0,c.chord 2} := by
  ext e
  simp [switched,switchPieces,pieces,assemble,sideBit,OddPath.closed,commonInterior]
  tauto

omit [Fintype V] [Fintype E] in
lemma switched_false_common : c.switched false = c.commonInterior ∪ {c.chord 1,c.chord 3} := by
  ext e
  simp [switched,switchPieces,pieces,assemble,sideBit,OddPath.closed,commonInterior]
  tauto

omit [Fintype E] in
lemma safe_switch (w : E → ℝ) (K : ℝ) (hw : ∀ i j, w (c.chord i) ≤ K*w (c.chord j))
    (R : Finset E) (A B : PM inc)
    (hA : A.val = R ∪ c.switched true) (hB : B.val = R ∪ c.switched false) :
    SafeSwitch w K A B := by
  refine ⟨fun i => (c.side i).vertex 0,c.chord,R ∪ c.commonInterior,
    c.corners_injective,?_,?_,?_,hw⟩
  · intro i x
    rw [c.chord_incidence,c.joins]
  · rw [hA,c.switched_true_common,Finset.union_assoc]
  · rw [hB,c.switched_false_common,Finset.union_assoc]

end CellPaths

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport.CellDemands

section

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

namespace Demand

variable (d : Demand hbags hG)

noncomputable def switchState (b : Bool) : PM (BagEdge.Incident (bags := bags)) :=
  let emb := d.corners.embeddedPair d.1.1 d.1.2 d.2.1.cycle_union
    d.paths.chord d.paths.chord_incidence 0
  emb.attachFirst (d.paths.switched b) (d.paths.switched_matching b)

omit [Fintype L] in
lemma switchState_val (b : Bool) : (d.switchState b).val = d.outside ∪ d.paths.switched b := by
  exact congrArg (fun R => R ∪ d.paths.switched b)
    (d.corners.embeddedPair_outside d.1.1 d.1.2 d.2.1.cycle_union
      d.paths.chord d.paths.chord_incidence 0)

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

variable (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi)

include hheight hstep hD hw hlo in
omit [Fintype L] in
lemma switchState_safe : SafeSwitch (fun e => max lo (min hi (w e))) (1000*D)
    (d.switchState true) (d.switchState false) := by
  apply d.paths.safe_switch _ _ _ d.outside _ _ (d.switchState_val true) (d.switchState_val false)
  intro i j
  exact d.cycle.cell_clamp_comparability hbags height hheight hstep d.cell d.last_lt D hD w hw
    lo hi (le_of_lt hlo) ⟨i,Or.inl rfl⟩ ⟨j,Or.inl rfl⟩

lemma switchChoice_first :
    (d.switchChoice height hheight hstep D hD w hw lo hi hlo hlohi).first = d.switchState true := by
  apply Subtype.ext
  exact (d.switchChoice_spec height hheight hstep D hD w hw lo hi hlo hlohi).1.trans
    (d.switchState_val true).symm

include hheight hstep hD hw hlohi

theorem switch_load_bound (M : PM (BagEdge.Incident (bags := bags)))
    (f : Finset (BagEdge bags) → ℝ) :
    let wt := fun e => max lo (min hi (w e))
    let π := gibbsLaw wt (fun _ => lt_of_lt_of_le hlo (le_max_left _ _)) M
    (∑ d : Demand hbags hG, π.weight d.1.1 * π.weight d.1.2 *
      (f (d.outside ∪ d.paths.switched true) - f (d.outside ∪ d.paths.switched false))^2) ≤
    ((1000*D)^4 * Fintype.card (DemandTag (V := V) (E := BagEdge bags))) *
      ∑ A : PM BagEdge.Incident, π.weight A *
        ∑ B ∈ safeDestinations wt (1000*D) A, (f A.val-f B.val)^2 := by
  classical
  dsimp only
  let wt := fun e => max lo (min hi (w e))
  let π := gibbsLaw wt (fun _ => lt_of_lt_of_le hlo (le_max_left _ _)) M
  let ρ := fun d : Demand hbags hG => π.weight d.1.1 * π.weight d.1.2
  let enc := fun d : Demand hbags hG => d.switchChoice height hheight hstep D hD w hw lo hi hlo hlohi
  let C := (1000*D)^4 * Fintype.card (DemandTag (V := V) (E := BagEdge bags))
  let cost := fun A : PM BagEdge.Incident =>
    ∑ B ∈ safeDestinations wt (1000*D) A, (f A.val-f B.val)^2
  have hc (A) : 0 ≤ cost A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hload (A : PM BagEdge.Incident) :
      MatchingFPRAS.PairEnergy.contextMass ρ (fun _ => ()) (fun d => (enc d).first) () A ≤ C*π.weight A := by
    have h := MatchingFPRAS.PairEnergy.tagged_context_bound π (fun _ : Unit => Finset.univ) ρ
      (fun _ => ()) (fun d => (enc d).first) (fun d => (enc d).second) (fun d => (enc d).tag)
      ((1000*D)^4) (by positivity) (fun _ => Finset.mem_univ _)
      (switchChoice_injective height hheight hstep D hD w hw lo hi hlo hlohi)
      (fun d => (d.switchChoice_spec height hheight hstep D hD w hw lo hi hlo hlohi).2) () A
    simpa only [MatchingFPRAS.PairEnergy.guideMass,π.total,mul_one] using h
  have hd (d : Demand hbags hG) :
      (f (d.outside ∪ d.paths.switched true)-f (d.outside ∪ d.paths.switched false))^2 ≤
      cost (enc d).first := by
    have he := d.switchChoice_first height hheight hstep D hD w hw lo hi hlo hlohi
    change _ ≤ cost _
    rw [he,← d.switchState_val true,← d.switchState_val false]
    exact Finset.single_le_sum (fun (B : PM (BagEdge.Incident (bags := bags))) _ =>
      sq_nonneg (f (d.switchState true).val-f B.val)) (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,d.switchState_safe height hheight hstep D hD w hw lo hi hlo⟩)
  calc
    _ ≤ ∑ d : Demand hbags hG, ρ d * cost (enc d).first :=
      Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (hd d)
        (mul_nonneg (π.nonneg _) (π.nonneg _))
    _ = ∑ A : PM BagEdge.Incident,
        MatchingFPRAS.PairEnergy.contextMass ρ (fun _ => ()) (fun d => (enc d).first) () A * cost A := by
      simpa using MatchingFPRAS.PairEnergy.sum_contextMass ρ (fun _ => ()) (fun d => (enc d).first)
        (fun _ : Unit => Finset.univ) (fun _ => Finset.mem_univ _) (fun _ => cost)
    _ ≤ ∑ A : PM BagEdge.Incident, C*π.weight A*cost A :=
      Finset.sum_le_sum fun A _ => mul_le_mul_of_nonneg_right (hload A) (hc A)
    _ = _ := by simp only [C,cost,π,wt,Finset.mul_sum,mul_assoc]

end Demand

end

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

namespace Demand

noncomputable def cellError (d : Demand hbags hG) (f : Finset (BagEdge bags) → ℝ) (b : Bool) : ℝ :=
  d.paths.contextError d.outside f b (if b then 2 else 3) (if b then 0 else 1)

noncomputable def cellSwitch (d : Demand hbags hG) (f : Finset (BagEdge bags) → ℝ) : ℝ :=
  f (d.outside ∪ d.paths.switched true)-f (d.outside ∪ d.paths.switched false)

noncomputable def cellCost (d : Demand hbags hG) (f : Finset (BagEdge bags) → ℝ) : ℝ :=
  (d.cellSwitch f)^2+(d.cellError f true)^2+(d.cellError f false)^2

end Demand

lemma sum_errorDemands (ρ : Demand hbags hG → ℝ) (f : Finset (BagEdge bags) → ℝ) :
    (∑ e : ErrorDemand hbags hG, ρ e.demand * (e.demand.cellError f e.bit)^2) =
    ∑ d : Demand hbags hG, ρ d * ((d.cellError f true)^2+(d.cellError f false)^2) := by
  classical
  let p := fun e : Bool × Demand hbags hG =>
    ∀ i : Fin 4, CellPaths.sideBit i = e.1 → (e.2.paths.side i).length ≠ 1
  let H := fun e : Bool × Demand hbags hG => ρ e.2 * (e.2.cellError f e.1)^2
  have hzero (e : Bool × Demand hbags hG) (he : ¬ p e) : H e = 0 := by
    have h := e.2.short_error_zero f e.1 he
    simp only [H,Demand.cellError,h,zero_pow (by decide : 2≠0),mul_zero]
  calc
    _ = ∑ e ∈ Finset.univ.filter p, H e := (Finset.sum_subtype (p := p) _
      (fun _ => by simp only [Finset.mem_filter,Finset.mem_univ,true_and]) H).symm
    _ = ∑ e : Bool × Demand hbags hG, H e :=
      Finset.sum_subset (Finset.filter_subset _ _) (by
        intro e _ he
        exact hzero e (fun hp => he (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩)))
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [H,Fintype.sum_bool,← Finset.sum_add_distrib,mul_add]

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

variable (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi)

include hheight hstep hD hw hlohi

theorem total_cell_demand_load (M : PM (BagEdge.Incident (bags := bags)))
    (f g : Finset (BagEdge bags) → ℝ) :
    let wt := fun e => max lo (min hi (w e))
    let π := gibbsLaw wt (fun _ => lt_of_lt_of_le hlo (le_max_left _ _)) M
    (∑ d : Demand hbags hG, π.weight d.1.1 * π.weight d.1.2 * d.cellCost f) ≤
    ((1000*D)^4 * Fintype.card (DemandTag (V := V) (E := BagEdge bags))) *
      ((∑ A : PM BagEdge.Incident, π.weight A *
          ∑ B ∈ safeDestinations wt (1000*D) A, (f A.val-f B.val)^2) +
       4 * ∑ A : PM BagEdge.Incident, ∑ B : PM BagEdge.Incident, π.weight A * π.weight B *
          ∑ S ∈ components (inc := BagEdge.Incident) (A.val ∪ B.val),
            ((f A.val+g B.val)-(f (exchange A.val B.val S)+g (exchange B.val A.val S)))^2) := by
  classical
  dsimp only
  let wt := fun e => max lo (min hi (w e))
  let π := gibbsLaw wt (fun _ => lt_of_lt_of_le hlo (le_max_left _ _)) M
  let C := (1000*D)^4 * Fintype.card (DemandTag (V := V) (E := BagEdge bags))
  have hC : 0 ≤ C := by positivity
  have hs := Demand.switch_load_bound (hbags := hbags) (hG := hG) height hheight hstep D hD w hw lo hi hlo hlohi M f
  have he := ErrorDemand.error_load_bound (hbags := hbags) (hG := hG) height hheight hstep D hD w hw lo hi hlo hlohi f g M
  have hsw := PatternCode.weighted_swap_bound π f g
  have herr := mul_le_mul_of_nonneg_left hsw (mul_nonneg (by norm_num : (0:ℝ)≤4) hC)
  have hsum := sum_errorDemands (hbags := hbags) (hG := hG)
    (fun d => π.weight d.1.1 * π.weight d.1.2) f
  change (∑ e : ErrorDemand hbags hG, π.weight e.demand.1.1 * π.weight e.demand.1.2 *
    (e.demand.cellError f e.bit)^2) ≤ _ at he
  rw [hsum] at he
  have hsplit : (∑ d : Demand hbags hG, π.weight d.1.1 * π.weight d.1.2 * d.cellCost f) =
      (∑ d : Demand hbags hG, π.weight d.1.1 * π.weight d.1.2 * (d.cellSwitch f)^2) +
      (∑ d : Demand hbags hG, π.weight d.1.1 * π.weight d.1.2 *
        ((d.cellError f true)^2+(d.cellError f false)^2)) := by
    simp only [Demand.cellCost,mul_add,Finset.sum_add_distrib]
    ring
  change (∑ d : Demand hbags hG, π.weight d.1.1 * π.weight d.1.2 * d.cellCost f) ≤ _
  rw [hsplit]
  change (∑ d : Demand hbags hG, π.weight d.1.1 * π.weight d.1.2 * (d.cellSwitch f)^2) ≤ _ at hs
  have h := add_le_add hs (he.trans herr)
  calc
    _ ≤ _ := h
    _ = _ := by dsimp only [C,π,wt]; ring

end MatchingFPRAS.Transport.CellDemands

end OAI
