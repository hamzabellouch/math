import Mathlib
import OAI.Probability.UnimodularPercolation.Clusters.Uniqueness

namespace OAI

/-! Bond paths, degree bounds and positivity of the critical parameter. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section BondPaths
attribute [local instance] Classical.propDecidable

 
inductive Along (G : BondGraph V E) : V → List E → V → Prop
  | nil (x : V) : Along G x [] x
  | cons {x z y : V} {l : List E} (e : E) (he : G e = s(x,z))
      (tail : Along G z l y) : Along G x (e :: l) y

 theorem Along.conn {G : BondGraph V E} {x y : V} {l : List E} (h : Along G x l y)
    {ω : Set E} (ho : ∀ e ∈ l, e ∈ ω) : Conn G ω x y := by
  induction h with
  | nil => exact conn_refl G ω _
  | @cons x z y l e he ht ih =>
    exact (Relation.ReflTransGen.single ⟨e, ho e (by simp), he⟩).trans
      (ih (fun e' he' => ho e' (by simp [he'])))

 def openSimpleGraph (G : BondGraph V E) (ω : Set E) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ e ∈ ω, G e = s(x,y)
  symm := ⟨by
    rintro x y ⟨hxy, e, he, h⟩
    exact ⟨hxy.symm, e, he, h.trans (Sym2.eq_swap ..)⟩⟩
  loopless := ⟨by simp⟩

 theorem conn_iff_reachable (G : BondGraph V E) (ω : Set E) (x y : V) :
    Conn G ω x y ↔ (openSimpleGraph G ω).Reachable x y := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨.nil⟩
    | @tail z y h hy ih =>
      obtain ⟨w⟩ := ih
      by_cases hzy : z = y
      · subst y; exact ⟨w⟩
      · exact ⟨w.concat ⟨hzy, hy⟩⟩
  · rintro ⟨w⟩
    induction w with
    | nil => exact conn_refl G ω _
    | @cons x z y hadj w ih =>
      exact (Relation.ReflTransGen.single hadj.2).trans ih

 theorem walk_lift_bonds (G : BondGraph V E) (ω : Set E) {x y : V}
    (w : (openSimpleGraph G ω).Walk x y) :
    ∃ l : List E, Along G x l y ∧ l.map G = w.edges ∧ ∀ e ∈ l, e ∈ ω := by
  induction w with
  | nil => exact ⟨[], .nil _, rfl, by simp⟩
  | @cons x z y hadj w ih =>
    obtain ⟨e, he, heq⟩ := hadj.2
    obtain ⟨l, hl, hmap, hopen⟩ := ih
    refine ⟨e :: l, .cons e heq hl, ?_, ?_⟩
    · simp [hmap, heq]
    · intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · exact he
      · exact hopen e' he'

 
 theorem conn_exists_bond_trail (G : BondGraph V E) {ω : Set E} {x y : V}
    (h : Conn G ω x y) :
    ∃ l : List E, Along G x l y ∧ l.Nodup ∧ ∀ e ∈ l, e ∈ ω := by
  obtain ⟨w⟩ := (conn_iff_reachable G ω x y).mp h
  obtain ⟨l, hl, hmap, hopen⟩ := walk_lift_bonds G ω (w.toPath : (openSimpleGraph G ω).Walk x y)
  refine ⟨l, hl, ?_, hopen⟩
  apply List.Nodup.of_map (f := G)
  rw [hmap]
  exact w.toPath.property.isTrail.edges_nodup

 theorem Along.append {G : BondGraph V E} {x y z : V} {l k : List E}
    (hl : Along G x l y) (hk : Along G y k z) : Along G x (l ++ k) z := by
  induction hl with
  | nil => exact hk
  | cons e he ht ih => exact .cons e he (ih hk)

end BondPaths

section DegreeBound
attribute [local instance] Classical.propDecidable

 def Step (G : BondGraph V E) (x : V) := {ey : E × V // G ey.1 = s(x,ey.2)}

 theorem finite_steps (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    Set.Finite {ey : E × V | G ey.1 = s(x,ey.2)} := by
  apply ((hloc x).prod (finite_neighbors hloc x)).subset
  rintro ⟨e,y⟩ he
  change G e = s(x,y) at he
  exact ⟨by change x ∈ G e; rw [he]; simp, e, he⟩

 noncomputable def stepEquiv (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (x : V) : Step G x ≃ Step G (a x) where
  toFun d := ⟨(b d.val.1, a d.val.2), by rw [h, d.property, Sym2.map_mk]⟩
  invFun d := ⟨(b.symm d.val.1, a.symm d.val.2), by
    rw [isAut_symm G h, d.property, Sym2.map_mk, Equiv.symm_apply_apply]⟩
  left_inv d := by apply Subtype.ext; exact Prod.ext (b.symm_apply_apply _) (a.symm_apply_apply _)
  right_inv d := by apply Subtype.ext; exact Prod.ext (b.apply_symm_apply _) (a.apply_symm_apply _)

 noncomputable def degree (G : BondGraph V E) (x : V) : ℕ := Nat.card (Step G x)

 theorem degree_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (x : V) : degree G (a x) = degree G x :=
  (Nat.card_congr (stepEquiv G h x)).symm

 theorem exists_degree_bound (G : BondGraph V E) (hqt : QuasiTransitive G) :
    ∃ D : ℕ, 0 < D ∧ ∀ x, degree G x ≤ D := by
  obtain ⟨F, hF⟩ := hqt
  refine ⟨(∑ x ∈ F, degree G x) + 1, Nat.zero_lt_succ _, ?_⟩
  intro x
  obtain ⟨o, ho, a, b, hab, rfl⟩ := hF x
  rw [degree_aut G hab]
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) ho).trans (Nat.le_succ _)

end DegreeBound

section SmallParameter
attribute [local instance] Classical.propDecidable

def TrailLength (G : BondGraph V E) (x : V) (n : ℕ) : Set (Set E) :=
  {ω | ∃ y l, Along G x l y ∧ l.Nodup ∧ l.length = n ∧ ∀ e ∈ l, e ∈ ω}

theorem trailLength_upper (G : BondGraph V E) (x : V) (n : ℕ) :
    IsUpperSet (TrailLength G x n) := by
  rintro ω η h ⟨y,l,hl,hn,hlen,ho⟩
  exact ⟨y,l,hl,hn,hlen,fun e he => h (ho e he)⟩

theorem finiteWitness_trailLength (G : BondGraph V E) (x : V) (n : ℕ) :
    FiniteWitness (TrailLength G x n) := by
  rintro ω ⟨y,l,hl,hn,hlen,ho⟩
  exact ⟨l.toFinset, fun e he => ho e (List.mem_toFinset.mp he),
    y,l,hl,hn,hlen, fun e he => List.mem_toFinset.mpr he⟩

theorem finiteWitness_edge (e : E) : FiniteWitness {ω : Set E | e ∈ ω} := by
  intro ω he
  exact ⟨{e}, by simpa using he, by simp⟩

theorem trailLength_succ_subset (G : BondGraph V E) (x : V) (n : ℕ) :
    TrailLength G x (n+1) ⊆ ⋃ d : Step G x,
      DisjointOccurrence {ω | d.val.1 ∈ ω} (TrailLength G d.val.2 n) := by
  rintro ω ⟨y,l,hl,hn,hlen,ho⟩
  cases hl with
  | nil => simp at hlen
  | @cons x z y l e he tail =>
    refine Set.mem_iUnion.mpr ⟨⟨(e,z),he⟩, {e}, l.toFinset, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using ho e (by simp)
    · intro e' he'; exact ho e' (by simpa using Or.inr (List.mem_toFinset.mp he'))
    · simpa using (List.nodup_cons.mp hn).1
    · simp
    · exact ⟨y,l,tail,(List.nodup_cons.mp hn).2, by simpa using hlen,
        fun e' he' => List.mem_toFinset.mpr he'⟩

theorem trailLength_probability_le [Countable E] (G : BondGraph V E)
    (hloc : LocallyFinite G) (D : ℕ) (hD : ∀ x, degree G x ≤ D)
    (p : unitInterval) (x : V) (n : ℕ) :
    (law p).real (TrailLength G x n) ≤ ((D : ℝ) * p) ^ n := by
  induction n generalizing x with
  | zero => simpa only [pow_zero] using (measureReal_le_one (μ := law p) (s := TrailLength G x 0))
  | succ n ih =>
    let : Fintype (Step G x) := (finite_steps G hloc x).fintype
    let F := fun d : Step G x =>
      DisjointOccurrence {ω : Set E | d.val.1 ∈ ω} (TrailLength G d.val.2 n)
    calc
      (law p).real (TrailLength G x (n+1)) ≤ (law p).real (⋃ d, F d) :=
        measureReal_mono (trailLength_succ_subset G x n)
      _ ≤ ∑ d, (law p).real (F d) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _d : Step G x, (p : ℝ) * ((D : ℝ) * p) ^ n := by
        apply Finset.sum_le_sum
        intro d _
        have hb := bk p {ω : Set E | d.val.1 ∈ ω} (TrailLength G d.val.2 n)
          (fun _ _ hω he => hω he) (trailLength_upper G d.val.2 n)
          (finiteWitness_edge _) (finiteWitness_trailLength G d.val.2 n)
        have heq : (law p).real {ω : Set E | d.val.1 ∈ ω} = (p : ℝ) := by
          simpa using finite_open_probability p {d.val.1}
        rw [heq] at hb
        exact hb.trans (mul_le_mul_of_nonneg_left (ih d.val.2) p.2.1)
      _ ≤ (D : ℝ) * ((p : ℝ) * ((D : ℝ) * p) ^ n) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg p.2.1 (pow_nonneg (mul_nonneg (Nat.cast_nonneg D) p.2.1) n))
        exact_mod_cast (show Fintype.card (Step G x) ≤ D by
          simpa only [degree, Nat.card_eq_fintype_card] using hD x)
      _ = ((D : ℝ) * p) ^ (n+1) := by ring

 theorem Along.mem_reachBall {G : BondGraph V E} {x y : V} {l : List E}
    (h : Along G x l y) : y ∈ reachBall G x l.length := by
  induction h with
  | nil => exact Set.mem_singleton _
  | @cons x z y l e he ht ih =>
    have hadj : Adj G x z := ⟨e,he⟩
    have hstep : ∀ n, reachBall G z n ⊆ reachBall G x (n+1) := by
      intro n
      induction n with
      | zero =>
        rintro w rfl
        exact Or.inr (Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨Set.mem_singleton _, hadj⟩⟩)
      | succ n ih =>
        rintro w (hw | hw)
        · exact Or.inl (ih hw)
        · right
          simp only [Set.mem_iUnion] at hw ⊢
          obtain ⟨v,hv,hvw⟩ := hw
          exact ⟨v,ih hv,hvw⟩
    exact hstep _ ih

 theorem Along.take {G : BondGraph V E} {x y : V} {l : List E}
    (h : Along G x l y) (n : ℕ) : ∃ z, Along G x (l.take n) z := by
  induction h generalizing n with
  | @nil z => exact ⟨z, by simpa using (Along.nil (G := G) z)⟩
  | @cons x z y l e he ht ih =>
    cases n with
    | zero => exact ⟨x,.nil x⟩
    | succ n =>
      obtain ⟨v,hv⟩ := ih n
      exact ⟨v,.cons e he hv⟩

 theorem reachBall_mono (G : BondGraph V E) (x : V) : Monotone (reachBall G x) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Set.subset_union_left

 theorem infinite_cluster_subset_trailLength (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (n : ℕ) : {ω | (cluster G ω x).Infinite} ⊆ TrailLength G x n := by
  intro ω hω
  obtain ⟨y,hy,hyball⟩ := hω.exists_notMem_finite (finite_reachBall hloc x n)
  obtain ⟨l,hl,hn,ho⟩ := conn_exists_bond_trail G hy
  have hlen : n ≤ l.length := by
    by_contra h
    exact hyball ((reachBall_mono G x (le_of_lt (Nat.lt_of_not_ge h))) hl.mem_reachBall)
  obtain ⟨z,hz⟩ := hl.take n
  exact ⟨z,l.take n,hz,hn.take,List.length_take_of_le hlen,
    fun e he => ho e (List.mem_of_mem_take he)⟩

 theorem infinite_cluster_probability_eq_zero_of_small [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (D : ℕ) (hD : ∀ x, degree G x ≤ D)
    (p : unitInterval) (hp : (D : ℝ) * p < 1) (x : V) :
    law p {ω | (cluster G ω x).Infinite} = 0 := by
  apply (measureReal_eq_zero_iff).mp
  apply le_antisymm _ measureReal_nonneg
  apply ge_of_tendsto (tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg (Nat.cast_nonneg D) p.2.1) hp)
  filter_upwards [] with n
  exact (measureReal_mono (infinite_cluster_subset_trailLength G hloc x n)).trans
    (trailLength_probability_le G hloc D hD p x n)

 theorem exists_infinite_cluster_probability_eq_zero_of_small [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (D : ℕ) (hD : ∀ x, degree G x ≤ D)
    (p : unitInterval) (hp : (D : ℝ) * p < 1) :
    law p {ω | (infiniteClusters G ω).Nonempty} = 0 := by
  have heq : {ω | (infiniteClusters G ω).Nonempty} =
      ⋃ x : V, {ω | (cluster G ω x).Infinite} := by
    ext ω
    simp only [Set.mem_ofPred_eq, infiniteClusters_nonempty_iff, Set.mem_iUnion]
  rw [heq, measure_iUnion_null_iff]
  exact infinite_cluster_probability_eq_zero_of_small G hloc D hD p hp

 theorem pc_pos [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G) :
    0 < pc G := by
  obtain ⟨D, hDpos, hD⟩ := exists_degree_bound G hqt
  let t : unitInterval := ⟨1 / ((D : ℝ) + 1), by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) D]⟩
  have ht : (0 : unitInterval) < t := by
    change (0 : ℝ) < 1 / ((D : ℝ) + 1)
    positivity
  apply ht.trans_le
  apply le_sInf
  intro p hp
  by_contra h
  have hp' : (p : ℝ) < 1 / ((D : ℝ) + 1) := lt_of_not_ge h
  have hsmall : (D : ℝ) * p < 1 := by
    have hmul := (lt_div_iff₀ (show (0 : ℝ) < D + 1 by positivity)).mp hp'
    nlinarith [p.2.1]
  have hz := exists_infinite_cluster_probability_eq_zero_of_small G hloc D hD p hsmall
  exact (ne_of_gt hp) hz

end SmallParameter

section MainBridge
attribute [local instance] Classical.propDecidable

 

theorem mainConclusion_of_strict_gap [Infinite V] (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hgap : pc G < ptwo G) : MainConclusion G := by
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  obtain ⟨q, hq, hpq⟩ := lt_sSup_iff.mp hgap
  obtain ⟨p₂, hp₂, hp₂q⟩ := exists_between hpq
  obtain ⟨p₁, hp₁, hp₁₂⟩ := exists_between hp₂
  have hc : OperatorBounded G (pc G) := operatorBounded_of_le G hpq.le hq
  refine ⟨(operatorNorm_eq_sup_below G (pc G) (pc_pos G hloc hqt)).symm,
    (operatorNorm_lt_top_iff G (pc G)).mpr hc, hgap, ptwo_le_pu G hconn hqt, ?_⟩
  refine ⟨p₁, p₂, hp₁, hp₁₂, hp₂q.trans_le (show q ≤ 1 from q.2.2), ?_⟩
  exact coupled_interval G hconn hloc hqt p₁ p₂ hp₁
    (operatorBounded_of_le G hp₂q.le hq)

end MainBridge

end Percolation

end OAI
