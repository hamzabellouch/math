import OAI.Probability.CriticalZ3.ExplorationConnectivity

namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace InfiniteConditioning.History
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

omit [Countable E] in
theorem observe_pattern (h : History E) (R : Finset E) {ω : E → Bool}
    (hω : ω ∈ pattern h.known h.values) :
    ω ∈ pattern (h.observe R ω).known (h.observe R ω).values := by
  intro e he
  change ω e = replace R ω h.values e
  by_cases heR : e ∈ R
  · simp only [replace,ite_eq_left heR]
  · have heK : e ∈ h.known := (Finset.mem_union.mp he).resolve_right heR
    simpa only [replace,ite_eq_right heR] using hω e heK
end InfiniteConditioning.History

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Model

def Connected : (m : Model) → m.Config → Vertex → Vertex → Prop
  | .bond,ω,x,y => BondConnected ω x y
  | .site,ω,x,y => SiteConnected ω x y

def Cluster (m : Model) (ω : m.Config) (x : Vertex) : Set Vertex :=
  {y | m.Connected ω x y}

theorem infiniteAt_iff (m : Model) (ω : m.Config) (x : Vertex) :
    ω ∈ m.InfiniteAt x ↔ (m.Cluster ω x).Infinite := by cases m <;> rfl

theorem measurableSet_infiniteAt (m : Model) (x : Vertex) : MeasurableSet (m.InfiniteAt x) := by
  cases m
  · exact measurableSet_bondInfiniteAt x
  · exact measurableSet_siteInfiniteAt x
end Model

namespace LatticeGraph

theorem conn_global (G : LatticeGraph) (m : Model) {ω : m.Config} {x y : G.Node}
    (h : G.Conn m ω x y) : m.Connected ω x.1 y.1 := by
  cases m
  · exact G.bondConn_global h
  · exact G.siteConn_global h
end LatticeGraph

namespace Coarse.Exploration
variable {m : Model} {r : ℕ}

def Sound (s : Exploration m r) (ω : m.Config) : Prop :=
  ∀ v ∈ s.good, ∃ y, (B r v).Contains y ∧ m.Connected ω 0 y

theorem accepted_event {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts)
    {ω : m.Config} (hω : ω ∈ pattern s.history.known s.history.values)
    (ha : s.Accept q δ t ω) : ω ∈ t.event m := by
  have hh := (accept_current_iff hs hq ω).mp ha.1
  change s.history.freeze ω ∈ t.event m at hh
  simpa only [History.freeze,replace_eq_of_pattern hω] using hh

theorem sound_advance {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {ω : m.Config}
    (hω : ω ∈ pattern s.history.known s.history.values) (hS : s.Sound ω) :
    (s.advance q δ ω).Sound ω := by
  cases hq : s.queue with
  | nil => rwa [advance_empty s q δ ω hq]
  | cons t ts =>
    intro v hv
    simp only [advance,hq] at hv
    split_ifs at hv with ha
    · rcases Finset.mem_insert.mp hv with rfl|hv
      · obtain ⟨y,hy,hpath⟩ := accepted_event hs hq hω ha
        exact ⟨y.1,hy,t.graph.conn_global m hpath⟩
      · exact hS v hv
    · exact hS v hv

theorem run_pattern (q : Set.Icc (0:ℝ) 1) (δ : ℝ) {s : Exploration m r}
    {ω : m.Config} (hω : ω ∈ pattern s.history.known s.history.values) (n : ℕ) :
    ω ∈ pattern (run q δ n s ω).history.known (run q δ n s ω).history.values := by
  induction n generalizing s with
  | zero => exact hω
  | succ n ih => exact ih (s.history.observe_pattern s.reveal hω)

theorem run_sound {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {ω : m.Config}
    (hω : ω ∈ pattern s.history.known s.history.values) (hS : s.Sound ω) (n : ℕ) :
    (run q δ n s ω).Sound ω := by
  induction n generalizing s with
  | zero => exact hS
  | succ n ih =>
    exact ih (valid_advance hs ω) (s.history.observe_pattern s.reveal hω)
      (sound_advance hs hω hS)

theorem good_finite_of_cluster_finite {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {ω : m.Config}
    (hω : ω ∈ pattern s.history.known s.history.values) (hS : s.Sound ω)
    (hfin : (m.Cluster ω 0).Finite) : (Good q δ s ω).Finite := by
  have hf (y : Vertex) : ({v | (B r v).Contains y} : Set Point).Finite := by
    apply Set.Subsingleton.finite
    intro v hv w hw
    exact cube_unique r (B_subset_Q r v y hv) (B_subset_Q r w y hw)
  apply (hfin.biUnion (fun y _ => hf y)).subset
  intro v hv
  obtain ⟨n,hn⟩ := hv
  obtain ⟨y,hy,hc⟩ := run_sound hs hω hS n v hn
  exact Set.mem_iUnion.mpr ⟨y,Set.mem_iUnion.mpr ⟨hc,hy⟩⟩
end Coarse.Exploration

namespace Coarse

theorem initial_sound (m : Model) (r : ℕ) {ω : m.Config}
    (hω : ω ∈ allValue (rootBits m r) true) : (initial m r).Sound ω := by
  intro v hv
  have hv0 : v = 0 := Finset.mem_singleton.mp hv
  subst v
  refine ⟨0,?_,?_⟩
  · rw [B,center_zero]
    exact Box.center_mem_cube _ _
  · cases m
    · exact Relation.ReflTransGen.refl
    · refine ⟨hω 0 ?_,Relation.ReflTransGen.refl⟩
      apply Finset.mem_union_left
      exact (Box.mem_vertices _ _).mpr (zero_in_Q r)

end Coarse
end CriticalZ3

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse

theorem scales_percolate {m : Model} (sc : ScaleData m) :
    0 < m.law (sc.q : ℝ) (m.InfiniteAt 0) := by
  let s := initial m sc.r
  let μ := ProductCylinder.law (s.history.parameter sc.q)
  let ν := ProductCylinder.law (fun _ : m.Bit => sc.q)
  have hs : s.Valid sc.q sc.δ := initial_valid sc
  have hb := Exploration.finite_good_bound sc hs (initial_colored m sc.r) rfl
    (initial_closed m sc.r) (initial_covered m sc.r)
  have hle : μ.real (m.InfiniteAt 0)ᶜ ≤ μ.real
      {ω | (Exploration.Good sc.q sc.δ s ω).Finite ∧ (0,0) ∈ Exploration.Good sc.q sc.δ s ω} := by
    apply finite_measureReal_mono_ae
    filter_upwards [ae_fixed_pattern (fun _ : m.Bit => sc.q) (rootBits m sc.r) (fun _ => true)] with ω hω
    intro hn
    have hfin : (m.Cluster ω 0).Finite := by
      by_contra hnf
      exact hn ((m.infiniteAt_iff ω 0).mpr hnf)
    exact ⟨Exploration.good_finite_of_cluster_finite hs hω (initial_sound m sc.r hω) hfin,
      Exploration.initial_good_subset sc.q sc.δ s ω (Finset.mem_singleton_self _)⟩
  have hpos : 0 < μ.real (m.InfiniteAt 0) := by
    rw [measureReal_compl (m.measurableSet_infiniteAt 0),probReal_univ] at hle
    dsimp [μ] at hle
    linarith
  let H := allValue (rootBits m sc.r) true
  have hH : 0 < ν.real H := by
    rw [show ν.real H = (sc.q : ℝ)^(rootBits m sc.r).card by
      exact allValue_probability_constant (fun _ : m.Bit => sc.q) (rootBits m sc.r)
        sc.q (fun _ _ => rfl) true]
    exact pow_pos sc.q_pos _
  have he : ν.real (H ∩ m.InfiniteAt 0) = ν.real H * μ.real (m.InfiniteAt 0) :=
    pattern_inter_real _ _ _ _ (m.measurableSet_infiniteAt 0)
  have hinf : 0 < ν.real (m.InfiniteAt 0) :=
    (he ▸ mul_pos hH hpos).trans_le (measureReal_mono Set.inter_subset_right)
  rw [m.law_coe_eq_product]
  exact ENNReal.toReal_pos_iff.mp hinf |>.1

/-- Positive percolation is open to the left throughout the open unit interval. -/
theorem lower_percolating_parameter (m : Model) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hInf : 0 < m.law p (m.InfiniteAt 0)) :
    ∃ q ∈ Set.Icc (0:ℝ) 1, q < p ∧ 0 < m.law q (m.InfiniteAt 0) := by
  obtain ⟨sc,hsc⟩ := exists_scales m hp hp1 hInf
  exact ⟨sc.q,sc.q.property,hsc ▸ sc.q_lt,scales_percolate sc⟩

end Coarse
end CriticalZ3

end OAI
