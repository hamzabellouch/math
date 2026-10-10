import Mathlib
import OAI.Probability.UnimodularPercolation.Main

namespace OAI

/-! Critical connection probabilities and nonamenable growth. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory Filter
open scoped Topology
universe u v
variable {V : Type u} {E : Type v}

theorem connectivity_twoPoint_mul_le [Countable E] (G : BondGraph V E) (p : unitInterval)
    (x y z : V) : twoPoint G p x y * twoPoint G p y z ≤ twoPoint G p x z := by
  have h := association_finiteWitness p {ω | Conn G ω x y} {ω | Conn G ω y z}
    (fun _ _ hst hxy => conn_mono G hst hxy)
    (fun _ _ hst hyz => conn_mono G hst hyz)
    (finiteWitness_conn G x y) (finiteWitness_conn G y z)
  refine h.trans (measureReal_mono ?_)
  intro ω hω
  exact conn_trans G ω hω.1 hω.2

theorem reachBall_split (G : BondGraph V E) (x z : V) (n m : ℕ)
    (hz : z ∈ reachBall G x (n+m)) :
    ∃ y ∈ reachBall G x n, z ∈ reachBall G y m := by
  induction m generalizing z with
  | zero =>
      exact ⟨z,by simpa using hz,by simp [reachBall]⟩
  | succ m ih =>
      change z ∈ reachBall G x (n+m) ∪ _ at hz
      rcases hz with hz | hz
      · obtain ⟨y,hy,hyz⟩ := ih z hz
        exact ⟨y,hy,Or.inl hyz⟩
      · simp only [Set.mem_iUnion,Set.mem_ofPred_eq] at hz
        obtain ⟨z',hz',hzz⟩ := hz
        obtain ⟨y,hy,hyz⟩ := ih z' hz'
        refine ⟨y,hy,Or.inr ?_⟩
        simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
        exact ⟨z',hyz,hzz⟩

theorem twoPoint_block_lower [Countable E] (G : BondGraph V E) (p : unitInterval)
    (n : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x y, y ∈ reachBall G x n → c ≤ twoPoint G p x y)
    (m : ℕ) (x y : V) (hy : y ∈ reachBall G x (n*m)) :
    c^m ≤ twoPoint G p x y := by
  induction m generalizing x y with
  | zero =>
      simp only [mul_zero,reachBall,Set.mem_singleton_iff] at hy
      subst y
      simp [twoPoint_self]
  | succ m ih =>
      rw [Nat.mul_succ] at hy
      obtain ⟨z,hz,hzy⟩ := reachBall_split G x y (n*m) n hy
      calc
        c^(m+1) = c^m*c := pow_succ _ _
        _ ≤ twoPoint G p x z * twoPoint G p z y :=
          mul_le_mul (ih x z hz) (h z y hzy) hc (twoPoint_nonneg G p x z)
        _ ≤ twoPoint G p x y := connectivity_twoPoint_mul_le G p x z y

theorem isoperimetric_ball_growth (G : BondGraph V E) (hloc : LocallyFinite G)
    (hh : 0 < hV G) (x : V) (n : ℕ) :
    (1+hV G)^n ≤ ((reachBall G x n).ncard : ℝ) := by
  classical
  induction n with
  | zero => simp [reachBall]
  | succ n ih =>
      let B := (finite_reachBall hloc x n).toFinset
      have heq : reachBall G x (n+1) = reachBall G x n ∪ vertexBoundary G B := by
        ext y
        simp only [reachBall,Set.mem_union,Set.mem_iUnion,Set.mem_ofPred_eq,vertexBoundary]
        constructor
        · rintro (hy | ⟨z,hz,hzy⟩)
          · exact Or.inl hy
          · by_cases hy : y ∈ reachBall G x n
            · exact Or.inl hy
            · exact Or.inr ⟨by simpa [B] using hy,z,by simpa [B] using hz,hzy⟩
        · rintro (hy | ⟨_,z,hz,hzy⟩)
          · exact Or.inl hy
          · exact Or.inr ⟨z,by simpa [B] using hz,hzy⟩
      have hd : Disjoint (reachBall G x n) (vertexBoundary G B) := by
        apply Set.disjoint_left.mpr
        intro y hy hb
        exact hb.1 (by simpa [B] using hy)
      have hb := hV_mul_card_le G B
      have hcard : B.card = (reachBall G x n).ncard :=
        (Set.ncard_eq_toFinset_card _ _).symm
      rw [hcard] at hb
      rw [heq,Set.ncard_union_eq hd (finite_reachBall hloc x n)
        (finite_vertexBoundary G hloc B),Nat.cast_add,pow_succ]
      have hh0 : 0 ≤ 1+hV G := by linarith
      nlinarith [mul_le_mul_of_nonneg_right ih hh0]

theorem subcritical_block_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hh : 0 < hV G) (p : unitInterval) (hp : p < pc G)
    (n : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x y, y ∈ reachBall G x n → c ≤ twoPoint G p x y) :
    (1+hV G)^n*c ≤ 1 := by
  classical
  by_contra hbad
  have hgt : 1 < (1+hV G)^n*c := lt_of_not_ge hbad
  let x : V := Classical.arbitrary V
  have hbound (m : ℕ) : ((1+hV G)^n*c)^m ≤ susceptibility G p x := by
    let B := (finite_reachBall hloc x (n*m)).toFinset
    calc
      ((1+hV G)^n*c)^m = (1+hV G)^(n*m)*c^m := by rw [mul_pow,pow_mul]
      _ ≤ (B.card:ℝ)*c^m := by
        simpa only [B, ← Set.ncard_eq_toFinset_card] using mul_le_mul_of_nonneg_right
          (isoperimetric_ball_growth G hloc hh x (n*m)) (pow_nonneg hc m)
      _ = ∑ y ∈ B, c^m := by simp
      _ ≤ ∑ y ∈ B, twoPoint G p x y := by
        apply Finset.sum_le_sum
        intro y hy
        exact twoPoint_block_lower G p n c hc h m x y (by simpa [B] using hy)
      _ ≤ susceptibility G p x :=
        (summable_twoPoint_subcritical G hloc hqt p hp x).sum_le_tsum B
          (fun y _ => twoPoint_nonneg G p x y)
  obtain ⟨m,hm⟩ := pow_unbounded_of_one_lt (susceptibility G p x) hgt
  exact (not_lt_of_ge (hbound m)) hm

theorem uniform_ball_lower_below [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (q : unitInterval) (hq : 0 < q) (n : ℕ) (a c : ℝ) (hac : a < c)
    (h : ∀ x y, c ≤ twoPoint G q x y) :
    ∃ p : unitInterval, p < q ∧ ∀ x y, y ∈ reachBall G x n → a < twoPoint G p x y := by
  classical
  obtain ⟨R,hR⟩ := hqt
  obtain ⟨ps,hps,hpsq,ht⟩ := exists_seq_strictMono_tendsto' hq
  have hev : ∀ᶠ k in atTop, ∀ o ∈ R, ∀ y ∈ reachBall G o n,
      a < twoPoint G (ps k) o y := by
    apply (eventually_all_finset R).mpr
    intro o _
    apply (eventually_all_finite (finite_reachBall hloc o n)).mpr
    intro y _
    exact (twoPoint_tendsto_of_monotone G ps hps.monotone q
      (fun k => (hpsq k).2.le) ht o y).eventually (eventually_gt_nhds (hac.trans_le (h o y)))
  obtain ⟨k,hk⟩ := hev.exists
  refine ⟨ps k,(hpsq k).2,?_⟩
  intro x y hy
  obtain ⟨o,ho,g,b,hg,hgx⟩ := hR x
  have hy' : g.symm y ∈ reachBall G o n := by
    apply (mem_reachBall_aut_iff G hg o (g.symm y) n).mp
    simpa only [g.apply_symm_apply,hgx] using hy
  have hb := hk o ho (g.symm y) hy'
  have he := twoPoint_aut G (ps k) hg o (g.symm y)
  rw [g.apply_symm_apply,hgx] at he
  rwa [he]

theorem critical_twoPoint_no_uniform_positive [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hh : 0 < hV G) (c : ℝ) (hc : 0 < c) :
    ¬ (∀ x y, c ≤ twoPoint G (pc G) x y) := by
  intro h
  have ha : 0 < c/2 := by positivity
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (1/(c/2)) (show 1 < 1+hV G by linarith)
  obtain ⟨p,hp,hball⟩ := uniform_ball_lower_below G hloc hqt (pc G)
    (pc_pos G hloc hqt) n (c/2) c (by linarith) h
  have hb := subcritical_block_bound G hloc hqt hh p hp n (c/2) ha.le
    (fun x y hy => (hball x y hy).le)
  exact (not_lt_of_ge hb) ((div_lt_iff₀ ha).mp hn)

theorem critical_not_ae_unique [Infinite V] (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hh : 0 < hV G) :
    law (pc G) {ω | ∃! C, C ∈ infiniteClusters G ω} ≠ 1 := by
  classical
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  intro hu
  have hpos : 0 < law (pc G) {ω | (infiniteClusters G ω).Nonempty} := by
    exact lt_of_lt_of_le (show 0 < law (pc G) {ω | ∃! C, C ∈ infiniteClusters G ω} by
      rw [hu]; exact zero_lt_one)
      (measure_mono fun ω hω => ⟨hω.choose,hω.choose_spec.1⟩)
  obtain ⟨θ,hθ,hroot⟩ := uniform_survival_pos G hconn hqt (pc G) (pc_pos G hloc hqt) hpos
  have hue : ∀ᵐ ω ∂law (pc G), ∃! C, C ∈ infiniteClusters G ω :=
    (mem_ae_iff_prob_eq_one (measurableSet_unique_infinite_cluster G)).mpr hu
  apply critical_twoPoint_no_uniform_positive G hloc hqt hh (θ*θ) (mul_pos hθ hθ)
  intro x y
  refine (mul_le_mul (hroot x) (hroot y) hθ.le measureReal_nonneg).trans
    ((association_infinite_cluster G (pc G) x y).trans ?_)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hue] with ω hω
  intro hi
  obtain ⟨r,_,hr⟩ := (unique_infinite_cluster_iff G ω).mp hω
  exact conn_trans G ω (conn_symm G ω (hr x hi.1)) (hr y hi.2)

end Percolation

end OAI
