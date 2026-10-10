import Mathlib
import OAI.Probability.UnimodularPercolation.Deformation.Corridors
import OAI.Probability.UnimodularPercolation.TwoCluster.Bounds

namespace OAI

/-! Critical two-cluster estimates, finite opening and almost-sure finite clusters. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

section RootData
variable [Countable V] [Countable E] [Nonempty V]
variable (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
  (hqt : QuasiTransitive G)
  {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
  (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
  (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
  (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
  (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
  (d : ℕ) (hd : ∀ y, {e | y ∈ G e}.ncard ≤ d)

include hconn hloc hqt hΓ htr hcov hw hw1 hc hmin hd

 

omit [Nonempty V] in
theorem critical_twoLarge_probability_bound
    (n : ℕ) (hn : 0 < n) (e : E) (a b : V) (he : G e = s(a,b)) :
    (pc G:ℝ) * ((n:ℝ) * (law (pc G)).real (twoLargeEvent G a b n)) ≤
      20*c*Real.sqrt (d*n:ℕ) := by
  obtain ⟨p,hp,hpc,hlim⟩ := exists_seq_strictMono_tendsto' (pc_pos G hloc hqt)
  have ht := (continuous_subtype_val.tendsto (pc G) |>.comp hlim).mul
    ((tendsto_const_nhds (x := (n:ℝ))).mul (twoLarge_probability_tendsto G p hp.monotone (pc G)
      (fun j => (hpc j).2.le) hlim a b n))
  apply le_of_tendsto ht
  apply Eventually.of_forall
  intro j
  have hb := twoLarge_probability_bound G hconn hloc root weight Γ hΓ htr hcov hw hw1
    c hc hmin d hd n hn (p j) (hpc j).1
      (subcritical_cluster_finite_ae G (p j) (hpc j).2) e a b he
  change (p j:ℝ) * ((n:ℝ) * (law (p j)).real (twoLargeEvent G a b n)) ≤ _
  rw [mul_comm (p j:ℝ)]
  exact (le_div_iff₀ (hpc j).1).mp hb

 

omit [Nonempty V] in
theorem critical_adjacent_infinite_connected (e : E) (a b : V) (he : G e = s(a,b)) :
    ∀ᵐ ω ∂law (pc G), (cluster G ω a).Infinite → (cluster G ω b).Infinite → Conn G ω a b := by
  let A : Set (Set E) := {ω | ¬Conn G ω a b ∧
    (cluster G ω a).Infinite ∧ (cluster G ω b).Infinite}
  have hA : MeasurableSet A := (measurableSet_conn G a b).compl.inter
    ((measurableSet_infinite_cluster G a).inter (measurableSet_infinite_cluster G b))
  have hp : 0 < (pc G:ℝ) := pc_pos G hloc hqt
  have hzero : (law (pc G)).real A = 0 := by
    by_contra hne
    have hθ : 0 < (law (pc G)).real A := lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
    have hb (n : ℕ) (hn : 0 < n) :
        (pc G:ℝ)*((n:ℝ)*(law (pc G)).real A) ≤ 20*c*Real.sqrt (d*n:ℕ) := by
      have hs : A ⊆ twoLargeEvent G a b n := by
        intro ω h
        refine ⟨h.1,?_,?_⟩
        · have hx : ω ∈ {ω | (cluster G ω a).Infinite} := h.2.1
          rw [infinite_cluster_eq_iInter G a] at hx
          exact Set.mem_iInter.mp hx n
        · have hx : ω ∈ {ω | (cluster G ω b).Infinite} := h.2.2
          rw [infinite_cluster_eq_iInter G b] at hx
          exact Set.mem_iInter.mp hx n
      exact (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (measureReal_mono hs) (Nat.cast_nonneg n)) hp.le).trans
          (critical_twoLarge_probability_bound G hconn hloc hqt root weight Γ hΓ htr hcov
            hw hw1 c hc hmin d hd n hn e a b he)
    let B := 20*c*Real.sqrt (d:ℝ)
    obtain ⟨m,hm⟩ := exists_nat_gt (B / ((pc G:ℝ)*(law (pc G)).real A) + 1)
    have hmpos : 0 < (m:ℝ) := lt_trans (by dsimp [B]; positivity) hm
    have hmn : 0 < m := by exact_mod_cast hmpos
    have hb' := hb (m^2) (pow_pos hmn _)
    have hsqrt : Real.sqrt (d*(m^2):ℕ) = Real.sqrt (d:ℝ)*(m:ℝ) := by
      rw [Nat.cast_mul,Nat.cast_pow,Real.sqrt_mul (Nat.cast_nonneg d),Real.sqrt_sq (Nat.cast_nonneg m)]
    rw [hsqrt,Nat.cast_pow] at hb'
    have hcancel : (pc G:ℝ)*(law (pc G)).real A*(m:ℝ) ≤ B := by
      apply (mul_le_mul_iff_left₀ hmpos).mp
      change ((pc G:ℝ)*(law (pc G)).real A*(m:ℝ))*(m:ℝ) ≤ B*(m:ℝ)
      dsimp only [B]
      nlinarith only [hb']
    have hlt : B < (pc G:ℝ)*(law (pc G)).real A*(m:ℝ) := by
      have hdiv : B / ((pc G:ℝ)*(law (pc G)).real A) < (m:ℝ) := by linarith
      have hh := (div_lt_iff₀ (mul_pos hp hθ)).mp hdiv
      nlinarith
    exact (not_lt_of_ge hcancel) hlt
  have hn : law (pc G) A = 0 := (measureReal_eq_zero_iff).mp hzero
  have hae : ∀ᵐ ω ∂law (pc G), ω ∉ A := by
    rw [ae_iff]; simpa using hn
  filter_upwards [hae] with ω hω ha hb
  by_contra hc
  exact hω ⟨hc,ha,hb⟩

end RootData
end Percolation

 

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem measure_union_finset_null [Countable E] (p : unitInterval) (hp : 0 < (p:ℝ))
    (A : Set (Set E)) (hA : MeasurableSet A) (hzero : law p A = 0) (F : Finset E) :
    law p {ω | ω ∪ (F:Set E) ∈ A} = 0 := by
  let B : Set (Set E) := {ω | ω ∪ (F:Set E) ∈ A}
  let C : Set (Set E) := {ω | (F:Set E) ⊆ ω}
  have hB : MeasurableSet B := hA.preimage
    (measurable_set_union_pair.comp (measurable_id.prodMk measurable_const))
  have hC : MeasurableSet C := by
    change MeasurableSet {ω | ∀ e ∈ F, e ∈ ω}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun e => MeasurableSet.iInter fun _ => measurableSet_mem e
  have heB : (fun ω : Set E => ω ∩ (F:Set E)ᶜ) ⁻¹' B = B := by
    ext ω
    have he : (ω ∩ (F:Set E)ᶜ) ∪ (F:Set E) = ω ∪ (F:Set E) := by
      ext t
      simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff]
      tauto
    simp only [Set.mem_preimage,B,Set.mem_ofPred_eq,he]
  have heC : (fun ω : Set E => ω ∩ (F:Set E)) ⁻¹' C = C := by
    ext ω
    simp [C]
  have hi := restriction_events_independent p (F:Set E)ᶜ (F:Set E)
    (Set.disjoint_left.mpr (fun _ hx hy => hx hy)) B C hB hC
  rw [heB,heC] at hi
  have hBC : law p (B ∩ C) = 0 := measure_mono_null (by
    intro ω h
    have he : ω ∪ (F:Set E) = ω := Set.union_eq_left.mpr h.2
    simpa only [B,Set.mem_ofPred_eq,he] using h.1) hzero
  have hCp : 0 < (law p).real C := by
    rw [show C = {ω | (F:Set E) ⊆ ω} from rfl,finite_open_probability]
    exact pow_pos hp _
  exact (mul_eq_zero.mp (hi.symm.trans hBC)).resolve_right
    (fun h => by simp [Measure.real,h] at hCp)

theorem ae_union_finset [Countable E] (p : unitInterval) (hp : 0 < (p:ℝ))
    (A : Set (Set E)) (hA : MeasurableSet A) (hae : ∀ᵐ ω ∂law p, ω ∈ A) (F : Finset E) :
    ∀ᵐ ω ∂law p, ω ∪ (F:Set E) ∈ A := by
  rw [ae_iff] at hae ⊢
  exact measure_union_finset_null p hp Aᶜ hA.compl hae F

 

theorem atMostOne_of_finite_openings (G : BondGraph V E) (hconn : Connected G) (ω : Set E)
    (h : ∀ F : Finset E, ∀ a b, Adj G a b →
      (cluster G (ω ∪ (F:Set E)) a).Infinite →
      (cluster G (ω ∪ (F:Set E)) b).Infinite → Conn G (ω ∪ (F:Set E)) a b) :
    ∀ x y, (cluster G ω x).Infinite → (cluster G ω y).Infinite → Conn G ω x y := by
  intro x y hx hy
  by_contra hxy
  have hF : ∀ F : Finset E, ¬Conn G (ω ∪ (F:Set E)) x y := by
    intro F
    induction F using Finset.induction_on with
    | empty => simpa only [Finset.coe_empty,Set.union_empty] using hxy
    | @insert e F he ih =>
      have heq : ω ∪ ((insert e F : Finset E):Set E) = insert e (ω ∪ (F:Set E)) := by
        ext t; simp only [Finset.coe_insert,Set.mem_union,Set.mem_insert_iff]; tauto
      rw [heq]
      obtain ⟨⟨a,b⟩,hab'⟩ := Sym2.mk_surjective (G e)
      have hab : G e = s(a,b) := hab'.symm
      rw [conn_insert_iff G _ e a b x y hab]
      rintro (hc | ⟨hxa,hby⟩ | ⟨hxb,hay⟩)
      · exact ih hc
      · have ha : (cluster G (ω ∪ (F:Set E)) a).Infinite := by
          rw [←cluster_eq_of_conn G _ hxa]
          exact hx.mono (fun z hz => conn_mono G Set.subset_union_left hz)
        have hb : (cluster G (ω ∪ (F:Set E)) b).Infinite := by
          rw [cluster_eq_of_conn G _ hby]
          exact hy.mono (fun z hz => conn_mono G Set.subset_union_left hz)
        exact ih (conn_trans G _ hxa (conn_trans G _ (h F a b ⟨e,hab⟩ ha hb) hby))
      · have hb : (cluster G (ω ∪ (F:Set E)) b).Infinite := by
          rw [←cluster_eq_of_conn G _ hxb]
          exact hx.mono (fun z hz => conn_mono G Set.subset_union_left hz)
        have ha : (cluster G (ω ∪ (F:Set E)) a).Infinite := by
          rw [cluster_eq_of_conn G _ hay]
          exact hy.mono (fun z hz => conn_mono G Set.subset_union_left hz)
        exact ih (conn_trans G _ hxb (conn_trans G _
          (conn_symm G _ (h F a b ⟨e,hab⟩ ha hb)) hay))
  obtain ⟨F,_,hFc⟩ := finiteWitness_conn G x y Set.univ (conn_univ_of_connected G hconn x y)
  exact hF F (conn_mono G Set.subset_union_right hFc)

end Percolation

 

 

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter Topology
open scoped ENNReal

 
theorem twoPoint_mul_le [Countable E] (G : BondGraph V E) (p : unitInterval)
    (x y z : V) : twoPoint G p x y * twoPoint G p y z ≤ twoPoint G p x z := by
  have h := association_finiteWitness p {ω : Set E | Conn G ω x y}
    {ω : Set E | Conn G ω y z}
    (fun _ _ hω h => conn_mono G hω h) (fun _ _ hω h => conn_mono G hω h)
    (finiteWitness_conn G x y) (finiteWitness_conn G y z)
  exact h.trans (measureReal_mono (fun ω hω => conn_trans G ω hω.1 hω.2))

 
theorem reachBall_add_split (G : BondGraph V E) (x : V) (n m : ℕ) {y : V}
    (hy : y ∈ reachBall G x (n+m)) :
    ∃ z ∈ reachBall G x n, y ∈ reachBall G z m := by
  induction m generalizing y with
  | zero => exact ⟨y,hy,Set.mem_singleton y⟩
  | succ m ih =>
    rcases hy with hy | hy
    · obtain ⟨z,hz,hyz⟩ := ih hy
      exact ⟨z,hz,Or.inl hyz⟩
    · simp only [Set.mem_iUnion,Set.mem_ofPred_eq] at hy
      obtain ⟨w,hw,hwy⟩ := hy
      obtain ⟨z,hz,hwz⟩ := ih hw
      refine ⟨z,hz,Or.inr ?_⟩
      exact Set.mem_iUnion.mpr ⟨w,Set.mem_iUnion.mpr ⟨hwz,hwy⟩⟩

 
theorem twoPoint_lower_on_multiples [Countable E] (G : BondGraph V E)
    (p : unitInterval) (n : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hball : ∀ x y, y ∈ reachBall G x n → c ≤ twoPoint G p x y)
    (k : ℕ) (x y : V) (hy : y ∈ reachBall G x (n*k)) :
    c^k ≤ twoPoint G p x y := by
  induction k generalizing x y with
  | zero =>
    have he : y = x := by simpa [reachBall] using hy
    subst y
    simp [twoPoint_self]
  | succ k ih =>
    rw [Nat.mul_succ] at hy
    obtain ⟨z,hz,hyz⟩ := reachBall_add_split G x (n*k) n hy
    calc
      c^(k+1) = c^k*c := pow_succ _ _
      _ ≤ twoPoint G p x z * twoPoint G p z y :=
        mul_le_mul (ih x z hz) (hball z y hyz) hc (twoPoint_nonneg G p x z)
      _ ≤ twoPoint G p x y := twoPoint_mul_le G p x z y

 
theorem reachBall_exponential_growth (G : BondGraph V E) (hloc : LocallyFinite G)
    (hh : 0 ≤ hV G) (x : V) (n : ℕ) :
    (1+hV G)^n ≤ ((reachBall G x n).ncard : ℝ) := by
  classical
  induction n with
  | zero => simp [reachBall]
  | succ n ih =>
    let A := (finite_reachBall hloc x n).toFinset
    have he : reachBall G x (n+1) = (A : Set V) ∪ vertexBoundary G A := by
      ext y
      simp only [reachBall,Set.mem_union,Finset.mem_coe,
        vertexBoundary,Set.mem_ofPred_eq,Set.mem_iUnion]
      simp only [A,Set.Finite.mem_toFinset]
      constructor
      · rintro (hy | ⟨z,hz,hzy⟩)
        · exact Or.inl hy
        · by_cases hy : y ∈ reachBall G x n
          · exact Or.inl hy
          · exact Or.inr ⟨hy,z,hz,hzy⟩
      · rintro (hy | ⟨_,z,hz,hzy⟩)
        · exact Or.inl hy
        · exact Or.inr ⟨z,hz,hzy⟩
    have hd : Disjoint (A : Set V) (vertexBoundary G A) := by
      exact Set.disjoint_left.mpr (fun y hy hb => hb.1 hy)
    have hc : (reachBall G x (n+1)).ncard = A.card + (vertexBoundary G A).ncard := by
      rw [he,Set.ncard_union_eq hd A.finite_toSet (finite_vertexBoundary G hloc A),Set.ncard_coe_finset]
    have hcard : A.card = (reachBall G x n).ncard :=
      (Set.ncard_eq_toFinset_card _ (finite_reachBall hloc x n)).symm
    have hs := hV_mul_card_le G A
    rw [hcard] at hs
    rw [hc,hcard,Nat.cast_add,pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right ih (show 0 ≤ 1+hV G by linarith)]

 

theorem exists_subcritical_ball_lower [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (c : ℝ) (hc : 0 < c) (hcrit : ∀ x y, c ≤ twoPoint G (pc G) x y)
    (n : ℕ) : ∃ p : unitInterval, p < pc G ∧
      ∀ x y, y ∈ reachBall G x n → c/2 ≤ twoPoint G p x y := by
  classical
  obtain ⟨p,hp,hpc,hlim⟩ := exists_seq_strictMono_tendsto' (pc_pos G hloc hqt)
  obtain ⟨s,hs⟩ := hqt
  have hev : ∀ᶠ k in atTop, ∀ x ∈ s, ∀ y ∈ reachBall G x n,
      c/2 ≤ twoPoint G (p k) x y := by
    apply (eventually_all_finset s).mpr
    intro x hx
    apply (finite_reachBall hloc x n).eventually_all.mpr
    intro y hy
    have ht := twoPoint_tendsto_of_monotone G p hp.monotone (pc G)
      (fun k => (hpc k).2.le) hlim x y
    have hlt : c/2 < twoPoint G (pc G) x y := lt_of_lt_of_le (by linarith) (hcrit x y)
    exact (ht.eventually (eventually_gt_nhds hlt)).mono (fun k hk => hk.le)
  obtain ⟨k,hk⟩ := hev.exists
  refine ⟨p k,(hpc k).2,?_⟩
  intro x y hy
  obtain ⟨o,ho,a,b,ha,hax⟩ := hs x
  have hy' : a.symm y ∈ reachBall G o n := by
    have hi := mem_reachBall_aut G (isAut_symm G ha) hy
    simpa [←hax] using hi
  have he := twoPoint_aut G (p k) ha o (a.symm y)
  rw [hax,a.apply_symm_apply] at he
  rw [he]
  exact hk o ho (a.symm y) hy'

 

theorem no_uniform_positive_twoPoint_critical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hh : 0 < hV G) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ x y, c ≤ twoPoint G (pc G) x y := by
  rintro ⟨c,hc,hcrit⟩
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (2/c) (show 1 < 1+hV G by linarith)
  have hn' : 1 < (c/2)*(1+hV G)^n := by
    have := (div_lt_iff₀ hc).mp hn
    nlinarith
  obtain ⟨p,hp,hball⟩ := exists_subcritical_ball_lower G hloc hqt c hc hcrit n
  obtain ⟨C,hC,hrow⟩ := subcritical_row_bound G hloc hqt p hp
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt C hn'
  let x : V := Classical.arbitrary V
  let A := (finite_reachBall hloc x (n*k)).toFinset
  have hcard : (reachBall G x (n*k)).ncard = A.card := Set.ncard_eq_toFinset_card _ _
  have hsum : (A.card:ℝ)*(c/2)^k ≤ ∑ y ∈ A, twoPoint G p x y := by
    calc
      _ = ∑ y ∈ A, (c/2)^k := by simp
      _ ≤ _ := Finset.sum_le_sum fun y hy =>
        twoPoint_lower_on_multiples G p n (c/2) (by linarith) hball k x y
          (by simpa [A] using hy)
  have hg := reachBall_exponential_growth G hloc hh.le x (n*k)
  rw [hcard] at hg
  have hpow : ((c/2)*(1+hV G)^n)^k ≤ (A.card:ℝ)*(c/2)^k := by
    calc
      _ = (1+hV G)^(n*k)*(c/2)^k := by rw [mul_pow,pow_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hg (pow_nonneg (half_pos hc).le k)
  exact (not_lt_of_ge (hpow.trans (hsum.trans (hrow x A)))) hk

 

theorem not_unique_infinite_cluster_critical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G) :
    law (pc G) {ω | ∃! C, C ∈ infiniteClusters G ω} ≠ 1 := by
  intro hu
  have hp := pc_pos G hloc hqt
  have hpos : 0 < law (pc G) {ω | (infiniteClusters G ω).Nonempty} :=
    lt_of_lt_of_le (show 0 < law (pc G) {ω | ∃! C, C ∈ infiniteClusters G ω} by
      rw [hu]; exact zero_lt_one)
      (measure_mono fun ω hω => ⟨hω.choose,hω.choose_spec.1⟩)
  obtain ⟨θ,hθ,hroot⟩ := uniform_survival_pos G hconn hqt (pc G) hp hpos
  have hue : ∀ᵐ ω ∂law (pc G), ∃! C, C ∈ infiniteClusters G ω :=
    (mem_ae_iff_prob_eq_one (measurableSet_unique_infinite_cluster G)).mpr hu
  apply no_uniform_positive_twoPoint_critical G hloc hqt hh
  refine ⟨θ*θ,mul_pos hθ hθ,fun x y => ?_⟩
  refine (mul_le_mul (hroot x) (hroot y) hθ.le measureReal_nonneg).trans
    ((association_infinite_cluster G (pc G) x y).trans ?_)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hue] with ω hω
  intro hi
  obtain ⟨r,_,hconnr⟩ := (unique_infinite_cluster_iff G ω).mp hω
  exact conn_trans G ω (conn_symm G ω (hconnr x hi.1)) (hconnr y hi.2)

end Percolation

 

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem critical_finite_of_transport [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1) :
    ∀ x, ∀ᵐ ω ∂law (pc G), (cluster G ω x).Finite := by
  let c : ℝ := ∑ i, 1/weight i
  have hc : 0 ≤ c := Finset.sum_nonneg (fun i _ => (one_div_pos.mpr (hw i)).le)
  have hmin (i : ι) : 1 ≤ c*weight i := by
    apply (div_le_iff₀ (hw i)).mp
    exact Finset.single_le_sum (fun j _ => (one_div_pos.mpr (hw j)).le) (Finset.mem_univ i)
  obtain ⟨d,_,hd⟩ := exists_degree_bound G hqt
  have hdn (x : V) := (incident_ncard_le_degree G hloc x).trans (hd x)
  let A : Set (Set E) := {ω | ∀ a b, Adj G a b →
    (cluster G ω a).Infinite → (cluster G ω b).Infinite → Conn G ω a b}
  have hA : MeasurableSet A := by
    simp only [A,Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro a
    apply MeasurableSet.iInter
    intro b
    apply MeasurableSet.iInter
    intro _
    simp only [imp_iff_not_or,Set.ofPred_or]
    exact (measurableSet_infinite_cluster G a).compl.union
      ((measurableSet_infinite_cluster G b).compl.union (measurableSet_conn G a b))
  have hae : ∀ᵐ ω ∂law (pc G), ω ∈ A := by
    change ∀ᵐ ω ∂law (pc G), ∀ a b, Adj G a b →
      (cluster G ω a).Infinite → (cluster G ω b).Infinite → Conn G ω a b
    rw [ae_all_iff]
    intro a
    rw [ae_all_iff]
    intro b
    rw [ae_all_iff]
    rintro ⟨e,he⟩
    exact critical_adjacent_infinite_connected G hconn hloc hqt root weight Γ hΓ htr hcov
      (fun i => (hw i).le) hw1 c hc hmin d hdn e a b he
  have haeF : ∀ᵐ ω ∂law (pc G), ∀ F : Finset E, ω ∪ (F:Set E) ∈ A := by
    rw [ae_all_iff]
    intro F
    exact ae_union_finset (pc G) (pc_pos G hloc hqt) A hA hae F
  have hat : ∀ᵐ ω ∂law (pc G), ∀ x y,
      (cluster G ω x).Infinite → (cluster G ω y).Infinite → Conn G ω x y := by
    filter_upwards [haeF] with ω hω
    exact atMostOne_of_finite_openings G hconn ω hω
  have hex := infinite_cluster_zero_one G (pc G)
  have he : (labelLaw : Measure (E → unitInterval))
      {labels | ∃ x, (cluster G (openEdges labels (pc G)) x).Infinite} =
      law (pc G) {ω | ∃ x, (cluster G ω x).Infinite} := by
    rw [←map_openEdges (pc G),Measure.map_apply (measurable_openEdges (pc G))
      (measurableSet_exists_infinite_cluster G)]
    rfl
  rw [he] at hex
  have hz : law (pc G) {ω | ∃ x, (cluster G ω x).Infinite} = 0 := by
    rcases hex with hzero | hone
    · exact hzero
    · exfalso
      apply not_unique_infinite_cluster_critical G hconn hloc hqt hh
      apply (mem_ae_iff_prob_eq_one (measurableSet_unique_infinite_cluster G)).mp
      have haex : ∀ᵐ ω ∂law (pc G), ∃ x, (cluster G ω x).Infinite :=
        (mem_ae_iff_prob_eq_one (measurableSet_exists_infinite_cluster G)).mpr hone
      filter_upwards [hat,haex] with ω hω hex
      obtain ⟨x,hx⟩ := hex
      exact (unique_infinite_cluster_iff G ω).mpr ⟨x,hx,fun y hy => hω x y hx hy⟩
  intro x
  rw [ae_iff]
  apply measure_mono_null (t := {ω | ∃ y, (cluster G ω y).Infinite}) ?_ hz
  intro ω hω
  exact ⟨x,hω⟩

end Percolation

end OAI
