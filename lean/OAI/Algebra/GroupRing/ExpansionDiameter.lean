import Mathlib
import OAI.Algebra.GroupRing.RawDecomposition

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ExpansionDiameter
open scoped Classical BigOperators
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def ball (v : V) (r : ℕ) : Finset V :=
  Finset.univ.filter fun w => G.edist v w  ≤  r

@[simp] lemma mem_ball (v w : V) (r : ℕ) : w∈ball G v r ↔ G.edist v w  ≤  r := by
  simp [ball]

lemma self_mem_ball (v : V) (r : ℕ) : v∈ball G v r := by simp

lemma ball_mono (v : V) {r s : ℕ} (h : r ≤ s) : ball G v r ⊆ ball G v s := by
  intro w hw
  exact (mem_ball G v w s).mpr (((mem_ball G v w r).mp hw).trans (by exact_mod_cast h))

def neighbors (S : Finset V) : Finset V :=
  S ∪ Finset.univ.filter fun w => ∃ v∈S, G.Adj v w

lemma neighbors_ball (v : V) (r : ℕ) : neighbors G (ball G v r) ⊆ ball G v (r+1) := by
  intro w hw
  rcases Finset.mem_union.mp hw with hw | hw
  · exact ball_mono G v (Nat.le_succ r) hw
  · obtain ⟨z,hz,hzw⟩ := (Finset.mem_filter.mp hw).2
    apply (mem_ball G v w (r+1)).mpr
    calc
      G.edist v w  ≤  G.edist v z + G.edist z w := G.edist_triangle
      _  ≤  (r:ℕ∞)+1 := by
        apply add_le_add
        · exact (mem_ball G v z r).mp hz
        · exact (SimpleGraph.edist_eq_one_iff_adj.mpr hzw).le
      _ = _ := by simp

/-- Doubling small sets forces every logarithmic-radius ball above the
expansion threshold, uniformly over all connected components. -/
theorem ball_large (B R : ℕ)
    (hexp : ∀ S : Finset V, S.Nonempty → S.card ≤ B → 2*S.card  ≤  (neighbors G S).card)
    (hR : B<2^R) (v : V) : B<(ball G v R).card := by
  have hstep (r : ℕ) : B<(ball G v r).card ∨ 2^r  ≤  (ball G v r).card := by
    induction r with
    | zero => exact Or.inr (by simpa using Finset.card_pos.mpr ⟨v,self_mem_ball G v 0⟩)
    | succ r ih =>
      have hmono := Finset.card_le_card (ball_mono G v (Nat.le_succ r))
      rcases ih with h | h
      · exact Or.inl (h.trans_le hmono)
      · by_cases ht : B<(ball G v r).card
        · exact Or.inl (ht.trans_le hmono)
        · right
          have hh := (hexp (ball G v r) ⟨v,self_mem_ball G v r⟩ (Nat.le_of_not_gt ht)).trans
            (Finset.card_le_card (neighbors_ball G v r))
          calc
            2^(r+1) = 2*2^r := by rw [pow_succ,Nat.mul_comm]
            _  ≤  2*(ball G v r).card := Nat.mul_le_mul_left _ h
            _  ≤  _ := hh
  rcases hstep R with h | h
  · exact h
  · exact hR.trans_le h

omit [Fintype V] in
lemma shortest_prefix {u v : V} (p : G.Walk u v)
    (hp : p.length=G.dist u v) (i : ℕ) (hi : i ≤ p.length) :
    G.edist u (p.getVert i) = i := by
  have hd := SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take i)
  have hdi : G.dist u (p.getVert i)=i := by
    rw [← hd,SimpleGraph.Walk.take_length,inf_eq_left.mpr hi]
  rw [← (p.take i).reachable.coe_dist_eq_edist,hdi]

lemma spaced_balls_disjoint {u v : V} (p : G.Walk u v)
    (hp : p.length=G.dist u v) (R i j : ℕ) (hij : i<j)
    (hj : j*(2*R+1) ≤ p.length) :
    Disjoint (ball G (p.getVert (i*(2*R+1))) R)
      (ball G (p.getVert (j*(2*R+1))) R) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  have hi : i*(2*R+1) ≤ p.length :=
    (Nat.mul_le_mul_right _ (Nat.le_of_lt hij)).trans hj
  have hzz : G.edist (p.getVert (i*(2*R+1))) (p.getVert (j*(2*R+1)))  ≤  (2*R:ℕ) := by
    calc
      _  ≤  G.edist (p.getVert (i*(2*R+1))) z +
          G.edist z (p.getVert (j*(2*R+1))) := G.edist_triangle
      _  ≤  (R:ℕ∞)+R := add_le_add ((mem_ball G _ _ _).mp hz)
        (by rw [G.edist_comm]; exact (mem_ball G _ _ _).mp hz')
      _ = _ := by push_cast; ring
  have htri := G.edist_triangle (u:=u) (v:=p.getVert (i*(2*R+1)))
    (w:=p.getVert (j*(2*R+1)))
  rw [shortest_prefix G p hp _ hi,shortest_prefix G p hp _ hj] at htri
  have hle := htri.trans (add_le_add le_rfl hzz)
  have hle' : j*(2*R+1) ≤ i*(2*R+1)+2*R := by exact_mod_cast hle
  have hgap := Nat.mul_le_mul_right (2*R+1) (Nat.succ_le_of_lt hij)
  rw [Nat.succ_mul] at hgap
  omega

/-- Quantitative packing: a shortest walk carries disjoint large balls at
uniformly spaced centers. -/
theorem diameter_bound (B R : ℕ)
    (hexp : ∀ S : Finset V, S.Nonempty → S.card ≤ B → 2*S.card  ≤  (neighbors G S).card)
    (hR : B<2^R) {u v : V} (huv : G.Reachable u v) :
    G.dist u v < (Fintype.card V/(B+1)+1)*(2*R+1) := by
  obtain ⟨p,hp⟩ := huv.exists_walk_length_eq_dist
  let step := 2*R+1
  let q := p.length/step+1
  let centers (i : Fin q) := p.getVert (i.val*step)
  have hpos : 0<step := by dsimp [step]; omega
  have hcenter (i : Fin q) : i.val*step ≤ p.length := by
    have hi : i.val ≤ p.length/step := by have := i.isLt; dsimp [q] at this; omega
    exact (Nat.mul_le_mul_right _ hi).trans (Nat.div_mul_le_self _ _)
  have hdis : (↑(Finset.univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint (fun i => ball G (centers i) R) := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
    · exact spaced_balls_disjoint G p hp R i.val j.val hlt (hcenter j)
    · exact (spaced_balls_disjoint G p hp R j.val i.val hlt (hcenter i)).symm
  have hpack : q*(B+1)  ≤  Fintype.card V := by
    calc
      _ = ∑ _i : Fin q, (B+1) := by simp
      _  ≤  ∑ i : Fin q, (ball G (centers i) R).card := by
        apply Finset.sum_le_sum
        intro i _
        exact Nat.succ_le_of_lt (ball_large G B R hexp hR (centers i))
      _ = (Finset.univ.biUnion (fun i : Fin q => ball G (centers i) R)).card :=
        (Finset.card_biUnion hdis).symm
      _  ≤  Fintype.card V := Finset.card_le_univ _
  have hq : q ≤ Fintype.card V/(B+1) := (Nat.le_div_iff_mul_le (by omega)).mpr hpack
  have hpq : p.length < q*step := by
    dsimp [q]
    simpa [Nat.mul_comm] using Nat.lt_mul_div_succ p.length hpos
  rw [← hp]
  exact hpq.trans_le (Nat.mul_le_mul_right _ (hq.trans (Nat.le_succ _)))

end TorsionFreeZeroDivisors.ExpansionDiameter

/-! Quantitative probability estimates for dense witnesses in conditioned
matchings. -/
namespace TorsionFreeZeroDivisors.DiameterProbability
open scoped BigOperators Topology Classical
open Filter

lemma choose_bound (n r : ℕ) (hr : 0<r) :
    (n.choose r : ℝ) ≤ (3*n/r)^r := by
  have hr0 : (0:ℝ)<r := by exact_mod_cast hr
  have hpow : (r:ℝ)^r/(r.factorial:ℝ) ≤ Real.exp (r:ℝ) :=
    Real.pow_div_factorial_le_exp _ (le_of_lt hr0) _
  have he : Real.exp (r:ℝ) ≤ (3:ℝ)^r := by
    rw [show (r:ℝ)=(r:ℝ)*1 by ring,Real.exp_nat_mul]
    exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1))
      (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) r
  calc
    (n.choose r : ℝ) ≤ (n:ℝ)^r/(r.factorial:ℝ) := Nat.choose_le_pow_div _ _
    _ = ((n:ℝ)/r)^r * ((r:ℝ)^r/(r.factorial:ℝ)) := by
      rw [div_pow]
      field_simp
    _ ≤ ((n:ℝ)/r)^r * (3:ℝ)^r :=
      mul_le_mul_of_nonneg_left (hpow.trans he) (by positivity)
    _ = (3*n/r)^r := by rw [← mul_pow]; congr 1; ring

/-- A summable envelope with exponent 62, sufficient to obtain an o(1) event. -/
lemma witness_envelope (n k r : ℕ) (d p R : ℝ)
    (hk : 0<k) (hn : (k:ℝ) ≤ n) (hd : 1 ≤ d) (hp : 0<p) (hp1 : p ≤ 1) (hR : p*n ≤ R)
    (hr₁ : 64*k ≤ r) (hr₂ : r ≤ 65*k) (hm : ℕ) (hhm : (hm:ℝ) ≤ (2*k*d)^2) :
    (n.choose (2*k):ℝ)*(hm.choose r:ℝ)/R^r ≤
      (9*(12*d^2/p)^65*((k:ℝ)/n)^62)^k := by
  have hk0 : (0:ℝ)<k := by exact_mod_cast hk
  have hn0 : (0:ℝ)<n := hk0.trans_le hn
  have hR0 : (0:ℝ)<R := (mul_pos hp hn0).trans_le hR
  have hr0 : 0<r := by omega
  have hr0' : (0:ℝ)<r := by exact_mod_cast hr0
  have hkr : (k:ℝ) ≤ r := by exact_mod_cast (show k ≤ r by omega)
  have ha : (0:ℝ) ≤ 3*n/(2*k) := by positivity
  have hb : (0:ℝ) ≤ 12*d^2*k/(p*n) := by positivity
  have hc : (0:ℝ) ≤ (hm.choose r:ℝ) := by positivity
  have hterm : (n.choose (2*k):ℝ)*(hm.choose r:ℝ)/R^r ≤
      (3*n/(2*k))^(2*k)*(12*d^2*k/(p*n))^r := by
    calc
      _ ≤ (3*n/(2*k))^(2*k) * (3*hm/r)^r / R^r := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul (by simpa using choose_bound n (2*k) (by omega))
          (choose_bound hm r hr0) hc (by positivity)
      _ = (3*n/(2*k))^(2*k) * (3*hm/r/R)^r := by rw [div_pow]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        apply (div_le_iff₀ hR0).mpr
        have hh : 3*(hm:ℝ)/r ≤ 12*d^2*k := by
          apply (div_le_iff₀ hr0').mpr
          have hkk := mul_le_mul_of_nonneg_left hkr (show 0 ≤ 12*d^2*k by positivity)
          nlinarith
        calc
          _ ≤ 12*d^2*k := hh
          _ = (12*d^2*k/(p*n))*(p*n) := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hR hb
  -- Keep constants independent of n,k and use 64k≤r≤65k.
  have ht : 0 ≤ (k:ℝ)/n := by positivity
  have ht1 : (k:ℝ)/n ≤ 1 := (div_le_one hn0).mpr hn
  have hC : 1 ≤ 12*d^2/p := (le_div_iff₀ hp).mpr (by nlinarith [sq_nonneg d])
  have hbase : (12*d^2*k/(p*n))^r ≤ (12*d^2/p)^(65*k)*((k:ℝ)/n)^(64*k) := by
    rw [show 12*d^2*k/(p*n)=(12*d^2/p)*((k:ℝ)/n) by ring,mul_pow]
    apply mul_le_mul
    · exact pow_le_pow_right₀ hC hr₂
    · exact pow_le_pow_of_le_one ht ht1 hr₁
    · positivity
    · positivity
  calc
    _ ≤ (3*n/(2*k))^(2*k)*((12*d^2/p)^(65*k)*((k:ℝ)/n)^(64*k)) :=
      hterm.trans (mul_le_mul_of_nonneg_left hbase (by positivity))
    _ ≤ (3*n/k)^(2*k)*((12*d^2/p)^(65*k)*((k:ℝ)/n)^(64*k)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      apply div_le_div_of_nonneg_left (by positivity) hk0
      nlinarith
    _ = _ := by
      rw [pow_mul,pow_mul,pow_mul,← mul_pow,← mul_pow]
      congr 1
      rw [show (64:ℕ)=2+62 by norm_num,pow_add]
      have hi : (3*(n:ℝ)/k)^2*((k:ℝ)/n)^2=9 := by
        rw [← mul_pow]
        have he : (3*(n:ℝ)/k)*((k:ℝ)/n)=3 := by
          field_simp
        rw [he]
        norm_num
      calc
        _ = ((3*(n:ℝ)/k)^2*((k:ℝ)/n)^2)*
            ((12*d^2/p)^65*((k:ℝ)/n)^62) := by ring
        _ = _ := by rw [hi]; ring

noncomputable def witnessTerm (C ρ : ℝ) (n k : ℕ) : ℝ :=
  if 0<k ∧ (k:ℝ) ≤ ρ*n then (C*((k:ℝ)/n)^62)^k else 0

lemma witnessTerm_nonneg {C ρ : ℝ} (hC : 0 ≤ C) (n k : ℕ) :
    0 ≤ witnessTerm C ρ n k := by
  unfold witnessTerm
  split_ifs <;> positivity

lemma witnessTerm_majorant {C ρ : ℝ} (hC : 0 ≤ C)
    (hsmall : C*ρ^62 ≤ 1/2) (n k : ℕ) (hn : 0<n) :
    ‖witnessTerm C ρ n k‖ ≤ (1/2:ℝ)^k := by
  rw [Real.norm_eq_abs,abs_of_nonneg (witnessTerm_nonneg hC n k)]
  unfold witnessTerm
  split_ifs with h
  · apply pow_le_pow_left₀ (by positivity)
    have hn0 : (0:ℝ)<n := by exact_mod_cast hn
    have ht : (k:ℝ)/n ≤ ρ := (div_le_iff₀ hn0).mpr h.2
    exact (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) ht 62) hC).trans hsmall
  · positivity

lemma witnessTerm_tendsto {C ρ : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    Tendsto (fun n : ℕ => witnessTerm C ρ n k) atTop (𝓝 0) := by
  by_cases hk : k=0
  · subst k
    simp [witnessTerm]
  · have ht : Tendsto (fun n : ℕ => (k:ℝ)/n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R:=ℝ))
    have ht' : Tendsto (fun n : ℕ => (C*((k:ℝ)/n)^62)^k) atTop (𝓝 0) := by
      simpa [hk] using ((ht.pow 62).const_mul C).pow k
    apply squeeze_zero (witnessTerm_nonneg hC · k) _ ht'
    intro n
    unfold witnessTerm
    split_ifs
    · exact le_rfl
    · positivity

/-- The full varying-size union bound tends to zero by dominated convergence. -/
theorem witness_sum_tendsto {C ρ : ℝ} (hC : 0 ≤ C)
    (hsmall : C*ρ^62 ≤ 1/2) :
    Tendsto (fun n : ℕ => ∑' k : ℕ, witnessTerm C ρ n k) atTop (𝓝 0) := by
  have hsum : Summable (fun k : ℕ => (1/2:ℝ)^k) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  have hh := tendsto_tsum_of_dominated_convergence hsum (witnessTerm_tendsto hC)
    (show ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, ‖witnessTerm C ρ n k‖ ≤ (1/2:ℝ)^k from by
      filter_upwards [eventually_gt_atTop 0] with n hn k
      exact witnessTerm_majorant hC hsmall n k hn)
  simpa using hh

end TorsionFreeZeroDivisors.DiameterProbability

namespace TorsionFreeZeroDivisors.MatchingDiameter
open scoped Classical BigOperators
open ConditionedMatchings DiameterCounting
variable {V D T : Type*} [Fintype V] [Fintype D]
variable (origin : D → V) {label : D → T} {bar : T → T}

/-- Forgetting multiplicities, with loops contributing only the already
present vertex to a closed neighborhood. -/
def simpleGraph (r : Matching label bar) : SimpleGraph V where
  Adj v w := v ≠ w ∧ ∃ e : D, origin e=v ∧ origin (r e)=w
  symm := ⟨by
    rintro v w ⟨h,e,he,hef⟩
    exact ⟨h.symm,r e,hef,by rw [r.reverse_reverse,he]⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma neighbors_eq (r : Matching label bar) (S : Finset V) :
    ExpansionDiameter.neighbors (simpleGraph origin r) S = closedNeighbors origin r S := by
  ext v
  simp only [ExpansionDiameter.neighbors,closedNeighbors,Finset.mem_union,
    Finset.mem_image,mem_ports,Finset.mem_filter,Finset.mem_univ,true_and]
  change (v ∈ S ∨ ∃ w ∈ S, w ≠ v ∧ ∃ e, origin e = w ∧ origin (r e) = v) ↔ _
  constructor
  · rintro (h | ⟨w,hw,_,e,he,hef⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e,he ▸ hw,hef⟩
  · rintro (h | ⟨e,he,hef⟩)
    · exact Or.inl h
    · by_cases h : origin e=v
      · exact Or.inl (h ▸ he)
      · exact Or.inr ⟨origin e,he,h,e,rfl,hef⟩

def Expands (B : ℕ) (r : Matching label bar) : Prop :=
  ∀ S : Finset V, S.Nonempty → S.card ≤ B → 2*S.card ≤ (closedNeighbors origin r S).card

def failure (B N : ℕ) : Finset (Matching label bar) :=
  (Matching.conditioned (label:=label) (bar:=bar) origin N ∅).filter (fun r => ¬Expands origin B r)

theorem failure_subset_dense (B N : ℕ) (hd : ∀ v, 129 ≤ Nat.card {e : D // origin e=v})
    (hB : 2*B ≤ Fintype.card V) :
    failure (label:=label) (bar:=bar) origin B N ⊆
      (Finset.Icc 1 B).biUnion (fun k => denseEvent (label:=label) (bar:=bar) origin N
        (2*k) ((129*k+1)/2)) := by
  intro r hr
  obtain ⟨hr,hf⟩ := Finset.mem_filter.mp hr
  simp only [Expands,not_forall,not_le] at hf
  obtain ⟨S,hS,hSB,hfail⟩ := hf
  apply Finset.mem_biUnion.mpr
  refine ⟨S.card,Finset.mem_Icc.mpr ⟨Finset.card_pos.mpr hS,hSB⟩,?_⟩
  exact mem_dense_of_failure origin N S.card 129 r hr hd
    ((Nat.mul_le_mul_left 2 hSB).trans hB) S rfl (le_of_lt hfail)

lemma r_bounds (k : ℕ) (hk : 0<k) :
    64*k ≤ (129*k+1)/2 ∧ (129*k+1)/2 ≤ 65*k := by omega

/-- A failure of doubling in the actual conditioned port graph is bounded
by the summable analytic witness envelope. -/
theorem failure_probability_bound (B N d R : ℕ) (p ρ : ℝ)
    (hbar : ∀ t, bar t ≠ t) (hd2 : 2 ≤ d)
    (hd₀ : ∀ v, 129 ≤ Nat.card {e : D // origin e=v})
    (hd : ∀ v, Nat.card {e : D // origin e=v} ≤ d)
    (hB : 2*B ≤ Fintype.card V) (hBρ : (B:ℝ) ≤ ρ*Fintype.card V)
    (hp : 0<p) (hp1 : p ≤ 1) (hρ : ρ ≤ 1)
    (hRreal : p*Fintype.card V ≤ R) (hR0 : 0<R)
    (hR : ∀ x, R+65*B+4*d^(2*N+1) ≤ Nat.card {e : D // label e=label x})
    (hΩ : (Matching.conditioned (label:=label) (bar:=bar) origin N ∅).Nonempty)
    (hsum : Summable (fun k : ℕ => DiameterProbability.witnessTerm
      (9*(12*(d:ℝ)^2/p)^65) ρ (Fintype.card V) k)) :
    (failure (label:=label) (bar:=bar) origin B N).card /
      ((Matching.conditioned (label:=label) (bar:=bar) origin N ∅).card:ℝ) ≤
      ∑' k : ℕ, DiameterProbability.witnessTerm
        (9*(12*(d:ℝ)^2/p)^65) ρ (Fintype.card V) k := by
  let Ω := Matching.conditioned (label:=label) (bar:=bar) origin N ∅
  let event := fun k => denseEvent (label:=label) (bar:=bar) origin N (2*k) ((129*k+1)/2)
  have hΩ0 : (0:ℝ)<Ω.card := by exact_mod_cast Finset.card_pos.mpr hΩ
  have hR0' : (0:ℝ)<R := by exact_mod_cast hR0
  have hkbound (k : ℕ) (hk : k∈Finset.Icc 1 B) :
      (event k).card/(Ω.card:ℝ) ≤ DiameterProbability.witnessTerm
        (9*(12*(d:ℝ)^2/p)^65) ρ (Fintype.card V) k := by
    have hk0 : 0<k := (Finset.mem_Icc.mp hk).1
    have hkB := (Finset.mem_Icc.mp hk).2
    have hkρ : (k:ℝ) ≤ ρ*Fintype.card V :=
      (show (k:ℝ) ≤ B by exact_mod_cast hkB).trans hBρ
    have hkn : (k:ℝ) ≤ Fintype.card V := hkρ.trans (by
      simpa using mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg (Fintype.card V)))
    have hr := r_bounds k hk0
    have hprob := dense_count (label:=label) (bar:=bar) origin N (2*k) ((129*k+1)/2)
      d R hbar hd2 hd (by
        intro x
        have hrr := hr.2.trans (Nat.mul_le_mul_left 65 hkB)
        exact (Nat.add_le_add_right (Nat.add_le_add_left hrr R) _).trans (hR x))
    have hprob' : (event k).card/(Ω.card:ℝ) ≤
        ((Fintype.card V).choose (2*k):ℝ)*((((2*k)*d)^2).choose ((129*k+1)/2):ℝ)/
          (R:ℝ)^((129*k+1)/2) := by
      apply (div_le_div_iff₀ hΩ0 (pow_pos hR0' _)).mpr
      exact_mod_cast hprob
    have hh := DiameterProbability.witness_envelope (Fintype.card V) k ((129*k+1)/2)
      (d:ℝ) p (R:ℝ) hk0 hkn (by exact_mod_cast (show 1 ≤ d by omega)) hp hp1
      hRreal hr.1 hr.2 (((2*k)*d)^2) (by push_cast; rfl)
    unfold DiameterProbability.witnessTerm
    rw [ite_eq_left (show 0 < k ∧ (k:ℝ) ≤ ρ*Fintype.card V from ⟨hk0,hkρ⟩)]
    exact hprob'.trans hh
  calc
    _ ≤ ((Finset.Icc 1 B).biUnion event).card/(Ω.card:ℝ) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hΩ0)
      exact_mod_cast Finset.card_le_card (failure_subset_dense origin B N hd₀ hB)
    _ ≤ (∑ k∈Finset.Icc 1 B, (event k).card:ℕ)/(Ω.card:ℝ) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hΩ0)
      exact_mod_cast (Finset.card_biUnion_le : ((Finset.Icc 1 B).biUnion event).card ≤ _)
    _ = ∑ k∈Finset.Icc 1 B, (event k).card/(Ω.card:ℝ) := by
      push_cast
      rw [Finset.sum_div]
    _ ≤ ∑ k∈Finset.Icc 1 B, DiameterProbability.witnessTerm
        (9*(12*(d:ℝ)^2/p)^65) ρ (Fintype.card V) k := Finset.sum_le_sum hkbound
    _ ≤ _ := Summable.sum_le_tsum (Finset.Icc 1 B)
      (fun k _ => DiameterProbability.witnessTerm_nonneg (by positivity) _ k) hsum

/-- On the complement of the counted event the diameter conclusion follows
with an explicit bound, including components of disconnected graphs. -/
theorem diameter_of_not_failure (B N R : ℕ) (r : Matching label bar)
    (hr : r∈Matching.conditioned (label:=label) (bar:=bar) origin N ∅)
    (hf : r∉failure (label:=label) (bar:=bar) origin B N) (hR : B<2^R)
    {u v : V} (huv : (simpleGraph origin r).Reachable u v) :
    (simpleGraph origin r).dist u v < (Fintype.card V/(B+1)+1)*(2*R+1) := by
  have hexp : Expands origin B r := by
    by_contra h
    exact hf (Finset.mem_filter.mpr ⟨hr,h⟩)
  apply ExpansionDiameter.diameter_bound _ B R _ hR huv
  intro S hs hSB
  rw [neighbors_eq]
  exact hexp S hs hSB

end TorsionFreeZeroDivisors.MatchingDiameter

end

end OAI
