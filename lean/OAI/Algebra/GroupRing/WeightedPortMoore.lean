import Mathlib
import OAI.Algebra.GroupRing.PortSubdivision
import OAI.Algebra.GroupRing.WeightedCycles

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WeightedPortMoore
open SimpleGraph WeightedMoore PortSubdivision WeightedCycles
variable {V D : Type*} (Γ : PortGraph V D)

/-- Validity as a chain of actual nonbacktracking directed edges. -/
def Good : {k : ℕ} → Chain D k → Prop
  | 0, _ => True
  | _+1, p => PortWalk.step Γ.origin Γ.reverse p.1 (head p.2) ∧ Good p.2

/-- The physical port walk, starting and ending at the first/last ports.
It has one middle edge per macro-edge, and two spokes between them. -/
def draw : {k : ℕ} → (p : Chain D k) → Good Γ p →
    Γ.subdivision.Walk (.inr (head p)) (.inr (Γ.reverse (last p)))
  | 0, d, _ => Walk.cons (show Γ.subdivision.Adj (.inr d) (.inr (Γ.reverse d)) from rfl) Walk.nil
  | _+1, p, h =>
    Walk.cons (show Γ.subdivision.Adj (.inr p.1) (.inr (Γ.reverse p.1)) from rfl)
      (Walk.cons (show Γ.subdivision.Adj (.inr (Γ.reverse p.1)) (.inl (Γ.origin (Γ.reverse p.1))) from rfl)
        (Walk.cons (show Γ.subdivision.Adj (.inl (Γ.origin (Γ.reverse p.1))) (.inr (head p.2)) from h.1.1.symm)
          (draw p.2 h.2)))

@[simp] theorem draw_head_edge {k : ℕ} (p : Chain D k) (hp : Good Γ p) :
    (draw Γ p hp).edges.head? = some s(Sum.inr (head p),Sum.inr (Γ.reverse (head p))) := by
  cases k <;> rfl

theorem middle_spoke_ne (d e : D) (v : V) :
    (s(Sum.inr d,Sum.inr (Γ.reverse d)) : Sym2 (V ⊕ D)) ≠ s(Sum.inr e,Sum.inl v) := by
  simp

theorem draw_reduced {k : ℕ} (p : Chain D k) (hp : Good Γ p) :
    (draw Γ p hp).edges.IsChain (· ≠ ·) := by
  induction k with
  | zero =>
    change ([s(Sum.inr p,Sum.inr (Γ.reverse p))] : List (Sym2 (V ⊕ D))).IsChain (· ≠ ·)
    exact List.IsChain.singleton _
  | succ k ih =>
    change ((s(Sum.inr p.1,Sum.inr (Γ.reverse p.1))) ::
      s(Sum.inr (Γ.reverse p.1),Sum.inl (Γ.origin (Γ.reverse p.1))) ::
      s(Sum.inl (Γ.origin (Γ.reverse p.1)),Sum.inr (head p.2)) ::
      (draw Γ p.2 hp.2).edges).IsChain (· ≠ ·)
    apply List.IsChain.cons_cons (middle_spoke_ne Γ _ _ _)
    apply List.IsChain.cons_cons
    · intro he
      have h := Sym2.eq_iff.mp he
      simp only [Sum.inr.injEq,reduceCtorEq,and_false,false_or] at h
      exact hp.1.2 h.1.symm
    · apply (ih p.2 hp.2).cons
      intro y hy
      rw [draw_head_edge] at hy
      have he : y = s(Sum.inr (head p.2),Sum.inr (Γ.reverse (head p.2))) := (Option.mem_some_iff.mp hy).symm
      subst y
      intro h
      exact middle_spoke_ne Γ (head p.2) (head p.2) (Γ.origin (Γ.reverse p.1))
        (h.symm.trans Sym2.eq_swap)

/-- Recording ports from the physical walk recovers each directed macro-edge. -/
def portWord : {k : ℕ} → Chain D k → List D
  | 0, d => [d,Γ.reverse d]
  | _+1, p => p.1 :: Γ.reverse p.1 :: portWord p.2

def onlyPort : V ⊕ D → Option D
  | .inl _ => none
  | .inr d => some d

theorem draw_portWord {k : ℕ} (p : Chain D k) (hp : Good Γ p) :
    (draw Γ p hp).support.filterMap onlyPort = portWord Γ p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change p.1 :: Γ.reverse p.1 :: (draw Γ p.2 hp.2).support.filterMap onlyPort =
      p.1 :: Γ.reverse p.1 :: portWord Γ p.2
    rw [ih p.2 hp.2]

theorem portWord_injective (k : ℕ) : Function.Injective (@portWord V D Γ k) := by
  induction k with
  | zero => intro p q h; exact (List.cons.inj h).1
  | succ k ih =>
    intro p q h
    have he := List.cons.inj h
    exact Prod.ext he.1 (ih (List.cons.inj he.2).2)

/-- Nonnegative symmetric length on the subdivision; spokes cost zero. -/
def edgeWeight (len : D → ℝ) : Sym2 (V ⊕ D) → ℝ :=
  Sym2.lift ⟨fun a b => match a,b with
    | .inr d,.inr e => (len d+len e)/2
    | _,_ => 0, by intro a b; cases a <;> cases b <;> simp [add_comm]⟩

theorem edgeWeight_nonneg (len : D → ℝ) (hlen : ∀ d, 0 ≤ len d) :
    ∀ e, 0 ≤ edgeWeight (V := V) len e := by
  intro e
  induction e using Sym2.inductionOn with
  | _ a b =>
    cases a with
    | inl v => cases b <;> exact le_rfl
    | inr d =>
      cases b with
      | inl v => exact le_rfl
      | inr e => exact div_nonneg (add_nonneg (hlen d) (hlen e)) (by norm_num)

@[simp] theorem edgeWeight_spoke (len : D → ℝ) (v : V) (d : D) :
    edgeWeight len s(Sum.inl v,Sum.inr d) = 0 := rfl

@[simp] theorem edgeWeight_middle (len : D → ℝ) (hsym : ∀ d, len (Γ.reverse d) = len d) (d : D) :
    edgeWeight (V := V) len s(Sum.inr d,Sum.inr (Γ.reverse d)) = len d := by
  change (len d+len (Γ.reverse d))/2 = len d
  rw [hsym]; ring

theorem draw_weight (len : D → ℝ) (hsym : ∀ d, len (Γ.reverse d) = len d)
    {k : ℕ} (p : Chain D k) (hp : Good Γ p) :
    weight (edgeWeight len) (draw Γ p hp) = cost len p := by
  induction k with
  | zero =>
    change (len p+len (Γ.reverse p))/2+0 = len p
    rw [hsym]; ring
  | succ k ih =>
    change (len p.1+len (Γ.reverse p.1))/2 +
      (0+(0+weight (edgeWeight len) (draw Γ p.2 hp.2))) = len p.1+cost len p.2
    rw [hsym,ih p.2 hp.2]
    ring

/-- Positive chain mass certifies every actual allowed transition. -/
theorem positive_good [Fintype D]
    (ht : Transition (PortWalk.transition Γ.origin Γ.reverse))
    {k : ℕ} (p : Chain D k)
    (hp : 0 < mass (PortWalk.transition Γ.origin Γ.reverse) p) : Good Γ p := by
  induction k with
  | zero => trivial
  | succ k ih =>
    have hs : PortWalk.step Γ.origin Γ.reverse p.1 (head p.2) := by
      by_contra hn
      simp only [mass,PortWalk.transition,ite_eq_right hn,zero_mul] at hp
      exact lt_irrefl _ hp
    have hne : mass (PortWalk.transition Γ.origin Γ.reverse) p.2 ≠ 0 := by
      intro he
      simp only [mass,he,mul_zero] at hp
      exact lt_irrefl _ hp
    exact ⟨hs,ih p.2 (lt_of_le_of_ne (mass_nonneg ht p.2) hne.symm)⟩

/-- The weighted Moore collision in an actual port multigraph gives an actual
simple cycle in its faithful subdivision, with exactly the expanded cost bound. -/
theorem short_cycle [Fintype D] [Nonempty D]
    (hdeg : ∀ d, 3 ≤ (PortWalk.out Γ.origin (Γ.origin d)).card)
    (len : D → ℝ) (hlen : ∀ d, 0 < len d)
    (hsym : ∀ d, len (Γ.reverse d) = len d) :
    let k := Nat.log 2 (Fintype.card D) + 2
    ∃ (a : V ⊕ D) (c : Γ.subdivision.Walk a a), c.IsCycle ∧
      weight (edgeWeight len) c ≤ 4*(k+1:ℝ)*(∑ d, len d)/Fintype.card D := by
  classical
  let T := PortWalk.transition Γ.origin Γ.reverse
  have ht : Transition T := PortWalk.transition_law Γ.origin Γ.reverse Γ.reverse_reverse hdeg
  obtain ⟨p,q,hne,hh,hl,hp,hq,hcost⟩ := logarithmic_short_collision ht len hlen
  have hgp : Good Γ p := positive_good Γ ht p hp
  have hgq : Good Γ q := positive_good Γ ht q hq
  let qp : Γ.subdivision.Walk (.inr (head p)) (.inr (Γ.reverse (last p))) :=
    (draw Γ q hgq).copy (congrArg Sum.inr hh.symm)
      (congrArg (fun d => Sum.inr (Γ.reverse d)) hl.symm)
  have hqp : (draw Γ p hgp) ≠ qp := by
    intro he
    have hr := congrArg (fun r => r.support.filterMap onlyPort) he
    simp only [qp,Walk.support_copy,draw_portWord] at hr
    exact hne (portWord_injective Γ _ hr)
  have hqred : qp.edges.IsChain (· ≠ ·) := by
    simpa only [qp,Walk.edges_copy] using draw_reduced Γ q hgq
  have hwq : weight (edgeWeight len) qp = cost len q := by
    simpa only [qp,weight,Walk.edges_copy] using draw_weight Γ len hsym q hgq
  obtain ⟨a,c,hc,hwc⟩ := distinct_reduced_cycle (edgeWeight len)
    (edgeWeight_nonneg len (fun d => (hlen d).le)) (draw Γ p hgp) qp hqp
    (draw_reduced Γ p hgp) hqred
  refine ⟨a,c,hc,?_⟩
  rw [draw_weight Γ len hsym p hgp,hwq] at hwc
  exact hwc.trans hcost

/-- Consequence used after suppressing degree-two core chains in the manuscript.
No bound on cycle rank or on the number of chains is assumed in this theorem. -/
theorem dart_count_inequality [Fintype D] [Nonempty D]
    (hdeg : ∀ d, 3 ≤ (PortWalk.out Γ.origin (Γ.origin d)).card)
    (len : D → ℝ) (hlen : ∀ d, 0 < len d)
    (hsym : ∀ d, len (Γ.reverse d) = len d)
    (L C : ℝ) (hL : 0 < L) (_hC : 0 ≤ C)
    (htotal : ∑ d, len d ≤ 2*C*L)
    (hgirth : ∀ a (c : Γ.subdivision.Walk a a), c.IsCycle → L ≤ weight (edgeWeight len) c) :
    (Fintype.card D : ℝ) ≤ 8*C*(Nat.log 2 (Fintype.card D)+3:ℝ) := by
  obtain ⟨a,c,hc,hbound⟩ := short_cycle Γ hdeg len hlen hsym
  have hD : (0:ℝ) < Fintype.card D := Nat.cast_pos.mpr Fintype.card_pos
  have hge := hgirth a c hc
  have he := (le_div_iff₀ hD).mp (hge.trans hbound)
  have hn : (0:ℝ) ≤ 4*((Nat.log 2 (Fintype.card D)+2:ℕ)+1:ℝ) := by positivity
  have hm := mul_le_mul_of_nonneg_left htotal hn
  push_cast at he hm
  nlinarith

/-- The logarithmic Moore inequality bounds the number of darts uniformly in
all positive edge lengths and in the girth scale. -/
theorem logarithmic_inequality_bounded (A : ℝ) (hA : 0 ≤ A) :
    ∃ R : ℕ, ∀ n : ℕ, (n : ℝ) ≤ A*((Nat.log 2 n:ℝ)+3) → n ≤ R := by
  have ht : Filter.Tendsto (fun n : ℕ => A*(Real.logb 2 n+3)/(n:ℝ))
      Filter.atTop (nhds 0) := by
    have hlog : Filter.Tendsto (fun n : ℕ => Real.logb 2 n/(n:ℝ))
        Filter.atTop (nhds 0) := by
      simpa [Function.comp_def] using (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 1
        one_ne_zero).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have hinv : Filter.Tendsto (fun n : ℕ => (3:ℝ)/(n:ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 3
    convert (hlog.add hinv).const_mul A using 1 <;> simp [add_div,mul_div_assoc]
  obtain ⟨R,hR⟩ := Filter.eventually_atTop.mp (ht.eventually_lt_const (by norm_num : (0:ℝ)<1))
  refine ⟨max R 1,fun n hn => ?_⟩
  by_contra hnR
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hl := hR n (by omega)
  have hb := mul_le_mul_of_nonneg_left (Real.natLog_le_logb n 2) hA
  norm_num only [Nat.cast_ofNat] at hb
  have hc : (n:ℝ) ≤ A*(Real.logb 2 n+3) := by nlinarith
  have hd := (div_lt_iff₀ hn0).mp hl
  linarith

/-- Fully uniform form of the weighted Moore bound needed by the actual-image
complexity argument; the bound is independent of L and of the multigraph. -/
theorem uniform_dart_bound (C : ℝ) (hC : 0 ≤ C) :
    ∃ R : ℕ, ∀ {V' D' : Type} [Fintype D'] [Nonempty D']
      (Γ' : PortGraph V' D')
      (_ : ∀ d, 3 ≤ (PortWalk.out Γ'.origin (Γ'.origin d)).card)
      (len : D' → ℝ) (_ : ∀ d, 0 < len d)
      (_ : ∀ d, len ((Γ').reverse d) = len d)
      (L : ℝ) (_ : 0 < L)
      (_ : ∑ d, len d ≤ 2*C*L)
      (_ : ∀ a (c : Γ'.subdivision.Walk a a), c.IsCycle →
        L ≤ weight (edgeWeight len) c), Fintype.card D' ≤ R := by
  obtain ⟨R,hR⟩ := logarithmic_inequality_bounded (8*C) (by positivity)
  refine ⟨R,?_⟩
  intro V' D' _ _ Γ' hdeg len hlen hsym L hL htotal hgirth
  exact hR _ (dart_count_inequality Γ' hdeg len hlen hsym L C hL hC htotal hgirth)

end TorsionFreeZeroDivisors.WeightedPortMoore

namespace TorsionFreeZeroDivisors.ChainSuppression
open Function
open scoped Classical

variable {D : Type*} (σ τ : D → D)
    (hσ : Involutive σ) (hτ : Involutive τ)

/-- The edge reversal followed by the unique turn at an unmarked degree-two
vertex. At marked vertices the turn fixes all outgoing darts. -/
def next : D → D := τ ∘ σ

include hσ hτ

lemma next_injective : Injective (next σ τ) := hτ.injective.comp hσ.injective

lemma folded_step (x : D) : next σ τ (τ (next σ τ x)) = τ x := by
  change τ (σ (τ (τ (σ x)))) = τ x
  rw [hτ (σ x),hσ x]

lemma folded_iterate (n : ℕ) (x : D) :
    (next σ τ)^[n] (τ ((next σ τ)^[n] x)) = τ x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply',iterate_succ_apply,ih,folded_step σ τ hσ hτ]

lemma reverse_segment {k i : ℕ} (hi : i ≤ k) (x : D) :
    (next σ τ)^[i] (τ ((next σ τ)^[k] x)) =
      τ ((next σ τ)^[k-i] x) := by
  have hk : k=i+(k-i) := by omega
  conv_lhs => rw [hk]
  rw [iterate_add_apply,folded_iterate σ τ hσ hτ]

variable [Finite D]

lemma exists_positive_return (x : D) (hx : τ x=x) :
    ∃ n : ℕ, 0<n ∧ τ ((next σ τ)^[n] x) = (next σ τ)^[n] x := by
  obtain ⟨n,hn,hp⟩ := (next_injective σ τ hσ hτ).mem_periodicPts x
  exact ⟨n,hn,by simpa only [hp.eq] using hx⟩

def length (x : D) (hx : τ x=x) : ℕ :=
  Nat.find (exists_positive_return σ τ hσ hτ x hx)

lemma length_pos (x : D) (hx : τ x=x) : 0 < length σ τ hσ hτ x hx :=
  (Nat.find_spec (exists_positive_return σ τ hσ hτ x hx)).1

lemma length_fixed (x : D) (hx : τ x=x) :
    τ ((next σ τ)^[length σ τ hσ hτ x hx] x) =
      (next σ τ)^[length σ τ hσ hτ x hx] x :=
  (Nat.find_spec (exists_positive_return σ τ hσ hτ x hx)).2

lemma no_internal_mark (x : D) (hx : τ x=x) {i : ℕ}
    (hi : 0 < i) (hik : i < length σ τ hσ hτ x hx) :
    τ ((next σ τ)^[i] x) ≠ (next σ τ)^[i] x := by
  intro he
  exact (not_lt_of_ge (Nat.find_min' (exists_positive_return σ τ hσ hτ x hx)
    ⟨hi,he⟩)) hik

/-- The opposite end of the maximal chain, given as its outgoing port. -/
def endpoint (x : {x : D // τ x=x}) : {x : D // τ x=x} :=
  ⟨(next σ τ)^[length σ τ hσ hτ x x.property] x,
    length_fixed σ τ hσ hτ x x.property⟩

lemma endpoint_reverse {x : {x : D // τ x=x}} {i : ℕ}
    (hi : i ≤ length σ τ hσ hτ x x.property) :
    (next σ τ)^[i] (endpoint σ τ hσ hτ x).val =
      τ ((next σ τ)^[length σ τ hσ hτ x x.property-i] x.val) := by
  have h := reverse_segment σ τ hσ hτ hi x.val
  rw [length_fixed σ τ hσ hτ x x.property] at h
  exact h

lemma endpoint_return (x : {x : D // τ x=x}) :
    (next σ τ)^[length σ τ hσ hτ x.val x.property] (endpoint σ τ hσ hτ x).val = x.val := by
  simpa only [Nat.sub_self,iterate_zero,id_eq,x.property] using
    (endpoint_reverse σ τ hσ hτ (x := x) (i := length σ τ hσ hτ x x.property) le_rfl)

lemma length_endpoint (x : {x : D // τ x=x}) :
    length σ τ hσ hτ (endpoint σ τ hσ hτ x).val (endpoint σ τ hσ hτ x).property =
      length σ τ hσ hτ x.val x.property := by
  let e := endpoint σ τ hσ hτ x
  let k := length σ τ hσ hτ x.val x.property
  let l := length σ τ hσ hτ e.val e.property
  have hk : 0<k := length_pos σ τ hσ hτ x.val x.property
  have hl : 0<l := length_pos σ τ hσ hτ e.val e.property
  have hret : (next σ τ)^[k] e.val=x.val := endpoint_return σ τ hσ hτ x
  have hle : l ≤ k := Nat.find_min' (exists_positive_return σ τ hσ hτ e.val e.property)
    ⟨hk,by rw [hret]; exact x.property⟩
  have heq : l=k := by
    by_contra he
    have hlt : l<k := lt_of_le_of_ne hle he
    have hr := endpoint_reverse σ τ hσ hτ (x := x) (i := l) hle
    have hef := length_fixed σ τ hσ hτ e.val e.property
    change τ ((next σ τ)^[l] e.val) = (next σ τ)^[l] e.val at hef
    rw [hr,hτ] at hef
    exact no_internal_mark σ τ hσ hτ x.val x.property (by omega : 0<k-l)
      (by omega : k-l<k) hef.symm
  exact heq

lemma endpoint_involutive : Involutive (endpoint σ τ hσ hτ) := by
  intro x
  apply Subtype.ext
  change (next σ τ)^[length σ τ hσ hτ (endpoint σ τ hσ hτ x).val
    (endpoint σ τ hσ hτ x).property] (endpoint σ τ hσ hτ x).val=x.val
  rw [length_endpoint]
  exact endpoint_return σ τ hσ hτ x

lemma endpoint_ne (hσne : ∀ d, σ d≠d) (x : {x : D // τ x=x}) :
    endpoint σ τ hσ hτ x ≠ x := by
  intro he
  let k := length σ τ hσ hτ x.val x.property
  have hk : 0<k := length_pos σ τ hσ hτ x.val x.property
  have hr (i : ℕ) (hi : i ≤ k) :
      (next σ τ)^[i] x.val=τ ((next σ τ)^[k-i] x.val) := by
    simpa only [he] using endpoint_reverse σ τ hσ hτ (x := x) hi
  rcases Nat.mod_two_eq_zero_or_one k with hp | hp
  · have hd : k-k/2=k/2 := by omega
    have hi : 0<k/2 := by omega
    have hit : k/2<k := by omega
    have hm := hr (k/2) (by omega)
    rw [hd] at hm
    exact no_internal_mark σ τ hσ hτ x.val x.property hi hit hm.symm
  · have hd : k-k/2=k/2+1 := by omega
    have hm := hr (k/2) (by omega)
    rw [hd,iterate_succ_apply'] at hm
    change (next σ τ)^[k/2] x.val = τ (τ (σ ((next σ τ)^[k/2] x.val))) at hm
    rw [hτ] at hm
    exact hσne _ hm.symm

/-- Each directed edge can be traversed at most once among all oriented
maximal chains. This is the exact disjoint-interior count, not a bound supplied
as an extra hypothesis. -/
lemma chain_dart_injective :
    Injective (fun p : (x : {x : D // τ x=x}) × Fin (length σ τ hσ hτ x.val x.property) =>
      (next σ τ)^[p.2.val] p.1.val) := by
  intro ⟨x,i⟩ ⟨y,j⟩ he
  have hone (x y : {x : D // τ x=x})
      (i : Fin (length σ τ hσ hτ x.val x.property))
      (j : Fin (length σ τ hσ hτ y.val y.property))
      (hij : i.val ≤ j.val)
      (he : (next σ τ)^[i.val] x.val=(next σ τ)^[j.val] y.val) :
      x=y ∧ i.val=j.val := by
    have hji : j.val=i.val+(j.val-i.val) := by omega
    rw [hji,iterate_add_apply] at he
    have hr := ((next_injective σ τ hσ hτ).iterate i.val) he
    have hzero : j.val-i.val=0 := by
      by_contra hz
      have hf : τ ((next σ τ)^[j.val-i.val] y.val)=(next σ τ)^[j.val-i.val] y.val := by
        rw [← hr]; exact x.property
      exact no_internal_mark σ τ hσ hτ y.val y.property (Nat.pos_of_ne_zero hz)
        (by omega) hf
    have hexy : x=y := by
      apply Subtype.ext
      simpa only [hzero,iterate_zero,id_eq] using hr
    exact ⟨hexy,by omega⟩
  have hxy : x=y ∧ i.val=j.val := by
    rcases le_total i.val j.val with hij | hji
    · exact hone x y i j hij he
    · obtain ⟨hexy,hij⟩ := hone y x j i hji he.symm
      exact ⟨hexy.symm,hij.symm⟩
  obtain ⟨rfl,hij⟩ := hxy
  congr 1
  exact Fin.ext hij

lemma total_length_le [Fintype D] :
    ∑ x : {x : D // τ x=x}, length σ τ hσ hτ x.val x.property ≤ Fintype.card D := by
  classical
  simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_le_of_injective _
    (chain_dart_injective σ τ hσ hτ)

end TorsionFreeZeroDivisors.ChainSuppression

end

end OAI
