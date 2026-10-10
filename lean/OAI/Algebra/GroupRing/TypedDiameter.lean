import Mathlib
import OAI.Algebra.GroupRing.ExpansionDiameter

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TypedDiameter
open Filter ConditionedMatchings MatchingDiameter DiameterProbability
open GirthAsymptotics TypedGraphs TorsionFreeZeroDivisors.Types
open scoped Topology Classical BigOperators

/-- A conservative effective prescription coefficient, for the diameter
union bound only. The empirical letter density remains 129/16513. -/
def p₀ : ℝ := 129/(4*16513)
def C₀ : ℝ := 9*(12*(132:ℝ)^2/p₀)^65
def ρ : ℝ := min (1/4) (min (p₀/65) (1/(2*C₀+2)))
def B (n : ℕ) : ℕ := ⌊ρ*n⌋₊
def R (rep : ℕ) : ℕ := 2130177*rep

theorem p₀_pos : 0<p₀ := by norm_num [p₀]
theorem p₀_le_one : p₀ ≤ 1 := by norm_num [p₀]
theorem C₀_pos : 0<C₀ := by unfold C₀; have := p₀_pos; positivity

theorem ρ_pos : 0<ρ := by
  unfold ρ
  exact lt_min (by norm_num) (lt_min (div_pos p₀_pos (by norm_num))
    (div_pos (by norm_num) (by have := C₀_pos; positivity)))

theorem ρ_le_quarter : ρ ≤ 1/4 := min_le_left _ _
theorem ρ_le_one : ρ ≤ 1 := ρ_le_quarter.trans (by norm_num)
theorem ρ_small : C₀*ρ^62 ≤ 1/2 := by
  have hle : ρ ≤ 1/(2*C₀+2) := (min_le_right _ _).trans (min_le_right _ _)
  have hmul : C₀*ρ ≤ 1/2 := by
    have hx := (le_div_iff₀ (show 0<2*C₀+2 by have := C₀_pos; positivity)).mp hle
    have := ρ_pos
    nlinarith
  have hpow : ρ^62 ≤ ρ := by
    simpa only [pow_one] using (pow_le_pow_of_le_one (le_of_lt ρ_pos) ρ_le_one (by norm_num : 1 ≤ 62))
  exact (mul_le_mul_of_nonneg_left hpow (le_of_lt C₀_pos)).trans hmul

theorem B_le (n : ℕ) : (B n:ℝ) ≤ ρ*n := Nat.floor_le (by have := ρ_pos; positivity)

theorem twice_B_le (n : ℕ) : 2*B n ≤ n := by
  have h := B_le n
  have hg := mul_le_mul_of_nonneg_right ρ_le_quarter (Nat.cast_nonneg n)
  have : (2:ℝ)*B n ≤ n := by linarith
  exact_mod_cast this

theorem sixtyfive_B_le (n : ℕ) : (65*B n:ℝ) ≤ p₀*n := by
  have hρ : ρ ≤ p₀/65 := (min_le_right _ _).trans (min_le_left _ _)
  have h := B_le n
  have hg := mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg n)
  linarith

theorem R_eq (rep : ℕ) : (R rep:ℝ) = 2*p₀*size rep := by
  unfold R p₀ size
  push_cast
  ring

theorem carrier_eq (rep : ℕ) : (4260354*rep:ℝ) = 4*p₀*size rep := by
  unfold p₀ size
  push_cast
  ring

theorem eventual_denom : ∀ᶠ rep : ℕ in atTop,
    R rep+65*B (size rep)+4*132^(2*(3*L (size rep))+1) ≤ 4260354*rep := by
  filter_upwards [size_tendsto.eventually (eventual_small p₀ p₀_pos)] with rep h
  have he : (4*132^(2*(3*L (size rep))+1):ℝ) < p₀*size rep := by
    simpa only [exclusion,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
      show 2*(3*L (size rep))=6*L (size rep) by omega] using h
  have hr := R_eq rep
  have hc := carrier_eq rep
  have hb := sixtyfive_B_le (size rep)
  have hh : (R rep:ℝ)+65*B (size rep)+4*132^(2*(3*L (size rep))+1) ≤
      4260354*rep := by linarith
  exact_mod_cast hh

theorem witness_summable (n : ℕ) (hn : 0<n) :
    Summable (fun k : ℕ => witnessTerm C₀ ρ n k) := by
  apply Summable.of_norm_bounded (summable_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)|<1))
  intro k
  exact witnessTerm_majorant (le_of_lt C₀_pos) ρ_small n k hn

/-- The exact empirical A-side conditioned sample space. -/
abbrev ΩA (rep : ℕ) := Matching.conditioned
  (label:=TypedGraphs.label (@outgoingA rep)) (bar:=inverse)
  (TypedGraphs.origin (@outgoingA rep)) (3*L (size rep)) ∅
abbrev ΩB (rep : ℕ) := Matching.conditioned
  (label:=TypedGraphs.label (@outgoingB rep)) (bar:=inverse)
  (TypedGraphs.origin (@outgoingB rep)) (3*L (size rep)) ∅

def badA (rep : ℕ) := failure
  (label:=TypedGraphs.label (@outgoingA rep)) (bar:=inverse)
  (TypedGraphs.origin (@outgoingA rep)) (B (size rep)) (3*L (size rep))
def badB (rep : ℕ) := failure
  (label:=TypedGraphs.label (@outgoingB rep)) (bar:=inverse)
  (TypedGraphs.origin (@outgoingB rep)) (B (size rep)) (3*L (size rep))

/-- Instantiation retains the actual vertex types, degree range, letter
carriers and prescribed girth conditioning. -/
theorem typed_bound {V : Type*} [Fintype V] (outgoing : V → Finset Letter)
    (rep : ℕ) (hrep : 0<rep) (hc : Fintype.card V=size rep)
    (hd : ∀ v, 129 ≤ (outgoing v).card ∧ (outgoing v).card ≤ 132)
    (hl : ∀ t, Fintype.card {v : V // t∈outgoing v}=4260354*rep)
    (hden : R rep+65*B (size rep)+4*132^(2*(3*L (size rep))+1) ≤ 4260354*rep)
    (hΩ : (Matching.conditioned (label:=TypedGraphs.label outgoing) (bar:=inverse)
      (TypedGraphs.origin outgoing) (3*L (size rep)) ∅).Nonempty) :
    (failure (label:=TypedGraphs.label outgoing) (bar:=inverse)
      (TypedGraphs.origin outgoing) (B (size rep)) (3*L (size rep))).card /
      ((Matching.conditioned (label:=TypedGraphs.label outgoing) (bar:=inverse)
        (TypedGraphs.origin outgoing) (3*L (size rep)) ∅).card:ℝ) ≤
      ∑' k : ℕ, witnessTerm C₀ ρ (size rep) k := by
  have hn : 0<size rep := by unfold size; positivity
  have hh := failure_probability_bound (TypedGraphs.origin outgoing)
    (B (size rep)) (3*L (size rep)) 132 (R rep) p₀ ρ
    inverse_ne (by norm_num)
    (fun v => by rw [origin_card]; exact (hd v).1)
    (fun v => by rw [origin_card]; exact (hd v).2)
    (by rw [hc]; exact twice_B_le _)
    (by rw [hc]; exact B_le _)
    p₀_pos p₀_le_one ρ_le_one
    (by rw [hc,R_eq]; have := p₀_pos; nlinarith [Nat.cast_nonneg (α:=ℝ) (size rep)])
    (by unfold R; positivity)
    (fun x => by rw [label_card,hl]; exact hden)
    hΩ (by rw [hc]; exact witness_summable _ hn)
  simpa only [hc,C₀,Nat.cast_ofNat] using hh

theorem eventual_bound : ∀ᶠ rep : ℕ in atTop,
    (badA rep).card/((ΩA rep).card:ℝ) ≤ ∑' k : ℕ, witnessTerm C₀ ρ (size rep) k ∧
    (badB rep).card/((ΩB rep).card:ℝ) ≤ ∑' k : ℕ, witnessTerm C₀ ρ (size rep) k := by
  filter_upwards [eventual_denom,eventual_nonempty,eventually_gt_atTop 0] with rep hd hΩ hr
  exact ⟨typed_bound _ rep hr (card_vertexA rep) degreeA_bounds (letter_frequencyA rep) hd hΩ.1,
    typed_bound _ rep hr (card_vertexB rep) degreeB_bounds (letter_frequencyB rep) hd hΩ.2⟩

theorem failureA_tendsto : Tendsto (fun rep : ℕ => (badA rep).card/((ΩA rep).card:ℝ))
    atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (by intro rep; positivity))
    (eventual_bound.mono (fun _ h => h.1))
  exact (witness_sum_tendsto (le_of_lt C₀_pos) ρ_small).comp size_tendsto

theorem failureB_tendsto : Tendsto (fun rep : ℕ => (badB rep).card/((ΩB rep).card:ℝ))
    atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (by intro rep; positivity))
    (eventual_bound.mono (fun _ h => h.2))
  exact (witness_sum_tendsto (le_of_lt C₀_pos) ρ_small).comp size_tendsto

/-- The deterministic constant in the manifestation of the diameter lemma. -/
def A₀ : ℕ := ⌈1/ρ⌉₊
def D₀ : ℕ := (A₀+1)*803

theorem packing_bound (n : ℕ) : n/(B n+1) ≤ A₀ := by
  have hfloor : ρ*n ≤ (B n:ℝ)+1 := (Nat.lt_floor_add_one (ρ*n)).le
  have hceil : 1/ρ ≤ (A₀:ℝ) := Nat.le_ceil _
  have hi : 1 ≤ ρ*(A₀:ℝ) := by
    have := (div_le_iff₀ ρ_pos).mp hceil
    nlinarith
  have h1 := mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg (α:=ℝ) n)
  have h2 := mul_le_mul_of_nonneg_right hfloor (Nat.cast_nonneg (α:=ℝ) A₀)
  have h3 : (n:ℝ) ≤ ((B n:ℝ)+1)*A₀ := by nlinarith
  apply Nat.div_le_of_le_mul
  exact_mod_cast h3

theorem log_radius_bound (n : ℕ) (hL : 1 ≤ L n) :
    2*(Nat.log 2 n+1)+1 ≤ 803*L n := by
  have hlog : (Nat.log 2 n:ℝ)*Real.log 2 ≤ Real.log n := by
    have := Real.natLog_le_logb n 2
    rw [Real.logb] at this
    norm_num only [Nat.cast_ofNat] at this
    exact (le_div_iff₀ (by linarith [Real.log_two_gt_d9])).mp this
  have hg := mul_le_mul_of_nonneg_left
    (show (1/2:ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9])
    (Nat.cast_nonneg (α:=ℝ) (Nat.log 2 n))
  have hl : Real.log n/100 < (L n:ℝ)+1 := Nat.lt_floor_add_one _
  have hL' : (1:ℝ) ≤ L n := by exact_mod_cast hL
  have hr : (Nat.log 2 n:ℝ) ≤ 400*L n := by nlinarith
  have hr' : Nat.log 2 n ≤ 400*L n := by exact_mod_cast hr
  omega

/-- This is the precise fixed-constant O(L) conclusion on the expansion
complement, with no degree or matching independence assumption. -/
theorem component_diameter {V D T : Type*} [Fintype V] [Fintype D]
    (origin : D → V) {label : D → T} {bar : T → T} (n N : ℕ)
    (hc : Fintype.card V=n) (hL : 1 ≤ L n) (r : Matching label bar)
    (hr : r∈Matching.conditioned (label:=label) (bar:=bar) origin N ∅)
    (hf : r∉failure (label:=label) (bar:=bar) origin (B n) N)
    {u v : V} (huv : (simpleGraph origin r).Reachable u v) :
    (simpleGraph origin r).dist u v ≤ D₀*L n := by
  have hpow : B n < 2^(Nat.log 2 n+1) :=
    (show B n ≤ n by have := twice_B_le n; omega).trans_lt
      (Nat.lt_pow_succ_log_self (by norm_num) n)
  have hh := diameter_of_not_failure origin (B n) N (Nat.log 2 n+1) r hr hf hpow huv
  rw [hc] at hh
  have hm := Nat.mul_le_mul (Nat.add_le_add_right (packing_bound n) 1)
    (log_radius_bound n hL)
  unfold D₀
  calc
    _ ≤ (n/(B n+1)+1)*(2*(Nat.log 2 n+1)+1) := hh.le
    _ ≤ (A₀+1)*(803*L n) := hm
    _ = _ := by ring

/-- The A-side actual diameter-failure event, still conditioned on girth. -/
def diameterBadA (rep : ℕ) := (ΩA rep).filter fun r =>
  ∃ u v, (simpleGraph (TypedGraphs.origin (@outgoingA rep)) r).Reachable u v ∧
    D₀*L (size rep) < (simpleGraph (TypedGraphs.origin (@outgoingA rep)) r).dist u v
def diameterBadB (rep : ℕ) := (ΩB rep).filter fun r =>
  ∃ u v, (simpleGraph (TypedGraphs.origin (@outgoingB rep)) r).Reachable u v ∧
    D₀*L (size rep) < (simpleGraph (TypedGraphs.origin (@outgoingB rep)) r).dist u v

theorem diameterBadA_subset (rep : ℕ) (hL : 1 ≤ L (size rep)) :
    diameterBadA rep ⊆ badA rep := by
  intro r hr
  obtain ⟨hr,u,v,huv,hlt⟩ := Finset.mem_filter.mp hr
  by_contra hf
  exact (not_lt_of_ge (component_diameter _ _ _ (card_vertexA rep) hL r hr hf huv)) hlt

theorem diameterBadB_subset (rep : ℕ) (hL : 1 ≤ L (size rep)) :
    diameterBadB rep ⊆ badB rep := by
  intro r hr
  obtain ⟨hr,u,v,huv,hlt⟩ := Finset.mem_filter.mp hr
  by_contra hf
  exact (not_lt_of_ge (component_diameter _ _ _ (card_vertexB rep) hL r hr hf huv)) hlt

/-- Diameter bound for the literal A empirical type table. -/
theorem diameterA_tendsto :
    Tendsto (fun rep : ℕ => (diameterBadA rep).card/((ΩA rep).card:ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (by intro rep; positivity)) _ failureA_tendsto
  filter_upwards [(L_tendsto.comp size_tendsto).eventually_ge_atTop 1] with rep hL
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (diameterBadA_subset rep hL)

/-- Diameter bound for the literal B empirical type table. -/
theorem diameterB_tendsto :
    Tendsto (fun rep : ℕ => (diameterBadB rep).card/((ΩB rep).card:ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (by intro rep; positivity)) _ failureB_tendsto
  filter_upwards [(L_tendsto.comp size_tendsto).eventually_ge_atTop 1] with rep hL
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (diameterBadB_subset rep hL)

end TorsionFreeZeroDivisors.TypedDiameter
namespace TorsionFreeZeroDivisors.FiniteJointAvoidance
open scoped Classical
lemma exists_outside {A B : Type} (s : Finset A) (t : Finset B) (a : Finset A) (b : Finset B)
    (P : A×B → Prop) (hs : s.Nonempty) (ht : t.Nonempty)
    (hp : (((s×ˢt).filter P).card:ℝ)/(s.card*t.card:ℕ)<1/3)
    (ha : (a.card:ℝ)/s.card<1/3) (hb : (b.card:ℝ)/t.card<1/3) :
    ∃ r∈s×ˢt,r.1∉a ∧ r.2∉b ∧ ¬P r := by
  by_contra hn
  push Not at hn
  have hsub : s×ˢt ⊆ ((s×ˢt).filter P) ∪ ((a×ˢt) ∪ (s×ˢb)) := by
    intro r hr
    by_cases hp : P r
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hr,hp⟩)
    apply Finset.mem_union_right
    have hh := hn r hr
    have hm := Finset.mem_product.mp hr
    by_cases he : r.1∈a
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨he,hm.2⟩)
    · have hf : r.2∈b := by by_contra hb; exact hp (hh he hb)
      exact Finset.mem_union_right _ (Finset.mem_product.mpr ⟨hm.1,hf⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hc' := Finset.card_union_le (a×ˢt) (s×ˢb)
  rw [Finset.card_product] at hc
  simp only [Finset.card_product] at hc'
  have hc'' : s.card*t.card≤((s×ˢt).filter P).card+a.card*t.card+s.card*b.card := by omega
  have hsr : (0:ℝ)<s.card := by exact_mod_cast Finset.card_pos.mpr hs
  have htr : (0:ℝ)<t.card := by exact_mod_cast Finset.card_pos.mpr ht
  have hpr := (div_lt_iff₀ (mul_pos hsr htr)).mp (by simpa only [Nat.cast_mul] using hp)
  have har := mul_lt_mul_of_pos_right ((div_lt_iff₀ hsr).mp ha) htr
  have hbr := mul_lt_mul_of_pos_left ((div_lt_iff₀ htr).mp hb) hsr
  have hcr : (s.card:ℝ)*t.card≤((s×ˢt).filter P).card+a.card*t.card+s.card*b.card := by exact_mod_cast hc''
  nlinarith
end TorsionFreeZeroDivisors.FiniteJointAvoidance

namespace TorsionFreeZeroDivisors.MatchingAlias
open scoped Classical
lemma conditioned_eq {V : Type} [Fintype V] (outgoing : V → Finset Types.Letter) (N : ℕ) :
    ConditionedMatchings.Matching.conditioned (label:=TypedGraphs.label outgoing)
      (bar:=Types.inverse) (TypedGraphs.origin outgoing) N ∅ =
    ConditionedMatchings.Matching.conditioned (label:=PatternEmbeddings.label outgoing)
      (bar:=Types.inverse) (PatternEmbeddings.origin outgoing) N ∅ := by
  unfold TypedGraphs.label TypedGraphs.origin PatternEmbeddings.label PatternEmbeddings.origin
  ext r
  simp only [ConditionedMatchings.Matching.conditioned,Finset.mem_filter,Finset.mem_univ,true_and]
end TorsionFreeZeroDivisors.MatchingAlias

namespace TorsionFreeZeroDivisors.GraphSample
open scoped Classical
open GirthAsymptotics TypedGraphs ActualPatternEvent Filter

lemma samples_eq (rep : ℕ) : samples rep = TypedDiameter.ΩA rep ×ˢ TypedDiameter.ΩB rep := by
  apply Finset.ext
  intro r
  rw [BoundedPattern.mem_samples]
  erw [Finset.mem_product]
  simp only [TypedDiameter.ΩA,TypedDiameter.ΩB,
    ConditionedMatchings.Matching.conditioned,Finset.mem_filter,Finset.mem_univ,true_and]
  rfl

/-- Both exact component diameter conclusions, including disconnected graphs. -/
def Diameters (rep : ℕ) (r : Match rep) : Prop :=
  (∀ u v,(MatchingDiameter.simpleGraph (TypedGraphs.origin (@Types.outgoingA rep)) r.1).Reachable u v →
    (MatchingDiameter.simpleGraph (TypedGraphs.origin (@Types.outgoingA rep)) r.1).dist u v≤TypedDiameter.D₀*L (size rep)) ∧
  (∀ u v,(MatchingDiameter.simpleGraph (TypedGraphs.origin (@Types.outgoingB rep)) r.2).Reachable u v →
    (MatchingDiameter.simpleGraph (TypedGraphs.origin (@Types.outgoingB rep)) r.2).dist u v≤TypedDiameter.D₀*L (size rep))

lemma diameters_of_not_bad (rep : ℕ) (r : Match rep) (hr : r∈samples rep)
    (ha : r.1∉TypedDiameter.diameterBadA rep) (hb : r.2∉TypedDiameter.diameterBadB rep) :
    Diameters rep r := by
  have hm : r.1∈TypedDiameter.ΩA rep ∧ r.2∈TypedDiameter.ΩB rep := by
    rw [samples_eq] at hr
    exact Finset.mem_product.mp hr
  constructor
  · intro u v huv
    by_contra h
    exact ha (Finset.mem_filter.mpr ⟨hm.1,u,v,huv,Nat.lt_of_not_ge h⟩)
  · intro u v huv
    by_contra h
    exact hb (Finset.mem_filter.mpr ⟨hm.2,u,v,huv,Nat.lt_of_not_ge h⟩)

/-- The diameter event and the entire bounded-pattern avoidance event occur
simultaneously in the literal conditional product sample. -/
theorem bounded_with_diameter (R K T I B Q M J : ℕ)
    (hR : 0<R) (hK : 0<K) (hI : 0<I) (hM : 0<M) :
    ∀ᶠ rep in atTop,∀ (x : Types.VertexA rep) (y : Types.VertexB rep),
      ∃ r∈samples rep,Diameters rep r ∧ ∀ a : BoundedPattern.Data R K T I (B*L (size rep)),
        a.Good B Q M J rep → ¬a.event rep x y r := by
  have hp := (BoundedPattern.polynomial_exp_tendsto (PatternTotalCoding.coefficient R K T I)
    B (R+3*I) M hM).eventually_lt_const (by norm_num : (0:ℝ)<1/3)
  have ha := TypedDiameter.diameterA_tendsto.eventually_lt_const (by norm_num : (0:ℝ)<1/3)
  have hb := TypedDiameter.diameterB_tendsto.eventually_lt_const (by norm_num : (0:ℝ)<1/3)
  filter_upwards [hp,ha,hb,BoundedPattern.samples_eventually_nonempty,
    PatternUniform.eventually_ready B M Q J hM] with rep hp ha hb hs hu
  intro x y
  have hprob := (BoundedPattern.probability_union R K T I (B*L (size rep)) B Q M J rep
    hR hK hI hM hs hu x y).trans_lt hp
  rw [samples_eq] at hs hprob
  have hn := Finset.nonempty_product.mp hs
  have hprob' :
      (((TypedDiameter.ΩA rep ×ˢ TypedDiameter.ΩB rep).filter
        (fun r => ∃ a : BoundedPattern.Data R K T I (B*L (size rep)),a.Good B Q M J rep ∧ a.event rep x y r)).card:ℝ) /
        ((TypedDiameter.ΩA rep).card*(TypedDiameter.ΩB rep).card:ℕ)<1/3 :=
    Eq.mp (congrArg (fun n : ℕ =>
      (((TypedDiameter.ΩA rep ×ˢ TypedDiameter.ΩB rep).filter
        (fun r => ∃ a : BoundedPattern.Data R K T I (B*L (size rep)),a.Good B Q M J rep ∧ a.event rep x y r)).card:ℝ) /
        (n:ℝ)<1/3) (Finset.card_product (TypedDiameter.ΩA rep) (TypedDiameter.ΩB rep))) hprob
  obtain ⟨r,hr,hra,hrb,hrp⟩ := FiniteJointAvoidance.exists_outside
    (TypedDiameter.ΩA rep) (TypedDiameter.ΩB rep)
    (TypedDiameter.diameterBadA rep) (TypedDiameter.diameterBadB rep)
    (fun r => ∃ a : BoundedPattern.Data R K T I (B*L (size rep)),a.Good B Q M J rep ∧ a.event rep x y r)
    hn.1 hn.2 hprob' ha hb
  have hr' : r∈samples rep := by
    rw [samples_eq]
    exact hr
  refine ⟨r,hr',diameters_of_not_bad rep r hr' hra hrb,?_⟩
  exact fun a hg he => hrp ⟨a,hg,he⟩

/-- Source entropy proposition for arbitrary literal immersed path systems,
with the independent short-closure diameter event included. -/
theorem raw_with_diameter (B K I : ℕ) (hK : 0<K) (hI : 0<I) :
    ∀ᶠ rep in atTop,∀ (x : Types.VertexA rep) (y : Types.VertexB rep),
      ∃ r∈samples rep,Diameters rep r ∧ ∀ a : RawSourcePattern.Data B K I rep,¬a.event x y r := by
  have hT : 0<SourcePattern.T B K := Nat.mul_pos (SourcePattern.R_pos B K) (by omega)
  filter_upwards [bounded_with_diameter (SourcePattern.R B K) K (SourcePattern.T B K)
    I B (SourcePattern.R B K) (SourcePattern.T B K) (I*(SourcePattern.T B K)^2)
    (SourcePattern.R_pos B K) hK hI hT,
    (L_tendsto.comp size_tendsto).eventually (eventually_ge_atTop 1)] with rep hr hL
  change 1≤L (size rep) at hL
  intro x y
  obtain ⟨r,hs,hd,ha⟩ := hr x y
  refine ⟨r,hs,hd,fun a he => ?_⟩
  exact ha (a.suppressed.bounded (by omega)) (a.suppressed.bounded_good (by omega))
    (a.suppressed_event x y r he)

end TorsionFreeZeroDivisors.GraphSample

end

end OAI
