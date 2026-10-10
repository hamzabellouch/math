import Mathlib
import OAI.Algebra.GroupRing.TwoSideFullStage

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TypedGraphs
open Filter GirthAsymptotics TorsionFreeZeroDivisors.Types ConditionedMatchings PortSubdivision
open scoped Topology

/-- Admissible sizes are exactly the multiplicities of the empirical table. -/
def size (rep : ℕ) : ℕ := 2 * 16513 ^ 2 * rep

theorem size_tendsto : Tendsto size atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ => n) _ tendsto_id
  intro n
  dsimp [size]
  omega

theorem eventual_carrier : ∀ᶠ rep : ℕ in atTop,
    4 * 132 ^ (2 * (3 * L (size rep)) + 1) < 4260354 * rep := by
  have h := size_tendsto.eventually (eventual_small (4260354 / (2 * 16513^2)) (by norm_num))
  filter_upwards [h] with rep hr
  have he : (4260354 / (2 * 16513^2) : ℝ) * (size rep : ℝ) = 4260354 * rep := by
    simp only [size,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    ring
  rw [he] at hr
  have hr' : exclusion (size rep) < 4260354 * rep := by exact_mod_cast hr
  simpa only [exclusion, show 2 * (3 * L (size rep)) = 6 * L (size rep) by omega] using hr'

/-- Both jointly conditioned graph spaces really exist for all sufficiently
large admissible sizes; no high-girth existence is a standing assumption. -/
theorem eventual_nonempty : ∀ᶠ rep : ℕ in atTop,
    (Matching.conditioned (label := label (@outgoingA rep)) (bar := inverse)
      (origin (@outgoingA rep)) (3 * L (size rep)) ∅).Nonempty ∧
    (Matching.conditioned (label := label (@outgoingB rep)) (bar := inverse)
      (origin (@outgoingB rep)) (3 * L (size rep)) ∅).Nonempty := by
  filter_upwards [eventual_carrier] with rep hr
  exact ⟨conditionedA_nonempty _ _ hr,conditionedB_nonempty _ _ hr⟩

/-- The simple-graph girth says exactly what is required of the original
multigraph's immersed closed paths. Loops and parallel edges were not discarded. -/
theorem reduced_circuit_length {V D : Type*} (Γ : PortGraph V D) (L : ℕ)
    (hg : (3 * L : ℕ) ≤ Γ.subdivision.egirth) {v : V}
    (p : Γ.Walk v v) (hp : p.IsReduced) (hne : 0 < p.length) : L ≤ p.length := by
  have h := GirthSwitch.reduced_closed_length (3*L) hg p.toSubdivision
    (by rw [p.length_toSubdivision]; omega) (p.reduced_toSubdivision hp)
  rw [p.length_toSubdivision] at h
  omega

end TorsionFreeZeroDivisors.TypedGraphs

namespace TorsionFreeZeroDivisors.TypedStage
open scoped Classical BigOperators Topology
open TorsionFreeZeroDivisors.Types TwoSideStage GirthAsymptotics Filter
local instance : DecidableEq Types.Letter := Classical.decEq _

variable {C V : Type} [Fintype C] [Fintype V]
variable (rep : ℕ) (len : C → ℕ) (first last : C → V)

abbrev sideA (pin : V → Option (VertexA rep)) : TwoSideStage.Side where
  C := C
  V := V
  TV := VertexA rep
  fC := inferInstance
  fV := inferInstance
  fTV := inferInstance
  len := len
  first := first
  last := last
  outgoing := @outgoingA rep
  pin := pin

abbrev sideB (pin : V → Option (VertexB rep)) : TwoSideStage.Side where
  C := C
  V := V
  TV := VertexB rep
  fC := inferInstance
  fV := inferInstance
  fTV := inferInstance
  len := len
  first := first
  last := last
  outgoing := @outgoingB rep
  pin := pin

theorem conditionsA (pin : V → Option (VertexA rep)) (N R : ℕ) (hR : 0 < R)
    (hroom : R + ∑ c, len c + 4*132^(2*N+1) ≤ 4260354*rep) :
    Conditions (sideA rep len first last pin) (TypedGraphs.size rep) (129/16513) N 132 R := by
  refine ⟨by norm_num,?_,?_,by norm_num,hR,?_,?_,?_⟩
  · change (Fintype.card (VertexA rep) : ℝ) ≤ (TypedGraphs.size rep : ℝ)
    simp only [← Nat.card_eq_fintype_card]
    rw [Nat.card_eq_fintype_card,card_vertexA]
    exact le_rfl
  · intro t u h
    dsimp only [sideA]
    rw [← Nat.card_eq_fintype_card]
    simpa only [← Nat.card_eq_fintype_card, show Nat.card (VertexA rep) = TypedGraphs.size rep by
      rw [Nat.card_eq_fintype_card,card_vertexA]; rfl] using TypeWeights.joint_countA_le rep t u h
  · intro v
    exact (TypedGraphs.origin_card (@outgoingA rep) v).le.trans (degreeA_bounds v).2
  · intro x
    change R + ∑ c, len c + 4*132^(2*N+1) ≤
      Nat.card {a : TypedGraphs.Dart (@outgoingA rep) // TypedGraphs.label _ a = TypedGraphs.label _ x}
    rw [TypedGraphs.label_card,letter_frequencyA]
    exact hroom
  · obtain ⟨r,hr⟩ := TypedGraphs.conditionedA_nonempty rep N (by omega)
    refine ⟨r,?_⟩
    dsimp only [sideA,Side.samples,ConditionedMatchings.Matching.conditioned]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    exact (Finset.mem_filter.mp hr).2

theorem conditionsB (pin : V → Option (VertexB rep)) (N R : ℕ) (hR : 0 < R)
    (hroom : R + ∑ c, len c + 4*132^(2*N+1) ≤ 4260354*rep) :
    Conditions (sideB rep len first last pin) (TypedGraphs.size rep) (129/16513) N 132 R := by
  refine ⟨by norm_num,?_,?_,by norm_num,hR,?_,?_,?_⟩
  · change (Fintype.card (VertexB rep) : ℝ) ≤ (TypedGraphs.size rep : ℝ)
    simp only [← Nat.card_eq_fintype_card]
    rw [Nat.card_eq_fintype_card,card_vertexB]
    exact le_rfl
  · intro t u h
    dsimp only [sideB]
    rw [← Nat.card_eq_fintype_card]
    simpa only [← Nat.card_eq_fintype_card, show Nat.card (VertexB rep) = TypedGraphs.size rep by
      rw [Nat.card_eq_fintype_card,card_vertexB]; rfl] using (TypeWeights.joint_countB rep t u h).le
  · intro v
    exact (TypedGraphs.origin_card (@outgoingB rep) v).le.trans (degreeB_bounds v).2
  · intro x
    change R + ∑ c, len c + 4*132^(2*N+1) ≤
      Nat.card {a : TypedGraphs.Dart (@outgoingB rep) // TypedGraphs.label _ a = TypedGraphs.label _ x}
    rw [TypedGraphs.label_card,letter_frequencyB]
    exact hroom
  · obtain ⟨r,hr⟩ := TypedGraphs.conditionedB_nonempty rep N (by omega)
    refine ⟨r,?_⟩
    dsimp only [sideB,Side.samples,ConditionedMatchings.Matching.conditioned]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    exact (Finset.mem_filter.mp hr).2

end TorsionFreeZeroDivisors.TypedStage

namespace TorsionFreeZeroDivisors.StageCost
open scoped BigOperators

/-- The exact vertex/table/prescription factor, before the retained turn cost. -/
def cost (n p r : ℝ) (f i e : ℕ) : ℝ := n^(f+i)*p^i/r^e

theorem cost_exp (n p r : ℝ) (hn : 0<n) (hp : 0<p) (hr : 0<r) (f i e : ℕ) :
    cost n p r f i e = Real.exp
      ((((f:ℝ)+i-e)*Real.log n) + (((i:ℝ)-e)*Real.log p) +
        e*Real.log (n*p/r)) := by
  rw [Real.log_div (ne_of_gt (mul_pos hn hp)) (ne_of_gt hr),
    Real.log_mul (ne_of_gt hn) (ne_of_gt hp)]
  have he : (((f:ℝ)+i-e)*Real.log n) + (((i:ℝ)-e)*Real.log p) +
      e*(Real.log n+Real.log p-Real.log r) =
      (f+i:ℕ)*Real.log n + (i:ℝ)*Real.log p - (e:ℝ)*Real.log r := by
    push_cast; ring
  rw [he,Real.exp_sub,Real.exp_add,Real.exp_nat_mul,Real.exp_nat_mul,Real.exp_nat_mul,
    Real.exp_log hn,Real.exp_log hp,Real.exp_log hr]
  rfl

theorem cost_chain_exp (n p r : ℝ) (hn : 0<n) (hp : 0<p) (hr : 0<r)
    (f i e q : ℕ) (he : i+q=e) :
    cost n p r f i e = Real.exp
      (((f:ℝ)-q)*Real.log n - (q:ℝ)*Real.log p + e*Real.log (n*p/r)) := by
  rw [cost_exp n p r hn hp hr]
  congr 1
  have he' : (i:ℝ)+q=e := by exact_mod_cast he
  rw [←he']
  ring

/-- Uniform error bound, with a bounded number q of chains and e ≤ k L edges.
It keeps the exact exponent f-q, including negative and zero cases. -/
theorem uniform_bound (n p r : ℝ) (hn : 0<n) (hp : 0<p) (hp1 : p≤1)
    (hr : 0<r) (hrnp : r≤n*p) (f i e q Q : ℕ) (he : i+q=e) (hq : q≤Q)
    (k L : ℝ) (heL : (e:ℝ)≤k*L) :
    cost n p r f i e ≤ Real.exp
      (((f:ℝ)-q)*Real.log n + (Q:ℝ)*(-Real.log p) + k*L*Real.log (n*p/r)) := by
  rw [cost_chain_exp n p r hn hp hr f i e q he]
  apply Real.exp_le_exp.mpr
  have hp' : 0 ≤ -Real.log p := neg_nonneg.mpr (Real.log_nonpos hp.le hp1)
  have hr' : 0 ≤ Real.log (n*p/r) := Real.log_nonneg ((le_div_iff₀ hr).mpr (by simpa using hrnp))
  have hq' := mul_le_mul_of_nonneg_right (show (q:ℝ)≤Q by exact_mod_cast hq) hp'
  have he' := mul_le_mul_of_nonneg_right heL hr'
  linarith

theorem internal_add_chains {C : Type*} [Fintype C] (len : C → ℕ) (hpos : ∀c,0<len c) :
    (∑c, (len c-1))+Fintype.card C=∑c,len c := by
  classical
  have h : (∑c : C, ((len c-1)+1)) = ∑c : C,len c := by
    apply Finset.sum_congr rfl
    intro c _
    exact Nat.sub_add_cancel (hpos c)
  simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using h

end TorsionFreeZeroDivisors.StageCost

namespace TorsionFreeZeroDivisors.StageDenominator

section
open scoped Topology
open Filter GirthAsymptotics TypedGraphs

def carrier (rep : ℕ) : ℕ := 4260354*rep
def denominator (K rep : ℕ) : ℕ :=
  carrier rep - (K*L (size rep)+exclusion (size rep))

theorem carrier_eq (rep : ℕ) : (carrier rep : ℝ) = (size rep : ℝ)*(129/16513) := by
  simp only [carrier,size,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring

theorem L_ratio : Tendsto (fun n : ℕ => (L n : ℝ)/n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    simpa only [pow_one,one_mul,add_zero,Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have h := hlog.div_const 100
  simp only [zero_div] at h
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ h
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hL : (L n:ℝ)≤Real.log (n:ℝ)/100 := Nat.floor_le (by positivity [Real.log_nonneg hn'])
  calc
    (L n:ℝ)/n ≤ (Real.log (n:ℝ)/100)/n := div_le_div_of_nonneg_right hL (by positivity)
    _ = (Real.log (n:ℝ)/n)/100 := by ring

theorem spent_ratio (K : ℕ) : Tendsto
    (fun rep => ((K*L (size rep)+exclusion (size rep):ℕ):ℝ)/(size rep)) atTop (𝓝 0) := by
  have h := ((L_ratio.comp size_tendsto).const_mul (K:ℝ)).add (exclusion_ratio.comp size_tendsto)
  simpa only [mul_zero,add_zero,Nat.cast_add,Nat.cast_mul,add_div,mul_div_assoc,Function.comp_def] using h

theorem eventually_room (K : ℕ) : ∀ᶠ rep in atTop,
    K*L (size rep)+exclusion (size rep)<carrier rep := by
  have h := (spent_ratio K).eventually_lt_const (by norm_num : (0:ℝ)<129/16513)
  filter_upwards [h,size_tendsto.eventually (eventually_ge_atTop 1)] with rep hh hn
  have hn0 : (0:ℝ)<size rep := by exact_mod_cast (show 0<size rep by omega)
  have hh' := (div_lt_iff₀ hn0).mp hh
  rw [mul_comm (129/16513:ℝ) (size rep),← carrier_eq] at hh'
  exact_mod_cast hh'

theorem eventually_pos (K : ℕ) : ∀ᶠ rep in atTop, 0<denominator K rep := by
  filter_upwards [eventually_room K] with rep hr
  exact Nat.sub_pos_of_lt hr

theorem denominator_ratio (K : ℕ) : Tendsto
    (fun rep => (denominator K rep:ℝ)/(size rep)) atTop (𝓝 (129/16513)) := by
  have h := (tendsto_const_nhds (x := (129/16513:ℝ))).sub (spent_ratio K)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_room K,size_tendsto.eventually (eventually_ge_atTop 1)] with rep hr hn
  have hn0 : (size rep:ℝ)≠0 := by exact_mod_cast (show size rep≠0 by omega)
  change (129/16513:ℝ) - _ = _
  rw [denominator,Nat.cast_sub hr.le,sub_div,carrier_eq,mul_div_cancel_left₀ _ hn0]

theorem relative_ratio (K : ℕ) : Tendsto
    (fun rep => ((size rep:ℝ)*(129/16513))/(denominator K rep)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (129/16513:ℝ))).div (denominator_ratio K) (by norm_num)
  norm_num only [div_self (by norm_num : (129/16513:ℝ)≠0)] at h
  apply h.congr'
  apply Eventually.of_forall
  intro rep
  change (129/16513:ℝ) / ((denominator K rep:ℝ)/(size rep)) = _
  rw [div_div_eq_mul_div]
  ring

def penalty (K rep : ℕ) : ℝ := Real.log ((size rep:ℝ)*(129/16513)/(denominator K rep))

theorem penalty_tendsto (K : ℕ) : Tendsto (penalty K) atTop (𝓝 0) := by
  change Tendsto (fun rep => Real.log ((size rep:ℝ)*(129/16513)/(denominator K rep))) _ _
  have h := (Real.continuousAt_log one_ne_zero).tendsto.comp (relative_ratio K)
  simpa only [Real.log_one,Function.comp_def] using h

theorem penalty_nonneg (K rep : ℕ) (hr : 0 < denominator K rep) : 0 ≤ penalty K rep := by
  apply Real.log_nonneg
  apply (le_div_iff₀ (show (0:ℝ)<denominator K rep by exact_mod_cast hr)).mpr
  simpa only [one_mul,←carrier_eq] using
    (show (denominator K rep:ℝ)≤carrier rep from Nat.cast_le.mpr (Nat.sub_le ..))

def error (K Q rep : ℕ) : ℝ :=
  Q*(-Real.log (129/16513)) + (K:ℝ)*L (size rep)*penalty K rep

theorem error_ratio (K Q : ℕ) : Tendsto
    (fun rep => error K Q rep / (L (size rep):ℝ)) atTop (𝓝 0) := by
  have hL : Tendsto (fun rep => (L (size rep):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (L_tendsto.comp size_tendsto)
  have hconst := (tendsto_inv_atTop_zero.comp hL).const_mul ((Q:ℝ)*(-Real.log (129/16513)))
  have hpen := (penalty_tendsto K).const_mul (K:ℝ)
  have h := hconst.add hpen
  simp only [mul_zero,add_zero] at h
  apply h.congr'
  filter_upwards [(L_tendsto.comp size_tendsto).eventually (eventually_ge_atTop 1)] with rep hn
  change 1≤L (size rep) at hn
  have hn0 : (L (size rep):ℝ)≠0 := by exact_mod_cast (show L (size rep)≠0 by omega)
  simp only [error,Function.comp_def]
  field_simp

end

open scoped BigOperators Topology
open Filter GirthAsymptotics TypedGraphs TwoSideStage

/-- Each side has the SAME empirical carrier denominator, not the sum of the
sizes of the two disjoint graphs. This bound is uniform in every stage. -/
theorem room (K rep e : ℕ) (hr : K*L (size rep)+exclusion (size rep) ≤ carrier rep)
    (he : e ≤ K*L (size rep)) :
    denominator K rep+e+4*132^(2*(3*L (size rep))+1) ≤ 4260354*rep := by
  have hh : 2*(3*L (size rep))=6*L (size rep) := by omega
  rw [hh]
  change denominator K rep+e+exclusion (size rep) ≤ carrier rep
  dsimp only [denominator]
  omega

variable {C V : Type} [Fintype C] [Fintype V]

theorem conditionsA (K rep : ℕ) (hr : K*L (size rep)+exclusion (size rep)<carrier rep)
    (len : C → ℕ) (first last : C → V) (pin : V → Option (Types.VertexA rep))
    (he : ∑c,len c ≤ K*L (size rep)) :
    Conditions (TypedStage.sideA rep len first last pin) (size rep) (129/16513)
      (3*L (size rep)) 132 (denominator K rep) :=
  TypedStage.conditionsA rep len first last pin _ _ (Nat.sub_pos_of_lt hr)
    (room K rep _ hr.le he)

theorem conditionsB (K rep : ℕ) (hr : K*L (size rep)+exclusion (size rep)<carrier rep)
    (len : C → ℕ) (first last : C → V) (pin : V → Option (Types.VertexB rep))
    (he : ∑c,len c ≤ K*L (size rep)) :
    Conditions (TypedStage.sideB rep len first last pin) (size rep) (129/16513)
      (3*L (size rep)) 132 (denominator K rep) :=
  TypedStage.conditionsB rep len first last pin _ _ (Nat.sub_pos_of_lt hr)
    (room K rep _ hr.le he)

/-- The edge/table cost is an exponential of f-q log n plus a uniform o(L),
for two sides jointly. The signed value f-q is NOT replaced by its positive part. -/
theorem joint_cost_bound (A B : Side) (K Q rep : ℕ) (hn : 0<size rep)
    (hr : 0<denominator K rep) (ha : ∀c,0<A.len c) (hb : ∀c,0<B.len c)
    (hQ : Fintype.card A.C+Fintype.card B.C ≤ Q)
    (hE : A.edges+B.edges ≤ K*L (size rep)) :
    A.cost (size rep) (129/16513) (denominator K rep) *
      B.cost (size rep) (129/16513) (denominator K rep) ≤
      Real.exp ((((A.freeMarks+B.freeMarks:ℕ):ℝ)-
        (Fintype.card A.C+Fintype.card B.C:ℕ))*Real.log (size rep)+error K Q rep) := by
  have hAI := StageCost.internal_add_chains A.len ha
  have hBI := StageCost.internal_add_chains B.len hb
  have he : A.internal+B.internal+(Fintype.card A.C+Fintype.card B.C)=A.edges+B.edges := by
    dsimp only [Side.internal,Side.edges] at *
    omega
  have hrnp : (denominator K rep:ℝ) ≤ (size rep:ℝ)*(129/16513) := by
    rw [←carrier_eq]
    exact Nat.cast_le.mpr (Nat.sub_le ..)
  have h := StageCost.uniform_bound (size rep) (129/16513) (denominator K rep)
    (by exact_mod_cast hn) (by norm_num) (by norm_num) (by exact_mod_cast hr) hrnp
    (A.freeMarks+B.freeMarks) (A.internal+B.internal) (A.edges+B.edges)
    (Fintype.card A.C+Fintype.card B.C) Q he hQ K (L (size rep)) (by exact_mod_cast hE)
  have hc : A.cost (size rep) (129/16513) (denominator K rep)*
      B.cost (size rep) (129/16513) (denominator K rep) =
      StageCost.cost (size rep) (129/16513) (denominator K rep)
        (A.freeMarks+B.freeMarks) (A.internal+B.internal) (A.edges+B.edges) := by
    rw [cost_product]
    unfold StageCost.cost
    have hex : A.freeMarks+A.internal+B.freeMarks+B.internal =
        (A.freeMarks+B.freeMarks)+(A.internal+B.internal) := by omega
    rw [hex]
  rw [hc]
  simpa only [error,penalty,add_assoc] using h

end TorsionFreeZeroDivisors.StageDenominator

end

end OAI
