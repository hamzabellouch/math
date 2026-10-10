import OAI.Combinatorics.CycleDecomposition.Routing

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai
noncomputable section
open Real Filter Asymptotics

lemma routing_length_upper (r h : ℝ) (hr : 2 ≤ r) (hh : 0 < h) (hhr : h ≤ r) :
    (routingLength r h : ℝ) ≤ 108*(r/h)*(logb 2 r)^2 := by
  have hr0 : 0 < r := by linarith
  have hl : 1 ≤ logb 2 r := by
    simpa using Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
      (by norm_num : (0:ℝ) < 2) hr
  have hR : 1 ≤ r/h := (le_div_iff₀ hh).mpr (by simpa using hhr)
  have hlog : logb 2 (2*r) = 1 + logb 2 r := by
    rw [Real.logb_mul (by norm_num) hr0.ne']
    norm_num
  have hg := Nat.ceil_lt_add_one (show 0 ≤ 8*(r/h)*logb 2 (2*r) by rw [hlog]; positivity)
  have hd := Nat.ceil_lt_add_one (show 0 ≤ logb 2 r by linarith)
  change (routingG r h : ℝ) < 8*(r/h)*logb 2 (2*r)+1 at hg
  change (routingDepth r : ℝ) < logb 2 r + 1 at hd
  rw [hlog] at hg
  have hprod : 1 ≤ (r/h)*logb 2 r := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr hl)]
  have hg' : (routingG r h : ℝ) ≤ 18*(r/h)*logb 2 r := by nlinarith
  have hd' : (1 + routingDepth r : ℝ) ≤ 3*logb 2 r := by linarith
  have hm := mul_le_mul hg' hd' (by positivity) (by positivity)
  dsimp [routingLength]
  push_cast
  nlinarith

lemma eventually_logb_le_power (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, logb 2 D ≤ D^ε := by
  have ho := (isLittleO_log_rpow_atTop hε).const_mul_left (1 / log 2)
  filter_upwards [ho.eventuallyLE, eventually_ge_atTop (1:ℝ)] with D hD h1
  simpa [Real.logb, div_eq_mul_inv, mul_comm, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg h1), abs_of_nonneg (Real.rpow_nonneg (by linarith) ε),
    abs_of_pos (show 0 < (log 2)⁻¹ by positivity),
    abs_of_pos (Real.log_pos (by norm_num : (1:ℝ) < 2))] using hD

lemma eventually_constant_le_power (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, C ≤ D^ε :=
  (tendsto_rpow_atTop hε).eventually (eventually_ge_atTop C)

lemma eventually_const_mul_power_le (C α β : ℝ) (hab : α < β) :
    ∀ᶠ D : ℝ in atTop, C*D^α ≤ D^β := by
  filter_upwards [eventually_constant_le_power C (β-α) (by linarith),
    eventually_gt_atTop (0:ℝ)] with D hc hD
  calc
    C*D^α ≤ D^(β-α)*D^α := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hD.le _)
    _ = D^β := by rw [← Real.rpow_add hD]; congr 1; ring

theorem eventually_routing_length (c β γ δ : ℝ) (hc : 0 < c) (hβ : 0 < β)
    (hδ : 0 < δ) :
    ∀ᶠ D : ℝ in atTop, ∀ r : ℝ, 2 ≤ r → r ≤ D^β → c*D^γ ≤ r →
      (routingLength r (c*D^γ) : ℝ) ≤ D^(β-γ+δ) := by
  filter_upwards [eventually_logb_le_power (δ/4) (by positivity),
    eventually_constant_le_power (108*β^2/c) (δ/2) (by positivity),
    eventually_gt_atTop (1:ℝ)] with D hlog hconst hD r hr hrD hhr
  have hD0 : 0 < D := by linarith
  have hpowγ : 0 < D^γ := Real.rpow_pos_of_pos hD0 _
  have hden : 0 < c*D^γ := mul_pos hc hpowγ
  have hlog0 : 0 ≤ logb 2 r := (Real.logb_pos (by norm_num) (by linarith)).le
  have hlogR : logb 2 r ≤ β*D^(δ/4) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
      (by linarith : 0 < r) hrD
    rw [Real.logb_rpow_eq_mul_logb_of_pos hD0] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hlog hβ.le)
  have hratio : r/(c*D^γ) ≤ D^(β-γ)/c := by
    calc
      _ ≤ D^β/(c*D^γ) := div_le_div_of_nonneg_right hrD hden.le
      _ = _ := by rw [Real.rpow_sub hD0]; ring
  have hsq : (logb 2 r)^2 ≤ β^2*D^(δ/2) := by
    calc
      _ ≤ (β*D^(δ/4))^2 := pow_le_pow_left₀ hlog0 hlogR 2
      _ = _ := by rw [mul_pow, ← Real.rpow_mul_natCast hD0.le]; congr 2; ring
  calc
    (routingLength r (c*D^γ) : ℝ) ≤ 108*(r/(c*D^γ))*(logb 2 r)^2 :=
      routing_length_upper r (c*D^γ) hr hden hhr
    _ ≤ 108*(D^(β-γ)/c)*(β^2*D^(δ/2)) := by gcongr
    _ = (108*β^2/c)*D^(β-γ+δ/2) := by rw [Real.rpow_add hD0]; ring
    _ ≤ D^(δ/2)*D^(β-γ+δ/2) :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hD0.le _)
    _ = D^(β-γ+δ) := by rw [← Real.rpow_add hD0]; congr 1; ring

theorem batch_routing_margin : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
    ∀ r : ℝ, D^(9/10:ℝ) ≤ r → r ≤ D^(51/50:ℝ) →
    2 ≤ r ∧ 64*((routingLength r (D^(9/10:ℝ)/4) : ℝ)^2*
      (D^(1/100:ℝ)+D^(3/10:ℝ))+2*D^(3/10:ℝ)) ≤ D^(9/10:ℝ)/4 := by
  have hev : ∀ᶠ D : ℝ in atTop, ∀ r : ℝ, D^(9/10:ℝ) ≤ r → r ≤ D^(51/50:ℝ) →
      2 ≤ r ∧ 64*((routingLength r (D^(9/10:ℝ)/4) : ℝ)^2*
        (D^(1/100:ℝ)+D^(3/10:ℝ))+2*D^(3/10:ℝ)) ≤ D^(9/10:ℝ)/4 := by
    filter_upwards [eventually_routing_length (1/4) (51/50) (9/10) (2/25)
      (by norm_num) (by norm_num) (by norm_num),
      eventually_const_mul_power_le 1024 (7/10) (9/10) (by norm_num),
      eventually_constant_le_power 2 (9/10) (by norm_num),
      eventually_gt_atTop (1:ℝ)] with D hlen hcost htwo hD r hr hrD
    have hD0 : 0 < D := by linarith
    have hr2 : 2 ≤ r := htwo.trans hr
    have hh : (1/4)*D^(9/10:ℝ) ≤ r := by
      have hh0 := Real.rpow_nonneg hD0.le (9/10:ℝ)
      linarith
    have hL := hlen r hr2 hrD hh
    norm_num at hL
    have hL' : (routingLength r (D^(9/10:ℝ)/4) : ℝ) ≤ D^(1/5:ℝ) := by
      convert hL using 1 ; ring_nf
    have hsmall : D^(1/100:ℝ) ≤ D^(3/10:ℝ) := Real.rpow_le_rpow_of_exponent_le hD.le (by norm_num)
    have h37 : D^(3/10:ℝ) ≤ D^(7/10:ℝ) := Real.rpow_le_rpow_of_exponent_le hD.le (by norm_num)
    have hprod : (routingLength r (D^(9/10:ℝ)/4) : ℝ)^2*
        (D^(1/100:ℝ)+D^(3/10:ℝ)) ≤ 2*D^(7/10:ℝ) := by
      calc
        _ ≤ (D^(1/5:ℝ))^2 * (2*D^(3/10:ℝ)) := by gcongr; linarith
        _ = _ := by
          rw [← Real.rpow_mul_natCast hD0.le]
          norm_num
          rw [mul_left_comm, ← Real.rpow_add hD0]
          norm_num
    refine ⟨hr2, ?_⟩
    nlinarith only [hprod, h37, hcost]
  obtain ⟨A,hA⟩ := eventually_atTop.mp hev
  refine ⟨max A 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro D hD
  exact hA D ((le_max_left _ _).trans hD)

lemma eventually_reservoir_capacity (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∀ᶠ D : ℝ in atTop, ∀ r : ℝ, 0 ≤ r → r ≤ D^(51/50:ℝ) →
      (⌈8*r/(p*(c*D^(9/10:ℝ)))⌉₊ : ℝ) ≤ D^(13/100:ℝ) := by
  filter_upwards [eventually_const_mul_power_le (8/(p*c)+1) (3/25) (13/100) (by norm_num),
    eventually_gt_atTop (1:ℝ)] with D hbound hD r hr hrD
  have hD0 : 0 < D := by linarith
  have hden : 0 < p*(c*D^(9/10:ℝ)) := by positivity
  have hone : 1 ≤ D^(3/25:ℝ) := Real.one_le_rpow hD.le (by norm_num)
  have hx : 8*r/(p*(c*D^(9/10:ℝ))) ≤ (8/(p*c))*D^(3/25:ℝ) := by
    calc
      _ ≤ 8*D^(51/50:ℝ)/(p*(c*D^(9/10:ℝ))) := by gcongr
      _ = _ := by
        have heq : D^(3/25:ℝ) = D^(51/50:ℝ)/D^(9/10:ℝ) := by
          rw [← Real.rpow_sub hD0]; norm_num
        rw [heq]; ring
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 8*r/(p*(c*D^(9/10:ℝ))) by positivity)
  nlinarith only [hx, hceil, hone, hbound]

theorem residue_routing_margin (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀, ∀ r rᵢ : ℝ,
      0 ≤ r → r ≤ D^(51/50:ℝ) → 2 ≤ rᵢ → rᵢ ≤ r → D^(37/50:ℝ) ≤ rᵢ →
      64*((routingLength rᵢ (D^(37/50:ℝ)) : ℝ)^2*
        ((⌈8*r/(p*(c*D^(9/10:ℝ)))⌉₊ : ℝ)+1)) ≤ D^(37/50:ℝ) := by
  have hev : ∀ᶠ D : ℝ in atTop, ∀ r rᵢ : ℝ,
      0 ≤ r → r ≤ D^(51/50:ℝ) → 2 ≤ rᵢ → rᵢ ≤ r → D^(37/50:ℝ) ≤ rᵢ →
      64*((routingLength rᵢ (D^(37/50:ℝ)) : ℝ)^2*
        ((⌈8*r/(p*(c*D^(9/10:ℝ)))⌉₊ : ℝ)+1)) ≤ D^(37/50:ℝ) := by
    filter_upwards [eventually_routing_length 1 (51/50) (37/50) (1/100)
      (by norm_num) (by norm_num) (by norm_num),
      eventually_reservoir_capacity c p hc hp,
      eventually_const_mul_power_le 128 (71/100) (37/50) (by norm_num),
      eventually_gt_atTop (1:ℝ)] with D hlen hcap hcost hD r rᵢ hr hrD hri2 hrir htau
    have hD0 : 0 < D := by linarith
    have hL := hlen rᵢ hri2 (hrir.trans hrD) (by simpa using htau)
    norm_num at hL
    have hk := hcap r hr hrD
    have hone : 1 ≤ D^(13/100:ℝ) := Real.one_le_rpow hD.le (by norm_num)
    have hprod : (routingLength rᵢ (D^(37/50:ℝ)) : ℝ)^2*
        ((⌈8*r/(p*(c*D^(9/10:ℝ)))⌉₊ : ℝ)+1) ≤ 2*D^(71/100:ℝ) := by
      calc
        _ ≤ (D^(29/100:ℝ))^2 * (2*D^(13/100:ℝ)) := by gcongr; linarith
        _ = _ := by
          rw [← Real.rpow_mul_natCast hD0.le]
          norm_num
          rw [mul_left_comm, ← Real.rpow_add hD0]
          norm_num
    nlinarith only [hprod, hcost]
  obtain ⟨A,hA⟩ := eventually_atTop.mp hev
  refine ⟨max A 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro D hD
  exact hA D ((le_max_left _ _).trans hD)

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V]

def CutExpansionOn (P : SimpleGraph V) [DecidableRel P.Adj] (W : Finset V) (h : ℝ) : Prop :=
  ∀ A : Finset V, A ⊆ W → h * min (A.card : ℝ) ((W \ A).card : ℝ) ≤
    ((P.interedges A (W \ A)).card : ℝ)

lemma subtype_image_compl {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (W : Finset V) (U : Finset (W : Set V)) :
    Uᶜ.image Subtype.val = W \ U.image Subtype.val := by
  ext v
  simp only [Finset.mem_image, Finset.mem_compl, Finset.mem_sdiff]
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨x.property,?_⟩
    rintro ⟨y,hy,he⟩
    exact hx (Subtype.ext he ▸ hy)
  · rintro ⟨hv,hvU⟩
    refine ⟨⟨v,hv⟩,?_,rfl⟩
    intro hx
    exact hvU ⟨⟨v,hv⟩,hx,rfl⟩

lemma induced_interedges_card (P : SimpleGraph V) [DecidableRel P.Adj]
    (W : Finset V) (U : Finset (W : Set V)) :
    (((P.induce (W : Set V)).interedges U Uᶜ).card : ℝ) =
      ((P.interedges (U.image Subtype.val) (W \ U.image Subtype.val)).card : ℝ) := by
  classical
  let f : ↥(W : Set V) × ↥(W : Set V) → V × V := fun e => (e.1.val,e.2.val)
  have hf : Function.Injective f := by
    intro a b h
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have heq : ((P.induce (W : Set V)).interedges U Uᶜ).image f =
      P.interedges (U.image Subtype.val) (W \ U.image Subtype.val) := by
    rw [← subtype_image_compl W U]
    ext e
    simp only [SimpleGraph.mem_interedges_iff, Finset.mem_image]
    constructor
    · rintro ⟨a,⟨ha,hb,hab⟩,rfl⟩
      exact ⟨⟨a.1,ha,rfl⟩,⟨a.2,hb,rfl⟩,hab⟩
    · rintro ⟨⟨x,hx,hxe⟩,⟨y,hy,hye⟩,he⟩
      refine ⟨(x,y),⟨hx,hy,?_⟩,Prod.ext hxe hye⟩
      change P.Adj x.val y.val
      simpa only [hxe,hye] using he
  rw [← heq, Finset.card_image_of_injective _ hf]

lemma cutExpansion_induce (P : SimpleGraph V) [DecidableRel P.Adj]
    (W : Finset V) (h : ℝ) (hexp : CutExpansionOn P W h) :
    CutExpansion (P.induce (W : Set V)) h := by
  classical
  intro U
  have hsub : U.image Subtype.val ⊆ W := by
    rintro v hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
    exact a.property
  have h := hexp (U.image Subtype.val) hsub
  have he : W \ U.image Subtype.val = Uᶜ.image Subtype.val :=
    (subtype_image_compl W U).symm
  rw [he] at h
  simp only [Finset.card_image_of_injective _ Subtype.val_injective] at h
  rw [induced_interedges_card,he]
  exact h

theorem routing_allow_equal {I : Type} [Fintype I]
    (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (x y : I → V) (k : ℝ) (hk : 1 ≤ k)
    (hload : ∀ v, (endpointLoad Finset.univ x y v : ℝ) ≤ k)
    (hbudget : 64 * ((routingLength (Fintype.card V) h : ℝ)^2 * (k+1)) ≤ h) :
    ∃ q : ∀ i, P.Walk (x i) (y i),
      (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength (Fintype.card V) h) ∧
      (∀ i j, i ≠ j → Disjoint (q i).edges.toFinset (q j).edges.toFinset) := by
  classical
  let J := {i : I // x i ≠ y i}
  have hjload (v : V) :
      (endpointLoad Finset.univ (fun i : J => x i.val) (fun i : J => y i.val) v : ℝ) ≤ k := by
    apply le_trans _ (hload v)
    exact_mod_cast (show endpointLoad Finset.univ (fun i : J => x i.val)
        (fun i : J => y i.val) v ≤ endpointLoad Finset.univ x y v from by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro a ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha).2⟩
      · intro a _ b _ hab
        exact Subtype.ext hab)
  obtain ⟨q,hq,hd,_⟩ := routing P h hh hexp hr
    (fun i : J => x i.val) (fun i : J => y i.val) (fun i => i.property)
    (fun i : J => i) (fun _ => ∅) k 1 0 hk (by norm_num) (by norm_num) hjload
    (by
      intro i
      have he : (univ.filter (fun j : J => j = i)) = {i} := by ext j; simp
      rw [he]; simp) (by intro i; simp) (by simpa only [add_zero] using hbudget)
  let Q : ∀ i, P.Walk (x i) (y i) := fun i =>
    if hi : x i = y i then (SimpleGraph.Walk.nil : P.Walk (x i) (x i)).copy rfl hi
    else q ⟨i,hi⟩
  refine ⟨Q,?_,?_⟩
  · intro i
    by_cases hi : x i = y i
    · simp [Q,hi]
    · simpa only [Q,dite_eq_right hi] using ⟨(hq ⟨i,hi⟩).1,(hq ⟨i,hi⟩).2.1⟩
  · intro i j hij
    by_cases hi : x i = y i
    · simp [Q,hi]
    by_cases hj : x j = y j
    · simp [Q,hj]
    simp only [Q,dite_eq_right hi,dite_eq_right hj]
    exact hd ⟨i,hi⟩ ⟨j,hj⟩ (fun he => hij (congrArg Subtype.val he))

theorem routing_in_reservoir {I : Type} [Fintype I]
    (G P : SimpleGraph V) [DecidableRel P.Adj] (hPG : P ≤ G)
    (W : Finset V) (h : ℝ) (hh : 0 < h)
    (hexp : CutExpansionOn P W h) (hr : 2 ≤ W.card)
    (x y : I → V) (hx : ∀ i, x i ∈ W) (hy : ∀ i, y i ∈ W)
    (k : ℝ) (hk : 1 ≤ k)
    (hload : ∀ v, (endpointLoad Finset.univ x y v : ℝ) ≤ k)
    (hbudget : 64 * ((routingLength W.card h : ℝ)^2 * (k+1)) ≤ h) :
    ∃ q : ∀ i, G.Walk (x i) (y i),
      (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength W.card h ∧
        ∀ v ∈ (q i).support, v ∈ W) ∧
      Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) := by
  classical
  let X : I → (W : Set V) := fun i => ⟨x i,hx i⟩
  let Y : I → (W : Set V) := fun i => ⟨y i,hy i⟩
  have hl (v : (W : Set V)) : (endpointLoad univ X Y v : ℝ) ≤ k := by
    simpa only [endpointLoad,X,Y,Subtype.ext_iff] using hload v.val
  obtain ⟨q,hq,hd⟩ := routing_allow_equal (P.induce (W : Set V)) h hh
    (cutExpansion_induce P W h hexp) (by simpa using hr) X Y k hk hl
    (by simpa using hbudget)
  let f : (P.induce (W : Set V)) →g G :=
    { toFun := Subtype.val, map_rel' := fun ha => hPG ha }
  have hf : Function.Injective f := Subtype.val_injective
  have hcard : Fintype.card ↥(W : Set V) = W.card := Fintype.card_coe W
  let Q : ∀ i, G.Walk (x i) (y i) := fun i => (q i).map f
  refine ⟨Q,?_,?_⟩
  · intro i
    refine ⟨(hq i).1.map hf,?_,?_⟩
    · simpa only [Q,SimpleGraph.Walk.length_map, hcard] using (hq i).2
    · intro v hv
      have hv' : v ∈ (q i).support.map f := by simpa only [Q,SimpleGraph.Walk.support_map] using hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv'
      exact a.property
  · intro i j hij
    change Disjoint ((q i).map f).edgeSet ((q j).map f).edgeSet
    rw [SimpleGraph.Walk.edgeSet_map,SimpleGraph.Walk.edgeSet_map]
    rw [Set.disjoint_image_iff (Sym2.map.injective hf)]
    apply Set.disjoint_left.mpr
    intro e he he'
    exact Finset.disjoint_left.mp (hd i j hij)
      (by simpa using he) (by simpa using he')

theorem uniform_reservoir_routing (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (G P : SimpleGraph V) [DecidableRel P.Adj], P ≤ G →
      ∀ W : Finset V, CutExpansionOn P W (D^(37/50:ℝ)) → 2 ≤ W.card →
      (Fintype.card V : ℝ) ≤ D^(51/50:ℝ) →
      ∀ (I : Type) [Fintype I] (x y : I → V),
      (∀ i, x i ∈ W) → (∀ i, y i ∈ W) →
      (∀ v, endpointLoad univ x y v ≤
        ⌈8*(Fintype.card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊) →
      ∃ q : ∀ i, G.Walk (x i) (y i),
        (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength W.card (D^(37/50:ℝ)) ∧
          ∀ v ∈ (q i).support, v ∈ W) ∧
        Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) := by
  obtain ⟨D₀,hD₀,hmargin⟩ := residue_routing_margin c p hc hp
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V _ _ G P _ hPG W hexp hW hr I _ x y hx hy hl
  have hDpos : 0 < D := lt_trans (by norm_num) (hD₀.trans_le hD)
  have horder : (D^(37/50:ℝ)) ≤ (W.card : ℝ) := by
    simpa using (cutExpansion_induce P W _ hexp).le_order (P.induce (W:Set V)) _
      (by simpa using hW)
  have hWupper : (W.card : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast W.card_le_univ
  have hrpos : 0 < (Fintype.card V : ℝ) := by
    have hWreal : (2:ℝ) ≤ W.card := by exact_mod_cast hW
    linarith
  have hk : 1 ≤ (⌈8*(Fintype.card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊ : ℝ) := by
    have hceil : 0 < ⌈8*(Fintype.card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊ :=
      Nat.ceil_pos.mpr (by positivity)
    exact_mod_cast hceil
  apply routing_in_reservoir G P hPG W (D^(37/50:ℝ)) (by positivity) hexp hW
    x y hx hy _ hk (by intro v; exact_mod_cast hl v)
  exact hmargin D hD _ _ hrpos.le hr (by exact_mod_cast hW) hWupper horder

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable

theorem occurrence_slots {A : Type cycleUniverse1} {V : Type cycleUniverse2} [Fintype A] (f : A → V) (k : ℕ)
    (h : ∀ v, Fintype.card {a // f a = v} ≤ k) :
    ∃ slot : A → Fin k, Function.Injective (fun a => (f a, slot a)) := by
  classical
  have he : ∀ v, Nonempty ({a // f a = v} ↪ Fin k) := by
    intro v
    exact Function.Embedding.nonempty_of_card_le (by simpa using h v)
  let e := fun v => Classical.choice (he v)
  refine ⟨fun a => e (f a) ⟨a,rfl⟩, ?_⟩
  intro a b hab
  have hf : f a = f b := congrArg Prod.fst hab
  have hs : e (f a) ⟨a,rfl⟩ = e (f b) ⟨b,rfl⟩ := congrArg Prod.snd hab
  have hσ : (⟨f a, e (f a) ⟨a,rfl⟩⟩ : Σ _ : V, Fin k) =
      ⟨f b, e (f b) ⟨b,rfl⟩⟩ := Sigma.ext hf (heq_of_eq hs)
  let E : (Σ v, {a // f a = v}) ↪ (Σ _ : V, Fin k) :=
    Function.Embedding.sigmaMap (Function.Embedding.refl V) e
  have heq : (⟨f a, ⟨a,rfl⟩⟩ : Σ v, {a // f a = v}) = ⟨f b, ⟨b,rfl⟩⟩ :=
    E.injective hσ
  exact congrArg (fun z : Σ v, {a // f a = v} => z.2.val) heq

def endpointOccurrence {I : Type cycleUniverse3} {V : Type cycleUniverse4} (x y : I → V) (a : I × Fin 2) : V :=
  if a.2 = 0 then x a.1 else y a.1

theorem endpoint_occurrence_slots {I : Type cycleUniverse5} {V : Type cycleUniverse6} [Fintype I]
    (x y : I → V) (hne : ∀ i, x i ≠ y i)
    (hload : ∀ v, (univ.filter (fun i => x i = v ∨ y i = v)).card ≤ 2) :
    ∃ slot : I × Fin 2 → Fin 2,
      Function.Injective (fun a => (endpointOccurrence x y a, slot a)) := by
  classical
  apply occurrence_slots
  intro v
  let f : {a : I × Fin 2 // endpointOccurrence x y a = v} →
      {i : I // x i = v ∨ y i = v} := fun a =>
    ⟨a.val.1, by
      by_cases h0 : a.val.2 = 0
      · exact Or.inl (by simpa [endpointOccurrence,h0] using a.property)
      · exact Or.inr (by simpa [endpointOccurrence,h0] using a.property)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have hi : a.val.1 = b.val.1 := congrArg Subtype.val hab
    apply Prod.ext hi
    by_contra ht
    have hcases : (a.val.2 = 0 ∧ b.val.2 ≠ 0) ∨ (a.val.2 ≠ 0 ∧ b.val.2 = 0) := by
      have ha := (a.val.2).isLt
      have hb := (b.val.2).isLt
      have hne : (a.val.2).val ≠ (b.val.2).val := fun h => ht (Fin.ext h)
      simp only [Fin.ext_iff, Fin.val_zero]
      omega
    rcases hcases with h | h
    · have ha : x a.val.1 = v := by simpa [endpointOccurrence,h.1] using a.property
      have hb : y b.val.1 = v := by simpa [endpointOccurrence,h.2] using b.property
      exact hne _ (ha.trans (hi ▸ hb).symm)
    · have ha : y a.val.1 = v := by simpa [endpointOccurrence,h.1] using a.property
      have hb : x b.val.1 = v := by simpa [endpointOccurrence,h.2] using b.property
      exact hne _ ((hi ▸ hb).trans ha.symm)
  exact (Fintype.card_le_of_injective f hf).trans (by simpa only [Fintype.card_subtype] using hload v)

theorem reserved_edges_injective {A : Type cycleUniverse7} {V : Type cycleUniverse8} (S W : Set V)
    (f : A → V) (slot : A → Fin 2) (r : V × Fin 2 → V)
    (hslots : Function.Injective (fun a => (f a,slot a)))
    (hout : ∀ a, f a ∈ S) (hin : ∀ v ∈ S, ∀ t, r (v,t) ∈ W)
    (hdisj : Disjoint S W) (hr : ∀ v ∈ S, r (v,0) ≠ r (v,1)) :
    Function.Injective (fun a => s(f a,r (f a,slot a))) := by
  intro a b hab
  rcases Sym2.eq_iff.mp hab with he | he
  · have hf : f a = f b := he.1
    have hh : r (f a,slot a) = r (f b,slot b) := he.2
    apply hslots
    apply Prod.ext hf
    have hrinj : Function.Injective (fun t : Fin 2 => r (f a,t)) := by
      intro i j hij
      have h0 := hr (f a) (hout a)
      fin_cases i <;> fin_cases j
      · rfl
      · exact (h0 hij).elim
      · exact (h0 hij.symm).elim
      · rfl
    exact hrinj (by simpa only [hf] using hh)
  · have hf : f a = r (f b,slot b) := he.1
    exact False.elim (Set.disjoint_left.mp hdisj (hout a)
      (hf.symm ▸ hin (f b) (hout b) (slot b)))

theorem assigned_representative_load {A : Type cycleUniverse9} {V : Type cycleUniverse10} [Fintype A] [DecidableEq V]
    (S : Finset V) (f : A → V) (slot : A → Fin 2) (r : V × Fin 2 → V)
    (hslots : Function.Injective (fun a => (f a,slot a)))
    (hout : ∀ a, f a ∈ S) (k : ℕ)
    (hcap : ∀ v, ((S ×ˢ univ).filter (fun a => r a = v)).card ≤ k) :
    ∀ v, (univ.filter (fun a => r (f a,slot a) = v)).card ≤ k := by
  classical
  intro v
  apply le_trans (Finset.card_le_card_of_injOn (fun a => (f a,slot a)) ?_ ?_) (hcap v)
  · intro a ha
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hout a,mem_univ _⟩, (mem_filter.mp ha).2⟩
  · intro a _ b _ hab
    exact hslots hab

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable

theorem choose_reservoir_endpoints {V I : Type} [Fintype V] [Fintype I]
    [DecidableEq V] (P : SimpleGraph V) (W : Finset V)
    (x y : I → V) (hne : ∀ i, x i ≠ y i)
    (houtx : ∀ i, x i ∉ W) (houty : ∀ i, y i ∉ W)
    (hload : ∀ v, endpointLoad univ x y v ≤ 2)
    (r : V × Fin 2 → V)
    (hr : ∀ v, v ∉ W → ∀ t, r (v,t) ∈ W ∧ P.Adj v (r (v,t)))
    (hrne : ∀ v, v ∉ W → r (v,0) ≠ r (v,1))
    (k : ℕ) (hcap : ∀ v, ((Wᶜ ×ˢ univ).filter (fun z => r z = v)).card ≤ k) :
    ∃ a b : I → V,
      (∀ i, a i ∈ W ∧ P.Adj (x i) (a i)) ∧
      (∀ i, b i ∈ W ∧ P.Adj (y i) (b i)) ∧
      Function.Injective (fun z : I × Fin 2 =>
        if z.2 = 0 then s(x z.1,a z.1) else s(y z.1,b z.1)) ∧
      (∀ v, endpointLoad univ a b v ≤ k) ∧
      (∀ i, ∃ t, a i = r (x i,t)) ∧ (∀ i, ∃ t, b i = r (y i,t)) := by
  classical
  obtain ⟨slot,hslot⟩ := endpoint_occurrence_slots x y hne (fun v => by
    convert hload v using 1
    congr 1
    ext i
    simp only [ Finset.mem_filter, Finset.mem_univ, true_and])
  let occ := endpointOccurrence x y
  have ho : ∀ z : I × Fin 2, occ z ∉ W := by
    rintro ⟨i,t⟩
    by_cases h : t = 0
    · simpa [occ,endpointOccurrence,h] using houtx i
    · simpa [occ,endpointOccurrence,h] using houty i
  let a := fun i => r (x i,slot (i,0))
  let b := fun i => r (y i,slot (i,1))
  have hsp := reserved_edges_injective (Wᶜ : Finset V) W occ slot r hslot
    (fun z => Finset.mem_compl.mpr (ho z))
    (fun v hv t => (hr v (Finset.mem_compl.mp hv) t).1)
    (Set.disjoint_left.mpr (fun _ hv hw => (Finset.mem_compl.mp hv) hw))
    (fun v hv => hrne v (Finset.mem_compl.mp hv))
  have hcap' := assigned_representative_load Wᶜ occ slot r hslot
    (fun z => Finset.mem_compl.mpr (ho z)) k hcap
  refine ⟨a,b,(fun i => hr _ (houtx i) _),(fun i => hr _ (houty i) _),?_,?_,?_,?_⟩
  · have heq : (fun z : I × Fin 2 =>
        if z.2 = 0 then s(x z.1,a z.1) else s(y z.1,b z.1)) =
        (fun z => s(occ z,r (occ z,slot z))) := by
      funext z
      rcases z with ⟨i,t⟩
      fin_cases t <;> simp [occ,endpointOccurrence,a,b]
    rw [heq]
    exact hsp
  · intro v
    apply le_trans (Finset.card_le_card_of_injOn
      (fun i => (i,if a i = v then (0 : Fin 2) else 1)) ?_ ?_) (hcap' v)
    · intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      by_cases hi0 : a i = v
      · simp [hi0,occ,endpointOccurrence,a]
      · have hi1 : b i = v := hi'.resolve_left hi0
        simpa [hi0,occ,endpointOccurrence,b] using hi1
    · intro i hi j hj he
      exact congrArg Prod.fst he
  · intro i; exact ⟨slot (i,0),rfl⟩
  · intro i; exact ⟨slot (i,1),rfl⟩

theorem uniform_assigned_reservoir_routing (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (G P : SimpleGraph V) [DecidableRel P.Adj], P ≤ G →
      ∀ W : Finset V, CutExpansionOn P W (D^(37/50:ℝ)) → 2 ≤ W.card →
      (Fintype.card V : ℝ) ≤ D^(51/50:ℝ) →
      ∀ (I : Type) [Fintype I] (x y : I → V),
      (∀ i, x i ≠ y i) → (∀ i, x i ∉ W) → (∀ i, y i ∉ W) →
      (∀ v, endpointLoad univ x y v ≤ 2) →
      ∀ r : V × Fin 2 → V,
      (∀ v, v ∉ W → ∀ t, r (v,t) ∈ W ∧ P.Adj v (r (v,t))) →
      (∀ v, v ∉ W → r (v,0) ≠ r (v,1)) →
      (∀ v, ((Wᶜ ×ˢ univ).filter (fun z => r z = v)).card ≤
        ⌈8*(Fintype.card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊) →
      ∃ (a b : I → V) (q : ∀ i, G.Walk (a i) (b i)),
        (∀ i, G.Adj (x i) (a i) ∧ G.Adj (y i) (b i)) ∧
        Function.Injective (fun z : I × Fin 2 =>
          if z.2 = 0 then s(x z.1,a z.1) else s(y z.1,b z.1)) ∧
        (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength W.card (D^(37/50:ℝ)) ∧
          ∀ v ∈ (q i).support, v ∈ W) ∧
        Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) ∧
        (∀ i, ∃ t, a i = r (x i,t)) ∧ (∀ i, ∃ t, b i = r (y i,t)) ∧
        (∀ i, (q i).edgeSet ⊆ P.edgeSet) := by
  obtain ⟨D₀,hD₀,hroute⟩ := uniform_reservoir_routing c p hc hp
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V _ _ G P _ hPG W hexp hW hr I _ x y hne hx hy hl r hrep hrepne hcap
  obtain ⟨a,b,ha,hb,hs,hl',ha',hb'⟩ :=
    choose_reservoir_endpoints P W x y hne hx hy hl r hrep hrepne _ hcap
  obtain ⟨q,hq,hd⟩ := hroute D hD V P P le_rfl W hexp hW hr I a b
    (fun i => (ha i).1) (fun i => (hb i).1) hl'
  let Q : ∀ i, G.Walk (a i) (b i) := fun i => (q i).mapLe hPG
  refine ⟨a,b,Q,(fun i => ⟨hPG (ha i).2,hPG (hb i).2⟩),hs,?_,?_,ha',hb',?_⟩
  · intro i
    refine ⟨(hq i).1.mapLe hPG,?_,?_⟩
    · simpa only [Q, SimpleGraph.Walk.length_mapLe] using (hq i).2.1
    · simpa only [Q, SimpleGraph.Walk.support_mapLe_eq_support] using (hq i).2.2
  · intro i j hij
    simpa only [Q, SimpleGraph.Walk.edgeSet_mapLe_eq_edgeSet] using hd hij
  · intro i
    rw [show (Q i).edgeSet = (q i).edgeSet from (q i).edgeSet_mapLe_eq_edgeSet hPG]
    intro e he
    exact (q i).edges_subset_edgeSet he

end
end ErdosGallai

namespace ErdosGallai
open SimpleGraph

variable {V : Type cycleUniverse11} {G : SimpleGraph V} {x y a b : V}

def reservoirReturn (P : G.Walk a b) (hx : G.Adj x a) (hy : G.Adj y b) :
    G.Walk y x := .cons hy (P.reverse.concat hx.symm)

lemma reservoirReturn_isPath (Q : G.Walk x y) (P : G.Walk a b)
    (hQ : Q.IsPath) (hQpos : 0 < Q.length) (hP : P.IsPath)
    (hdisj : Q.support.Disjoint P.support) (hx : G.Adj x a) (hy : G.Adj y b) :
    (reservoirReturn P hx hy).IsPath := by
  have hxy : x ≠ y := by
    intro h
    subst y
    have := hQ.nil_iff_eq.mpr rfl
    have hz : Q.length = 0 := this.length_eq_zero
    omega
  have hxP : x ∉ P.reverse.support := by
    simpa using hdisj Q.start_mem_support
  have hyP : y ∉ P.reverse.support := by
    simpa using hdisj Q.end_mem_support
  exact (hP.reverse.concat hxP hx.symm).cons (by simpa using And.intro hyP hxy.symm)

theorem reservoir_path_closure (Q : G.Walk x y) (P : G.Walk a b)
    (hQ : Q.IsPath) (hQpos : 0 < Q.length) (hP : P.IsPath)
    (hdisj : Q.support.Disjoint P.support) (hx : G.Adj x a) (hy : G.Adj y b) :
    (Q.append (reservoirReturn P hx hy)).IsCycle ∧
    (Q.append (reservoirReturn P hx hy)).edgeSet =
      Q.edgeSet ∪ P.edgeSet ∪ {s(x,a), s(y,b)} ∧
    3 ≤ (Q.append (reservoirReturn P hx hy)).length := by
  have hreturn := reservoirReturn_isPath Q P hQ hQpos hP hdisj hx hy
  have htail : Q.support.tail.Disjoint (reservoirReturn P hx hy).support.tail := by
    rw [List.disjoint_left]
    intro v hv
    have hvQ := List.mem_of_mem_tail hv
    have hvP : v ∉ P.support := hdisj hvQ
    have hvx : v ≠ x := by
      have hn := hQ.support_nodup
      rw [← Q.cons_tail_support, List.nodup_cons] at hn
      exact fun heq => hn.1 (heq ▸ hv)
    simpa [reservoirReturn] using And.intro hvP hvx
  have hcycle := hQ.isCycle_append hreturn htail (Or.inr (by simp [reservoirReturn]))
  refine ⟨hcycle, ?_, ?_⟩
  · ext e
    simp only [Walk.edgeSet_append, reservoirReturn, Walk.edgeSet_cons,
      Walk.edgeSet_concat, Walk.edgeSet_reverse, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    rw [Sym2.eq_swap (a := x) (b := a)]
    tauto
  · simpa [reservoirReturn] using (by omega : 3 ≤ Q.length + (P.length + 1 + 1))

end ErdosGallai

namespace ErdosGallai
noncomputable section
open SimpleGraph
attribute [local instance] Classical.propDecidable

lemma spoke_sets_pairwise {I : Type cycleUniverse12} {E : Type cycleUniverse13} (e : I × Fin 2 → E)
    (he : Function.Injective e) :
    Pairwise (fun i j => Disjoint ({e (i,0), e (i,1)} : Set E) {e (j,0), e (j,1)}) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro a hai haj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hai haj
  rcases hai with hai | hai <;> rcases haj with haj | haj
  all_goals exact hij (congrArg Prod.fst (he (hai.symm.trans haj)))

lemma pairwise_union_three {I : Type cycleUniverse14} {E : Type cycleUniverse15} (A B S : I → Set E)
    (hA : Pairwise fun i j => Disjoint (A i) (A j))
    (hB : Pairwise fun i j => Disjoint (B i) (B j))
    (hS : Pairwise fun i j => Disjoint (S i) (S j))
    (hAB : ∀ i j, Disjoint (A i) (B j))
    (hAS : ∀ i j, Disjoint (A i) (S j))
    (hBS : ∀ i j, Disjoint (B i) (S j)) :
    Pairwise (fun i j => Disjoint (A i ∪ B i ∪ S i) (A j ∪ B j ∪ S j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro e ((ha | hb) | hs) ((ha' | hb') | hs')
  all_goals first
    | exact Set.disjoint_left.mp (hA hij) ha ha'
    | exact Set.disjoint_left.mp (hB hij) hb hb'
    | exact Set.disjoint_left.mp (hS hij) hs hs'
    | exact Set.disjoint_left.mp (hAB i j) ha hb'
    | exact Set.disjoint_left.mp (hAS i j) ha hs'
    | exact Set.disjoint_left.mp (hBS i j) hb hs'
    | exact Set.disjoint_left.mp (hAB j i) ha' hb
    | exact Set.disjoint_left.mp (hAS j i) ha' hs
    | exact Set.disjoint_left.mp (hBS j i) hb' hs

theorem reservoir_cycle_family {V : Type cycleUniverse16} {I : Type cycleUniverse17} {G : SimpleGraph V}
    {x y a b : I → V} (Q : ∀ i, G.Walk (x i) (y i))
    (P : ∀ i, G.Walk (a i) (b i))
    (hx : ∀ i, G.Adj (x i) (a i)) (hy : ∀ i, G.Adj (y i) (b i))
    (hQ : ∀ i, (Q i).IsPath) (hQpos : ∀ i, 0 < (Q i).length)
    (hP : ∀ i, (P i).IsPath)
    (hsep : ∀ i, (Q i).support.Disjoint (P i).support)
    (hQQ : Pairwise fun i j => Disjoint (Q i).edgeSet (Q j).edgeSet)
    (hPP : Pairwise fun i j => Disjoint (P i).edgeSet (P j).edgeSet)
    (hspoke : Function.Injective (fun z : I × Fin 2 =>
      if z.2 = 0 then s(x z.1,a z.1) else s(y z.1,b z.1)))
    (hQP : ∀ i j, Disjoint (Q i).edgeSet (P j).edgeSet)
    (hQS : ∀ i j, Disjoint (Q i).edgeSet {s(x j,a j),s(y j,b j)})
    (hPS : ∀ i j, Disjoint (P i).edgeSet {s(x j,a j),s(y j,b j)}) :
    let C := fun i => (Q i).append (reservoirReturn (P i) (hx i) (hy i))
    (∀ i, (C i).IsCycle) ∧
    Pairwise (fun i j => Disjoint (C i).edgeSet (C j).edgeSet) ∧
    (⋃ i, (C i).edgeSet) =
      (⋃ i, (Q i).edgeSet) ∪ (⋃ i, (P i).edgeSet) ∪
        (⋃ i, ({s(x i,a i),s(y i,b i)} : Set (Sym2 V))) := by
  dsimp only
  have hC := fun i => reservoir_path_closure (Q i) (P i) (hQ i) (hQpos i)
    (hP i) (hsep i) (hx i) (hy i)
  refine ⟨fun i => (hC i).1, ?_, ?_⟩
  · have hSS : Pairwise (fun i j => Disjoint
        ({s(x i,a i),s(y i,b i)} : Set (Sym2 V)) {s(x j,a j),s(y j,b j)}) := by
      simpa using spoke_sets_pairwise _ hspoke
    simpa only [fun i => (hC i).2.1] using
      pairwise_union_three (fun i => (Q i).edgeSet) (fun i => (P i).edgeSet)
        (fun i => ({s(x i,a i),s(y i,b i)} : Set (Sym2 V)))
        hQQ hPP hSS hQP hQS hPS
  · simp only [fun i => (hC i).2.1, Set.iUnion_union_distrib]

lemma reservoir_edge_ledger {E : Type cycleUniverse18} {I : Type cycleUniverse19} (G O R : Set E)
    (A B S C : I → Set E)
    (hcover : (⋃ i, A i) ∪ O ∪ R = G)
    (hAO : Disjoint (⋃ i, A i) O) (hAR : Disjoint (⋃ i, A i) R)
    (hOR : Disjoint O R)
    (hB : (⋃ i, B i) ⊆ R) (hS : (⋃ i, S i) ⊆ O)
    (hC : (⋃ i, C i) = (⋃ i, A i) ∪ (⋃ i, B i) ∪ (⋃ i, S i)) :
    let unusedSpokes := O \ (⋃ i, S i)
    let remaining := R \ (⋃ i, B i)
    Disjoint (⋃ i, C i) unusedSpokes ∧
    Disjoint (⋃ i, C i) remaining ∧
    Disjoint unusedSpokes remaining ∧
    (⋃ i, C i) ∪ unusedSpokes ∪ remaining = G := by
  dsimp only
  rw [hC]
  have hBO := hOR.symm.mono_left hB
  have hSR := hOR.mono_left hS
  refine ⟨?_,?_,hOR.mono Set.sdiff_subset Set.sdiff_subset,?_⟩
  · apply Set.disjoint_left.mpr
    rintro e ((he | he) | he) ⟨ho,hs⟩
    · exact Set.disjoint_left.mp hAO he ho
    · exact Set.disjoint_left.mp hBO he ho
    · exact hs he
  · apply Set.disjoint_left.mpr
    rintro e ((he | he) | he) ⟨hr,hb⟩
    · exact Set.disjoint_left.mp hAR he hr
    · exact hb he
    · exact Set.disjoint_left.mp hSR he hr
  · rw [← hcover]
    ext e
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · rintro ((((ha | hb) | hs) | ho) | hr)
      · exact Or.inl (Or.inl ha)
      · exact Or.inr (hB hb)
      · exact Or.inl (Or.inr (hS hs))
      · exact Or.inl (Or.inr ho.1)
      · exact Or.inr hr.1
    · rintro ((ha | ho) | hr)
      · exact Or.inl (Or.inl (Or.inl (Or.inl ha)))
      · by_cases hs : e ∈ ⋃ i, S i
        · exact Or.inl (Or.inl (Or.inr hs))
        · exact Or.inl (Or.inr ⟨ho,hs⟩)
      · by_cases hb : e ∈ ⋃ i, B i
        · exact Or.inl (Or.inl (Or.inl (Or.inr hb)))
        · exact Or.inr ⟨hr,hb⟩

end
end ErdosGallai

end
end
end

end OAI
