import OAI.Combinatorics.CycleDecomposition.BatchRouting

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch
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
end ErdosGallai.Batch

namespace ErdosGallai.Batch
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

lemma pathInterior_map {A B : Type} [DecidableEq A] [DecidableEq B]
    {H : SimpleGraph A} {J : SimpleGraph B} (f : H →g J)
    (hf : Function.Injective f) {a b : A} (p : H.Walk a b) :
    pathInterior (p.map f) = (pathInterior p).image f := by
  classical
  simp only [pathInterior, SimpleGraph.Walk.support_map]
  rw [Finset.image_sdiff _ _ hf]
  have hm : (p.support.map f).toFinset = p.support.toFinset.image f := by
    ext v; simp
  rw [hm]
  simp

theorem team_routing_on_set {I T : Type} [Fintype I]
    (G P : SimpleGraph V) [DecidableRel P.Adj] (hPG : P ≤ G)
    (W : Finset V) (h : ℝ) (hh : 0 < h)
    (hexp : CutExpansionOn P W h) (hr : 2 ≤ W.card)
    (x y : I → V) (hx : ∀ i, x i ∈ W) (hy : ∀ i, y i ∈ W)
    (hxy : ∀ i, x i ≠ y i) (team : I → T) (Z : I → Finset V)
    (k b z : ℝ) (hk : 1 ≤ k) (hb : 1 ≤ b) (hz : 0 ≤ z)
    (hload : ∀ v, (endpointLoad univ x y v : ℝ) ≤ k)
    (hteam : ∀ i, ((univ.filter (fun j => team j = team i)).card : ℝ) ≤ b)
    (hZ : ∀ i, ((Z i).card : ℝ) ≤ z)
    (hbudget : 64 * ((routingLength W.card h : ℝ)^2 * (k+b) + z) ≤ h) :
    ∃ q : ∀ i, G.Walk (x i) (y i),
      (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength W.card h ∧
        (∀ v ∈ (q i).support, v ∈ W) ∧ (q i).edgeSet ⊆ P.edgeSet ∧
        Disjoint (pathInterior (q i)) (Z i)) ∧
      Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) ∧
      (∀ i j, i ≠ j → team i = team j →
        Disjoint (pathInterior (q i)) (pathInterior (q j))) := by
  classical
  let X : I → (W : Set V) := fun i => ⟨x i,hx i⟩
  let Y : I → (W : Set V) := fun i => ⟨y i,hy i⟩
  let Z' : I → Finset (W : Set V) := fun i => univ.filter (fun v => v.val ∈ Z i)
  have hl (v : (W : Set V)) : (endpointLoad univ X Y v : ℝ) ≤ k := by
    simpa only [endpointLoad,X,Y,Subtype.ext_iff] using hload v.val
  have hz' : ∀ i, ((Z' i).card : ℝ) ≤ z := by
    intro i
    apply le_trans _ (hZ i)
    have hc : (Z' i).card ≤ (Z i).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro v hv; exact (Finset.mem_filter.mp hv).2
      · exact Subtype.val_injective.injOn
    exact_mod_cast hc
  obtain ⟨q,hq,hd,ht⟩ := routing (P.induce (W : Set V)) h hh
    (cutExpansion_induce P W h hexp) (by simpa using hr) X Y
    (fun i he => hxy i (congrArg Subtype.val he)) team Z' k b z hk hb hz hl hteam hz'
    (by simpa using hbudget)
  let f : (P.induce (W : Set V)) →g G :=
    { toFun := Subtype.val, map_rel' := fun ha => hPG ha }
  have hf : Function.Injective f := Subtype.val_injective
  have hcard : Fintype.card ↥(W : Set V) = W.card := Fintype.card_coe W
  let Q : ∀ i, G.Walk (x i) (y i) := fun i => (q i).map f
  refine ⟨Q,?_,?_,?_⟩
  · intro i
    refine ⟨(hq i).1.map hf,?_,?_,?_,?_⟩
    · simpa only [Q,SimpleGraph.Walk.length_map,hcard] using (hq i).2.1
    · intro v hv
      have hv' : v ∈ (q i).support.map f := by simpa only [Q,SimpleGraph.Walk.support_map] using hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv'
      exact a.property
    · intro e he
      rw [SimpleGraph.Walk.edgeSet_map] at he
      obtain ⟨d,hd,rfl⟩ := he
      induction d using Sym2.ind with
      | _ a b => exact (q i).adj_of_mem_edges hd
    · rw [show Q i = (q i).map f from rfl, pathInterior_map f hf]
      apply Finset.disjoint_left.mpr
      intro v hv hzv
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
      exact Finset.disjoint_left.mp (hq i).2.2 ha (by simpa [Z',f] using hzv)
  · intro i j hij
    change Disjoint ((q i).map f).edgeSet ((q j).map f).edgeSet
    rw [SimpleGraph.Walk.edgeSet_map,SimpleGraph.Walk.edgeSet_map,
      Set.disjoint_image_iff (Sym2.map.injective hf)]
    apply Set.disjoint_left.mpr
    intro e he he'
    exact Finset.disjoint_left.mp (hd i j hij) (by simpa using he) (by simpa using he')
  · intro i j hij hteam'
    change Disjoint (pathInterior ((q i).map f)) (pathInterior ((q j).map f))
    rw [pathInterior_map f hf,pathInterior_map f hf,Finset.disjoint_image hf]
    exact ht i j hij hteam'

theorem uniform_batch_routing :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (A : Type) [Fintype A] [DecidableEq A],
      ∀ (G P : SimpleGraph A) [DecidableRel P.Adj], P ≤ G →
      ∀ W : Finset A, CutExpansionOn P W (D^(9/10:ℝ)/4) →
      D^(9/10:ℝ) ≤ (W.card : ℝ) → (W.card : ℝ) ≤ D^(51/50:ℝ) →
      ∀ (I T : Type) [Fintype I] (x y : I → A),
      (∀ i, x i ∈ W) → (∀ i, y i ∈ W) → (∀ i, x i ≠ y i) →
      ∀ (team : I → T) (Z : I → Finset A),
      (∀ v, (endpointLoad univ x y v : ℝ) ≤ D^(1/100:ℝ)) →
      (∀ i, ((univ.filter (fun j => team j = team i)).card : ℝ) ≤ D^(3/10:ℝ)) →
      (∀ i, ((Z i).card : ℝ) ≤ 2*D^(3/10:ℝ)) →
      ∃ q : ∀ i, G.Walk (x i) (y i),
        (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength W.card (D^(9/10:ℝ)/4) ∧
          (∀ v ∈ (q i).support, v ∈ W) ∧ (q i).edgeSet ⊆ P.edgeSet ∧
          Disjoint (pathInterior (q i)) (Z i)) ∧
        Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) ∧
        (∀ i j, i ≠ j → team i = team j →
          Disjoint (pathInterior (q i)) (pathInterior (q j))) := by
  obtain ⟨D₀,hD₀,hm⟩ := batch_routing_margin
  refine ⟨D₀,hD₀,?_⟩
  intro D hD A _ _ G P _ hPG W hexp hr₁ hr₂ I T _ x y hx hy hxy team Z hl ht hZ
  have hD1 : 1 < D := hD₀.trans_le hD
  have hD0 : 0 < D := lt_trans zero_lt_one hD1
  obtain ⟨hr,hbudget⟩ := hm D hD W.card hr₁ hr₂
  apply team_routing_on_set G P hPG W _ (by positivity) hexp (by exact_mod_cast hr)
    x y hx hy hxy team Z _ _ _ _ _ (by positivity) hl ht hZ hbudget
  · exact Real.one_le_rpow hD1.le (by norm_num)
  · exact Real.one_le_rpow hD1.le (by norm_num)

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
open SimpleGraph

variable {V : Type cycleUniverse1} {G : SimpleGraph V}

structure CycleVisit (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish

inductive VisitChain (G : SimpleGraph V) : V → V → Type _
  | single {u v : V} (p : G.Walk u v) : VisitChain G u v
  | cons {u v w z : V} (p : G.Walk u v) (h : G.Adj v w)
      (q : VisitChain G w z) : VisitChain G u z

namespace VisitChain

variable {u v : V}

def walk : {u v : V} → VisitChain G u v → G.Walk u v
  | _, _, .single p => p
  | _, _, .cons p h q => p.append (.cons h q.walk)

def visits : {u v : V} → VisitChain G u v → List (CycleVisit G)
  | u, v, .single p => [⟨u,v,p⟩]
  | u, _, .cons (v := v) p _ q => ⟨u,v,p⟩ :: q.visits

def links : {u v : V} → VisitChain G u v → Set (Sym2 V)
  | _, _, .single _ => ∅
  | _, _, .cons (v := v) (w := w) _ _ q => {s(v,w)} ∪ q.links

def switchEdges (q : VisitChain G u v) : Set (Sym2 V) :=
  ⋃ p ∈ q.visits, p.walk.edgeSet

lemma mem_support_iff (q : VisitChain G u v) (x : V) :
    x ∈ q.walk.support ↔ ∃ p ∈ q.visits, x ∈ p.walk.support := by
  induction q with
  | single p => simp [walk, visits]
  | cons p h q ih =>
    simp only [walk, Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons,
      ih, visits, List.mem_cons]
    constructor
    · rintro (hp | rfl | ⟨r,hr,hx⟩)
      · exact ⟨_, Or.inl rfl, hp⟩
      · exact ⟨_, Or.inl rfl, p.end_mem_support⟩
      · exact ⟨r, Or.inr hr, hx⟩
    · rintro ⟨r, rfl | hr, hx⟩
      · exact Or.inl hx
      · exact Or.inr (Or.inr ⟨r,hr,hx⟩)

lemma isPath_of_separated (q : VisitChain G u v)
    (hp : ∀ p ∈ q.visits, p.walk.IsPath)
    (hd : q.visits.Pairwise (fun p r => p.walk.support.Disjoint r.walk.support)) :
    q.walk.IsPath := by
  induction q with
  | single p => exact hp ⟨_,_,p⟩ (by simp [visits])
  | cons p h q ih =>
    have hpd := (List.pairwise_cons.mp hd).1
    have hqt := ih (fun r hr => hp r (by simp [visits, hr]))
      (List.pairwise_cons.mp hd).2
    have hpt := hp ⟨_,_,p⟩ (by simp [visits])
    have hdisj : p.support.Disjoint q.walk.support := by
      rw [List.disjoint_left]
      intro x hx hqx
      obtain ⟨r,hr,hxr⟩ := q.mem_support_iff x |>.mp hqx
      exact hpd r hr hx hxr
    apply Walk.IsPath.mk'
    simpa only [walk, Walk.support_append, Walk.support_cons, List.tail_cons]
      using (List.nodup_append').mpr ⟨hpt.support_nodup, hqt.support_nodup, hdisj⟩

lemma length_visits_le (q : VisitChain G u v) : q.visits.length ≤ q.walk.length + 1 := by
  induction q with
  | single p => simp [visits, walk]
  | cons p h q ih => simp only [visits, List.length_cons, walk, Walk.length_append,
      Walk.length_cons]; omega

lemma edgeSet_eq (q : VisitChain G u v) :
    q.walk.edgeSet = q.links ∪ q.switchEdges := by
  induction q with
  | single p => simp [walk, links, switchEdges, visits]
  | cons p h q ih =>
    simp only [walk, Walk.edgeSet_append, Walk.edgeSet_cons, ih, links,
      switchEdges, visits]
    ext e
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff,
      Set.mem_iUnion, List.mem_cons, exists_prop, or_and_right, exists_or, exists_eq_left]
    tauto

theorem close_cycle (q : VisitChain G u v) (hc : G.Adj v u)
    (hp : ∀ p ∈ q.visits, p.walk.IsPath)
    (hd : q.visits.Pairwise (fun p r => p.walk.support.Disjoint r.walk.support))
    (hn : 3 ≤ q.visits.length) :
    (Walk.cons hc q.walk).IsCycle ∧
    (Walk.cons hc q.walk).edgeSet = {s(v,u)} ∪ q.links ∪ q.switchEdges ∧
    3 ≤ (Walk.cons hc q.walk).length := by
  have hpath := q.isPath_of_separated hp hd
  have hlength := q.length_visits_le
  have he : s(v,u) ∉ q.walk.edges := by
    intro he
    have hh := hpath.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
    omega
  refine ⟨Path.cons_isCycle ⟨q.walk,hpath⟩ hc he, ?_, ?_⟩
  · rw [Walk.edgeSet_cons, q.edgeSet_eq]
    ext e
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · simp only [Walk.length_cons]
    omega

end VisitChain

namespace CycleVisit

def ends (p : CycleVisit G) : Set V := {p.start, p.finish}
def interior (p : CycleVisit G) : Set V := {x | x ∈ p.walk.support} \ p.ends

lemma separated_of_interiors (p q : CycleVisit G)
    (he : Disjoint p.ends q.ends)
    (hpq : Disjoint p.interior q.ends) (hqp : Disjoint q.interior p.ends)
    (hi : Disjoint p.interior q.interior) :
    p.walk.support.Disjoint q.walk.support := by
  rw [List.disjoint_left]
  intro x hx hy
  by_cases hpx : x ∈ p.ends
  · by_cases hqx : x ∈ q.ends
    · exact Set.disjoint_left.mp he hpx hqx
    · exact Set.disjoint_left.mp hqp ⟨hy,hqx⟩ hpx
  · by_cases hqx : x ∈ q.ends
    · exact Set.disjoint_left.mp hpq ⟨hx,hpx⟩ hqx
    · exact Set.disjoint_left.mp hi ⟨hx,hpx⟩ ⟨hy,hqx⟩

end CycleVisit

theorem quotient_cycle_inflation {u v : V} (q : VisitChain G u v) (hc : G.Adj v u)
    (hp : ∀ p ∈ q.visits, p.walk.IsPath)
    (he : q.visits.Pairwise (fun p r => Disjoint p.ends r.ends))
    (hf : ∀ p ∈ q.visits, ∀ r ∈ q.visits, Disjoint p.interior r.ends)
    (hi : q.visits.Pairwise (fun p r => Disjoint p.interior r.interior))
    (hn : 3 ≤ q.visits.length) :
    (Walk.cons hc q.walk).IsCycle ∧
    (Walk.cons hc q.walk).edgeSet = {s(v,u)} ∪ q.links ∪ q.switchEdges ∧
    3 ≤ (Walk.cons hc q.walk).length := by
  apply q.close_cycle hc hp _ hn
  have hh := he.and hi
  apply hh.imp_of_mem
  intro p r hpm hrm hpr
  exact p.separated_of_interiors r hpr.1 (hf p hpm r hrm) (hf r hrm p hpm) hpr.2

namespace VisitChain
variable {W : Type cycleUniverse2} {Q : SimpleGraph W}

def of_walk (s t : W → V) (q : ∀ z, G.Walk (s z) (t z)) :
    {a b : W} → (p : Q.Walk a b) →
    (∀ d ∈ p.darts, G.Adj (t d.fst) (s d.snd)) → VisitChain G (s a) (t b)
  | _, _, .nil, _ => .single (q _)
  | a, b, .cons (v := c) h p, hr => .cons (q a)
      (hr ⟨(a,c),h⟩ (by simp))
      (of_walk s t q p (by intro d hd; exact hr d (by simp [hd])))

lemma of_walk_visits (s t : W → V) (q : ∀ z, G.Walk (s z) (t z))
    {a b : W} (p : Q.Walk a b)
    (hr : ∀ d ∈ p.darts, G.Adj (t d.fst) (s d.snd)) :
    (of_walk s t q p hr).visits = p.support.map (fun z => (⟨s z,t z,q z⟩ : CycleVisit G)) := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [of_walk, visits, ih]

lemma of_walk_links (s t : W → V) (q : ∀ z, G.Walk (s z) (t z))
    {a b : W} (p : Q.Walk a b)
    (hr : ∀ d ∈ p.darts, G.Adj (t d.fst) (s d.snd)) :
    (of_walk s t q p hr).links = {e | ∃ d ∈ p.darts, e = s(t d.fst,s d.snd)} := by
  induction p with
  | nil => ext e; simp [of_walk, links]
  | cons h p ih =>
    ext e
    simp [of_walk, links, ih,  ]

lemma of_walk_switchEdges (s t : W → V) (q : ∀ z, G.Walk (s z) (t z))
    {a b : W} (p : Q.Walk a b)
    (hr : ∀ d ∈ p.darts, G.Adj (t d.fst) (s d.snd)) :
    (of_walk s t q p hr).switchEdges = ⋃ z ∈ p.support, (q z).edgeSet := by
  rw [switchEdges, of_walk_visits]
  ext e
  simp only [Set.mem_iUnion, List.mem_map, exists_prop]
  constructor
  · rintro ⟨r,⟨z,hz,rfl⟩,he⟩
    exact ⟨z,hz,he⟩
  · rintro ⟨z,hz,he⟩
    exact ⟨⟨s z,t z,q z⟩,⟨z,hz,rfl⟩,he⟩

end VisitChain

theorem lift_quotient_cycle {W : Type cycleUniverse3} {Q : SimpleGraph W}
    (s t : W → V) (q : ∀ z, G.Walk (s z) (t z))
    {a : W} (p : Q.Walk a a) (hp : p.IsCycle)
    (hr : ∀ d ∈ p.dropLast.darts, G.Adj (t d.fst) (s d.snd))
    (hc : G.Adj (t p.penultimate) (s a))
    (hq : ∀ z ∈ p.dropLast.support, (q z).IsPath)
    (hsep : ∀ z ∈ p.dropLast.support, ∀ w ∈ p.dropLast.support,
      z ≠ w → (q z).support.Disjoint (q w).support) :
    ∃ c : G.Walk (t p.penultimate) (t p.penultimate), c.IsCycle ∧
      c.edgeSet = {s(t p.penultimate,s a)} ∪
        {e | ∃ d ∈ p.dropLast.darts, e = s(t d.fst,s d.snd)} ∪
        (⋃ z ∈ p.dropLast.support, (q z).edgeSet) := by
  let chain := VisitChain.of_walk s t q p.dropLast hr
  have hv : chain.visits = p.dropLast.support.map (fun z => (⟨s z,t z,q z⟩ : CycleVisit G)) :=
    VisitChain.of_walk_visits s t q p.dropLast hr
  have hpaths : ∀ v ∈ chain.visits, v.walk.IsPath := by
    intro v hvv
    rw [hv] at hvv
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hvv
    exact hq z hz
  have hpair : chain.visits.Pairwise (fun v w => v.walk.support.Disjoint w.walk.support) := by
    rw [hv, List.pairwise_map]
    apply (List.pairwise_iff_getElem).mpr
    intro i j hi hj hij
    have hne : p.dropLast.support[i] ≠ p.dropLast.support[j] := by
      intro he
      have hij' := hp.isPath_dropLast.support_nodup.getElem_inj_iff.mp he
      omega
    exact hsep _ (List.getElem_mem _) _ (List.getElem_mem _) hne
  have hn : 3 ≤ chain.visits.length := by
    rw [hv, List.length_map, Walk.length_support, Walk.length_dropLast]
    have := hp.three_le_length
    omega
  obtain ⟨hcycle,hedges,_⟩ := chain.close_cycle hc hpaths hpair hn
  refine ⟨Walk.cons hc chain.walk,hcycle,?_⟩
  rw [hedges, VisitChain.of_walk_links, VisitChain.of_walk_switchEdges]

noncomputable section
attribute [local instance] Classical.propDecidable

theorem orient_edge_representatives {W : Type cycleUniverse4} {Q : SimpleGraph W}
    (projMap : V → W) (S : Set (Sym2 V)) (hSG : S ⊆ G.edgeSet)
    (hrep : ∀ e ∈ Q.edgeSet, ∃ f ∈ S, Sym2.map projMap f = e) :
    ∃ R : Q.Dart → G.Dart, ∀ d,
      (R d).edge ∈ S ∧ projMap (R d).fst = d.fst ∧ projMap (R d).snd = d.snd := by
  have hex : ∀ d : Q.Dart, ∃ r : G.Dart,
      r.edge ∈ S ∧ projMap r.fst = d.fst ∧ projMap r.snd = d.snd := by
    intro d
    obtain ⟨f,hf,hmap⟩ := hrep d.edge d.edge_mem
    induction f using Sym2.ind with
    | _ x y =>
      have hadj : G.Adj x y := hSG hf
      change s(projMap x,projMap y) = s(d.fst,d.snd) at hmap
      rcases Sym2.eq_iff.mp hmap with he | he
      · exact ⟨⟨(x,y),hadj⟩,hf,he.1,he.2⟩
      · refine ⟨⟨(y,x),hadj.symm⟩,?_,he.2,he.1⟩
        change s(y,x) ∈ S
        simpa only [Sym2.eq_swap] using hf
  exact Classical.axiomOfChoice hex

def portFrom {A : Type cycleUniverse5} {W : Type cycleUniverse6} (L : List A) (f : A → W) (g : A → V)
    (v₀ : V) (z : W) : V :=
  if h : ∃ d ∈ L, f d = z then g h.choose else v₀

lemma portFrom_on {A : Type cycleUniverse7} {W : Type cycleUniverse8} (L : List A) (f : A → W) (g : A → V)
    (v₀ : V) (hn : (L.map f).Nodup) {d : A} (hd : d ∈ L) :
    portFrom L f g v₀ (f d) = g d := by
  have hex : ∃ e ∈ L, f e = f d := ⟨d,hd,rfl⟩
  rw [portFrom, dite_eq_left hex]
  congr 1
  exact List.inj_on_of_nodup_map hn hex.choose_spec.1 hd hex.choose_spec.2

theorem choose_cycle_ports {W : Type cycleUniverse9} {Q : SimpleGraph W}
    (projMap : V → W) (R : Q.Dart → G.Dart)
    (hprojMap : ∀ d, projMap (R d).fst = d.fst ∧ projMap (R d).snd = d.snd)
    {a : W} (p : Q.Walk a a) (hp : p.IsCycle) (v₀ : V) :
    ∃ s t : W → V,
      (∀ d ∈ p.darts, t d.fst = (R d).fst ∧ s d.snd = (R d).snd) ∧
      (∀ z ∈ p.dropLast.support, projMap (s z) = z ∧ projMap (t z) = z) := by
  let s := portFrom p.darts (fun d => d.snd) (fun d => (R d).snd) v₀
  let t := portFrom p.darts (fun d => d.fst) (fun d => (R d).fst) v₀
  have hnf : (p.darts.map (fun d => d.fst)).Nodup := by
    rw [Walk.map_fst_darts]
    exact hp.nodup_dropLast_support
  have hns : (p.darts.map (fun d => d.snd)).Nodup := by
    rw [Walk.map_snd_darts]
    exact hp.support_nodup
  have ht : ∀ d ∈ p.darts, t d.fst = (R d).fst := fun d hd =>
    portFrom_on _ _ _ _ hnf hd
  have hs : ∀ d ∈ p.darts, s d.snd = (R d).snd := fun d hd =>
    portFrom_on _ _ _ _ hns hd
  refine ⟨s,t,fun d hd => ⟨ht d hd,hs d hd⟩,?_⟩
  intro z hz
  have hz' : z ∈ p.support.dropLast := by
    rw [← p.support_dropLast hp.not_nil]
    exact hz
  have hzt : z ∈ p.support.tail :=
    p.tail_support_perm_dropLast_support.mem_iff.mpr hz'
  have hzf : z ∈ p.darts.map (fun d => d.fst) := by rwa [Walk.map_fst_darts]
  have hzs : z ∈ p.darts.map (fun d => d.snd) := by rwa [Walk.map_snd_darts]
  obtain ⟨d,hd,he⟩ := List.mem_map.mp hzf
  obtain ⟨e,he',hee⟩ := List.mem_map.mp hzs
  exact ⟨by rw [← hee,hs e he']; exact (hprojMap e).2,
    by rw [← he,ht d hd]; exact (hprojMap d).1⟩

lemma last_dart_mem {W : Type cycleUniverse10} {Q : SimpleGraph W} {a b : W}
    (p : Q.Walk a b) (hp : ¬p.Nil) :
    (⟨(p.penultimate,b),p.adj_penultimate hp⟩ : Q.Dart) ∈ p.darts := by
  have he := congrArg Walk.darts (p.concat_dropLast (p.adj_penultimate hp))
  rw [Walk.darts_concat] at he
  rw [← he]
  simp

lemma cycle_darts_split {W : Type cycleUniverse11} {Q : SimpleGraph W} {a b : W}
    (p : Q.Walk a b) (hp : ¬p.Nil) :
    p.darts = p.dropLast.darts ++ [⟨(p.penultimate,b),p.adj_penultimate hp⟩] := by
  have he := congrArg Walk.darts (p.concat_dropLast (p.adj_penultimate hp))
  simpa only [Walk.darts_concat, List.concat_eq_append] using he.symm

theorem inflate_represented_cycle {W : Type cycleUniverse12} {Q : SimpleGraph W}
    (R : Q.Dart → G.Dart) (s t : W → V)
    {a : W} (p : Q.Walk a a) (hp : p.IsCycle)
    (hports : ∀ d ∈ p.darts, t d.fst = (R d).fst ∧ s d.snd = (R d).snd)
    (q : ∀ z, G.Walk (s z) (t z))
    (hq : ∀ z ∈ p.dropLast.support, (q z).IsPath)
    (hsep : ∀ z ∈ p.dropLast.support, ∀ w ∈ p.dropLast.support,
      z ≠ w → (q z).support.Disjoint (q w).support) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      c.edgeSet = {e | ∃ d ∈ p.darts, e = (R d).edge} ∪
        (⋃ z ∈ p.dropLast.support, (q z).edgeSet) := by
  let last : Q.Dart := ⟨(p.penultimate,a),p.adj_penultimate hp.not_nil⟩
  have hlast : last ∈ p.darts := last_dart_mem p hp.not_nil
  have hsub : p.dropLast.darts ⊆ p.darts := by
    rw [Walk.darts_dropLast]; exact List.dropLast_subset _
  have hed : ∀ d ∈ p.darts, s(t d.fst,s d.snd) = (R d).edge := by
    intro d hd
    rw [(hports d hd).1,(hports d hd).2]
    rfl
  have hadj : ∀ d ∈ p.darts, G.Adj (t d.fst) (s d.snd) := by
    intro d hd
    rw [(hports d hd).1,(hports d hd).2]
    exact (R d).adj
  obtain ⟨c,hc,he⟩ := lift_quotient_cycle s t q p hp
    (fun d hd => hadj d (hsub hd)) (hadj last hlast) hq hsep
  refine ⟨_,c,hc,?_⟩
  rw [he]
  have hlinks : {s(t p.penultimate,s a)} ∪
      {e | ∃ d ∈ p.dropLast.darts, e = s(t d.fst,s d.snd)} =
      {e | ∃ d ∈ p.darts, e = (R d).edge} := by
    ext e
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro (rfl | ⟨d,hd,rfl⟩)
      · exact ⟨last,hlast,hed last hlast⟩
      · exact ⟨d,hsub hd,hed d (hsub hd)⟩
    · rintro ⟨d,hd,rfl⟩
      rw [cycle_darts_split p hp.not_nil] at hd
      simp only [List.mem_append,List.mem_singleton] at hd
      rcases hd with hd | rfl
      · exact Or.inr ⟨d,hd,(hed d (hsub hd)).symm⟩
      · exact Or.inl (hed last hlast).symm
  rw [hlinks]

theorem interiors_disjoint_across_routers {I : Type cycleUniverse13} {R : Type cycleUniverse14}
    (U : R → Set V) (hi : Pairwise (fun r s => Disjoint (U r) (U s)))
    (router : I → R) (A : I → Set V)
    (hA : ∀ i, A i ⊆ U (router i))
    (hteam : ∀ i j, i ≠ j → router i = router j → Disjoint (A i) (A j)) :
    Pairwise (fun i j => Disjoint (A i) (A j)) := by
  intro i j hij
  by_cases hr : router i = router j
  · exact hteam i j hij hr
  · exact (hi hr).mono (hA i) (hA j)

def cyclePortSet {W : Type cycleUniverse15} (S : Set W) (s t : W → V) : Set V :=
  {v | ∃ z ∈ S, v = s z ∨ v = t z}

def visitInterior {W : Type cycleUniverse16} (s t : W → V) (q : ∀ z, G.Walk (s z) (t z))
    (z : W) : Set V := {x | x ∈ (q z).support ∧ x ≠ s z ∧ x ≠ t z}

theorem switch_supports_separated {W : Type cycleUniverse17}
    (S : Set W) (projMap : V → W) (s t : W → V)
    (q : ∀ z, G.Walk (s z) (t z))
    (hproj : ∀ z ∈ S, projMap (s z) = z ∧ projMap (t z) = z)
    (havoid : ∀ z ∈ S, Disjoint (visitInterior s t q z) (cyclePortSet S s t))
    (hinter : ∀ z ∈ S, ∀ w ∈ S, z ≠ w →
      Disjoint (visitInterior s t q z) (visitInterior s t q w)) :
    ∀ z ∈ S, ∀ w ∈ S, z ≠ w → (q z).support.Disjoint (q w).support := by
  intro z hz w hw hzw
  rw [List.disjoint_left]
  intro x hx hy
  by_cases hxend : x = s z ∨ x = t z
  · have hxZ : x ∈ cyclePortSet S s t := ⟨z,hz,hxend⟩
    by_cases hyend : x = s w ∨ x = t w
    · have hxprojMap : projMap x = z := by rcases hxend with rfl | rfl <;> simp_all
      have hyprojMap : projMap x = w := by rcases hyend with rfl | rfl <;> simp_all
      exact hzw (hxprojMap.symm.trans hyprojMap)
    · exact Set.disjoint_left.mp (havoid w hw)
        ⟨hy,fun he => hyend (Or.inl he),fun he => hyend (Or.inr he)⟩ hxZ
  · have hxI : x ∈ visitInterior s t q z :=
      ⟨hx,fun he => hxend (Or.inl he),fun he => hxend (Or.inr he)⟩
    by_cases hyend : x = s w ∨ x = t w
    · exact Set.disjoint_left.mp (havoid z hz) hxI ⟨w,hw,hyend⟩
    · exact Set.disjoint_left.mp (hinter z hz w hw hzw) hxI
        ⟨hy,fun he => hyend (Or.inl he),fun he => hyend (Or.inr he)⟩

theorem cyclePortSet_eq_representative_vertices {W : Type cycleUniverse18} {Q : SimpleGraph W}
    (R : Q.Dart → G.Dart) (s t : W → V)
    {a : W} (p : Q.Walk a a) (hp : p.IsCycle)
    (hports : ∀ d ∈ p.darts, t d.fst = (R d).fst ∧ s d.snd = (R d).snd) :
    cyclePortSet {z | z ∈ p.dropLast.support} s t =
      {v | ∃ d ∈ p.darts, v = (R d).fst ∨ v = (R d).snd} := by
  have hmF : p.darts.map (fun d => d.fst) = p.dropLast.support := by
    rw [Walk.map_fst_darts, p.support_dropLast hp.not_nil]
  have hmS : ∀ z, z ∈ p.darts.map (fun d => d.snd) ↔ z ∈ p.dropLast.support := by
    intro z
    rw [Walk.map_snd_darts, p.support_dropLast hp.not_nil]
    exact p.tail_support_perm_dropLast_support.mem_iff
  ext v
  constructor
  · rintro ⟨z,hz,hv | hv⟩
    · obtain ⟨d,hd,hds⟩ := List.mem_map.mp ((hmS z).mpr hz)
      exact ⟨d,hd,Or.inr (hv.trans (by rw [← hds]; exact (hports d hd).2))⟩
    · have hz' : z ∈ p.darts.map (fun d => d.fst) := by rwa [hmF]
      obtain ⟨d,hd,hdf⟩ := List.mem_map.mp hz'
      exact ⟨d,hd,Or.inl (hv.trans (by rw [← hdf]; exact (hports d hd).1))⟩
  · rintro ⟨d,hd,hv | hv⟩
    · refine ⟨d.fst,?_,Or.inr (hv.trans (hports d hd).1.symm)⟩
      rw [← hmF]
      exact List.mem_map.mpr ⟨d,hd,rfl⟩
    · exact ⟨d.snd,(hmS _).mp (List.mem_map.mpr ⟨d,hd,rfl⟩),
        Or.inl (hv.trans (hports d hd).2.symm)⟩

theorem complete_batch_cycle {W : Type cycleUniverse19} {Ridx : Type cycleUniverse20} {Q : SimpleGraph W}
    (projMap : V → W) (R : Q.Dart → G.Dart)
    (_hprojMap : ∀ d, projMap (R d).fst = d.fst ∧ projMap (R d).snd = d.snd)
    {a : W} (p : Q.Walk a a) (hp : p.IsCycle)
    (s t : W → V)
    (hports : ∀ d ∈ p.darts, t d.fst = (R d).fst ∧ s d.snd = (R d).snd)
    (hproj : ∀ z ∈ p.dropLast.support, projMap (s z) = z ∧ projMap (t z) = z)
    (q : ∀ z, G.Walk (s z) (t z))
    (hq : ∀ z ∈ p.dropLast.support, (q z).IsPath)
    (U : Ridx → Set V) (hU : Pairwise (fun i j => Disjoint (U i) (U j)))
    (router : {z // z ∈ p.dropLast.support} → Ridx)
    (hroute : ∀ z : {z // z ∈ p.dropLast.support},
      visitInterior s t q z ⊆ U (router z))
    (hteam : ∀ z w : {z // z ∈ p.dropLast.support}, z ≠ w →
      router z = router w → Disjoint (visitInterior s t q z) (visitInterior s t q w))
    (havoid : ∀ z ∈ p.dropLast.support, Disjoint (visitInterior s t q z)
      {v | ∃ d ∈ p.darts, v = (R d).fst ∨ v = (R d).snd}) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      c.edgeSet = {e | ∃ d ∈ p.darts, e = (R d).edge} ∪
        (⋃ z ∈ p.dropLast.support, (q z).edgeSet) := by
  have hinter := interiors_disjoint_across_routers U hU router
    (fun z => visitInterior s t q z) hroute hteam
  apply inflate_represented_cycle R s t p hp hports q hq
  apply switch_supports_separated {z | z ∈ p.dropLast.support} projMap s t q hproj
  · intro z hz
    rw [cyclePortSet_eq_representative_vertices R s t p hp hports]
    exact havoid z hz
  · intro z hz w hw hzw
    exact hinter (show (⟨z,hz⟩ : {z // z ∈ p.dropLast.support}) ≠ ⟨w,hw⟩ from
      fun he => hzw (congrArg Subtype.val he))

end
end ErdosGallai.Batch

end
end
end

end OAI
