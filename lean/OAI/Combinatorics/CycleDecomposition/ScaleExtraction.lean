import OAI.Combinatorics.CycleDecomposition.ExpansionBoxes

namespace OAI

universe u

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Scale
open Finset SimpleGraph Classical
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]
lemma edgeCount_eq_card {V : Type cycleUniverse2} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (S : Finset (Sym2 V))
    (hS : ∀ e, e ∈ S ↔ e ∈ G.edgeSet) : edgeCount G = S.card := by
  unfold edgeCount
  congr 1
  ext e
  simp only [SimpleGraph.mem_edgeFinset]
  exact (hS e).symm

def IsCycleGraph (K : SimpleGraph V) : Prop :=
  ∃ a : V, ∃ p : K.Walk a a, p.IsCycle ∧ K.edgeSet = p.edgeSet

def NoLongCycle (G : SimpleGraph V) (ℓ : ℝ) : Prop :=
  ∀ a : V, ∀ p : G.Walk a a, p.IsCycle → (p.length : ℝ) < ℓ

lemma NoLongCycle.mono {V : Type cycleUniverse3} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {G H : SimpleGraph V} {ℓ : ℝ}
    (h : NoLongCycle G ℓ) (hle : H ≤ G) : NoLongCycle H ℓ := by
  intro a p hp
  simpa using h a (p.mapLe hle) (hp.mapLe hle)

lemma cycle_graph_of_walk (G : SimpleGraph V) {a : V} (p : G.Walk a a) (hp : p.IsCycle) :
    ∃ K : SimpleGraph V, K ≤ G ∧ IsCycleGraph K ∧ edgeCount K = p.length := by
  classical
  let K := SimpleGraph.fromEdgeSet p.edgeSet
  have he : K.edgeSet = p.edgeSet := by
    rw [SimpleGraph.edgeSet_fromEdgeSet,sdiff_eq_left]
    exact Set.disjoint_left.mpr (fun e he hd =>
      G.not_isDiag_of_mem_edgeSet (p.edges_subset_edgeSet he) hd)
  have hle : K ≤ G := SimpleGraph.edgeSet_subset_edgeSet.mp (he ▸ p.edges_subset_edgeSet)
  have htransfer : ∀ e ∈ p.edges, e ∈ K.edgeSet := by
    intro e he'; rw [he]; exact he'
  refine ⟨K,hle,⟨a,p.transfer K htransfer,hp.transfer htransfer,?_⟩,?_⟩
  · simpa using he
  · rw [edgeCount_eq_card K p.edges.toFinset (by
      intro e; simp only [List.mem_toFinset,he]; rfl)]
    exact (List.toFinset_card_of_nodup hp.isTrail.edges_nodup).trans p.length_edges

lemma edgeCount_sdiff_add {G K : SimpleGraph V} (hle : K ≤ G) :
    edgeCount (G \ K) + edgeCount K = edgeCount G := by
  classical
  rw [edgeCount_eq_card (G \ K) (G.edgeFinset \ K.edgeFinset) (by
    intro e; simp only [Finset.mem_sdiff,SimpleGraph.mem_edgeFinset,SimpleGraph.edgeSet_sdiff,
      Set.mem_sdiff]),
    edgeCount_eq_card K K.edgeFinset (by intro e; simp),
    edgeCount_eq_card G G.edgeFinset (by intro e; simp)]
  exact Finset.card_sdiff_add_card_eq_card (SimpleGraph.edgeFinset_mono hle)

lemma edgeCount_cycle_pos {K : SimpleGraph V} (h : IsCycleGraph K) : 0 < edgeCount K := by
  classical
  obtain ⟨a,p,hp,he⟩ := h
  have hf : K.edgeFinset = p.edges.toFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset,he,List.mem_toFinset]
    rfl
  simp only [edgeCount,hf,List.toFinset_card_of_nodup hp.isTrail.edges_nodup,
    SimpleGraph.Walk.length_edges]
  exact hp.three_le_length.trans_lt' (by omega)

theorem remove_long_cycles (G : SimpleGraph V) (ℓ : ℝ) :
    ∃ (H : SimpleGraph V) (L : List (SimpleGraph V)),
      H ≤ G ∧ NoLongCycle H ℓ ∧
      (∀ K ∈ L, IsCycleGraph K ∧ ℓ ≤ (edgeCount K : ℝ)) ∧
      GraphPartition G (H::L) ∧
      (L.length : ℝ)*ℓ + edgeCount H ≤ edgeCount G := by
  classical
  induction hn : edgeCount G using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hstop : NoLongCycle G ℓ
    · refine ⟨G,[],le_rfl,hstop,by simp,?_,?_⟩
      · intro x y; simp
      · simp [← hn]
    · obtain ⟨a,p,hp,hplen⟩ : ∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ ℓ ≤ (p.length : ℝ) := by
        by_contra hh
        apply hstop
        intro a p hp
        by_contra hlen
        exact hh ⟨a,p,hp,le_of_not_gt hlen⟩
      obtain ⟨K,hle,hK,hKlen⟩ := cycle_graph_of_walk G p hp
      have heq := edgeCount_sdiff_add hle
      have hpos := edgeCount_cycle_pos hK
      have hlt : edgeCount (G \ K) < n := by omega
      obtain ⟨H,L,hH,hNL,hL,hpart,hbudget⟩ := ih _ hlt (G \ K) rfl
      refine ⟨H,K::L,hH.trans sdiff_le,hNL,?_,?_,?_⟩
      · intro J hJ
        rcases List.mem_cons.mp hJ with rfl | hJ
        · exact ⟨hK,by simpa [hKlen] using hplen⟩
        · exact hL J hJ
      · intro x y
        have hh := @hH x y
        have hk := @hle x y
        have he := hpart x y
        simp only [edgeOccurrences_cons,SimpleGraph.sdiff_adj] at he ⊢
        by_cases hG : G.Adj x y <;> by_cases hK : K.Adj x y <;>
          by_cases hH : H.Adj x y <;> simp_all
      · have heqR : (edgeCount (G \ K) : ℝ) + edgeCount K = edgeCount G := by exact_mod_cast heq
        have hKbound : ℓ ≤ (edgeCount K : ℝ) := by simpa [hKlen] using hplen
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
        rw [← hn]
        nlinarith

open Real Filter Asymptotics

lemma longCycle_power_margin : ∀ᶠ u : ℝ in atTop,
    4 ≤ u ∧ u^(199/200:ℝ) ≤ ((1/32:ℝ)/(logb 2 u)^2)^2*u/100 := by
  have hlog := (isLittleO_log_rpow_rpow_atTop (4:ℝ)
    (s:=1/200) (by norm_num)).const_mul_left ((102400:ℝ)/(log 2)^4)
  filter_upwards [eventually_ge_atTop (4:ℝ),hlog.eventuallyLE] with u hu hh
  have hu0 : 0 < u := by linarith
  have hln : 0 ≤ log u := log_nonneg (by linarith)
  have hln2 : 0 < log 2 := log_pos (by norm_num)
  have hLu : 0 < logb 2 u := logb_pos (by norm_num) (by linarith)
  have hr0 : 0 ≤ u^(1/200:ℝ) := rpow_nonneg hu0.le _
  have hnum0 : 0 ≤ (102400:ℝ)/(log 2)^4 * (log u)^(4:ℝ) := by positivity
  simp only [Real.norm_eq_abs,abs_of_nonneg hnum0,abs_of_nonneg hr0] at hh
  have hden : (102400:ℝ)*(logb 2 u)^4 ≤ u^(1/200:ℝ) := by
    calc
      (102400:ℝ)*(logb 2 u)^4 = (102400:ℝ)/(log 2)^(4:ℕ) * (log u)^(4:ℕ) := by
        simp only [Real.logb,div_pow]; ring
      _ ≤ u^(1/200:ℝ) := by simpa only [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast] using hh
  have hm := mul_le_mul_of_nonneg_left hden (rpow_nonneg hu0.le (199/200:ℝ))
  have he : u^(199/200:ℝ)*u^(1/200:ℝ) = u := by
    rw [← Real.rpow_add hu0]; norm_num
  rw [he] at hm
  refine ⟨hu,?_⟩
  have hid : ((1/32:ℝ)/(logb 2 u)^2)^2*u/100 = u/(102400*(logb 2 u)^4) := by
    field_simp
    ; ring
  rw [hid]
  exact (le_div_iff₀ (by positivity : (0:ℝ) < 102400*(logb 2 u)^4)).mpr (by nlinarith)

lemma longCycle_scale_ready : ∃ Dsp : ℝ, ∀ D ≥ Dsp,
    4 ≤ D ∧ 4 ≤ D^(51/50:ℝ) ∧
    ∀ u : ℝ, D^(51/50:ℝ) < u →
      0 < (1/32:ℝ)/(logb 2 u)^2 ∧ (1/32:ℝ)/(logb 2 u)^2 ≤ 1 ∧
      1 ≤ ((1/32:ℝ)/(logb 2 u)^2)^2*u/100 ∧
      D^(101/100:ℝ) < ((1/32:ℝ)/(logb 2 u)^2)^2*u/100 := by
  obtain ⟨Q,hQ⟩ := eventually_atTop.mp longCycle_power_margin
  refine ⟨max 4 Q,?_⟩
  intro D hD
  have hD4 : 4 ≤ D := (le_max_left _ _).trans hD
  have hD1 : 1 ≤ D := by linarith
  have hDp : 0 < D := by linarith
  have hTD : D ≤ D^(51/50:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hD1
      (by norm_num : (1:ℝ) ≤ 51/50)
  refine ⟨hD4,hD4.trans hTD,?_⟩
  intro u hu
  have huQ : Q ≤ u := (le_max_right 4 Q).trans (hD.trans (hTD.trans hu.le))
  obtain ⟨hu4,hq⟩ := hQ u huQ
  have hlog : 1 ≤ logb 2 u := by
    have h := Real.logb_le_logb_of_le (b:=2) (x:=2) (y:=u)
      (by norm_num) (by norm_num) (by linarith)
    norm_num [Real.logb] at h
    exact h
  have hd : 0 < (logb 2 u)^2 := by positivity
  have hα : 0 < (1/32:ℝ)/(logb 2 u)^2 := by positivity
  have hα1 : (1/32:ℝ)/(logb 2 u)^2 ≤ 1 := by
    apply (div_le_one hd).mpr
    nlinarith [sq_nonneg (logb 2 u-1)]
  have hmargin : D^(101/100:ℝ) < u^(199/200:ℝ) := by
    have hstrict := Real.rpow_lt_rpow (Real.rpow_nonneg hDp.le (51/50:ℝ)) hu
      (by norm_num : (0:ℝ) < 199/200)
    rw [← Real.rpow_mul hDp.le] at hstrict
    have hle := Real.rpow_le_rpow_of_exponent_le hD1
      (by norm_num : (101/100:ℝ) ≤ (51/50)*(199/200))
    exact hle.trans_lt hstrict
  have hpow1 : 1 ≤ D^(101/100:ℝ) := Real.one_le_rpow hD1 (by norm_num)
  exact ⟨hα,hα1,hpow1.trans (hmargin.le.trans hq),hmargin.trans_le hq⟩

lemma external_induce_image (G : SimpleGraph V) (A : Finset V) (hG : SupportedOn G A)
    (U : Finset {x // x ∈ A}) :
    externalOn G (U.image Subtype.val) =
      (externalOn (G.induce (A : Set V)) U).image Subtype.val := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨_,hyU,x,hx,hxy⟩ := Finset.mem_filter.mp hy
    have hyA := (hG hxy).2
    obtain ⟨x',hx',heq⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨⟨y,hyA⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩,rfl⟩
    · intro hy'
      exact hyU (Finset.mem_image.mpr ⟨⟨y,hyA⟩,hy',rfl⟩)
    · exact ⟨x',hx',by simpa only [SimpleGraph.induce_adj,heq] using hxy⟩
  · intro hy
    obtain ⟨y',hy',rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨_,hyU,x,hx,hxy⟩ := Finset.mem_filter.mp hy'
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩
    · intro hy
      obtain ⟨z,hz,heq⟩ := Finset.mem_image.mp hy
      have heq' : z = y' := Subtype.ext heq
      exact hyU (heq' ▸ hz)
    · exact ⟨x,Finset.mem_image.mpr ⟨x,hx,rfl⟩,hxy⟩

lemma sparse_neighborhood_from_cycle_exclusion (G : SimpleGraph V) (A : Finset V)
    (hG : SupportedOn G A) (ℓ : ℝ) (hNL : NoLongCycle G ℓ)
    (hα : 0 < (1/32:ℝ)/(logb 2 A.card)^2)
    (hα1 : (1/32:ℝ)/(logb 2 A.card)^2 ≤ 1)
    (hq : 1 ≤ ((1/32:ℝ)/(logb 2 A.card)^2)^2*A.card/100)
    (hmargin : ℓ < ((1/32:ℝ)/(logb 2 A.card)^2)^2*A.card/100) :
    ∃ U ⊆ A, U.Nonempty ∧ 2*U.card ≤ A.card ∧
      ((externalOn G U).card : ℝ) < (1/32:ℝ)*U.card/(logb 2 A.card)^2 := by
  classical
  by_contra hno
  let H := G.induce (A : Set V)
  let α := (1/32:ℝ)/(logb 2 A.card)^2
  have hexp : VertexExpansion H α := by
    intro U hU hhalf
    let W := U.image Subtype.val
    have hW : W ⊆ A := by
      intro x hx
      obtain ⟨x',hx',rfl⟩ := Finset.mem_image.mp hx
      exact x'.property
    have hcard : W.card = U.card := Finset.card_image_of_injective _ Subtype.val_injective
    have hWne : W.Nonempty := hU.image _
    have hWhalf : 2*W.card ≤ A.card := by simpa [hcard] using hhalf
    have hs : ¬ ((externalOn G W).card : ℝ) < (1/32:ℝ)*W.card/(logb 2 A.card)^2 :=
      fun hs => hno ⟨W,hW,hWne,hWhalf,hs⟩
    have hbound := le_of_not_gt hs
    have heq := external_induce_image G A hG U
    have hcardext := congrArg Finset.card heq
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at hcardext
    have hext : externalNeighbors H U = externalOn H U := by rfl
    rw [hext]
    change α*(U.card:ℝ) ≤ (externalOn H U).card
    rw [← hcardext]
    dsimp [α]
    rw [← hcard]
    calc
      (1/32:ℝ)/(logb 2 A.card)^2 * (W.card:ℝ) = (1/32:ℝ)*(W.card:ℝ)/(logb 2 A.card)^2 := by ring
      _ ≤ ((externalOn G W).card:ℝ) := hbound
  have hq' : 1 ≤ α^2*(Fintype.card {x // x ∈ A})/100 := by simpa [α] using hq
  obtain ⟨a,p,hp,hplen⟩ := long_cycle_of_vertex_expansion H α hα hα1 hexp hq'
  let f : H →g G := ⟨Subtype.val,fun h => h⟩
  have hc := hp.map (f:=f) (by exact Subtype.val_injective)
  have hlen := hNL a.val (p.map f) hc
  simp only [SimpleGraph.Walk.length_map] at hlen
  have hplen' : α^2*(A.card:ℝ)/100 < (p.length:ℝ) := by simpa using hplen
  dsimp [α] at hplen'
  linarith

lemma splitPotential_scale_bound (D x : ℝ) (hD : 4 ≤ D) :
    splitPotential (D^(51/50:ℝ)) x ≤ 1+2/logb 2 D := by
  have hD1 : 1 ≤ D := by linarith
  have hDp : 0 < D := by linarith
  have hLD : 2 ≤ logb 2 D := by
    have h := Real.logb_le_logb_of_le (b:=2) (x:=4) (y:=D)
      (by norm_num) (by norm_num) hD
    have h4 : logb 2 (4:ℝ) = 2 := by
      rw [show (4:ℝ) = 2^(2:ℕ) by norm_num,Real.logb_pow]
      norm_num
    rw [h4] at h
    exact h
  have hLD0 : 0 < logb 2 D := by linarith
  have hlogT : logb 2 (D^(51/50:ℝ)/2) = (51/50:ℝ)*logb 2 D-1 := by
    rw [Real.logb_div (Real.rpow_pos_of_pos hDp _).ne' (by norm_num),
      Real.logb_rpow_eq_mul_logb_of_pos hDp]
    norm_num
  have hT0 : 0 < logb 2 (D^(51/50:ℝ)/2) := by rw [hlogT]; linarith
  have hrecip : 1/logb 2 (D^(51/50:ℝ)/2) ≤ 2/logb 2 D := by
    apply (div_le_div_iff₀ hT0 hLD0).mpr
    rw [hlogT]
    linarith
  have hbasepos : 0 < D^(51/50:ℝ)/2 := by positivity
  have hmaxlog := Real.logb_le_logb_of_le (b:=2) (by norm_num) hbasepos
    (le_max_right x (D^(51/50:ℝ)/2))
  have hmax0 : 0 < logb 2 (max x (D^(51/50:ℝ)/2)) := lt_of_lt_of_le hT0 hmaxlog
  have hinv := one_div_pos.mpr hmax0
  dsimp [splitPotential]
  linarith

lemma partition_replace_head {G H : SimpleGraph V} {C L : List (SimpleGraph V)}
    (hG : GraphPartition G (H::C)) (hH : GraphPartition H L) :
    GraphPartition G (C++L) := by
  intro x y
  have h := hG x y
  simp only [edgeOccurrences_cons] at h
  rw [edgeOccurrences_append,hH x y]
  omega

theorem scale_boxes : ∃ Dsp : ℝ, ∀ D ≥ Dsp,
    ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (A : Finset V), A.Nonempty → SupportedOn G A →
      2*(edgeCount G : ℝ)/A.card ≤ D →
    ∃ (C : List (SimpleGraph V)) (L : List (AssignedPiece V)),
      (∀ K ∈ C, IsCycleGraph K ∧ D^(101/100:ℝ) ≤ (edgeCount K : ℝ)) ∧
      (C.length : ℝ) ≤ A.card/(2*D^(1/100:ℝ)) ∧
      (∀ P ∈ L, P.vertices ⊆ A ∧ P.vertices.Nonempty ∧ (P.vertices.card : ℝ) ≤ D^(51/50:ℝ)) ∧
      (∀ x ∈ A, ∃ P ∈ L, x ∈ P.vertices) ∧
      GraphPartition G (C++L.map AssignedPiece.graph) ∧
      (L.map (fun P => (P.vertices.card : ℝ))).sum ≤ (1+2/logb 2 D)*A.card := by
  classical
  obtain ⟨Dsp,hsp⟩ := longCycle_scale_ready
  refine ⟨Dsp,?_⟩
  intro D hD V _ _ G A hA hG hdeg
  obtain ⟨hD4,hT4,hnum⟩ := hsp D hD
  have hDp : 0 < D := by linarith
  have hA0 : (0:ℝ) < A.card := by exact_mod_cast hA.card_pos
  obtain ⟨H,C,hHG,hNL,hC,hpartC,hbudget⟩ := remove_long_cycles G (D^(101/100:ℝ))
  have hHA : SupportedOn H A := fun _ _ h => hG (hHG h)
  have hsplit : ∀ B ⊆ A, ∀ K : SimpleGraph V, K ≤ H → SupportedOn K B → D^(51/50:ℝ) < (B.card:ℝ) →
      ∃ U ⊆ B, U.Nonempty ∧ 2*U.card ≤ B.card ∧
        ((externalOn K U).card : ℝ) < (1/32:ℝ)*U.card/(logb 2 B.card)^2 := by
    intro B hB K hK hs hlarge
    obtain ⟨ha,ha1,hq,hm⟩ := hnum B.card hlarge
    exact sparse_neighborhood_from_cycle_exclusion K B hs _ (hNL.mono hK) ha ha1 hq hm
  obtain ⟨L,hL,hcov,hpartL,hcost⟩ := box_recursion H A (D^(51/50:ℝ)) hT4 hA hHA hsplit
  refine ⟨C,L,hC,?_,hL,hcov,partition_replace_head hpartC hpartL,?_⟩
  · have hdeg' := (div_le_iff₀ hA0).mp hdeg
    have he : D^(101/100:ℝ) = D*D^(1/100:ℝ) := by
      rw [show (101/100:ℝ) = 1+1/100 by norm_num,Real.rpow_add hDp,Real.rpow_one]
    rw [he] at hbudget
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 2*D^(1/100:ℝ))).mpr
    have hnonneg : (0:ℝ) ≤ edgeCount H := Nat.cast_nonneg _
    nlinarith
  · have hfbound := splitPotential_scale_bound D A.card hD4
    have hplain : (L.map (fun P => (P.vertices.card:ℝ))).sum ≤
        (L.map (fun P => (P.vertices.card:ℝ)*splitPotential (D^(51/50:ℝ)) P.vertices.card)).sum := by
      apply List.sum_le_sum
      intro P hP
      have hb := (splitPotential_bounds (D^(51/50:ℝ)) P.vertices.card hT4).1
      have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg P.vertices.card)
      simpa using hm
    have hmul := mul_le_mul_of_nonneg_left hfbound hA0.le
    nlinarith

end ErdosGallai.Scale

namespace ErdosGallai.Scale
open Finset SimpleGraph Classical Real
variable {V : Type cycleUniverse4} [Fintype V] [DecidableEq V]

lemma edgeCount_sup_le (G H : SimpleGraph V) : edgeCount (G ⊔ H) ≤ edgeCount G + edgeCount H := by
  classical
  simpa [edgeCount, SimpleGraph.edgeFinset_sup] using Finset.card_union_le G.edgeFinset H.edgeFinset

lemma crossing_count (G : SimpleGraph V) (A B : Finset V) (hd : Disjoint A B) :
    edgeCount (crossingGraph G A B) = cutCount G A B := by
  classical
  have hinj : Set.InjOn (fun e : V × V => s(e.1,e.2)) (G.interedges A B : Set (V×V)) := by
    intro e he f hf hh
    rcases Sym2.mk_eq_mk_iff.mp hh with hh | hh
    · exact hh
    · have heA := (G.mem_interedges_iff.mp he).1
      have hfB := (G.mem_interedges_iff.mp hf).2.1
      have heq : e.1 = f.2 := congrArg Prod.fst hh
      exact False.elim (Finset.disjoint_left.mp hd heA (heq.symm ▸ hfB))
  have heq : (crossingGraph G A B).edgeFinset =
      (G.interedges A B).image (fun e : V×V => s(e.1,e.2)) := by
    ext e
    induction e using Sym2.inductionOn with | _ x y =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      constructor
      · rintro ⟨hxy,(⟨hx,hy⟩|⟨hx,hy⟩)⟩
        · exact Finset.mem_image.mpr ⟨(x,y),G.mem_interedges_iff.mpr ⟨hx,hy,hxy⟩,rfl⟩
        · exact Finset.mem_image.mpr ⟨(y,x),G.mem_interedges_iff.mpr ⟨hy,hx,hxy.symm⟩,
            Sym2.eq_swap⟩
      · rintro h
        obtain ⟨⟨a,b⟩,hab,he⟩ := Finset.mem_image.mp h
        obtain ⟨ha,hb,hg⟩ := G.mem_interedges_iff.mp hab
        rcases (Sym2.mk_eq_mk_iff (p := (a,b)) (q := (x,y))).mp he with he | he
        · cases he; exact ⟨hg,Or.inl ⟨ha,hb⟩⟩
        · cases he; exact ⟨hg.symm,Or.inr ⟨hb,ha⟩⟩
  simp only [edgeCount,heq,Finset.card_image_of_injOn hinj,cutCount]

lemma log2_split_budget {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    min a b + a*a.log2 + b*b.log2 ≤ (a+b)*(a+b).log2 := by
  have hm : Monotone Nat.log2 := by
    intro m n h
    simpa only [Nat.log2_eq_log_two] using (Nat.log_mono_right (b:=2) h)
  have hla := hm (show a ≤ a+b by omega)
  have hlb := hm (show b ≤ a+b by omega)
  rcases le_total a b with hab | hba
  · have hhalf := hm (show 2*a ≤ a+b by omega)
    rw [Nat.log2_two_mul (by omega)] at hhalf
    rw [min_eq_left hab]
    nlinarith
  · have hhalf := hm (show 2*b ≤ a+b by omega)
    rw [Nat.log2_two_mul (by omega)] at hhalf
    rw [min_eq_right hba]
    nlinarith

lemma partition_combine {G K G₁ G₂ H₁ H₂ : SimpleGraph V}
    {L₁ L₂ : List (SimpleGraph V)}
    (hp₁ : GraphPartition G₁ (H₁::L₁)) (hp₂ : GraphPartition G₂ (H₂::L₂))
    (hcover : ∀ x y, G.Adj x y ↔ K.Adj x y ∨ G₁.Adj x y ∨ G₂.Adj x y)
    (hd₁ : Disjoint K G₁) (hd₂ : Disjoint K G₂) (hd₃ : Disjoint G₁ G₂) :
    GraphPartition G ((K ⊔ H₁ ⊔ H₂)::(L₁++L₂)) := by
  classical
  have hle₁ : H₁ ≤ G₁ := partition_member_le hp₁ (by simp)
  have hle₂ : H₂ ≤ G₂ := partition_member_le hp₂ (by simp)
  intro x y
  have h₁ := hp₁ x y
  have h₂ := hp₂ x y
  have hd₁ := SimpleGraph.disjoint_left.mp hd₁ x y
  have hd₂ := SimpleGraph.disjoint_left.mp hd₂ x y
  have hd₃ := SimpleGraph.disjoint_left.mp hd₃ x y
  have hh₁ := @hle₁ x y
  have hh₂ := @hle₂ x y
  have hc := hcover x y
  simp only [edgeOccurrences_cons,edgeOccurrences_append,SimpleGraph.sup_adj] at *
  by_cases hK : K.Adj x y <;> by_cases hG₁ : G₁.Adj x y <;>
    by_cases hG₂ : G₂.Adj x y <;> by_cases hH₁ : H₁.Adj x y <;>
    by_cases hH₂ : H₂.Adj x y <;> simp_all

lemma cut_split_properties {V : Type cycleUniverse5} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (A U : Finset V)
    (hG : SupportedOn G A) (_hU : U ⊆ A) :
    (∀ x y, G.Adj x y ↔ (crossingGraph G U (A\U)).Adj x y ∨
        (restrictGraph G U).Adj x y ∨ (restrictGraph G (A\U)).Adj x y) ∧
    Disjoint (crossingGraph G U (A\U)) (restrictGraph G U) ∧
    Disjoint (crossingGraph G U (A\U)) (restrictGraph G (A\U)) ∧
    Disjoint (restrictGraph G U) (restrictGraph G (A\U)) := by
  constructor
  · intro x y
    change G.Adj x y ↔ (G.Adj x y ∧ _) ∨ (G.Adj x y ∧ _) ∨ (G.Adj x y ∧ _)
    have hs := @hG x y
    simp only [Finset.mem_sdiff]
    tauto
  · simp only [SimpleGraph.disjoint_left, crossingGraph, restrictGraph,Finset.mem_sdiff]
    tauto

lemma empty_supported_graph {V : Type cycleUniverse6} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {G : SimpleGraph V} {A : Finset V}
    (hG : SupportedOn G A) (hA : A.card ≤ 1) : G = ⊥ := by
  ext x y
  constructor
  · intro h
    obtain ⟨hx,hy⟩ := hG h
    have hxy := Finset.card_le_one.mp hA x hx y hy
    exact False.elim (G.ne_of_adj h hxy)
  · simp

theorem cut_extraction (G : SimpleGraph V) (A : Finset V)
    (hG : SupportedOn G A) (σ : ℝ) (hσ : 0 ≤ σ) :
    ∃ (R : List (AssignedPiece V)) (H : SimpleGraph V),
      (∀ P ∈ R, P.vertices ⊆ A ∧ 2 ≤ P.vertices.card ∧
        CutExpansionOn P.graph P.vertices σ) ∧
      R.Pairwise (fun P Q => Disjoint P.vertices Q.vertices) ∧
      GraphPartition G (H :: R.map AssignedPiece.graph) ∧
      SupportedOn H A ∧
      (edgeCount H : ℝ) ≤ σ * A.card * A.card.log2 := by
  classical
  induction hcard : A.card using Nat.strong_induction_on generalizing A G with
  | h n ih =>
    by_cases hsmall : A.card ≤ 1
    · have he := empty_supported_graph hG hsmall
      refine ⟨[],⊥,by simp,by simp,?_,?_,?_⟩
      · subst G
        intro x y
        simp
      · intro x y h; exact False.elim h
      · simp only [edgeCount_bot,Nat.cast_zero]
        positivity
    by_cases hexp : CutExpansionOn G A σ
    · refine ⟨[⟨A,G,hG⟩],⊥,?_,by simp,?_,?_,?_⟩
      · intro P hP
        have he := List.mem_singleton.mp hP
        subst P
        exact ⟨fun _ h => h,by change 2 ≤ A.card; omega,hexp⟩
      · intro x y; simp
      · intro x y h; exact False.elim h
      · simp only [edgeCount_bot,Nat.cast_zero]
        positivity
    unfold CutExpansionOn at hexp
    push Not at hexp
    obtain ⟨U,hU,hcut⟩ := hexp
    have hdisUB : Disjoint U (A\U) := Finset.disjoint_left.mpr
      (fun _ hu hb => (Finset.mem_sdiff.mp hb).2 hu)
    have hcnt : (0 : ℝ) ≤ cutCount G U (A\U) := Nat.cast_nonneg _
    have hσpos : 0 < σ := by
      by_contra h
      have : σ = 0 := le_antisymm (le_of_not_gt h) hσ
      rw [this,zero_mul] at hcut
      linarith
    have hUpos : 0 < U.card := by
      by_contra h
      have hz : U.card = 0 := by omega
      simp [hz] at hcut
      linarith [min_le_left (0:ℝ) ((A\U).card:ℝ)]
    have hBpos : 0 < (A\U).card := by
      by_contra h
      have hz : (A\U).card = 0 := by omega
      simp [hz] at hcut
      linarith [min_le_right (U.card:ℝ) (0:ℝ)]
    have hcardSum := Finset.card_sdiff_add_card_eq_card hU
    have hUlt : U.card < n := by omega
    have hBlt : (A\U).card < n := by omega
    obtain ⟨R₁,H₁,hR₁,hd₁,hp₁,hs₁,hc₁⟩ := ih U.card hUlt (restrictGraph G U) U
      (restrictGraph_supported G U) rfl
    obtain ⟨R₂,H₂,hR₂,hd₂,hp₂,hs₂,hc₂⟩ := ih (A\U).card hBlt (restrictGraph G (A\U)) (A\U)
      (restrictGraph_supported G (A\U)) rfl
    let K := crossingGraph G U (A\U)
    obtain ⟨hcover,hdis₁,hdis₂,hdis₃⟩ := cut_split_properties G A U hG hU
    refine ⟨R₁++R₂,K ⊔ H₁ ⊔ H₂,?_,?_,?_,?_,?_⟩
    · intro P hP
      rcases List.mem_append.mp hP with hP | hP
      · obtain ⟨hPA,hPc,hPe⟩ := hR₁ P hP
        exact ⟨hPA.trans hU,hPc,hPe⟩
      · obtain ⟨hPA,hPc,hPe⟩ := hR₂ P hP
        exact ⟨hPA.trans Finset.sdiff_subset,hPc,hPe⟩
    · apply List.pairwise_append.mpr
      refine ⟨hd₁,hd₂,?_⟩
      intro P hP Q hQ
      exact hdisUB.mono
        (hR₁ P hP).1 (hR₂ Q hQ).1
    · simpa only [List.map_append] using partition_combine hp₁ hp₂ hcover hdis₁ hdis₂ hdis₃
    · intro x y h
      rcases h with (h|h)|h
      · exact hG h.1
      · exact ⟨hU (hs₁ h).1,hU (hs₁ h).2⟩
      · exact ⟨(Finset.mem_sdiff.mp (hs₂ h).1).1,(Finset.mem_sdiff.mp (hs₂ h).2).1⟩
    · have hcardK : edgeCount K = cutCount G U (A\U) :=
        crossing_count G U (A\U) hdisUB
      have hcost : (edgeCount (K⊔H₁⊔H₂) : ℝ) ≤
          edgeCount K + edgeCount H₁ + edgeCount H₂ := by
        exact_mod_cast (edgeCount_sup_le (K⊔H₁) H₂).trans
          (Nat.add_le_add_right (edgeCount_sup_le K H₁) _)
      have hpot := log2_split_budget hUpos hBpos
      have hpotR : min (U.card:ℝ) ((A\U).card:ℝ) + U.card*U.card.log2 +
          (A\U).card*(A\U).card.log2 ≤ (A.card:ℝ) * A.card.log2 := by
        have he : U.card+(A\U).card = A.card := by omega
        rw [he] at hpot
        exact_mod_cast hpot
      have hpay := mul_le_mul_of_nonneg_left hpotR hσ
      rw [hcardK] at hcost
      rw [← hcard]
      nlinarith

lemma cast_log2_le_logb {n : ℕ} (hn : 0 < n) : (n.log2 : ℝ) ≤ Real.logb 2 n := by
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) (by exact_mod_cast hn)).mpr
  rw [Real.rpow_natCast, Nat.log2_eq_log_two]
  exact_mod_cast Nat.pow_log_le_self 2 hn.ne'

lemma expansion_order_lower {V : Type cycleUniverse7} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {G : SimpleGraph V} {A : Finset V} {σ : ℝ}
    (hA : 2 ≤ A.card) (he : CutExpansionOn G A σ) : σ+1 ≤ A.card := by
  classical
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
  have hsub : {x} ⊆ A := Finset.singleton_subset_iff.mpr hx
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  simp only [Finset.card_singleton] at hcard
  have hB : (1:ℝ) ≤ (A\{x}).card := by exact_mod_cast (show 1 ≤ (A\{x}).card by omega)
  have hc := he {x} hsub
  simp only [Finset.card_singleton,Nat.cast_one,min_eq_left hB,mul_one] at hc
  have hbound : cutCount G {x} (A\{x}) ≤ (A\{x}).card := by
    simpa only [cutCount,Finset.card_singleton,one_mul] using G.card_interedges_le_mul {x} (A\{x})
  have hboundR : (cutCount G {x} (A\{x}) : ℝ) ≤ (A\{x}).card := by exact_mod_cast hbound
  have heqR : ((A\{x}).card:ℝ)+1 = A.card := by exact_mod_cast hcard
  linarith

open Filter Asymptotics Real in
lemma cut_scale_ready : ∀ᶠ D : ℝ in atTop,
    1 ≤ D ∧ 2*D^(9/10:ℝ)*logb 2 (D^(51/50:ℝ)) ≤ D^(19/20:ℝ) := by
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have he := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/20)).const_mul_left
    ((51/25:ℝ)/log 2)).eventuallyLE
  filter_upwards [eventually_ge_atTop (1:ℝ),he] with D hD h
  have hDp : 0 < D := by linarith
  have hn : 0 ≤ (51/25:ℝ)/log 2 * log D := mul_nonneg (by positivity) (Real.log_nonneg hD)
  have hh : (51/25:ℝ)/log 2 * log D ≤ D^(1/20:ℝ) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hn,abs_of_nonneg (Real.rpow_nonneg hDp.le _)] using h
  refine ⟨hD,?_⟩
  calc
    2*D^(9/10:ℝ)*logb 2 (D^(51/50:ℝ)) = D^(9/10:ℝ)*((51/25:ℝ)/log 2*log D) := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos hDp]
      simp only [Real.logb]
      ring
    _ ≤ D^(9/10:ℝ)*D^(1/20:ℝ) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = D^(19/20:ℝ) := by rw [← Real.rpow_add hDp]; norm_num

theorem scale_cut_extraction : ∃ Dcut : ℝ, ∀ D ≥ Dcut,
    ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (A : Finset V), A.Nonempty → SupportedOn G A →
      (A.card : ℝ) ≤ D^(51/50:ℝ) →
    ∃ (R : List (AssignedPiece V)) (H : SimpleGraph V),
      (∀ P ∈ R, P.vertices ⊆ A ∧ D^(9/10:ℝ) ≤ P.vertices.card ∧
        (P.vertices.card:ℝ) ≤ D^(51/50:ℝ) ∧ CutExpansionOn P.graph P.vertices (D^(9/10:ℝ))) ∧
      R.Pairwise (fun P Q => Disjoint P.vertices Q.vertices) ∧
      GraphPartition G (H :: R.map AssignedPiece.graph) ∧ SupportedOn H A ∧
      2*(edgeCount H : ℝ)/A.card ≤ D^(19/20:ℝ) := by
  classical
  obtain ⟨Dcut,hready⟩ := Filter.eventually_atTop.mp cut_scale_ready
  refine ⟨Dcut,?_⟩
  intro D hD V _ _ G A hA hG hhi
  obtain ⟨hD₁,hscale⟩ := hready D hD
  have hDp : 0 < D := by linarith
  have hAp : 0 < A.card := Finset.card_pos.mpr hA
  have hAr : (0:ℝ) < A.card := by exact_mod_cast hAp
  obtain ⟨R,H,hR,hd,hp,hs,hcost⟩ := cut_extraction G A hG (D^(9/10:ℝ)) (by positivity)
  refine ⟨R,H,?_,hd,hp,hs,?_⟩
  · intro P hP
    obtain ⟨hsub,hsize,hexp⟩ := hR P hP
    have hlo := expansion_order_lower hsize hexp
    have hle : (P.vertices.card:ℝ) ≤ A.card := by exact_mod_cast Finset.card_le_card hsub
    exact ⟨hsub,by linarith,hle.trans hhi,hexp⟩
  · have hlog := (cast_log2_le_logb hAp).trans
      (Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hAr hhi)
    have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ D^(9/10:ℝ)*(A.card:ℝ) by positivity)
    have hscaleA := mul_le_mul_of_nonneg_right hscale hAr.le
    apply (div_le_iff₀ hAr).mpr
    nlinarith

end ErdosGallai.Scale
end
end
end

end OAI
