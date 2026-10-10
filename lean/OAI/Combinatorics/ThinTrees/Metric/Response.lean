import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.CenteredDomain
import OAI.Combinatorics.ThinTrees.Restriction

namespace OAI

/-! Metric response. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m m' : ℕ}

lemma laplacian_mono (G : MultiGraph n m) {F B : Finset (Fin m)} (hFB : F ⊆ B) :
    G.laplacian F ≤ G.laplacian B := by
  unfold MultiGraph.laplacian
  apply sum_le_sum_of_subset_of_nonneg hFB
  intro e _ _
  exact Matrix.nonneg_iff_posSemidef.mpr (by
    simpa only [star_trivial] using posSemidef_vecMulVec_self_star (G.incidence e))

lemma restrict_laplacian (H : MultiGraph n m') (F : Finset (Fin m')) :
    (H.restrict F).laplacian univ=H.laplacian F := by
  conv_rhs => rw [←lift_univ F]
  simp only [MultiGraph.laplacian,liftEdges,sum_map]
  rfl

lemma restrict_laplacian_le (H : MultiGraph n m') (F : Finset (Fin m')) :
    (H.restrict F).laplacian univ ≤ H.laplacian univ := by
  rw [restrict_laplacian]
  exact laplacian_mono H (subset_univ _)

lemma metric_shortcut_response (G : MultiGraph n m) (H : MultiGraph n m')
    (hn : 0 < n) (hGH : G.laplacian univ ≤ H.laplacian univ)
    {J : Hierarchy n} {h : ℕ} (hh : 0 < h) {a t : ℝ}
    (ha : 0 ≤ a) (ht : 0 < t)
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : CenteredPositive D)
    (htr : ∀Z, CenteredTest Z → (D*Z).trace ≤ (G.laplacian univ*Z).trace)
    (havg : ∀A ∈ J.nodes, A ≠ univ →
      ((G.cut univ A).card:ℝ)/h ≤ (J.parentBoundary G A).card →
      boundaryResistance G J D A ≤ a) :
    ∃Y ∈ metricDomain H, CenteredPositive Y ∧ ∀A ∈ J.nodes,
      (((univ.filter (fun e => t < resistance G Y e)) ∩ J.parentBoundary G A).card:ℝ) ≤
      (a/t+1/(h:ℝ))*(G.cut univ A).card := by
  let Y := H.laplacian univ+D
  have hY : CenteredPositive Y := by
    rw [show Y=D+H.laplacian univ by dsimp [Y]; ac_rfl]
    exact centeredPositive_add_psd hD (H.laplacian_psd univ) (laplacian_ones H)
  have hRY (e : Fin m) : resistance G Y e ≤ resistance G D e := by
    apply centered_inverse_antitone hn hD hY
    exact le_add_of_nonneg_left (Matrix.nonneg_iff_posSemidef.mpr (H.laplacian_psd univ))
  have hcoeff : 0 ≤ a/t := div_nonneg ha ht.le
  have hhR : (0:ℝ) < h := Nat.cast_pos.mpr hh
  refine ⟨Y,shortcut_add_mem_domain G H hn hGH hD htr,hY,fun A hA => ?_⟩
  have hsub := G.parentBoundary_sub J A
  have hcard : ((J.parentBoundary G A).card:ℝ) ≤ (G.cut univ A).card := by
    exact_mod_cast card_le_card hsub
  have hbadsub : (univ.filter (fun e => t < resistance G Y e)) ∩ J.parentBoundary G A ⊆
      (J.parentBoundary G A).filter (fun e => t < resistance G D e) := by
    intro e he
    obtain ⟨hb,heA⟩ := mem_inter.mp he
    exact mem_filter.mpr ⟨heA,(mem_filter.mp hb).2.trans_le (hRY e)⟩
  by_cases hroot : A=univ
  · subst A
    have he : G.cut univ univ=∅ := by ext e; simp [cut]
    have ho : J.parentBoundary G univ=∅ := subset_empty.mp (he ▸ hsub)
    simp [ho,he]
  by_cases hmark : ((G.cut univ A).card:ℝ)/h ≤ (J.parentBoundary G A).card
  · have hm := finite_markov (J.parentBoundary G A) (resistance G D)
      (fun e _ => centered_resistance_nonneg G hn hD e) ht (havg A hA hroot hmark)
    calc
      _ ≤ (((J.parentBoundary G A).filter (fun e => t < resistance G D e)).card:ℝ) := by
        exact_mod_cast card_le_card hbadsub
      _ ≤ a/t*(J.parentBoundary G A).card := hm
      _ ≤ a/t*(G.cut univ A).card := mul_le_mul_of_nonneg_left hcard hcoeff
      _ ≤ _ := by
        have hnon : 0 ≤ 1/(h:ℝ)*(G.cut univ A).card := by positivity
        nlinarith
  · have hb : (((univ.filter (fun e => t < resistance G Y e)) ∩ J.parentBoundary G A).card:ℝ) ≤
        (J.parentBoundary G A).card := by exact_mod_cast card_le_card inter_subset_right
    have hm := (lt_of_not_ge hmark).le
    have hnon : 0 ≤ a/t*(G.cut univ A).card := mul_nonneg hcoeff (Nat.cast_nonneg _)
    calc
      _ ≤ ((J.parentBoundary G A).card:ℝ) := hb
      _ ≤ ((G.cut univ A).card:ℝ)/h := hm
      _ ≤ _ := by
        nlinarith [show ((G.cut univ A).card:ℝ)/h=(1/(h:ℝ))*(G.cut univ A).card by ring]

theorem simultaneous_metric_response_bound :
    ∃ h0 : ℕ, 2 ≤ h0 ∧ ∀h : ℕ, h0 ≤ h →
      ∀(n m m' : ℕ) (G : MultiGraph n m) (H : MultiGraph n m'), 2 ≤ n →
      G.laplacian univ ≤ H.laplacian univ →
      ∀(P : PartitionChain n) (z : ℕ), P.parts z={univ} →
      (∀i ≤ z, ∀A ∈ P.parts i, G.EdgeConnectedReal A h) →
      ∀t : ℝ, 0 < t → ∃Y ∈ metricDomain H, CenteredPositive Y ∧
        ∀i ≤ z, (((univ.filter (fun e => t < resistance G Y e)) ∩ P.crossing G i).card:ℝ) ≤
          16*((h:ℝ)^(-31/40:ℝ)/t+1/(h:ℝ))*(P.crossing G i).card := by
  obtain ⟨h0,hh0,hshortcut⟩ := metric_hierarchy_bound
  refine ⟨h0,hh0,?_⟩
  intro h hh n m m' G H hn hGH P z hz hlocal t ht
  let I := insert z (Dyadic.selected (fun j => (P.crossing G j).card) z)
  obtain ⟨J,hJ⟩ := P.exists_hierarchy I ⟨z,mem_insert_self _ _,hz ▸ mem_singleton_self _⟩
  have hloc : J.LocallyConnectedReal G h := by
    apply G.chain_locally P I J hJ
    intro i hi A hA
    have hiz : i ≤ z := by
      rcases mem_insert.mp hi with rfl | hi
      · exact le_rfl
      · exact (Dyadic.selected_spec hi).1
    exact hlocal i hiz A hA
  let M := J.nodes.filter (fun A => A ≠ univ ∧
    ((G.cut univ A).card:ℝ)/h ≤ (J.parentBoundary G A).card)
  obtain ⟨D,hD,htr,havg⟩ := hshortcut h hh n m G J hn hloc M (filter_subset _ _)
    (fun A hA => (mem_filter.mp hA).2.1) (fun A hA => (mem_filter.mp hA).2.2)
  obtain ⟨Y,hYm,hY,hnode⟩ := metric_shortcut_response G H (by omega) hGH (by omega : 0 < h)
    (Real.rpow_nonneg (Nat.cast_nonneg h) _) ht hD htr
    (fun A hA hA' hr => havg A (mem_filter.mpr ⟨hA,hA',hr⟩))
  refine ⟨Y,hYm,hY,?_⟩
  intro i hiz
  exact P.simultaneous_bad_bound G hz hJ (univ.filter (fun e => t < resistance G Y e))
    (by positivity : 0 ≤ (h:ℝ)^(-31/40:ℝ)/t+1/(h:ℝ)) hnode i hiz

lemma quarter_negative_power {x y : ℝ} (hx : 0 < x) (hxy : x/4 ≤ y) :
    y^(-31/40:ℝ) ≤ 4*x^(-31/40:ℝ) := by
  have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < x/4) hxy
    (by norm_num : (-31/40:ℝ) ≤ 0)
  have hp : (4:ℝ)^(31/40:ℝ) ≤ 4 :=
    Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have heq : (x/4)^(-31/40:ℝ)=x^(-31/40:ℝ)*(4:ℝ)^(31/40:ℝ) := by
    rw [Real.div_rpow hx.le (by norm_num),div_eq_mul_inv,
      ←Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4)]
    norm_num
  rw [heq] at hh
  exact hh.trans (by nlinarith [Real.rpow_nonneg hx.le (-31/40:ℝ)])

lemma response_fraction_cutoff :
    ∃r0 : ℕ, 2 ≤ r0 ∧ ∀r : ℕ, r0 ≤ r → ∀s : ℝ,
      0 < s → s ≤ (r:ℝ)^(1/4:ℝ) →
      16*(((r/2:ℕ):ℝ)^(-31/40:ℝ)/(1/(6*s))+1/((r/2:ℕ):ℝ)) ≤ (r:ℝ)^(-1/3:ℝ) := by
  open Filter in
  have he : ∀ᶠ x : ℝ in atTop,
      128*x^(-1:ℝ) ≤ x^(-1/3:ℝ) ∧ 768*x^(-21/40:ℝ) ≤ x^(-1/3:ℝ) := by
    exact (ShortcutNumeric.eventually_const_mul_rpow_le_rpow 128 (by norm_num)).and
      (ShortcutNumeric.eventually_const_mul_rpow_le_rpow 768 (by norm_num))
  open Filter in
  have heN : ∀ᶠ r : ℕ in atTop,
      128*(r:ℝ)^(-1:ℝ) ≤ (r:ℝ)^(-1/3:ℝ) ∧
      768*(r:ℝ)^(-21/40:ℝ) ≤ (r:ℝ)^(-1/3:ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun r : ℕ => (r:ℝ)) atTop atTop).eventually he
  obtain ⟨r0,hr0⟩ := heN.exists_forall_of_atTop
  refine ⟨max 2 r0,le_max_left _ _,?_⟩
  intro r hr s hs hsR
  have hr2 : 2 ≤ r := (le_max_left _ _).trans hr
  have hlarge := hr0 r ((le_max_right _ _).trans hr)
  have hrR : (0:ℝ) < r := Nat.cast_pos.mpr (by omega)
  have hrh : (r:ℝ)/4 ≤ ((r/2:ℕ):ℝ) := by
    have hnn : r ≤ 4*(r/2) := by omega
    have hrr : (r:ℝ) ≤ 4*((r/2:ℕ):ℝ) := by exact_mod_cast hnn
    linarith
  have hhR : (0:ℝ) < ((r/2:ℕ):ℝ) := lt_of_lt_of_le (by positivity) hrh
  have hpow := quarter_negative_power hrR hrh
  have hprod : (r:ℝ)^(1/4:ℝ)*(r:ℝ)^(-31/40:ℝ)=(r:ℝ)^(-21/40:ℝ) := by
    rw [←Real.rpow_add hrR]
    norm_num
  have hp := mul_le_mul hsR hpow (Real.rpow_nonneg hhR.le _) (Real.rpow_nonneg hrR.le _)
  have hp' : s*((r/2:ℕ):ℝ)^(-31/40:ℝ) ≤ 4*(r:ℝ)^(-21/40:ℝ) := by
    nlinarith only [hp,hprod]
  have hi : 1/((r/2:ℕ):ℝ) ≤ 4/(r:ℝ) := by
    apply (div_le_div_iff₀ hhR hrR).mpr
    linarith
  have ht : ((r/2:ℕ):ℝ)^(-31/40:ℝ)/(1/(6*s))=
      6*(s*((r/2:ℕ):ℝ)^(-31/40:ℝ)) := by
    simp only [one_div,div_inv_eq_mul]
    ring
  rw [ht]
  have hl1 := hlarge.1
  rw [Real.rpow_neg_one] at hl1
  have hl2 := hlarge.2
  nlinarith [show 4/(r:ℝ)=4*(r:ℝ)⁻¹ by ring]

theorem simultaneous_metric_response :
    ∃r0 : ℕ, 2 ≤ r0 ∧ ∀r : ℕ, r0 ≤ r →
      ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.Connected univ →
      ∀(F : Finset (Fin m)) (P : PartitionChain n) (z : ℕ), P.parts z={univ} →
      (∀i ≤ z, ∀A ∈ P.parts i, (H.restrict F).EdgeConnectedReal A (r/2:ℕ)) →
      ∀s : ℝ, 0 < s → s ≤ (r:ℝ)^(1/4:ℝ) →
      ∃Y ∈ metricDomain H, CenteredPositive Y ∧ ∀i ≤ z,
        (((P.crossing (H.restrict F) i).filter (fun e =>
          ¬ (6*s) • vecMulVec ((H.restrict F).incidence e) ((H.restrict F).incidence e) ≤ Y)).card:ℝ) ≤
          (r:ℝ)^(-1/3:ℝ)*(P.crossing (H.restrict F) i).card := by
  obtain ⟨h0,hh0,hresp⟩ := simultaneous_metric_response_bound
  obtain ⟨r1,hr1,hfrac⟩ := response_fraction_cutoff
  refine ⟨max (2*h0) r1,hr1.trans (le_max_right _ _),?_⟩
  intro r hr n m H hn _ F P z hz hlocal s hs hsR
  have hrh : h0 ≤ r/2 := by have := (le_max_left _ _).trans hr; omega
  have hrr : r1 ≤ r := (le_max_right _ _).trans hr
  have ht : 0 < 1/(6*s) := by positivity
  obtain ⟨Y,hYm,hY,hbad⟩ := hresp (r/2) hrh n F.card m (H.restrict F) H hn
    (restrict_laplacian_le H F) P z hz hlocal (1/(6*s)) ht
  refine ⟨Y,hYm,hY,?_⟩
  intro i hi
  have heq : (P.crossing (H.restrict F) i).filter (fun e =>
      ¬ (6*s) • vecMulVec ((H.restrict F).incidence e) ((H.restrict F).incidence e) ≤ Y) =
      (univ.filter (fun e => 1/(6*s) < resistance (H.restrict F) Y e)) ∩
        P.crossing (H.restrict F) i := by
    ext e
    simp only [mem_filter,mem_inter,mem_univ,true_and]
    have hor := centered_resistance_order (by omega : 0 < n) hY
      (incidence_sum (H.restrict F) e) (by positivity : 0 < 6*s)
    rw [Matrix.le_iff,hor,not_le]
    have he : 1 < 6*s*qform (inverseOnZeroSum Y) ((H.restrict F).incidence e) ↔
        1/(6*s) < resistance (H.restrict F) Y e := by
      unfold resistance
      rw [div_lt_iff₀ (by positivity : 0 < 6*s)]
      rw [mul_comm]
    rw [he,and_comm]
  rw [heq]
  exact (hbad i hi).trans (mul_le_mul_of_nonneg_right (hfrac r hrr s hs hsR) (Nat.cast_nonneg _))

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
