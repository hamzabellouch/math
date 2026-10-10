import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ClassSlotsMem
import OAI.Combinatorics.KMedianRecovery.Recovery.Threshold

namespace OAI

namespace MetricKMedianRecovery.Anchoring

lemma threshold_times_power (mu : ℝ) (a : ℕ) :
    threshold mu a*(2:ℝ)^a = mu/100 := by
  rw [threshold,mul_assoc,← mul_pow]
  norm_num

lemma threshold_count_factor {mu : ℝ} (hmu : 0 < mu) {a : ℕ} (ha : a < rounds mu) :
    10*threshold mu a+6 ≤ threshold mu a*countConstant mu := by
  have he : threshold mu a*((600/mu)*(2:ℝ)^a) = 6 := by
    calc
      _ = (threshold mu a*(2:ℝ)^a)*(600/mu) := by ring
      _ = _ := by rw [threshold_times_power]; field_simp [ne_of_gt hmu]; ring
  have hpow : (2:ℝ)^a ≤ (2:ℝ)^(rounds mu-1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hh := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ threshold mu a*(600/mu) from mul_nonneg (threshold_pos hmu a).le (by positivity))
  unfold countConstant
  nlinarith

variable {I : Type*}

lemma selected_count_bound (O : Finset I) (scale V : I → ℝ) (b P mu ell : ℝ)
    (hb : 0 < b) (hP : 0 ≤ P) (hmu : 0 < mu) (hell : 0 ≤ ell)
    (hV : ∀ i ∈ O, 0 ≤ V i) (hsum : (∑ i ∈ O, V i) ≤ 6*P)
    (hscale : b*(ell+(shortCenters O scale b).card) ≤ 10*P)
    (a : ℕ) (ha : a < rounds mu) :
    ((badCenters O scale V b (threshold mu a)).card:ℝ) ≤ countConstant mu*P/b := by
  have ht := threshold_pos hmu a
  have hc := bad_count_pointwise O scale V b (threshold mu a) hV
  have hq : b*(shortCenters O scale b).card ≤ 10*P := by nlinarith
  have hfac := threshold_count_factor hmu ha
  have hm : threshold mu a*b*(badCenters O scale V b (threshold mu a)).card ≤
      threshold mu a*(countConstant mu*P) := by
    nlinarith [mul_le_mul_of_nonneg_left hq ht.le,mul_le_mul_of_nonneg_right hfac hP]
  apply (le_div_iff₀ hb).mpr
  have hm' : threshold mu a*(b*(badCenters O scale V b (threshold mu a)).card) ≤
      threshold mu a*(countConstant mu*P) := by nlinarith [hm]
  have hh := (mul_le_mul_iff_right₀ ht).mp hm'
  nlinarith

theorem threshold_with_count (O : Finset I) (scale V : I → ℝ) (b P mu ell : ℝ)
    (hb : 0 < b) (hP : 0 < P) (hmu : 0 < mu) (hmu1 : mu ≤ 1) (hell : 0 ≤ ell)
    (hV : ∀ i ∈ O, 0 ≤ V i) (hsum : (∑ i ∈ O, V i) ≤ 6*P)
    (hscale : b*(ell+(shortCenters O scale b).card) ≤ 10*P) :
    ∃ a ∈ Finset.range (rounds mu),
      0 < threshold mu a ∧ threshold mu a ≤ mu/100 ∧
      threshold mu a*b*((badCenters O scale V b (threshold mu a)).card+ell) ≤ mu*P/2 ∧
      ((badCenters O scale V b (threshold mu a)).card:ℝ) ≤ countConstant mu*P/b := by
  obtain ⟨a,ha,ha'⟩ := selected_threshold O scale V b P mu ell hb hP hmu hmu1 hell hV hsum hscale
  exact ⟨a,ha,threshold_pos hmu a,threshold_le hmu.le a,ha',
    selected_count_bound O scale V b P mu ell hb hP.le hmu hell hV hsum hscale a
      (Finset.mem_range.mp ha)⟩

end MetricKMedianRecovery.Anchoring

namespace MetricKMedianRecovery.Anchoring
open MetricKMedianRecovery.LocalSearch
variable {V : Type*} [MetricSpace V] [DecidableEq V]

noncomputable def separation (O : Finset V) (i : V) : ℝ := connection (O.erase i) i
noncomputable def cluster (D : Finset V) (assign : V → V) (i : V) : Finset V :=
  D.filter (fun p => assign p = i)
noncomputable def clusterWeight (D S : Finset V) (assign : V → V) (i : V) : ℝ :=
  ∑ p ∈ cluster D assign i, (connection S p + dist p i)
noncomputable def ballFacilities (O S : Finset V) (i : V) : Finset V :=
  S.filter (fun s => dist i s < separation O i/4)

lemma separation_le {O : Finset V} {i j : V} (hj : j ∈ O) (hji : j ≠ i) :
    separation O i ≤ dist i j := connection_le (Finset.mem_erase.mpr ⟨hji,hj⟩)

lemma separation_pos (O : Finset V) (hO : 2 ≤ O.card) (i : V) : 0 < separation O i := by
  obtain ⟨j,hj,k,hk,hjk⟩ := Finset.one_lt_card.mp hO
  have hne : (O.erase i).Nonempty := by
    by_cases hji : j = i
    · exact ⟨k,Finset.mem_erase.mpr ⟨by intro hki; exact hjk (hji.trans hki.symm),hk⟩⟩
    · exact ⟨j,Finset.mem_erase.mpr ⟨hji,hj⟩⟩
  rw [separation,← nearest_distance (O.erase i) hne i]
  exact dist_pos.mpr (Ne.symm (Finset.mem_erase.mp (nearest_mem (O.erase i) hne i)).1)

lemma clusterWeight_nonneg (D S : Finset V) (assign : V → V) (i : V) :
    0 ≤ clusterWeight D S assign i :=
  Finset.sum_nonneg (fun p _ => add_nonneg (connection_nonneg S p) dist_nonneg)

lemma nearest_cluster_radius (D S : Finset V) (hS : S.Nonempty) (assign : V → V) (i : V) :
    ((cluster D assign i).card:ℝ)*dist i (nearest S hS i) ≤ clusterWeight D S assign i := by
  have hp (p : V) : dist i (nearest S hS i) ≤ (connection S p + dist p i) := by
    rw [nearest_distance]
    calc
      connection S i ≤ dist i (nearest S hS p) := connection_le (nearest_mem S hS p)
      _ ≤ dist i p+dist p (nearest S hS p) := dist_triangle _ _ _
      _ = _ := by rw [nearest_distance,dist_comm i p]; ring
  simpa only [clusterWeight,Finset.sum_const,nsmul_eq_mul] using
    (Finset.sum_le_sum (s := cluster D assign i) (fun p _ => hp p))

lemma good_radius_bound (D O S : Finset V) (hS : S.Nonempty) (assign : V → V)
    (i : V) (b t : ℝ) (hb : 0 < b) (ht : 0 ≤ t)
    (hscale : b ≤ ((cluster D assign i).card:ℝ)*separation O i)
    (hweight : clusterWeight D S assign i ≤ t*b) :
    0 < (cluster D assign i).card ∧ dist i (nearest S hS i) ≤ t*separation O i := by
  have hn : 0 < (cluster D assign i).card := by
    by_contra h
    have hz : (cluster D assign i).card = 0 := by omega
    simp only [hz,Nat.cast_zero,zero_mul] at hscale
    linarith
  have hnr : (0:ℝ) < (cluster D assign i).card := by exact_mod_cast hn
  refine ⟨hn,?_⟩
  have hh := nearest_cluster_radius D S hS assign i
  have hh2 := mul_le_mul_of_nonneg_left hscale ht
  nlinarith

lemma ballFacilities_disjoint (O S : Finset V) {i j : V} (hi : i ∈ O) (hj : j ∈ O)
    (hij : i ≠ j) : Disjoint (ballFacilities O S i) (ballFacilities O S j) := by
  apply Finset.disjoint_left.mpr
  intro s his hjs
  have his' := (Finset.mem_filter.mp his).2
  have hjs' := (Finset.mem_filter.mp hjs).2
  have hsi := separation_le hj (Ne.symm hij)
  have hsj := separation_le hi hij
  have htri := dist_triangle i s j
  rw [dist_comm s j] at htri
  rw [dist_comm j i] at hsj
  linarith [dist_nonneg (x := i) (y := j)]

lemma proxy_in_ball (O S : Finset V) (hO : 2 ≤ O.card) (hS : S.Nonempty)
    (i : V) (t : ℝ) (ht : t ≤ 1/100)
    (hr : dist i (nearest S hS i) ≤ t*separation O i) :
    nearest S hS i ∈ ballFacilities O S i := by
  refine Finset.mem_filter.mpr ⟨nearest_mem S hS i,?_⟩
  have hp := separation_pos O hO i
  nlinarith

lemma proxies_injective (O S G : Finset V) (hGO : G ⊆ O) (hS : S.Nonempty)
    (hball : ∀ i ∈ G, nearest S hS i ∈ ballFacilities O S i) :
    Set.InjOn (nearest S hS) G := by
  intro i hi j hj he
  by_contra hij
  exact Finset.disjoint_left.mp (ballFacilities_disjoint O S (hGO hi) (hGO hj) hij)
    (hball i hi) (he ▸ hball j hj)

omit [MetricSpace V] in

lemma crowded_card_bound {I : Type*} [DecidableEq I] (G : Finset I) (S : Finset V)
    (boxes : I → Finset V) (hsub : ∀ i ∈ G, boxes i ⊆ S)
    (hne : ∀ i ∈ G, (boxes i).Nonempty) (hd : (G : Set I).PairwiseDisjoint boxes) :
    G.card+(G.filter (fun i => 2 ≤ (boxes i).card)).card ≤ S.card := by
  have hsum : G.card+(G.filter (fun i => 2 ≤ (boxes i).card)).card ≤
      ∑ i ∈ G, (boxes i).card := by
    have he : (G.filter (fun i => 2 ≤ (boxes i).card)).card =
        ∑ i ∈ G, if 2 ≤ (boxes i).card then 1 else 0 := by
      rw [← Finset.sum_filter]; simp
    rw [he,Finset.card_eq_sum_ones,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have hc := Finset.card_pos.mpr (hne i hi)
    split_ifs <;> omega
  calc
    _ ≤ ∑ i ∈ G, (boxes i).card := hsum
    _ = (G.biUnion boxes).card := (Finset.card_biUnion hd).symm
    _ ≤ S.card := Finset.card_le_card (by
      intro s hs
      obtain ⟨i,hi,hs⟩ := Finset.mem_biUnion.mp hs
      exact hsub i hi hs)

end MetricKMedianRecovery.Anchoring

end OAI
