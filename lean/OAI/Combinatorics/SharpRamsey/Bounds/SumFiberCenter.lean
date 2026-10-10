import Mathlib
import OAI.Combinatorics.SharpRamsey.Construction.FiniteStreamTail
import OAI.Combinatorics.SharpRamsey.Bounds.Upper

namespace OAI

/-! The off-diagonal Ramsey upper bound. -/

section
open scoped BigOperators Classical
open Finset
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.TriangleFree
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
theorem sum_fiber_center (htri : G.CliqueFree 3) {x : V} {J : Finset V}
    (hJ : Admissible G x J) : ∑ S ∈ fiber G x J, (if x ∈ S then (1:ℝ) else 0) = 1 := by
  rw [sum_fiber G htri hJ]
  simp only [mem_insert_self, ite_true]
  have hx : ∀ K ∈ (available G x J).powerset, x ∉ J ∪ K := by
    intro K hK h
    rcases mem_union.mp h with hx | hx
    · exact admissible_not_center G hJ hx
    · exact center_not_available G x J (mem_powerset.mp hK hx)
  rw [sum_eq_zero (fun K hK => ite_eq_right (hx K hK)), add_zero]

theorem twice_sum_fiber_neighbors (htri : G.CliqueFree 3) {x : V} {J : Finset V}
    (hJ : Admissible G x J) :
    2 * (∑ S ∈ fiber G x J, ((S ∩ G.neighborFinset x).card : ℝ)) =
      (available G x J).card * (2:ℝ)^(available G x J).card := by
  rw [sum_fiber G htri hJ, center_neighbor_inter G hJ, card_empty, Nat.cast_zero,
    zero_add]
  have he : ∑ K ∈ (available G x J).powerset,
      (((J ∪ K) ∩ G.neighborFinset x).card : ℝ) =
      ∑ K ∈ (available G x J).powerset, (K.card : ℝ) := by
    apply sum_congr rfl
    intro K hK
    rw [extend_neighbor_inter G hJ (mem_powerset.mp hK)]
  rw [he]
  exact twice_sum_powerset_card (available G x J)

noncomputable def Z (x : V) (S : Finset V) : ℕ :=
  (available G x (outside G x S)).card

theorem fiber_empty_of_not_admissible {x : V} {J : Finset V}
    (hJ : ¬Admissible G x J) : fiber G x J = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro S hS
  obtain ⟨hS, hout⟩ := mem_filter.mp hS
  exact hJ (hout ▸ admissible_outside G x hS)

theorem sum_fiber_Z (x : V) (J : Finset V) (f : ℕ → ℝ) :
    ∑ S ∈ fiber G x J, f (Z G x S) = (fiber G x J).card * f (available G x J).card := by
  calc
    _ = ∑ _S ∈ fiber G x J, f (available G x J).card := by
      apply sum_congr rfl
      intro S hS
      simp only [Z, (mem_filter.mp hS).2]
    _ = _ := by simp

theorem exp_neg_log_two_mul (z : ℕ) :
    Real.exp (-(Real.log 2) * z) = ((2:ℝ)^z)⁻¹ := by
  rw [show -(Real.log 2) * z = -((z:ℝ) * Real.log 2) by ring,
    Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num)]

theorem half_sum_exp_le_center (htri : G.CliqueFree 3) (x : V) :
    (∑ S ∈ independentSets G, Real.exp (-Real.log 2 * Z G x S)) / 2 ≤
      ∑ S ∈ independentSets G, (if x ∈ S then (1:ℝ) else 0) := by
  rw [← Finset.sum_fiberwise (independentSets G) (outside G x)
       (fun S => Real.exp (-Real.log 2 * Z G x S)),
    ← Finset.sum_fiberwise (independentSets G) (outside G x)
       (fun S => if x ∈ S then (1:ℝ) else 0), sum_div]
  apply sum_le_sum
  intro J _
  change (∑ S ∈ fiber G x J, _) / 2 ≤ ∑ S ∈ fiber G x J, _
  by_cases hJ : Admissible G x J
  · rw [sum_fiber_Z G x J (fun z => Real.exp (-Real.log 2 * z)),
      card_fiber G htri hJ, sum_fiber_center G htri hJ, exp_neg_log_two_mul]
    push_cast
    have hp : (1:ℝ) ≤ 2^(available G x J).card := one_le_pow₀ (by norm_num)
    have hpp : (0:ℝ) < 2^(available G x J).card := by positivity
    field_simp
    nlinarith
  · rw [fiber_empty_of_not_admissible G hJ]
    simp

theorem sum_Z_le_four_neighbors (htri : G.CliqueFree 3) (x : V) :
    (∑ S ∈ independentSets G, (Z G x S : ℝ)) ≤
      4 * ∑ S ∈ independentSets G, ((S ∩ G.neighborFinset x).card : ℝ) := by
  rw [← Finset.sum_fiberwise (independentSets G) (outside G x)
       (fun S => (Z G x S : ℝ)),
    ← Finset.sum_fiberwise (independentSets G) (outside G x)
       (fun S => ((S ∩ G.neighborFinset x).card : ℝ)), mul_sum]
  apply sum_le_sum
  intro J _
  change (∑ S ∈ fiber G x J, _) ≤ 4 * ∑ S ∈ fiber G x J, _
  by_cases hJ : Admissible G x J
  · rw [sum_fiber_Z G x J (fun z => (z:ℝ)), card_fiber G htri hJ]
    have hn := twice_sum_fiber_neighbors G htri hJ
    have hp : (1:ℝ) ≤ 2^(available G x J).card := one_le_pow₀ (by norm_num)
    have hz : (0:ℝ) ≤ (available G x J).card := by positivity
    push_cast
    nlinarith
  · rw [fiber_empty_of_not_admissible G hJ]
    simp

theorem sum_center (S : Finset V) :
    (∑ x : V, if x ∈ S then (1:ℝ) else 0) = S.card := by
  simp

theorem sum_neighbors (S : Finset V) :
    (∑ x : V, ((S ∩ G.neighborFinset x).card : ℝ)) =
      ∑ v ∈ S, (G.degree v : ℝ) := by
  calc
    _ = ∑ x : V, ∑ v ∈ S, (if G.Adj x v then (1:ℝ) else 0) := by
      apply sum_congr rfl
      intro x _
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul, mul_one]
      congr 2
      ext v
      simp []
    _ = ∑ v ∈ S, ∑ x : V, (if G.Adj x v then (1:ℝ) else 0) := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro v _
      simp_rw [G.adj_comm]
      rw [← sum_filter]
      have he : univ.filter (G.Adj v) = G.neighborFinset v := by ext x; simp
      rw [he]
      simp

theorem exp_mean_le {α : Type*} (A : Finset α) (hA : A.Nonempty) (f : α → ℝ) :
    Real.exp ((∑ i ∈ A, f i) / A.card) ≤ (∑ i ∈ A, Real.exp (f i)) / A.card := by
  have hc : (0:ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hsum : ∑ _i ∈ A, ((A.card:ℝ)⁻¹) = 1 := by
    simp [hc.ne']
  have hj := convexOn_exp.map_sum_le (t := A) (w := fun _ => (A.card:ℝ)⁻¹)
    (p := f) (fun _ _ => inv_nonneg.mpr hc.le) hsum (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul, ← mul_sum] at hj
  simpa only [div_eq_mul_inv, mul_comm] using hj

theorem occupation_lower_bound {D μ : ℝ} (hD : 1 ≤ D) (hμ : 0 ≤ μ)
    (hkey : Real.exp (-4 * D * μ * Real.log 2) ≤ 2 * μ) :
    Real.log (D+1) / (8 * (D+1)) ≤ μ := by
  by_contra! hbad
  have hu : 0 < D + 1 := by linarith
  have hlog : 0 < Real.log (D+1) := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by
    convert Real.log_lt_sub_one_of_pos (x := (2:ℝ)) (by norm_num) (by norm_num) using 1 ; norm_num
  have hb : 8 * (D+1) * μ < Real.log (D+1) := by
    have := (lt_div_iff₀ (show 0 < 8*(D+1) by positivity)).mp hbad
    nlinarith
  have hDμ : 0 ≤ D * μ := mul_nonneg (by linarith) hμ
  have he : -Real.log (D+1)/2 < -4 * D * μ * Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_left hl2'.le hDμ
    nlinarith
  have hlow : Real.exp (-Real.log (D+1)/2) < 2 * μ :=
    (Real.exp_lt_exp.mpr he).trans_le hkey
  have hid : (D+1) * Real.exp (-Real.log (D+1)/2) =
      Real.exp (Real.log (D+1)/2) := by
    conv_lhs => lhs; rw [← Real.exp_log hu]
    rw [← Real.exp_add]
    congr 1
    ring
  have hupper := Real.add_one_le_exp (Real.log (D+1)/2)
  have hmul := mul_lt_mul_of_pos_left hlow (show 0 < 4*(D+1) by positivity)
  nlinarith

theorem exists_occupation (htri : G.CliqueFree 3) [Nonempty V]
    {D : ℝ} (hD : ∀ x, (G.degree x : ℝ) ≤ D) :
    ∃ μ : ℝ, 0 ≤ μ ∧ (Fintype.card V : ℝ) * μ ≤ G.indepNum ∧
      Real.exp (-4 * D * μ * Real.log 2) ≤ 2 * μ := by
  let A := independentSets G
  let Ω := (univ : Finset V) ×ˢ A
  let M : ℝ := ∑ S ∈ A, (S.card : ℝ)
  let m : ℝ := (Fintype.card V : ℝ) * A.card
  have hn : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have ha : (0:ℝ) < A.card := by exact_mod_cast (independentSets_nonempty G).card_pos
  have hm : 0 < m := mul_pos hn ha
  have hmcard : (Ω.card:ℝ) = m := by simp [Ω, m]
  have hM : 0 ≤ M := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have he : (∑ a ∈ Ω, Real.exp (-Real.log 2 * Z G a.1 a.2)) ≤ 2*M := by
    have hh := sum_le_sum (s := (univ : Finset V))
      (fun x _ => half_sum_exp_le_center G htri x)
    rw [← sum_div] at hh
    have hcenter : (∑ x : V, ∑ S ∈ independentSets G,
        (if x ∈ S then (1:ℝ) else 0)) = M := by
      rw [sum_comm]
      simp only [sum_center]
      rfl
    rw [hcenter] at hh
    unfold Ω
    rw [sum_product]
    dsimp only
    change (∑ x : V, ∑ S ∈ independentSets G, _) ≤ 2*M
    linarith
  have hz : (∑ a ∈ Ω, (Z G a.1 a.2 : ℝ)) ≤ 4*D*M := by
    have hh := sum_le_sum (s := (univ : Finset V))
      (fun x _ => sum_Z_le_four_neighbors G htri x)
    rw [← mul_sum] at hh
    have hneigh : (∑ x : V, ∑ S ∈ independentSets G,
        ((S ∩ G.neighborFinset x).card:ℝ)) =
        ∑ S ∈ independentSets G, ∑ v ∈ S, (G.degree v:ℝ) := by
      rw [sum_comm]
      simp_rw [sum_neighbors]
    rw [hneigh] at hh
    have hd : (∑ S ∈ independentSets G, ∑ v ∈ S, (G.degree v : ℝ)) ≤ D*M := by
      calc
        _ ≤ ∑ S ∈ independentSets G, ∑ _v ∈ S, D := by
          apply sum_le_sum
          intro S _
          exact sum_le_sum (fun v _ => hD v)
        _ = D*M := by simp [M, A, mul_sum, mul_comm]
    unfold Ω
    rw [sum_product]
    dsimp only
    change (∑ x : V, ∑ S ∈ independentSets G, _) ≤ 4*D*M
    linarith
  have hind : M ≤ (A.card:ℝ) * G.indepNum := by
    calc
      M ≤ ∑ _S ∈ A, (G.indepNum : ℝ) := by
        apply sum_le_sum
        intro S hS
        exact_mod_cast (mem_independentSets G S |>.mp hS).card_le_indepNum
      _ = _ := by simp
  refine ⟨M/m, div_nonneg hM hm.le, ?_, ?_⟩
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ hm).mpr
    dsimp only [m]
    nlinarith [mul_le_mul_of_nonneg_left hind hn.le]
  · have hΩ : Ω.Nonempty := nonempty_product.mpr ⟨univ_nonempty, independentSets_nonempty G⟩
    have hj := exp_mean_le Ω hΩ (fun a => -Real.log 2 * Z G a.1 a.2)
    rw [hmcard, ← mul_sum] at hj
    have hl : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    have hexp : Real.exp (-4*D*(M/m)*Real.log 2) ≤
        Real.exp (-Real.log 2 * (∑ a ∈ Ω, (Z G a.1 a.2:ℝ)) / m) := by
      apply Real.exp_le_exp.mpr
      rw [show -4*D*(M/m)*Real.log 2 = (-4*D*M*Real.log 2)/m by ring]
      apply (div_le_div_iff_of_pos_right hm).mpr
      have hh := mul_le_mul_of_nonpos_left hz (neg_nonpos.mpr hl)
      convert hh using 1 ; ring
    have hfinal := hexp.trans hj
    have hdiv := div_le_div_of_nonneg_right he hm.le
    calc
      _ ≤ (∑ a ∈ Ω, Real.exp (-Real.log 2 * Z G a.1 a.2))/m := hfinal
      _ ≤ 2*M/m := hdiv
      _ = 2*(M/m) := by ring

theorem indepNum_lower_bound (htri : G.CliqueFree 3) [Nonempty V]
    {D : ℝ} (hD : 1 ≤ D) (hdeg : ∀ x, (G.degree x : ℝ) ≤ D) :
    (Fintype.card V : ℝ) * Real.log (D+1) / (8*(D+1)) ≤ G.indepNum := by
  obtain ⟨μ, hμ, hind, hkey⟩ := exists_occupation G htri hdeg
  have hb := occupation_lower_bound hD hμ hkey
  have hh := mul_le_mul_of_nonneg_left hb
    (show (0:ℝ) ≤ Fintype.card V by positivity)
  rw [← mul_div_assoc] at hh
  exact hh.trans hind

end SharpLogRamsey.TriangleFree

open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Sampling
variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V)

noncomputable def internalDegree (S : Finset V) (x : V) : ℕ :=
  (S.filter (G.Adj x)).card

noncomputable def degreeMass (S : Finset V) : ℕ := ∑ x ∈ S, internalDegree G S x

theorem degreeMass_pair_sum (S : Finset V) :
    (degreeMass G S : ℝ) = ∑ x : V, ∑ y : V,
      if G.Adj x y then (if ({x,y} : Finset V) ⊆ S then 1 else 0) else 0 := by
  have hi (x : V) : (∑ y : V,
      if G.Adj x y then (if ({x,y} : Finset V) ⊆ S then (1:ℝ) else 0) else 0) =
      if x ∈ S then (internalDegree G S x : ℝ) else 0 := by
    by_cases hx : x ∈ S
    · rw [ite_eq_left hx]
      have he : S = univ.filter (· ∈ S) := by simp
      change _ = ((S.filter (G.Adj x)).card : ℝ)
      conv_rhs => rw [he]
      rw [filter_filter, ← sum_boole]
      apply sum_congr rfl
      intro y _
      simp only [insert_subset_iff, singleton_subset_iff, hx, true_and]
      by_cases h : G.Adj x y <;> by_cases hy : y ∈ S <;> simp [h, hy]
    · simp [insert_subset_iff, singleton_subset_iff, hx]
  simp_rw [hi]
  rw [← sum_filter]
  simp [degreeMass, Nat.cast_sum]

theorem degreeMass_moment (p : ℝ) :
    (∑ f : V → Bool, weight p f * degreeMass G (selected f)) =
      p^2 * ∑ x : V, (G.degree x : ℝ) := by
  simp_rw [degreeMass_pair_sum, mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ x : V, ∑ y : V, if G.Adj x y then p^2 else 0 := by
      apply sum_congr rfl
      intro x _
      rw [sum_comm]
      apply sum_congr rfl
      intro y _
      by_cases h : G.Adj x y
      · simp only [ite_eq_left h]
        rw [containment_moment]
        simp [h.ne]
      · simp [h]
    _ = p^2 * ∑ x : V, (G.degree x : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      rw [← sum_filter]
      simp [← G.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_def,
        mul_comm]
    _ = _ := by simp [mul_sum]

omit [Fintype V] in

theorem exists_avoid_family (F : Finset (Finset V))
    (hF : ∀ A ∈ F, A.Nonempty) (S : Finset V) :
    ∃ U ⊆ S, S.card ≤ U.card + F.card ∧ ∀ A ∈ F, ¬ A ⊆ U := by
  induction F using Finset.induction_on generalizing S with
  | empty => exact ⟨S, Subset.rfl, by simp, by simp⟩
  | @insert A F hAF ih =>
    obtain ⟨U, hUS, hUcard, hU⟩ := ih (fun B hB => hF B (mem_insert_of_mem hB)) S
    by_cases hAU : A ⊆ U
    · obtain ⟨x, hx⟩ := hF A (mem_insert_self A F)
      refine ⟨U.erase x, (erase_subset x U).trans hUS, ?_, ?_⟩
      · have he := card_erase_of_mem (hAU hx)
        rw [card_insert_of_notMem hAF]
        omega
      · intro B hB hBU
        rcases mem_insert.mp hB with rfl | hB
        · exact (notMem_erase x U) (hBU hx)
        · exact hU B hB (hBU.trans (erase_subset x U))
    · refine ⟨U, hUS, ?_, ?_⟩
      · rw [card_insert_of_notMem hAF]
        omega
      · intro B hB hBU
        rcases mem_insert.mp hB with rfl | hB
        · exact hAU hBU
        · exact hU B hB hBU

theorem prune (S : Finset V) {D : ℝ} (hD : 0 < D) :
    ∃ U ⊆ S,
      (S.card : ℝ) - degreeMass G S / D - count (G.cliqueFinset 3) S ≤ U.card ∧
      (∀ x ∈ U, (internalDegree G U x : ℝ) ≤ D) ∧
      (G.induce (U : Set V)).CliqueFree 3 := by
  let bad := S.filter (fun x => D < (internalDegree G S x : ℝ))
  have hbad : (bad.card : ℝ) ≤ degreeMass G S / D := by
    apply (le_div_iff₀ hD).mpr
    calc
      (bad.card : ℝ) * D = ∑ _x ∈ bad, D := by simp
      _ ≤ ∑ x ∈ bad, (internalDegree G S x : ℝ) := by
        exact sum_le_sum (fun x hx => (mem_filter.mp hx).2.le)
      _ ≤ ∑ x ∈ S, (internalDegree G S x : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
      _ = degreeMass G S := by simp [degreeMass, Nat.cast_sum]
  let T := S \ bad
  let F := (G.cliqueFinset 3).filter (· ⊆ S)
  have hF : ∀ A ∈ F, A.Nonempty := by
    intro A hA
    have ha := (SimpleGraph.mem_cliqueFinset_iff.mp (mem_filter.mp hA).1).2
    exact card_pos.mp (by omega)
  obtain ⟨U, hUT, hcard, havoid⟩ := exists_avoid_family F hF T
  have hUS : U ⊆ S := hUT.trans sdiff_subset
  refine ⟨U, hUS, ?_, ?_, ?_⟩
  · have hc : (S.card : ℝ) ≤ T.card + bad.card := by
      exact_mod_cast card_le_card_sdiff_add_card
    have hu : (T.card : ℝ) ≤ U.card + F.card := by exact_mod_cast hcard
    change (S.card : ℝ) - degreeMass G S / D - F.card ≤ _
    linarith
  · intro x hx
    have hxT := mem_sdiff.mp (hUT hx)
    have hd : (internalDegree G S x : ℝ) ≤ D := by
      by_contra! hh
      exact hxT.2 (mem_filter.mpr ⟨hxT.1, hh⟩)
    exact (Nat.cast_le.mpr (card_le_card (filter_subset_filter _ hUS))).trans hd
  · rw [G.cliqueFree_induce_iff]
    intro A hAU hA
    have hAF : A ∈ F := mem_filter.mpr
      ⟨SimpleGraph.mem_cliqueFinset_iff.mpr hA, (show A ⊆ U from hAU).trans hUS⟩
    exact havoid A hAF hAU

omit [Fintype V] [DecidableEq V] in
theorem induced_degree (U : Finset V) (x : (U : Set V)) :
    (G.induce (U : Set V)).degree x = internalDegree G U x := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  let e : ((G.induce (U : Set V)).neighborSet x) ≃
      {y : V // y ∈ U.filter (G.Adj x)} :=
    { toFun := fun y => ⟨y.1, mem_filter.mpr ⟨y.1.2, y.2⟩⟩
      invFun := fun y => ⟨⟨y.1, (mem_filter.mp y.2).1⟩, (mem_filter.mp y.2).2⟩
      left_inv := by intro y; rfl
      right_inv := by intro y; rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe (U.filter (G.Adj x)))

theorem sample_prune {p D : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hD : 0 < D) :
    ∃ U : Finset V,
      p * Fintype.card V - p^2 * (∑ x, (G.degree x : ℝ)) / D -
        p^3 * (G.cliqueFinset 3).card ≤ U.card ∧
      (∀ x : (U : Set V), ((G.induce (U : Set V)).degree x : ℝ) ≤ D) ∧
      (G.induce (U : Set V)).CliqueFree 3 := by
  let X (f : V → Bool) : ℝ := (selected f).card -
    degreeMass G (selected f) / D - count (G.cliqueFinset 3) (selected f)
  have hmean : (∑ f, weight p f * X f) =
      p * Fintype.card V - p^2 * (∑ x, (G.degree x : ℝ)) / D -
        p^3 * (G.cliqueFinset 3).card := by
    simp only [X, mul_sub, ← mul_div_assoc, sum_sub_distrib, ← sum_div]
    rw [size_moment, degreeMass_moment, family_moment]
    intro A hA
    exact (SimpleGraph.mem_cliqueFinset_iff.mp hA).2
  obtain ⟨f, hf⟩ := exists_ge_mean hp hp1 X
  rw [hmean] at hf
  obtain ⟨U, _hUS, hU, hdeg, htri⟩ := prune G (selected f) hD
  refine ⟨U, hf.trans hU, ?_, htri⟩
  intro x
  rw [induced_degree]
  exact hdeg x x.2

theorem triangle_count_le {h m : ℕ} (hdeg : ∀ x, G.degree x ≤ h)
    (hcommon : ∀ x y, G.Adj x y → Fintype.card (G.commonNeighbors x y) ≤ m) :
    (G.cliqueFinset 3).card ≤ Fintype.card V * h * m := by
  let T := Σ x : V, Σ y : G.neighborSet x, G.commonNeighbors x y
  have hex (A : {A // A ∈ G.cliqueFinset 3}) :
      ∃ t : T, A.1 = {t.1, t.2.1.1, t.2.2.1} := by
    obtain ⟨x,y,z,hxy,hxz,hyz,hA⟩ := SimpleGraph.is3Clique_iff.mp
      (SimpleGraph.mem_cliqueFinset_iff.mp A.2)
    exact ⟨⟨x, ⟨y,hxy⟩, ⟨z,hxz,hyz⟩⟩, hA⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro A B hAB
    apply Subtype.ext
    rw [hf A, hf B, hAB]
  calc
    (G.cliqueFinset 3).card = Fintype.card {A // A ∈ G.cliqueFinset 3} := (Fintype.card_coe _).symm
    _ ≤ Fintype.card T := Fintype.card_le_of_injective f hinj
    _ = ∑ x : V, ∑ y : G.neighborSet x, Fintype.card (G.commonNeighbors x y) := by
      simp [T, Fintype.card_sigma]
    _ ≤ ∑ x : V, ∑ _y : G.neighborSet x, m := by
      exact sum_le_sum (fun x _ => sum_le_sum (fun y _ => hcommon x y y.2))
    _ ≤ ∑ _x : V, h*m := by
      apply sum_le_sum
      intro x _
      simpa [G.card_neighborSet_eq_degree] using Nat.mul_le_mul_right m (hdeg x)
    _ = Fintype.card V * h * m := by simp [mul_assoc]

end SharpLogRamsey.Sampling

open scoped BigOperators
namespace SharpLogRamsey.Upper

end SharpLogRamsey.Upper
end

end OAI
