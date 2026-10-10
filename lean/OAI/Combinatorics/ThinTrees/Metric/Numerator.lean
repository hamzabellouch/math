import Mathlib
import OAI.Combinatorics.ThinTrees.Metric.ScaleCharging
import OAI.Combinatorics.ThinTrees.Metric.SpectralMetricBridge

namespace OAI

/-! Metric numerator. -/

section

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (truncationBins truncationGain truncationGain_pos)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open scoped Classical
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord]
  {H : Hierarchy n} {G : MultiGraph n m} {X : Fin n → Doubled Coord → ℝ}

omit [PseudoMetricSpace Coord] in
lemma diagonal_sq_le (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ normDistance (X u) (X v)) (e : Fin m) :
    ((Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤ normDistance (X (G.left e)) (X (G.right e)) := by
  have hh := pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (Y (G.left e)-Y (G.right e)) e) 2
  have he : ((Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤ ‖Y (G.left e)-Y (G.right e)‖^2 := by
    simpa only [Real.norm_eq_abs,sq_abs] using hh
  exact he.trans (hcontract _ _)

lemma positive_bad_bound {q L R : ℕ} (hq : 0 < q) (hL : 0 < L) (hR : 0 < R)
    (hk : G.EdgeConnected q) (hX : ∀v, isProfile (X v))
    (hconn : LocallyConnectedReal H G q)
    (T : Finset (Finset (Fin n))) (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    {α ε ρ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (he : 0 < ε) (he1 : ε < 1/3)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ normDistance (X u) (X v))
    (hpositive : ∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e)
    (hpos : ∀t ∈ T, 0 < ∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)
    (hbad : ∀t ∈ T, α*((parentBoundary H G t).card : ℝ)*
      (∑e ∈ parentBoundary H G t, normDistance (X (G.left e)) (X (G.right e))) ≤
      (∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hsmall : (α*truncationGain α/32)^ε ≤ 1/(1728*(1024/ε^2)))
    (hassign : (6144:ℝ)/q ≤ (α*truncationGain α/32)^(1+2*ε))
    (hratio : ∀t ∈ T, (q:ℝ)*ρ*((G.cut univ t).card : ℝ) ≤ (parentBoundary H G t).card)
    (hlogL : Real.logb 2 (16/(α*truncationGain α))+1 < L)
    (hlogR : Real.logb 2 (24/(ρ*(α*truncationGain α/32)^2)) < R) :
    let γ := truncationGain α
    let s := α*γ/32
    let N := ∑t ∈ T, (∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
      ((parentBoundary H G t).card : ℝ)
    ((q:ℝ)/8192)*(s^ε/(6912*(1024/ε^2)))*(γ*N/(L:ℝ)) ≤
      2*R*(∑e : Fin m, normDistance (X (G.left e)) (X (G.right e))) := by
  let γ := truncationGain α
  let s := α*γ/32
  let a : Fin m → ℝ := fun e => (Y (G.left e)-Y (G.right e)).ofLp e
  let d : Fin m → ℝ := fun e => normDistance (X (G.left e)) (X (G.right e))
  let O := parentBoundary H G
  have hγ : 0 < γ := truncationGain_pos α
  have hs : 0 < s := by dsimp [s]; positivity
  have hex : ∀t : Finset (Fin n), ∃B : Finset (Fin m), ∃i : ℤ, ∃o : Fin L,
      t ∈ T → B.Nonempty ∧ B ⊆ O t ∧ γ*(∑e ∈ O t, a e)^2 ≤ (∑e ∈ B, a e)^2 ∧
      (∀e ∈ B, 2^(i:ℝ) ≤ (a e)^2) ∧
      (∀e ∈ B, (a e)^2 ≤ 4*2^(i:ℝ)) ∧
      (∀e ∈ B, 2^((i:ℝ)+o.val) ≤ d e) ∧
      (∀e ∈ B, d e ≤ 4*2^((i:ℝ)+o.val)) := by
    intro t
    by_cases ht : t ∈ T
    · have hOn : (O t).Nonempty := by
        by_contra hh
        have heq : O t=∅ := not_nonempty_iff_eq_empty.mp hh
        have hp := hpos t ht
        change 0 < ∑e ∈ O t, a e at hp
        simp only [heq,sum_empty,lt_self_iff_false] at hp
      obtain ⟨B,i,o,hB⟩ := Truncation.scaled_subset (O t) a d hα hα1 hOn
        (fun e _ => hpositive e) (fun e _ => diagonal_sq_le Y hcontract e) (hpos t ht) (hbad t ht) hlogL
      exact ⟨B,i,o,fun _ => hB⟩
    · exact ⟨∅,0,⟨0,hL⟩,fun hh => (ht hh).elim⟩
  choose F idx off hf using hex
  have hh := homogeneous_scale_bound hq hL hR hk hX hconn T F idx off Y hT hroot
    (fun t ht => (hf t ht).2.1) (fun t ht => (hf t ht).1) hα hγ he he1 hρ hρsmall
    hcontract hpositive (fun t ht => (hf t ht).2.2.2.1)
    (fun t ht => (hf t ht).2.2.2.2.1) (fun t ht => (hf t ht).2.2.2.2.2.1)
    (fun t ht => (hf t ht).2.2.2.2.2.2) hbad (fun t ht => (hf t ht).2.2.1)
    hsmall hassign hratio hlogR
  have hsum : γ*(∑t ∈ T, (∑e ∈ O t, a e)^2/((O t).card:ℝ)) ≤
      ∑t ∈ T, (∑e ∈ F t, a e)^2/((O t).card:ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro t ht
    rw [←mul_div_assoc]
    exact div_le_div_of_nonneg_right (hf t ht).2.2.1 (Nat.cast_nonneg _)
  have hgain := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg L : (0:ℝ)≤L)
  have hc : 0 ≤ ((q:ℝ)/8192)*(s^ε/(6912*(1024/ε^2))) := by positivity
  exact (mul_le_mul_of_nonneg_left hgain hc).trans hh
lemma weighted_boundary_sum (M : Finset (Finset (Fin n)))
    (hM : M ⊆ H.nodes) (hroot : ∀t ∈ M, t ≠ univ)
    (d : Fin m → ℝ) (hd : ∀e, 0 ≤ d e) :
    (∑t ∈ M, ∑e ∈ parentBoundary H G t, d e) ≤ 2*∑e, d e := by
  have heq : (∑t ∈ M, ∑e ∈ parentBoundary H G t, d e) =
      ∑e, ((M.filter (fun t => e ∈ parentBoundary H G t)).card : ℝ)*d e := by
    calc
      _ = ∑t ∈ M, ∑e : Fin m, if e ∈ parentBoundary H G t then d e else 0 := by
        apply sum_congr rfl
        intro t ht
        rw [←sum_filter]
        simp
      _ = ∑e : Fin m, ∑t ∈ M, if e ∈ parentBoundary H G t then d e else 0 := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro e he
        rw [←sum_filter, sum_const,nsmul_eq_mul]
  rw [heq,mul_sum]
  apply sum_le_sum
  intro e _
  apply mul_le_mul_of_nonneg_right _ (hd e)
  exact_mod_cast H.parentBoundary_multiplicity G M hM hroot e

lemma hierarchy_numerator_bound {q L R : ℕ} (hq : 0 < q) (hL : 0 < L) (hR : 0 < R)
    (hk : G.EdgeConnected q) (hX : ∀v, isProfile (X v))
    (hconn : LocallyConnectedReal H G q)
    (M : Finset (Finset (Fin n))) (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hM : M ⊆ H.nodes) (hroot : ∀t ∈ M, t ≠ univ)
    {α ε ρ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (he : 0 < ε) (he1 : ε < 1/3)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ normDistance (X u) (X v))
    (hpositive : ∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e)
    (hsmall : (α*truncationGain α/32)^ε ≤ 1/(1728*(1024/ε^2)))
    (hassign : (6144:ℝ)/q ≤ (α*truncationGain α/32)^(1+2*ε))
    (hratio : ∀t ∈ M, (q:ℝ)*ρ*((G.cut univ t).card : ℝ) ≤ (parentBoundary H G t).card)
    (hlogL : Real.logb 2 (16/(α*truncationGain α))+1 < L)
    (hlogR : Real.logb 2 (24/(ρ*(α*truncationGain α/32)^2)) < R) :
    let γ := truncationGain α
    let s := α*γ/32
    (∑t ∈ M, (∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
      ((parentBoundary H G t).card : ℝ)) ≤
      (2*α+2*(R:ℝ)*(L:ℝ)/(((q:ℝ)/8192)*(s^ε/(6912*(1024/ε^2)))*γ))*
        (∑e : Fin m, normDistance (X (G.left e)) (X (G.right e))) := by
  let O := parentBoundary H G
  let a : Fin m → ℝ := fun e => (Y (G.left e)-Y (G.right e)).ofLp e
  let d : Fin m → ℝ := fun e => normDistance (X (G.left e)) (X (G.right e))
  let N : Finset (Fin n) → ℝ := fun t => (∑e ∈ O t, a e)^2/((O t).card:ℝ)
  let T := M.filter (fun t => 0 < ∑e ∈ O t, a e ∧
    α*((O t).card:ℝ)*(∑e ∈ O t, d e) ≤ (∑e ∈ O t, a e)^2)
  have hTM : T ⊆ M := filter_subset _ _
  have hgood : ∀t ∈ M\T, N t ≤ α*∑e ∈ O t, d e := by
    intro t ht
    have htM := (mem_sdiff.mp ht).1
    have htT := (mem_sdiff.mp ht).2
    have hd : 0 ≤ α*∑e ∈ O t, d e := mul_nonneg hα.le (sum_nonneg (fun e _ => normDistance_nonneg _ _))
    by_cases hp : 0 < ∑e ∈ O t, a e
    · have hn : ¬α*((O t).card:ℝ)*(∑e ∈ O t, d e) ≤ (∑e ∈ O t, a e)^2 := by
        intro hh; exact htT (mem_filter.mpr ⟨htM,hp,hh⟩)
      have hc : 0 < ((O t).card:ℝ) := by
        by_contra h
        have hz : (O t).card=0 := by exact_mod_cast le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
        have hz' : O t=∅ := card_eq_zero.mp hz
        simp [hz'] at hp
      apply (div_le_iff₀ hc).mpr
      nlinarith only [lt_of_not_ge hn]
    · have hz : ∑e ∈ O t, a e=0 := le_antisymm (le_of_not_gt hp) (sum_nonneg (fun e _ => hpositive e))
      simpa [N,hz] using hd
  have hg : (∑t ∈ M\T, N t) ≤ 2*α*∑e, d e := by
    calc
      (∑t ∈ M\T, N t) ≤ ∑t ∈ M\T, α*∑e ∈ O t, d e := sum_le_sum hgood
      _ = α*∑t ∈ M\T, ∑e ∈ O t, d e := (mul_sum _ _ _).symm
      _ ≤ α*(2*∑e, d e) := mul_le_mul_of_nonneg_left
        (weighted_boundary_sum (M\T) (fun _ ht => hM (mem_sdiff.mp ht).1)
          (fun t ht => hroot t (mem_sdiff.mp ht).1) d (fun _ => normDistance_nonneg _ _)) hα.le
      _ = 2*α*∑e, d e := by ring
  have hb := positive_bad_bound hq hL hR hk hX hconn T Y (hTM.trans hM)
    (fun t ht => hroot t (hTM ht)) hα hα1 he he1 hρ hρsmall hcontract hpositive
    (fun t ht => (mem_filter.mp ht).2.1) (fun t ht => (mem_filter.mp ht).2.2)
    hsmall hassign (fun t ht => hratio t (hTM ht)) hlogL hlogR
  let γ := truncationGain α
  let s := α*γ/32
  let c := ((q:ℝ)/8192)*(s^ε/(6912*(1024/ε^2)))*γ
  have hγ : 0 < γ := truncationGain_pos α
  have hs : 0 < s := by dsimp [s]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hL' : 0 < (L:ℝ) := Nat.cast_pos.mpr hL
  have hb' : (∑t ∈ T, N t) ≤ (2*(R:ℝ)*(L:ℝ)/c)*(∑e, d e) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    have hh := (div_le_iff₀ hL').mp (show c*(∑t ∈ T, N t)/L ≤ 2*(R:ℝ)*∑e, d e by
      convert hb using 1 ; dsimp [c,N,γ,s,O,a,d] ; ring)
    nlinarith only [hh]
  change (∑t ∈ M, N t) ≤ (2*α+2*(R:ℝ)*(L:ℝ)/c)*(∑e, d e)
  rw [←sum_sdiff hTM]
  nlinarith only [hg,hb']
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (truncationGain shortcutCoefficient)
open AssignedGeometry CompactGeometry
open scoped Classical
variable {n m : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma squared_euclidean_numerator_bound {q L R : ℕ} (hq : 0 < q)
    (hL : 0 < L) (hR : 0 < R) (hk : G.EdgeConnected q)
    (hconn : LocallyConnectedReal H G q)
    (M : Finset (Finset (Fin n))) (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hM : M ⊆ H.nodes) (hroot : ∀t ∈ M, t ≠ univ)
    {α ε ρ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (he : 0 < ε) (he1 : ε < 1/3)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (p : Fin n → E) (ht : SquaredTriangle p)
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ ‖p u-p v‖^2)
    (hpositive : ∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e)
    (hsmall : (α*truncationGain α/32)^ε ≤ 1/(1728*(1024/ε^2)))
    (hassign : (6144:ℝ)/q ≤ (α*truncationGain α/32)^(1+2*ε))
    (hratio : ∀t ∈ M, (q:ℝ)*ρ*((G.cut univ t).card : ℝ) ≤ (parentBoundary H G t).card)
    (hlogL : Real.logb 2 (16/(α*truncationGain α))+1 < L)
    (hlogR : Real.logb 2 (24/(ρ*(α*truncationGain α/32)^2)) < R) :
    (∑t ∈ M, (∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
      ((parentBoundary H G t).card : ℝ)) ≤
      shortcutCoefficient q L R α ε * (∑e : Fin m, ‖p (G.left e)-p (G.right e)‖^2) := by
  let := squaredPseudoMetric p ht
  have hd (u v : Fin n) : dist u v = ‖p u-p v‖^2 := rfl
  have hc : ∀u v, ‖Y u-Y v‖^2 ≤ normDistance (profile (plus u)) (profile (plus v)) := by
    intro u v
    simpa only [normDistance,profile_norm_sub,dist_plus,hd] using hcontract u v
  have hh := AssignedGeometry.hierarchy_numerator_bound hq hL hR hk
    (fun v : Fin n => (show isProfile (profile (plus v)) from ⟨plus v,rfl⟩))
    hconn M Y hM hroot hα hα1 he he1 hρ hρsmall hc hpositive
    hsmall hassign hratio hlogL hlogR
  simpa only [normDistance,profile_norm_sub,dist_plus,hd,shortcutCoefficient] using hh

theorem polynomial_metric_numerator :
    ∃ qH : ℕ, 2 ≤ qH ∧ ∀ q : ℕ, qH ≤ q →
      ∀ (n m : ℕ) (G : MultiGraph n m) (H : Hierarchy n),
      LocallyConnectedReal H G q →
      ∀ M : Finset (Finset (Fin n)), M ⊆ H.nodes →
      (∀t ∈ M, t ≠ univ) →
      (∀t ∈ M, ((G.cut univ t).card : ℝ)/q ≤ (parentBoundary H G t).card) →
      ∀ (d : ℕ) (p : Fin n → EuclideanSpace ℝ (Fin d)), SquaredTriangle p →
      ∀ (Y : Fin n → EuclideanSpace ℝ (Fin m)),
      (∀u v, ‖Y u-Y v‖^2 ≤ ‖p u-p v‖^2) →
      (∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e) →
      (∑t ∈ M, (∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
        ((parentBoundary H G t).card : ℝ)) ≤
        ((q:ℝ)^(-31/40:ℝ)/2)*(∑e : Fin m, ‖p (G.left e)-p (G.right e)‖^2) := by
  obtain ⟨qH,hqH,hgood⟩ := ShortcutNumeric.exists_cutoff
  refine ⟨qH,hqH,?_⟩
  intro q hq n m G H hconn M hM hroot hratio d p ht Y hcontract hpositive
  have hg := hgood q hq
  have hqpos : 0 < q := lt_of_lt_of_le (by omega : 0 < qH) hq
  have hqp : (0:ℝ) < q := Nat.cast_pos.mpr hqpos
  have hq1 : (1:ℝ) ≤ q := le_trans (by norm_num) hg.large
  have hα : 0 < ShortcutNumeric.alpha q := Real.rpow_pos_of_pos hqp _
  have hα1 : ShortcutNumeric.alpha q ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hq1 (by norm_num)
  have hρ : 0 < ShortcutNumeric.rho q := by dsimp [ShortcutNumeric.rho]; positivity
  have hr : ∀t ∈ M, (q:ℝ)*ShortcutNumeric.rho q*((G.cut univ t).card : ℝ) ≤
      (parentBoundary H G t).card := by
    intro t ht
    have heq : (q:ℝ)*ShortcutNumeric.rho q*((G.cut univ t).card : ℝ)=
        ((G.cut univ t).card : ℝ)/q/2 := by
      unfold ShortcutNumeric.rho
      field_simp
    rw [heq]
    have hp : (0:ℝ) ≤ ((G.cut univ t).card : ℝ)/q := div_nonneg (Nat.cast_nonneg _) hqp.le
    exact (by linarith : ((G.cut univ t).card : ℝ)/q/2 ≤
      ((G.cut univ t).card : ℝ)/q).trans (hratio t ht)
  have hb := squared_euclidean_numerator_bound hqpos
    (ShortcutNumeric.count_pos hqp) (ShortcutNumeric.count_pos hqp)
    (Hierarchy.edgeConnected_of_locally hconn) hconn M Y hM hroot hα hα1
    (by norm_num : (0:ℝ)<1/10) (by norm_num : (1/10:ℝ)<1/3)
    hρ hg.rho_small p ht hcontract hpositive
    hg.small hg.assignment hr hg.log_left hg.log_right
  have hcoef : shortcutCoefficient q (ShortcutNumeric.count q) (ShortcutNumeric.count q)
      (ShortcutNumeric.alpha q) (1/10)=ShortcutNumeric.coefficient q := rfl
  rw [hcoef] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right hg.coefficient_small
    (sum_nonneg (fun e _ => sq_nonneg _)))

end
end AlgorithmicThinTrees.MetricProfiles
end

end OAI
