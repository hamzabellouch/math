import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.LowCandidate
import OAI.Combinatorics.KMedianRecovery.Encoding.RationalSlack

namespace OAI

namespace MetricKMedianRecovery.IntegralAssembly
open LocalSearch Anchoring Completion Sampling Surplus FiniteSampling IntegralCandidates

noncomputable def commonL (v : ℝ) (Nstar n M : ℕ) : ℕ :=
  max Nstar (3*(HistoryPhaseBound.limit v ((M:ℝ)+8*(n:ℝ)*(M:ℝ))+1))

noncomputable def countBound (L : ℕ) : ℕ :=
  max (2*L) ⌈4*countConstant (1/100)*(L:ℝ)/(gamma/16)⌉₊

noncomputable def repetitions (c : ℝ) (L0 : ℕ) (ζ : ℝ) : ℕ :=
  ⌈Real.log (1/ζ)/Real.exp (-c*L0)⌉₊

theorem uniform_finite_experiment : ∃ v : ℚ, 0 < v ∧ ∃ Nstar : ℕ, 1 ≤ Nstar ∧
    ∃ c : ℝ, 0 < c ∧
    ∀ (V : Type*) [MetricSpace V] [LinearOrder V] [Fintype V],
    ∀ (δ : V → V → ℕ) (F D : Finset V) (k M : ℕ) (ζ : ℝ),
    D.Nonempty → 0 < k → k ≤ F.card → 0 < M →
    (∀ p ∈ D, ∀ i ∈ F, (δ p i : ℝ) = dist p i) →
    (∀ x, ∀ i ∈ F, dist x i ≤ M) →
    (∀ i ∈ F, ∀ p ∈ D, 1 ≤ dist i p) → 0 < ζ →
    let L0 := countBound (commonL v Nstar D.card M)
    let n := repetitions c L0 ζ
    ∃ run : RecoverySeed D F M L0 (D.card*M) n → Finset V,
      (∀ seed, run seed ⊆ F ∧ (run seed).Nonempty ∧ (run seed).card ≤ k ∧
        cost D (run seed) ≤ 5*optimum F D k) ∧
      1-ζ ≤ probability (fun seed => cost D (run seed) ≤ (2-gamma)*(1+gamma/16)*optimum F D k) ∧
      average (fun seed => cost D (run seed)) ≤
        ((2-gamma)*(1+gamma/16)+5*ζ)*optimum F D k := by
  have hT : 0 < 200*countConstant (1/100) := by
    linarith [PhaseSurplusProducer.countConstant_ge_ten]
  have hstrict := strictnessGap_pos hT
  obtain ⟨v,hv,hv1,hvc,hvs⟩ := ParameterBounds.exists_rational_slack _ _ hstrict hT
  have hvR : (0:ℝ) < v := by exact_mod_cast hv
  obtain ⟨Nstar,hNstar,hsize⟩ := ParameterBounds.exists_size_threshold _ _ hstrict hvR
  obtain ⟨c,hc,hcprop⟩ := finite_experiment
  refine ⟨v,hv,Nstar,hNstar,c,hc,?_⟩
  intro V _ _ _ δ F D k M ζ hD hk hkF hM hδ hbound hfar hζ
  let L := commonL v Nstar D.card M
  have hNL : Nstar ≤ L := le_max_left _ _
  have hL : 0 < L := by omega
  have hlarge (hl : 2*L < k) : Nstar ≤ D.card+F.card := by omega
  have hxi : 0 < gamma/16 := div_pos gamma_pos (by norm_num)
  have hxi1 : gamma/16 ≤ 1 := by linarith [gamma_lt_one]
  exact hcprop V δ F D k L (countBound L) M (D.card+F.card) v (gamma/16) ζ
    hD hk hL hkF rfl hM hδ hbound hfar hvR hv1 hvc hvs
    (fun hl => (hsize _ (hlarge hl)).2) (fun hl => (hsize _ (hlarge hl)).1)
    (le_max_right _ _) hxi hxi1 (le_max_left _ _)
    ((Nat.le_ceil _).trans (by exact_mod_cast (le_max_right (2*L) ⌈4*countConstant (1/100)*(L:ℝ)/(gamma/16)⌉₊)))
    hζ (repetitions c (countBound L) ζ) (Nat.le_ceil _)

lemma commonL_bound (v C : ℝ) (Nstar n M N p : ℕ) (hv : 0 < v)
    (hN : 1 ≤ N) (hn : n ≤ N) (hC : 1 ≤ C) (hM : 1 ≤ M)
    (hupper : (M:ℝ) ≤ C*((N:ℝ)+2)^p) :
    (commonL v Nstar n M : ℝ) < (Nstar:ℝ)+
      3*((Real.log (9*C)+(p+1)*Real.log ((N:ℝ)+2))/Real.log (1+v^2)+2)+3 := by
  have hN' : (3:ℝ) ≤ (N:ℝ)+2 := by exact_mod_cast (by omega : 3 ≤ N+2)
  have hn' : (n:ℝ) ≤ (N:ℝ)+2 := by exact_mod_cast (by omega : n ≤ N+2)
  have hM' : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hsmall : HistoryPhaseBound.limit v ((M:ℝ)+8*(n:ℝ)*M) ≤
      HistoryPhaseBound.limit v ((M:ℝ)+8*((N:ℝ)+2)*M) := by
    unfold HistoryPhaseBound.limit
    gcongr
    · exact (Real.log_pos (by nlinarith : (1:ℝ) < 1+v^2)).le
  have hb := HistoryPhaseBound.polynomial_limit_bound v M ((N:ℝ)+2) C p hv hN' hC hM' hupper
  have hmax : max Nstar (3*(HistoryPhaseBound.limit v ((M:ℝ)+8*(n:ℝ)*M)+1)) ≤
      Nstar+3*(HistoryPhaseBound.limit v ((M:ℝ)+8*(n:ℝ)*M)+1) := by omega
  have hcast : (commonL v Nstar n M:ℝ) ≤ (Nstar:ℝ)+
      3*(HistoryPhaseBound.limit v ((M:ℝ)+8*((N:ℝ)+2)*M):ℝ)+3 := by
    dsimp only [commonL]
    exact_mod_cast hmax.trans (by omega : Nstar+3*(HistoryPhaseBound.limit v ((M:ℝ)+8*(n:ℝ)*M)+1) ≤
      Nstar+3*HistoryPhaseBound.limit v ((M:ℝ)+8*((N:ℝ)+2)*M)+3)
  linarith

lemma countBound_bound (L : ℕ) : (countBound L:ℝ) ≤
    (2+4*countConstant (1/100)/(gamma/16))*(L:ℝ)+1 := by
  have hC := PhaseSurplusProducer.countConstant_ge_ten
  have hq : 0 ≤ 4*countConstant (1/100)*(L:ℝ)/(gamma/16) := by
    apply div_nonneg
    · positivity
    · exact (div_pos gamma_pos (by norm_num)).le
  have hc := Nat.ceil_lt_add_one hq
  have hm : max (2*L) ⌈4*countConstant (1/100)*(L:ℝ)/(gamma/16)⌉₊ ≤
      2*L+⌈4*countConstant (1/100)*(L:ℝ)/(gamma/16)⌉₊ := by omega
  have hm' : (countBound L:ℝ) ≤ 2*(L:ℝ)+(⌈4*countConstant (1/100)*(L:ℝ)/(gamma/16)⌉₊:ℝ) := by
    exact_mod_cast hm
  calc
    (countBound L:ℝ) ≤ 2*(L:ℝ)+(⌈4*countConstant (1/100)*(L:ℝ)/(gamma/16)⌉₊:ℝ) := hm'
    _ ≤ 2*(L:ℝ)+(4*countConstant (1/100)*(L:ℝ)/(gamma/16)+1) := by linarith
    _ = _ := by ring

end MetricKMedianRecovery.IntegralAssembly
namespace MetricKMedianRecovery.Rounding
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

noncomputable def edge (u : ℝ) (C : ℕ) (x y : V) : ℕ :=
  if x = y then 0 else min C (max 1 ⌈dist x y/u⌉₊)

lemma edge_self (u : ℝ) (C : ℕ) (x : V) : edge u C x x = 0 := by simp [edge]
lemma edge_symm (u : ℝ) (C : ℕ) (x y : V) : edge u C x y = edge u C y x := by
  simp only [edge,dist_comm y x,eq_comm]
lemma edge_le_cap (u : ℝ) (C : ℕ) (x y : V) : edge u C x y ≤ C := by
  unfold edge
  split_ifs
  · exact Nat.zero_le _
  · exact min_le_left _ _
lemma edge_pos (u : ℝ) {C : ℕ} (hC : 0 < C) {x y : V} (hxy : x ≠ y) :
    0 < edge u C x y := by
  rw [edge,ite_eq_right hxy]
  exact lt_min hC (lt_of_lt_of_le (by omega : 0 < (1:ℕ)) (le_max_left _ _))

lemma edge_triangle (u : ℝ) (hu : 0 < u) (C : ℕ) (x y z : V) :
    edge u C x z ≤ edge u C x y+edge u C y z := by
  by_cases hxz : x = z
  · subst z; rw [edge_self]; omega
  by_cases hxy : x = y
  · subst y; simp only [edge_self,zero_add,le_refl]
  by_cases hyz : y = z
  · subst z; simp only [edge_self,add_zero,le_refl]
  have hceil : ⌈dist x z/u⌉₊ ≤ ⌈dist x y/u⌉₊+⌈dist y z/u⌉₊ := by
    calc
      _ ≤ ⌈dist x y/u+dist y z/u⌉₊ := Nat.ceil_mono (by
        rw [← add_div]; exact div_le_div_of_nonneg_right (dist_triangle x y z) hu.le)
      _ ≤ _ := Nat.ceil_add_le _ _
  simp only [edge,ite_eq_right hxz,ite_eq_right hxy,ite_eq_right hyz]
  omega

@[instance_reducible]
noncomputable def metric (u : ℝ) (hu : 0 < u) (C : ℕ) (hC : 0 < C) : MetricSpace V where
  dist x y := edge u C x y
  dist_self x := by exact_mod_cast edge_self u C x
  dist_comm x y := by exact_mod_cast edge_symm u C x y
  dist_triangle x y z := by exact_mod_cast edge_triangle u hu C x y z
  eq_of_dist_eq_zero := by
    intro x y he
    by_contra hn
    have hh := edge_pos u hC hn
    have hz : edge u C x y = 0 := by exact_mod_cast he
    omega

lemma edge_upper (u : ℝ) (hu : 0 < u) (C : ℕ) (x y : V) :
    (edge u C x y:ℝ) ≤ dist x y/u+1 := by
  have hd : 0 ≤ dist x y/u := div_nonneg dist_nonneg hu.le
  by_cases hxy : x = y
  · simp only [edge,ite_eq_left hxy,Nat.cast_zero]; linarith
  rw [edge,ite_eq_right hxy]
  calc
    ((min C (max 1 ⌈dist x y/u⌉₊):ℕ):ℝ) ≤ ((max 1 ⌈dist x y/u⌉₊:ℕ):ℝ) :=
      by exact_mod_cast min_le_right C (max 1 ⌈dist x y/u⌉₊)
    _ ≤ _ := by
      rw [Nat.cast_max,Nat.cast_one]
      exact max_le (by linarith) (Nat.ceil_lt_add_one hd).le

lemma original_le_uncapped (u : ℝ) (hu : 0 < u) (C : ℕ) (x y : V)
    (hcap : edge u C x y < C) : dist x y ≤ u*(edge u C x y:ℝ) := by
  by_cases hxy : x = y
  · subst y; simp only [dist_self,edge_self,Nat.cast_zero,mul_zero,le_refl]
  have he : edge u C x y = max 1 ⌈dist x y/u⌉₊ := by
    simp only [edge,ite_eq_right hxy] at hcap ⊢
    omega
  have hh : dist x y/u ≤ (edge u C x y:ℝ) := by
    rw [he]
    exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈dist x y/u⌉₊)
  exact (div_le_iff₀ hu).mp hh |>.trans_eq (mul_comm _ _)

noncomputable def connection (u : ℝ) (C : ℕ) (S : Finset V) (p : V) : ℕ :=
  if h : S.Nonempty then S.inf' h (edge u C p) else 0
noncomputable def cost (u : ℝ) (C : ℕ) (D S : Finset V) : ℕ :=
  ∑ p ∈ D, connection u C S p
noncomputable def nearest (u : ℝ) (C : ℕ) (S : Finset V) (hS : S.Nonempty) (p : V) : V :=
  Classical.choose (Finset.exists_min_image S (edge u C p) hS)
lemma nearest_mem (u : ℝ) (C : ℕ) (S : Finset V) (hS : S.Nonempty) (p : V) :
    nearest u C S hS p ∈ S :=
  (Classical.choose_spec (Finset.exists_min_image S (edge u C p) hS)).1
lemma nearest_edge (u : ℝ) (C : ℕ) (S : Finset V) (hS : S.Nonempty) (p : V) :
    edge u C p (nearest u C S hS p) = connection u C S p := by
  rw [connection,dite_eq_left hS]
  exact le_antisymm (Finset.le_inf' hS _
    (Classical.choose_spec (Finset.exists_min_image S (edge u C p) hS)).2)
    (Finset.inf'_le _ (nearest_mem u C S hS p))
lemma connection_le (u : ℝ) (C : ℕ) {S : Finset V} {p s : V} (hs : s ∈ S) :
    connection u C S p ≤ edge u C p s := by
  rw [connection,dite_eq_left ⟨s,hs⟩]
  exact Finset.inf'_le _ hs

lemma rounded_cost_upper (u : ℝ) (hu : 0 < u) (C : ℕ) (D S : Finset V) (hS : S.Nonempty) :
    (cost u C D S:ℝ) ≤ LocalSearch.cost D S/u+D.card := by
  have hpoint (p : V) : (connection u C S p:ℝ) ≤ LocalSearch.connection S p/u+1 := by
    calc
      _ ≤ (edge u C p (LocalSearch.nearest S hS p):ℝ) :=
        by exact_mod_cast connection_le u C (LocalSearch.nearest_mem S hS p)
      _ ≤ _ := by simpa only [LocalSearch.nearest_distance] using
        edge_upper u hu C p (LocalSearch.nearest S hS p)
  have hsum := Finset.sum_le_sum (s := D) (fun p _ => hpoint p)
  simpa only [cost,Nat.cast_sum,Finset.sum_add_distrib,← Finset.sum_div,
    LocalSearch.cost,Finset.sum_const,nsmul_eq_mul,mul_one] using hsum

lemma original_cost_le (u : ℝ) (hu : 0 < u) (C : ℕ) (D S : Finset V) (hS : S.Nonempty)
    (hcap : cost u C D S < C) : LocalSearch.cost D S ≤ u*(cost u C D S:ℝ) := by
  have hpoint (p : V) (hp : p ∈ D) :
      LocalSearch.connection S p ≤ u*(connection u C S p:ℝ) := by
    have hh : connection u C S p ≤ cost u C D S :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hp
    have he : edge u C p (nearest u C S hS p) < C := by
      rw [nearest_edge]; omega
    calc
      _ ≤ dist p (nearest u C S hS p) := LocalSearch.connection_le (nearest_mem u C S hS p)
      _ ≤ _ := by
        simpa only [nearest_edge] using
          original_le_uncapped u hu C p (nearest u C S hS p) he
  have hsum := Finset.sum_le_sum hpoint
  simpa only [LocalSearch.cost,← Finset.mul_sum,cost,Nat.cast_sum] using hsum

end MetricKMedianRecovery.Rounding

end OAI
