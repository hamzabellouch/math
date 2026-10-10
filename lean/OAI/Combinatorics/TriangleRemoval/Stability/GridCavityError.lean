import Mathlib
import OAI.Combinatorics.TriangleRemoval.Queries.TreeBind
import OAI.Combinatorics.TriangleRemoval.Stability.GeometricVolterraIdentity

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
open Filter
open scoped BigOperators Topology

section GridApproximation
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem messageIntegral_time_lipschitz (H : τ → Finset ι) (e : ι) (T : τ)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |messageIntegral H (cavityLimit H) e T t - messageIntegral H (cavityLimit H) e T s| ≤
      |t - s| := by
  let f : ℝ → ℝ := fun x => ∏ a ∈ (H T).erase e, cavityLimit H a (some T) x
  have hc : Continuous f := continuous_message_integrand H _ (continuous_cavityLimit H) e T
  have hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    exact ⟨Finset.prod_nonneg (fun a _ => (cavityLimit_mem_unit H a (some T) x).1),
      Finset.prod_le_one₀ (fun a _ => (cavityLimit_mem_unit H a (some T) x).1)
        (fun a _ => (cavityLimit_mem_unit H a (some T) x).2)⟩
  simp only [messageIntegral, unitTime_of_mem hs, unitTime_of_mem ht]
  change |(∫ x in (0 : ℝ)..t, f x) - ∫ x in (0 : ℝ)..s, f x| ≤ _
  rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    ← Real.norm_eq_abs]
  simpa only [one_mul] using
    (intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t) (C := (1 : ℝ))
      (f := f) (fun x _ => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hf x).1] using (hf x).2))

theorem cavityLimit_time_lipschitz (H : τ → Finset ι) (e : ι) (p : Option τ)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |cavityLimit H e p t - cavityLimit H e p s| ≤ (Fintype.card τ : ℝ) * |t - s| := by
  rw [cavityLimit_product H e p t, cavityLimit_product H e p s]
  unfold cavityOperator
  have hm : ∀ T u, 1 - messageIntegral H (cavityLimit H) e T u ∈ Set.Icc (0 : ℝ) 1 := by
    intro T u
    have h := messageIntegral_mem_unit H _ (continuous_cavityLimit H) (cavityLimit_mem_unit H) e T u
    constructor <;> linarith [h.1, h.2]
  calc
    _ ≤ ∑ T ∈ messageCandidates H e p,
        |(1 - messageIntegral H (cavityLimit H) e T t) -
          (1 - messageIntegral H (cavityLimit H) e T s)| :=
      abs_prod_sub_prod_le_sum _ _ _ (fun T _ => hm T t) (fun T _ => hm T s)
    _ ≤ ∑ _T ∈ messageCandidates H e p, |t - s| := by
      apply Finset.sum_le_sum
      intro T _
      rw [sub_sub_sub_cancel_left, abs_sub_comm]
      exact messageIntegral_time_lipschitz H e T hs ht
    _ ≤ (Fintype.card τ : ℝ) * |t - s| := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      gcongr
      exact_mod_cast Finset.card_le_univ (messageCandidates H e p)

theorem cavity_integrand_time_lipschitz (H : τ → Finset ι) (e : ι) (T : τ)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |(∏ f ∈ (H T).erase e, cavityLimit H f (some T) t) -
      ∏ f ∈ (H T).erase e, cavityLimit H f (some T) s| ≤
        ((Fintype.card ι : ℝ) * Fintype.card τ) * |t - s| := by
  calc
    _ ≤ ∑ f ∈ (H T).erase e, |cavityLimit H f (some T) t - cavityLimit H f (some T) s| :=
      abs_prod_sub_prod_le_sum _ _ _ (fun f _ => cavityLimit_mem_unit H f (some T) t)
        (fun f _ => cavityLimit_mem_unit H f (some T) s)
    _ ≤ ∑ _f ∈ (H T).erase e, (Fintype.card τ : ℝ) * |t - s| :=
      Finset.sum_le_sum (fun f _ => cavityLimit_time_lipschitz H f (some T) hs ht)
    _ ≤ ((Fintype.card ι : ℝ) * Fintype.card τ) * |t - s| := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      gcongr
      exact_mod_cast Finset.card_le_univ ((H T).erase e)

omit [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ] in
theorem sum_fin_filter_lt_eq_range (N k : ℕ) (hk : k ≤ N) (f : ℕ → ℝ) :
    (∑ u ∈ Finset.univ.filter (fun u : Fin N => u.val < k), f u.val) =
      ∑ j ∈ Finset.range k, f j := by
  rw [Finset.sum_filter]
  calc
    _ = ∑ j ∈ Finset.range N, if j < k then f j else 0 :=
      Fin.sum_univ_eq_sum_range (fun j => if j < k then f j else 0) N
    _ =
        ∑ j ∈ Finset.range k, if j < k then f j else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hk)
      intro j _ hj
      simp only [Finset.mem_range] at hj
      simp only [hj, ↓reduceIte]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range.mp hj, ↓reduceIte]

omit [Fintype ι] in

theorem gridMessage_exact_range (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (hk : k ≤ N) (e : ι) (parent : Option τ) :
    gridMessage H N N k e parent =
      ∏ T ∈ messageCandidates H e parent,
        (1 - (1 / (N : ℝ)) * ∑ j ∈ Finset.range k,
          ∏ f ∈ (H T).erase e, gridMessage H N N j f (some T)) := by
  rw [gridMessage_exact H N k hk]
  apply Finset.prod_congr rfl
  intro T _
  congr 2
  exact sum_fin_filter_lt_eq_range N k hk
    (fun j => ∏ f ∈ (H T).erase e, gridMessage H N N j f (some T))

omit [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ] in
theorem uniform_subaverage_mem_unit (N k : ℕ) (hN : 0 < N) (hk : k ≤ N)
    (f : ℕ → ℝ) (hf : ∀ j < k, f j ∈ Set.Icc (0 : ℝ) 1) :
    1 - (1 / (N : ℝ)) * ∑ j ∈ Finset.range k, f j ∈ Set.Icc (0 : ℝ) 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs0 : 0 ≤ (1 / (N : ℝ)) * ∑ j ∈ Finset.range k, f j :=
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun j hj => (hf j (Finset.mem_range.mp hj)).1))
  have hs1 : (∑ j ∈ Finset.range k, f j) ≤ (N : ℝ) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range k, (1 : ℝ) :=
        Finset.sum_le_sum (fun j hj => (hf j (Finset.mem_range.mp hj)).2)
      _ = (k : ℝ) := by simp
      _ ≤ (N : ℝ) := by exact_mod_cast hk
  have hs2 : (1 / (N : ℝ)) * ∑ j ∈ Finset.range k, f j ≤ 1 := by
    calc
      _ ≤ (1 / (N : ℝ)) * N := mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = 1 := by field_simp
  constructor <;> linarith

omit [Fintype ι] in
theorem gridMessage_mem_unit (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (e : ι) (p : Option τ) : gridMessage H N d k e p ∈ Set.Icc (0 : ℝ) 1 :=
  gridAnswerProbability_mem_unit H N d k {e} p

noncomputable def gridCavityError (H : τ → Finset ι) (N : ℕ) [NeZero N] (k : ℕ) : ℝ :=
  ‖(fun ep : ι × Option τ => gridMessage H N N k ep.1 ep.2 -
    cavityLimit H ep.1 ep.2 ((k : ℝ) / N))‖

theorem gridCavityError_nonneg (H : τ → Finset ι) (N : ℕ) [NeZero N] (k : ℕ) :
    0 ≤ gridCavityError H N k := norm_nonneg _

theorem gridCavityError_coord (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (e : ι) (p : Option τ) :
    |gridMessage H N N k e p - cavityLimit H e p ((k : ℝ) / N)| ≤ gridCavityError H N k := by
  exact norm_le_pi_norm (fun ep : ι × Option τ =>
    gridMessage H N N k ep.1 ep.2 - cavityLimit H ep.1 ep.2 ((k : ℝ) / N)) (e, p)

theorem grid_integrand_error (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (e : ι) (T : τ) :
    |(∏ f ∈ (H T).erase e, gridMessage H N N k f (some T)) -
      ∏ f ∈ (H T).erase e, cavityLimit H f (some T) ((k : ℝ) / N)| ≤
        (Fintype.card ι : ℝ) * gridCavityError H N k := by
  calc
    _ ≤ ∑ f ∈ (H T).erase e,
        |gridMessage H N N k f (some T) - cavityLimit H f (some T) ((k : ℝ) / N)| :=
      abs_prod_sub_prod_le_sum _ _ _ (fun f _ => gridMessage_mem_unit H N N k f (some T))
        (fun f _ => cavityLimit_mem_unit H f (some T) ((k : ℝ) / N))
    _ ≤ ∑ _f ∈ (H T).erase e, gridCavityError H N k :=
      Finset.sum_le_sum (fun f _ => gridCavityError_coord H N k f (some T))
    _ ≤ (Fintype.card ι : ℝ) * gridCavityError H N k := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (gridCavityError_nonneg H N k)
      exact_mod_cast Finset.card_le_univ ((H T).erase e)

theorem grid_message_integral_error (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (hk : k ≤ N) (e : ι) (T : τ) :
    |(1 / (N : ℝ)) * (∑ j ∈ Finset.range k,
        ∏ f ∈ (H T).erase e, gridMessage H N N j f (some T)) -
      messageIntegral H (cavityLimit H) e T ((k : ℝ) / N)| ≤
        ((Fintype.card ι : ℝ) / N) * ∑ j ∈ Finset.range k, gridCavityError H N j +
          ((Fintype.card ι : ℝ) * Fintype.card τ) / N := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let f : ℝ → ℝ := fun s => ∏ a ∈ (H T).erase e, cavityLimit H a (some T) s
  have hc : Continuous f := continuous_message_integrand H _ (continuous_cavityLimit H) e T
  have hquad := uniform_grid_quadrature f hc (by positivity :
      0 ≤ (Fintype.card ι : ℝ) * Fintype.card τ)
    (fun x hx y hy => cavity_integrand_time_lipschitz H e T hy hx) N k hN hk
  have htime : (k : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hNr).mpr (by exact_mod_cast hk)⟩
  have hi : messageIntegral H (cavityLimit H) e T ((k : ℝ) / N) =
      ∫ s in (0 : ℝ)..((k : ℝ) / N), f s := by
    simp only [messageIntegral, unitTime_of_mem htime, f]
  rw [hi]
  calc
    _ ≤ |(1 / (N : ℝ)) * (∑ j ∈ Finset.range k,
        ∏ a ∈ (H T).erase e, gridMessage H N N j a (some T)) -
          (1 / (N : ℝ)) * ∑ j ∈ Finset.range k, f ((j : ℝ) / N)| +
        |(1 / (N : ℝ)) * (∑ j ∈ Finset.range k, f ((j : ℝ) / N)) -
          ∫ s in (0 : ℝ)..((k : ℝ) / N), f s| := abs_sub_le _ _ _
    _ ≤ ((Fintype.card ι : ℝ) / N) * ∑ j ∈ Finset.range k, gridCavityError H N j +
          ((Fintype.card ι : ℝ) * Fintype.card τ) / N := by
      apply add_le_add _ (by simpa only [abs_sub_comm] using hquad)
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (N : ℝ)),
        ← Finset.sum_sub_distrib]
      calc
        _ ≤ (1 / (N : ℝ)) * ∑ j ∈ Finset.range k,
            |(∏ a ∈ (H T).erase e, gridMessage H N N j a (some T)) - f ((j : ℝ) / N)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
        _ ≤ (1 / (N : ℝ)) * ∑ j ∈ Finset.range k,
            (Fintype.card ι : ℝ) * gridCavityError H N j := by
          gcongr with j hj
          exact grid_integrand_error H N j e T
        _ = _ := by rw [← Finset.mul_sum]; ring

theorem gridCavityError_volterra (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (hk : k ≤ N) :
    gridCavityError H N k ≤
      ((Fintype.card τ : ℝ) ^ 2 * Fintype.card ι) / N +
        ((Fintype.card τ : ℝ) * Fintype.card ι / N) *
          ∑ j ∈ Finset.range k, gridCavityError H N j := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hb : 0 ≤ ((Fintype.card ι : ℝ) / N) * ∑ j ∈ Finset.range k, gridCavityError H N j +
      ((Fintype.card ι : ℝ) * Fintype.card τ) / N := by
    have := Finset.sum_nonneg (s := Finset.range k) (fun j _ => gridCavityError_nonneg H N j)
    positivity
  unfold gridCavityError
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro ep
  rw [Real.norm_eq_abs, gridMessage_exact_range H N k hk,
    cavityLimit_product H ep.1 ep.2 ((k : ℝ) / N)]
  unfold cavityOperator
  let g : τ → ℝ := fun T => 1 - (1 / (N : ℝ)) * ∑ j ∈ Finset.range k,
    ∏ f ∈ (H T).erase ep.1, gridMessage H N N j f (some T)
  let q : τ → ℝ := fun T => 1 - messageIntegral H (cavityLimit H) ep.1 T ((k : ℝ) / N)
  have hg : ∀ T, g T ∈ Set.Icc (0 : ℝ) 1 := by
    intro T
    apply uniform_subaverage_mem_unit N k hN hk
    intro j _
    exact ⟨Finset.prod_nonneg (fun f _ => (gridMessage_mem_unit H N N j f (some T)).1),
      Finset.prod_le_one₀ (fun f _ => (gridMessage_mem_unit H N N j f (some T)).1)
        (fun f _ => (gridMessage_mem_unit H N N j f (some T)).2)⟩
  have hq : ∀ T, q T ∈ Set.Icc (0 : ℝ) 1 := by
    intro T
    have h := messageIntegral_mem_unit H _ (continuous_cavityLimit H) (cavityLimit_mem_unit H)
      ep.1 T ((k : ℝ) / N)
    change 1 - _ ∈ _
    constructor <;> linarith [h.1, h.2]
  change |(∏ T ∈ messageCandidates H ep.1 ep.2, g T) -
    ∏ T ∈ messageCandidates H ep.1 ep.2, q T| ≤ _
  calc
    _ ≤ ∑ T ∈ messageCandidates H ep.1 ep.2, |g T - q T| :=
      abs_prod_sub_prod_le_sum _ _ _ (fun T _ => hg T) (fun T _ => hq T)
    _ ≤ ∑ _T ∈ messageCandidates H ep.1 ep.2,
        (((Fintype.card ι : ℝ) / N) * ∑ j ∈ Finset.range k, gridCavityError H N j +
          ((Fintype.card ι : ℝ) * Fintype.card τ) / N) := by
      apply Finset.sum_le_sum
      intro T _
      dsimp only [g, q]
      rw [sub_sub_sub_cancel_left, abs_sub_comm]
      exact grid_message_integral_error H N k hk ep.1 T
    _ ≤ (Fintype.card τ : ℝ) *
        (((Fintype.card ι : ℝ) / N) * ∑ j ∈ Finset.range k, gridCavityError H N j +
          ((Fintype.card ι : ℝ) * Fintype.card τ) / N) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ hb
      exact_mod_cast Finset.card_le_univ (messageCandidates H ep.1 ep.2)
    _ = _ := by unfold gridCavityError; ring

theorem gridCavityError_bound (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (hk : k ≤ N) :
    gridCavityError H N k ≤
      (((Fintype.card τ : ℝ) ^ 2 * Fintype.card ι) / N) *
        Real.exp ((Fintype.card τ : ℝ) * Fintype.card ι) := by
  exact discrete_volterra_exp_bound (gridCavityError H N)
    ((Fintype.card τ : ℝ) * Fintype.card ι)
    ((Fintype.card τ : ℝ) ^ 2 * Fintype.card ι) (by positivity) (by positivity)
    N (Nat.pos_of_ne_zero (NeZero.ne N)) (gridCavityError_volterra H N) k hk

theorem gridMessage_tendsto_terminal (H : τ → Finset ι) (e : ι) (p : Option τ) :
    Tendsto (fun n : ℕ => gridMessage H (n + 1) (n + 1) (n + 1) e p)
      atTop (𝓝 (cavityLimit H e p 1)) := by
  have hden : Tendsto (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0))
  let C : ℝ := ((Fintype.card τ : ℝ) ^ 2 * Fintype.card ι) *
    Real.exp ((Fintype.card τ : ℝ) * Fintype.card ι)
  have hbound : ∀ n : ℕ,
      ‖gridMessage H (n + 1) (n + 1) (n + 1) e p - cavityLimit H e p 1‖ ≤
        C * (1 / ((n + 1 : ℕ) : ℝ)) := by
    intro n
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hx := (gridCavityError_coord H (n + 1) (n + 1) e p).trans
      (gridCavityError_bound H (n + 1) (n + 1) le_rfl)
    simpa only [div_self hn, Real.norm_eq_abs, C, div_eq_mul_inv, one_mul,
      mul_assoc, mul_comm, mul_left_comm] using hx
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) hbound
    (by simpa using tendsto_const_nhds.mul hden)

end GridApproximation
end SharpTerminalLeave

end

end OAI
