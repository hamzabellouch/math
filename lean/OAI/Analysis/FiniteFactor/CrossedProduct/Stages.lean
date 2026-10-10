import OAI.Analysis.FiniteFactor.Polynomial
import OAI.Analysis.FiniteFactor.Coupling.Products
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

namespace FiniteFactor
open Filter Finset
open scoped Topology
noncomputable section

def sourceNextCutoff (m : ℕ) : ℕ := Nat.ceil ((m : ℝ)^((3/4 : ℝ)*(m : ℝ)))

theorem sourceNextCutoff_large (m : ℕ) (hm : 100 ≤ m) : 2*m < sourceNextCutoff m := by
  have hmR : (100 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (m : ℝ)^2 ≤ (m : ℝ)^((3/4 : ℝ)*(m : ℝ)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num; linarith)
  have hh := hp.trans (Nat.le_ceil _)
  have hh2 : (2 : ℝ)*m < (sourceNextCutoff m : ℝ) := by
    change (m : ℝ)^2 ≤ (sourceNextCutoff m : ℝ) at hh
    nlinarith
  exact_mod_cast hh2

theorem exists_source_block_length (R κ L G : ℝ) (hκ : 0 < κ) (hG : 0 < G) :
    ∃ m : ℕ, R ≤ (m : ℝ) ∧ 100 ≤ m ∧ κ*(m : ℝ)^(1/40 : ℝ) ≥ L ∧
      G*(sourceNextCutoff m : ℝ) < (m : ℝ)^((4/5 : ℝ)*(m : ℝ)) := by
  have ht : Tendsto (fun m : ℕ => (m : ℝ)^(1/40 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨m, hmR, hm100, hmG, hmκ⟩ :=
    ((tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop R)).and
      ((eventually_ge_atTop (100 : ℕ)).and
        ((tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (2*G))).and
          (ht.eventually (eventually_ge_atTop (L/κ)))))).exists
  refine ⟨m, hmR, hm100, (div_le_iff₀ hκ).mp hmκ |>.trans_eq (mul_comm _ _), ?_⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hm1
  let A : ℝ := (m : ℝ)^((3/4 : ℝ)*(m : ℝ))
  have hApos : 0 < A := Real.rpow_pos_of_pos hm0 _
  have hA1 : 1 ≤ A := Real.one_le_rpow hm1 (by positivity)
  have hceil : (sourceNextCutoff m : ℝ) ≤ 2*A := by
    have hh := Nat.ceil_lt_add_one hApos.le
    change (Nat.ceil A : ℝ) ≤ 2*A
    linarith
  calc
    G*(sourceNextCutoff m : ℝ) ≤ G*(2*A) := mul_le_mul_of_nonneg_left hceil hG.le
    _ < (m : ℝ)*A := by nlinarith
    _ = (m : ℝ)^((3/4 : ℝ)*(m : ℝ)+1) := by rw [Real.rpow_add hm0, Real.rpow_one]; ring
    _ ≤ (m : ℝ)^((4/5 : ℝ)*(m : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hm1 (by
        have hh : (100 : ℝ) ≤ m := by exact_mod_cast hm100
        linarith)

/-- State already fixed before the new block length is chosen. B is the
previous weighted block-size sum; d is the previous coordinate count. -/
structure SourceStageState where
  K : ℕ
  G : ℝ
  d : ℕ
  B : ℝ
  previousL : ℝ
  K_ge : 1 ≤ K
  G_ge : 1 ≤ G
  B_nonneg : 0 ≤ B
  previousL_ge : 1 ≤ previousL

def SourceStageState.D (a : SourceStageState) : ℝ := Real.exp (((a.K : ℝ)+1)*a.B)

/-- Complete numerical output of one source stage. The polynomial bound is
proved before L, Gnext and m are selected. Stages use s=0 for source j=1. -/
structure SourceStageChoice (s : ℕ) (a : SourceStageState) where
  ε : ℝ
  L : ℝ
  Gnext : ℝ
  m : ℕ
  ε_pos : 0 < ε
  polynomial : ∀ u v : Coefficients a.K,
    (∀ i, ‖u i‖ ≤ a.D) → (∀ i, ‖v i‖ ≤ a.D) →
    1/((s : ℝ)+1) ≤ ‖u ⟨a.K, by omega⟩‖ → 1/((s : ℝ)+1) ≤ ‖v ⟨a.K, by omega⟩‖ →
    ∃ n : Fin (2*a.K+1), ε ≤ ‖productCoefficient u v n.val‖
  L_ge : a.previousL ≤ L
  decay : ((2*a.K : ℕ)+1 : ℝ)*3*Real.exp (-L/10000) ≤ ε/((s : ℝ)+1)
  Gnext_ge : 1 ≤ Gnext
  next_budget : sourceKappa (s+1) * Real.sqrt Gnext ≥ L
  m_ge_K : a.K ≤ m
  m_ge_pow : 2^(s+1) ≤ m
  m_ge_G : 4*a.G ≤ (m : ℝ)
  m_ge_100 : 100 ≤ m
  previous_size : (a.d : ℝ) ≤ (m : ℝ)/100
  current_budget : sourceKappa s * (m : ℝ)^(1/40 : ℝ) ≥ L
  next_gap : Gnext*(sourceNextCutoff m : ℝ) < (m : ℝ)^((4/5 : ℝ)*(m : ℝ))

theorem exists_sourceStageChoice (s : ℕ) (a : SourceStageState) :
    Nonempty (SourceStageChoice s a) := by
  have hs : 0 < (s : ℝ)+1 := by positivity
  have hk (j : ℕ) : 0 < sourceKappa j := by unfold sourceKappa; positivity
  obtain ⟨ε, hε, hp⟩ := uniform_product_coefficient_bound a.K a.D (1/((s : ℝ)+1)) (by positivity)
  let target : ℝ := (ε/((s : ℝ)+1))/(((2*a.K : ℕ)+1 : ℝ)*3)
  have ht : 0 < target := by dsimp [target]; positivity
  obtain ⟨t, htL, htt⟩ := ((eventually_ge_atTop (a.previousL/10000)).and
    (Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds ht))).exists
  let L : ℝ := 10000*t
  have hL : a.previousL ≤ L := by dsimp [L]; linarith
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith [a.previousL_ge]) hL
  let G : ℝ := (1+L/sourceKappa (s+1))^2
  have hG : 1 ≤ G := by dsimp [G]; nlinarith [div_pos hLpos (hk (s+1))]
  have hbudget : L ≤ sourceKappa (s+1)*Real.sqrt G := by
    rw [show Real.sqrt G = 1+L/sourceKappa (s+1) by
      dsimp [G]; rw [Real.sqrt_sq (by linarith [div_pos hLpos (hk (s+1))])]]
    rw [mul_add, mul_one, mul_div_cancel₀ _ (hk (s+1)).ne']
    linarith [hk (s+1)]
  let R : ℝ := max (a.K : ℝ) (max ((2^(s+1) : ℕ) : ℝ) (max (4*a.G) (100*(a.d : ℝ))))
  obtain ⟨m, hmR, hm100, hmκ, hmgap⟩ := exists_source_block_length R (sourceKappa s) L G (hk s) (by linarith)
  have hmK : (a.K : ℝ) ≤ m := (le_max_left _ _).trans hmR
  have hm2 : (((2^(s+1) : ℕ)) : ℝ) ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hmR)
  have hmG : 4*a.G ≤ (m : ℝ) := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hmR))
  have hmd : 100*(a.d : ℝ) ≤ m := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hmR))
  refine ⟨⟨ε, L, G, m, hε, hp, hL, ?_, hG, hbudget,
    by exact_mod_cast hmK, by exact_mod_cast hm2, hmG, hm100, by linarith, hmκ, hmgap⟩⟩
  have hden : 0 < (((2*a.K : ℕ)+1 : ℝ)*3) := by positivity
  have htt' := (lt_div_iff₀ hden).mp htt
  have he : -L/10000 = -t := by dsimp [L]; ring
  rw [he]
  nlinarith

def selectedSourceStage (s : ℕ) (a : SourceStageState) : SourceStageChoice s a :=
  Classical.choice (exists_sourceStageChoice s a)

def SourceStageChoice.C {s : ℕ} {a : SourceStageState} (b : SourceStageChoice s a) : ℝ :=
  max b.L ((a.K : ℝ)^2)

def SourceStageChoice.next {s : ℕ} {a : SourceStageState} (b : SourceStageChoice s a) : SourceStageState where
  K := sourceNextCutoff b.m
  G := b.Gnext
  d := a.d+b.m
  B := a.B+b.C*(b.m : ℝ)
  previousL := b.L
  K_ge := by have := sourceNextCutoff_large b.m b.m_ge_100; omega
  G_ge := b.Gnext_ge
  B_nonneg := add_nonneg a.B_nonneg (mul_nonneg (le_max_of_le_right (sq_nonneg _)) (Nat.cast_nonneg _))
  previousL_ge := a.previousL_ge.trans b.L_ge

/-- The infinite numerical construction is fixed without an operator or a
candidate invariant projection as an input. -/
def sourceStageState : ℕ → SourceStageState
  | 0 => ⟨100, 1, 0, 0, 1, by norm_num, le_rfl, le_rfl, le_rfl⟩
  | s+1 => (selectedSourceStage s (sourceStageState s)).next

def sourceStage (s : ℕ) : SourceStageChoice s (sourceStageState s) :=
  selectedSourceStage s (sourceStageState s)

theorem sourceStage_cutoff_growth (s : ℕ) :
    2*(sourceStageState s).K < (sourceStageState (s+1)).K := by
  have h := sourceNextCutoff_large (sourceStage s).m (sourceStage s).m_ge_100
  exact (Nat.mul_le_mul_left 2 (sourceStage s).m_ge_K).trans_lt h

theorem sourceStage_previous_size (s : ℕ) :
    (sourceStageState s).d = ∑ t ∈ Finset.range s, (sourceStage t).m := by
  induction s with
  | zero => rfl
  | succ s ih => simpa [Finset.sum_range_succ, sourceStageState, SourceStageChoice.next, sourceStage] using congrArg (fun x => x+(sourceStage s).m) ih

theorem sourceStage_previous_weight (s : ℕ) :
    (sourceStageState s).B = ∑ t ∈ Finset.range s, (sourceStage t).C*((sourceStage t).m : ℝ) := by
  induction s with
  | zero => rfl
  | succ s ih => simpa [Finset.sum_range_succ, sourceStageState, SourceStageChoice.next, sourceStage] using congrArg (fun x => x+(sourceStage s).C*((sourceStage s).m : ℝ)) ih

end
end FiniteFactor

end OAI
