import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace BinPackingGap

def primaryScoreBound : ℕ := 100 ^ 11

def lossAllowance (c : ℕ) : ℕ := 25 * (c + 1) * (1 + 5 * primaryScoreBound)

def depthDemand (c : ℕ) (ρ : ℝ) : ℕ :=
  Nat.ceil (max (72 * (lossAllowance c : ℝ)) (120 * (lossAllowance c : ℝ) / ρ))

def repetitions (P n K : ℕ) : ℕ := 100 * (P + n * K + 1)

theorem primaryScoreBound_pos : 0 < primaryScoreBound := by
  unfold primaryScoreBound
  positivity

theorem lossAllowance_pos (c : ℕ) : 0 < lossAllowance c := by
  unfold lossAllowance
  positivity

theorem primary_loss_lt_lossAllowance (c : ℕ) :
    25 * c * (1 + 5 * primaryScoreBound) < lossAllowance c := by
  unfold lossAllowance
  apply mul_lt_mul_of_pos_right _ (by positivity)
  exact mul_lt_mul_of_pos_left (Nat.lt_succ_self c) (by norm_num)

theorem depthDemand_ge_72_real (c : ℕ) (ρ : ℝ) :
    72 * (lossAllowance c : ℝ) ≤ (depthDemand c ρ : ℝ) := by
  exact (le_max_left _ _).trans (Nat.le_ceil _)

theorem depthDemand_ge_72 (c : ℕ) (ρ : ℝ) :
    72 * lossAllowance c ≤ depthDemand c ρ := by
  exact_mod_cast depthDemand_ge_72_real c ρ

theorem depthDemand_ge_120_div (c : ℕ) (ρ : ℝ) :
    120 * (lossAllowance c : ℝ) / ρ ≤ (depthDemand c ρ : ℝ) := by
  exact (le_max_right _ _).trans (Nat.le_ceil _)

theorem depthDemand_pos (c : ℕ) (ρ : ℝ) : 0 < depthDemand c ρ :=
  lt_of_lt_of_le (Nat.mul_pos (by norm_num) (lossAllowance_pos c))
    (depthDemand_ge_72 c ρ)

theorem depthDemand_one_le (c : ℕ) (ρ : ℝ) : 1 ≤ depthDemand c ρ :=
  Nat.succ_le_of_lt (depthDemand_pos c ρ)

theorem depthDemand_ge_12 (c : ℕ) (ρ : ℝ) :
    12 * lossAllowance c ≤ depthDemand c ρ := by
  exact (Nat.mul_le_mul_right (lossAllowance c) (by norm_num : 12 ≤ 72)).trans
    (depthDemand_ge_72 c ρ)

theorem depthDemand_spec (c : ℕ) (ρ : ℝ) :
    1 ≤ depthDemand c ρ ∧
      max (72 * (lossAllowance c : ℝ)) (120 * (lossAllowance c : ℝ) / ρ) ≤
        (depthDemand c ρ : ℝ) :=
  ⟨depthDemand_one_le c ρ, Nat.le_ceil _⟩

theorem threshold_gap {d K : ℝ} (hd : 0 < d) (h72 : 72 * K ≤ d) :
    d / 8 < d - 6 * K := by
  linarith

theorem three_quarter_lower {d K x L : ℝ} (h72 : 72 * K ≤ d)
    (hx : x ≤ d / 8) (hL : d - x - 9 * K ≤ L) : 3 * d / 4 ≤ L := by
  linarith

theorem depthDemand_threshold_gap (c : ℕ) (ρ : ℝ) :
    (depthDemand c ρ : ℝ) / 8 < (depthDemand c ρ : ℝ) - 6 * (lossAllowance c : ℝ) :=
  threshold_gap (Nat.cast_pos.mpr (depthDemand_pos c ρ)) (depthDemand_ge_72_real c ρ)

theorem repetitions_pos (P n K : ℕ) : 0 < repetitions P n K := by
  unfold repetitions
  positivity

theorem repetitions_gt_P (P n K : ℕ) : P < repetitions P n K := by
  have hnK : 0 ≤ n * K := Nat.zero_le _
  unfold repetitions
  nlinarith

theorem repetitions_cast (P n K : ℕ) :
    (repetitions P n K : ℝ) = 100 * ((P : ℝ) + (n : ℝ) * K + 1) := by
  simp [repetitions]

theorem edge_demand_exceeds_capacity_real {P n K d : ℝ}
    (hP : 0 ≤ P) (hn : 0 ≤ n) (hK : 0 ≤ K) (hd : 1 ≤ d) :
    d * (100 * (P + n * K + 1)) + 3 * n * K <
      2 * (100 * (P + n * K + 1) - P) * (3 * d / 4) := by
  have hd0 : 0 ≤ d := le_trans zero_le_one hd
  have hdP : 0 ≤ d * P := mul_nonneg hd0 hP
  have hnK : 0 ≤ n * K := mul_nonneg hn hK
  have hrest : 0 ≤ (50 * d - 3) * (n * K) :=
    mul_nonneg (by linarith) hnK
  nlinarith

theorem edge_demand_exceeds_capacity (P n K d : ℕ) (hd : 1 ≤ d) :
    (d : ℝ) * (repetitions P n K : ℝ) + 3 * (n : ℝ) * K <
      2 * ((repetitions P n K : ℝ) - P) * (3 * (d : ℝ) / 4) := by
  rw [repetitions_cast]
  exact edge_demand_exceeds_capacity_real (Nat.cast_nonneg P) (Nat.cast_nonneg n)
    (Nat.cast_nonneg K) (by exact_mod_cast hd)

theorem sixty_loss_div_le {ρ d K n : ℝ} (hρ : 0 < ρ) (hd : 0 < d)
    (hK : 0 ≤ K) (hn : 0 ≤ n) (h120 : 120 * K / ρ ≤ d) :
    60 * K * n / d ≤ ρ * n := by
  have hmul := (div_le_iff₀ hρ).mp h120
  have h60 : 60 * K ≤ ρ * d := by nlinarith
  apply (div_le_iff₀ hd).mpr
  calc
    60 * K * n ≤ (ρ * d) * n := mul_le_mul_of_nonneg_right h60 hn
    _ = (ρ * n) * d := by ring

theorem depthDemand_sixty_loss_div_le (c n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    60 * (lossAllowance c : ℝ) * (n : ℝ) / (depthDemand c ρ : ℝ) ≤ ρ * n :=
  sixty_loss_div_le hρ (Nat.cast_pos.mpr (depthDemand_pos c ρ))
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (depthDemand_ge_120_div c ρ)

structure GraphInput where
  n : ℕ
  edges : List (Fin n × Fin n)
  ordered : ∀ e ∈ edges, e.1 < e.2
  distinct : edges.Nodup

namespace GraphInput

abbrev Vertex (G : GraphInput) := Fin G.n

abbrev Edge (G : GraphInput) := Fin G.edges.length

def left (G : GraphInput) (e : G.Edge) : G.Vertex := (G.edges[e]).1

def right (G : GraphInput) (e : G.Edge) : G.Vertex := (G.edges[e]).2

def IsCover (G : GraphInput) (C : Finset G.Vertex) : Prop :=
  ∀ e ∈ G.edges, e.1 ∈ C ∨ e.2 ∈ C

def CoverAtMost (G : GraphInput) (k : ℕ) : Prop :=
  ∃ C : Finset G.Vertex, G.IsCover C ∧ C.card ≤ k

end GraphInput

open scoped BigOperators

namespace GraphInput

def endpoint (G : GraphInput) (e : G.Edge) (s : Fin 2) : G.Vertex :=
  if s = 0 then G.left e else G.right e

@[simp] theorem endpoint_zero (G : GraphInput) (e : G.Edge) :
    G.endpoint e 0 = G.left e := by simp [endpoint]

@[simp] theorem endpoint_one (G : GraphInput) (e : G.Edge) :
    G.endpoint e 1 = G.right e := by simp [endpoint]

theorem left_lt_right (G : GraphInput) (e : G.Edge) : G.left e < G.right e :=
  G.ordered _ (List.getElem_mem e.isLt)

theorem left_ne_right (G : GraphInput) (e : G.Edge) : G.left e ≠ G.right e :=
  (G.left_lt_right e).ne

theorem endpoint_injective (G : GraphInput) (e : G.Edge) :
    Function.Injective (G.endpoint e) := by
  intro s t h
  have hs : s = 0 ∨ s = 1 := by omega
  have ht : t = 0 ∨ t = 1 := by omega
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · rfl
  · exact False.elim (G.left_ne_right e (by simpa using h))
  · exact False.elim (G.left_ne_right e (by simpa using h.symm))
  · rfl

abbrev Incidence (G : GraphInput) (v : G.Vertex) :=
  {es : G.Edge × Fin 2 // G.endpoint es.1 es.2 = v}

def incidenceEquiv (G : GraphInput) :
    (Σ v : G.Vertex, G.Incidence v) ≃ G.Edge × Fin 2 :=
  Equiv.sigmaFiberEquiv (fun es : G.Edge × Fin 2 => G.endpoint es.1 es.2)

def degree (G : GraphInput) (v : G.Vertex) : ℕ :=
  Fintype.card (G.Incidence v)

theorem sum_degree (G : GraphInput) :
    (∑ v : G.Vertex, G.degree v) = 2 * G.edges.length := by
  have h := Fintype.card_congr (G.incidenceEquiv)
  simpa [degree, Fintype.card_sigma, Fintype.card_prod, Nat.mul_comm] using h

abbrev IncidencePosition (G : GraphInput) (R : ℕ) (v : G.Vertex) :=
  G.Incidence v × Fin R

abbrev JobCopy (G : GraphInput) (R d : ℕ) (v : G.Vertex) :=
  G.IncidencePosition R v × Fin d

theorem card_incidencePosition (G : GraphInput) (R : ℕ) (v : G.Vertex) :
    Fintype.card (G.IncidencePosition R v) = R * G.degree v := by
  simp [IncidencePosition, degree, Nat.mul_comm]

theorem card_jobCopy (G : GraphInput) (R d : ℕ) (v : G.Vertex) :
    Fintype.card (G.JobCopy R d v) = d * R * G.degree v := by
  simp [JobCopy, IncidencePosition, degree, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc]

theorem sum_card_jobCopy (G : GraphInput) (R d : ℕ) :
    (∑ v : G.Vertex, Fintype.card (G.JobCopy R d v)) =
      2 * d * G.edges.length * R := by
  simp_rw [card_jobCopy]
  rw [← Finset.mul_sum, sum_degree]
  ac_rfl

end GraphInput

end BinPackingGap

section
open scoped BigOperators

namespace BinPackingGap

variable {V : Type*} [Fintype V] [DecidableEq V]

def thresholdCover (d : ℕ) (xplus : V → ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => (d : ℝ) / 8 < (xplus v : ℝ)

def largePlus (d K : ℕ) (xplus : V → ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => (d : ℝ) - 6 * K ≤ (xplus v : ℝ)

theorem residual_plus_le {d K : ℕ} (xplus xminus : V → ℕ)
    (htotal : (∑ v, (xplus v + xminus v)) ≤ d * Fintype.card V)
    (hside : ∀ v, d ≤ xplus v + 6 * K ∨ d ≤ xminus v + 6 * K) :
    (∑ v, if v ∈ largePlus d K xplus then (0 : ℝ) else (xplus v : ℝ)) ≤
      6 * (K : ℝ) * Fintype.card V := by
  classical
  let charge : V → ℝ := fun v =>
    if v ∈ largePlus d K xplus then (xplus v : ℝ) else (xminus v : ℝ)
  let rest : V → ℝ := fun v =>
    if v ∈ largePlus d K xplus then 0 else (xplus v : ℝ)
  have hcharge : ∀ v, (d : ℝ) - 6 * K ≤ charge v := by
    intro v
    by_cases hv : v ∈ largePlus d K xplus
    · simpa only [charge, ite_eq_left hv] using (Finset.mem_filter.mp hv).2
    · have hnot : ¬ ((d : ℝ) - 6 * K ≤ (xplus v : ℝ)) := by
        simpa [largePlus] using hv
      rcases hside v with hp | hm
      · have hp' : (d : ℝ) ≤ (xplus v : ℝ) + 6 * K := by exact_mod_cast hp
        exact (hnot (by linarith)).elim
      · have hm' : (d : ℝ) ≤ (xminus v : ℝ) + 6 * K := by exact_mod_cast hm
        simp only [charge, ite_eq_right hv]
        linarith
  have hcharged : (Fintype.card V : ℝ) * ((d : ℝ) - 6 * K) ≤ ∑ v, charge v := by
    calc
      _ = ∑ _v : V, ((d : ℝ) - 6 * K) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ v, charge v := Finset.sum_le_sum fun v _ => hcharge v
  have hpoint : ∀ v, charge v + rest v ≤ (xplus v : ℝ) + xminus v := by
    intro v
    dsimp only [charge, rest]
    split_ifs <;> nlinarith [show (0 : ℝ) ≤ xplus v from Nat.cast_nonneg _,
      show (0 : ℝ) ≤ xminus v from Nat.cast_nonneg _]
  have hsum : (∑ v, charge v) + (∑ v, rest v) ≤
      (d : ℝ) * Fintype.card V := by
    calc
      _ = ∑ v, (charge v + rest v) := (Finset.sum_add_distrib).symm
      _ ≤ ∑ v, ((xplus v : ℝ) + xminus v) := Finset.sum_le_sum fun v _ => hpoint v
      _ ≤ (d : ℝ) * Fintype.card V := by exact_mod_cast htotal
  change (∑ v, rest v) ≤ _
  nlinarith

theorem thresholdCover_card_le_fractions {d K k : ℕ} (xplus xminus : V → ℕ)
    (hd : 0 < d) (h72 : 72 * K ≤ d)
    (hplus : (∑ v, xplus v) ≤ d * k)
    (htotal : (∑ v, (xplus v + xminus v)) ≤ d * Fintype.card V)
    (hside : ∀ v, d ≤ xplus v + 6 * K ∨ d ≤ xminus v + 6 * K) :
    ((thresholdCover d xplus).card : ℝ) ≤
      (d : ℝ) * k / ((d : ℝ) - 6 * K) + 48 * (K : ℝ) * Fintype.card V / d := by
  classical
  let A := largePlus d K xplus
  let C := thresholdCover d xplus
  let B := C \ A
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h72' : 72 * (K : ℝ) ≤ d := by exact_mod_cast h72
  have hgap := threshold_gap hd0 h72'
  have hden : 0 < (d : ℝ) - 6 * K := lt_trans (by positivity) hgap
  have hAC : A ⊆ C := by
    intro v hv
    have hv' : (d : ℝ) - 6 * K ≤ (xplus v : ℝ) := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hgap.trans_le hv'⟩
  have hAlower : (A.card : ℝ) * ((d : ℝ) - 6 * K) ≤ ∑ v, (xplus v : ℝ) := by
    calc
      _ = ∑ _v ∈ A, ((d : ℝ) - 6 * K) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ v ∈ A, (xplus v : ℝ) :=
        Finset.sum_le_sum fun v hv => (Finset.mem_filter.mp hv).2
      _ ≤ ∑ v, (xplus v : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
  have hA : (A.card : ℝ) ≤ (d : ℝ) * k / ((d : ℝ) - 6 * K) := by
    apply (le_div_iff₀ hden).mpr
    exact hAlower.trans (by exact_mod_cast hplus)
  let rest : V → ℝ := fun v => if v ∈ A then 0 else (xplus v : ℝ)
  have hrest : (∑ v, rest v) ≤ 6 * (K : ℝ) * Fintype.card V :=
    residual_plus_le xplus xminus htotal hside
  have hBlower : (B.card : ℝ) * ((d : ℝ) / 8) ≤ ∑ v, rest v := by
    calc
      _ = ∑ _v ∈ B, ((d : ℝ) / 8) := by simp
      _ ≤ ∑ v ∈ B, rest v := by
        apply Finset.sum_le_sum
        intro v hv
        obtain ⟨hvC, hvA⟩ := Finset.mem_sdiff.mp hv
        have hv' : (d : ℝ) / 8 < (xplus v : ℝ) := (Finset.mem_filter.mp hvC).2
        simpa only [rest, ite_eq_right hvA] using hv'.le
      _ ≤ ∑ v, rest v := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro v _ _
        dsimp only [rest]
        split_ifs <;> positivity
  have hB : (B.card : ℝ) ≤ 48 * (K : ℝ) * Fintype.card V / d := by
    apply (le_div_iff₀ hd0).mpr
    nlinarith
  have hcard : (C.card : ℝ) = (A.card : ℝ) + B.card := by
    have hh := Finset.card_sdiff_add_card_eq_card hAC
    dsimp only [B]
    exact_mod_cast hh.symm.trans (Nat.add_comm _ _)
  change (C.card : ℝ) ≤ _
  rw [hcard]
  exact add_le_add hA hB

theorem cover_fraction_bound {d K k n : ℝ} (hd : 0 < d) (hK : 0 ≤ K)
    (hk0 : 0 ≤ k) (hkn : k ≤ n) (h12 : 12 * K ≤ d) :
    d * k / (d - 6 * K) + 48 * K * n / d ≤ k + 60 * K * n / d := by
  have hn : 0 ≤ n := hk0.trans hkn
  have hden : 0 < d - 6 * K := by linarith
  have hmult := mul_le_mul_of_nonneg_left hkn (show 0 ≤ 6 * K * d by positivity)
  have hslack := mul_nonneg (show 0 ≤ 6 * K * n by positivity) (sub_nonneg.mpr h12)
  have hfrac : 6 * K * k / (d - 6 * K) ≤ 12 * K * n / d := by
    apply (div_le_div_iff₀ hden hd).mpr
    nlinarith
  have hid : d * k / (d - 6 * K) = k + 6 * K * k / (d - 6 * K) := by
    field_simp [hden.ne']; ring
  rw [hid]
  have hsplit : 60 * K * n / d = 12 * K * n / d + 48 * K * n / d := by ring
  rw [hsplit]
  linarith

theorem thresholdCover_card_le {d K k : ℕ} {ρ : ℝ} (xplus xminus : V → ℕ)
    (hd : 0 < d) (h72 : 72 * K ≤ d) (hk : k ≤ Fintype.card V)
    (hρ : 0 < ρ) (h120 : 120 * (K : ℝ) / ρ ≤ d)
    (hplus : (∑ v, xplus v) ≤ d * k)
    (htotal : (∑ v, (xplus v + xminus v)) ≤ d * Fintype.card V)
    (hside : ∀ v, d ≤ xplus v + 6 * K ∨ d ≤ xminus v + 6 * K) :
    ((thresholdCover d xplus).card : ℝ) ≤ (k : ℝ) + ρ * Fintype.card V := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h72' : 72 * (K : ℝ) ≤ d := by exact_mod_cast h72
  calc
    _ ≤ (d : ℝ) * k / ((d : ℝ) - 6 * K) + 48 * (K : ℝ) * Fintype.card V / d :=
      thresholdCover_card_le_fractions xplus xminus hd h72 hplus htotal hside
    _ ≤ (k : ℝ) + 60 * (K : ℝ) * Fintype.card V / d :=
      cover_fraction_bound hd0 (Nat.cast_nonneg K) (Nat.cast_nonneg k)
        (by exact_mod_cast hk) (by linarith)
    _ ≤ (k : ℝ) + ρ * Fintype.card V :=
      add_le_add (le_refl (k : ℝ)) (sixty_loss_div_le hρ hd0 (Nat.cast_nonneg K)
        (Nat.cast_nonneg _) h120)

theorem longMatch_sum_lower {R P : ℕ} (S : Finset (Fin R)) (L : Fin R → ℕ)
    {a : ℝ} (ha : 0 ≤ a) (hS : (R : ℝ) - P ≤ (S.card : ℝ))
    (hL : ∀ j ∈ S, a ≤ (L j : ℝ)) :
    ((R : ℝ) - P) * a ≤ ∑ j, (L j : ℝ) := by
  calc
    _ ≤ (S.card : ℝ) * a := mul_le_mul_of_nonneg_right hS ha
    _ = ∑ _j ∈ S, a := by simp
    _ ≤ ∑ j ∈ S, (L j : ℝ) := Finset.sum_le_sum hL
    _ ≤ ∑ j, (L j : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)

theorem thresholdCover_isCover (G : GraphInput) {d K P R : ℕ}
    (xplus : G.Vertex → ℕ)
    (Sleft Sright : G.Edge → Finset (Fin R))
    (Lleft Lright : G.Edge → Fin R → ℕ)
    (hd : 1 ≤ d) (h72 : 72 * K ≤ d) (hR : R = repetitions P G.n K)
    (hSleft : ∀ e, (R : ℝ) - P ≤ ((Sleft e).card : ℝ))
    (hSright : ∀ e, (R : ℝ) - P ≤ ((Sright e).card : ℝ))
    (hLleft : ∀ e j, j ∈ Sleft e → d ≤ Lleft e j + xplus (G.left e) + 9 * K)
    (hLright : ∀ e j, j ∈ Sright e → d ≤ Lright e j + xplus (G.right e) + 9 * K)
    (hcapacity : ∀ e, (∑ j, Lleft e j) + (∑ j, Lright e j) ≤
      d * R + 3 * G.n * K) :
    G.IsCover (thresholdCover d xplus) := by
  classical
  let C := thresholdCover d xplus
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
  have h72' : 72 * (K : ℝ) ≤ d := by exact_mod_cast h72
  have hstrict : (d : ℝ) * R + 3 * (G.n : ℝ) * K <
      2 * ((R : ℝ) - P) * (3 * (d : ℝ) / 4) := by
    rw [hR]
    exact edge_demand_exceeds_capacity P G.n K d hd
  have hindex : ∀ e : G.Edge, G.left e ∈ C ∨ G.right e ∈ C := by
    intro e
    by_cases hv : G.left e ∈ C
    · exact Or.inl hv
    right
    by_contra hw
    have hxleft : (xplus (G.left e) : ℝ) ≤ (d : ℝ) / 8 := by
      apply le_of_not_gt
      simpa [C, thresholdCover] using hv
    have hxright : (xplus (G.right e) : ℝ) ≤ (d : ℝ) / 8 := by
      apply le_of_not_gt
      simpa [C, thresholdCover] using hw
    have hleft : ((R : ℝ) - P) * (3 * (d : ℝ) / 4) ≤
        ∑ j, (Lleft e j : ℝ) := by
      apply longMatch_sum_lower _ _ (by positivity) (hSleft e)
      intro j hj
      have hmatch : (d : ℝ) ≤ (Lleft e j : ℝ) + xplus (G.left e) + 9 * K := by
        exact_mod_cast hLleft e j hj
      exact three_quarter_lower h72' hxleft (by linarith)
    have hright : ((R : ℝ) - P) * (3 * (d : ℝ) / 4) ≤
        ∑ j, (Lright e j : ℝ) := by
      apply longMatch_sum_lower _ _ (by positivity) (hSright e)
      intro j hj
      have hmatch : (d : ℝ) ≤ (Lright e j : ℝ) + xplus (G.right e) + 9 * K := by
        exact_mod_cast hLright e j hj
      exact three_quarter_lower h72' hxright (by linarith)
    have hcap : (∑ j, (Lleft e j : ℝ)) + (∑ j, (Lright e j : ℝ)) ≤
        (d : ℝ) * R + 3 * (G.n : ℝ) * K := by exact_mod_cast hcapacity e
    linarith
  intro e he
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp he
  have h := hindex ⟨i, hi⟩
  change (G.edges[i]).1 ∈ C ∨ (G.edges[i]).2 ∈ C at h
  rw [heq] at h
  exact h

theorem thresholdCover_card_le_graph (G : GraphInput) {d K k : ℕ} {ρ : ℝ}
    (xplus xminus : G.Vertex → ℕ)
    (hd : 0 < d) (h72 : 72 * K ≤ d) (hk : k ≤ G.n)
    (hρ : 0 < ρ) (h120 : 120 * (K : ℝ) / ρ ≤ d)
    (hplus : (∑ v, xplus v) ≤ d * k)
    (htotal : (∑ v, (xplus v + xminus v)) ≤ d * G.n)
    (hside : ∀ v, d ≤ xplus v + 6 * K ∨ d ≤ xminus v + 6 * K) :
    ((thresholdCover d xplus).card : ℝ) ≤ (k : ℝ) + ρ * G.n := by
  simpa only [Fintype.card_fin] using
    thresholdCover_card_le xplus xminus hd h72
      (by simpa only [Fintype.card_fin] using hk) hρ h120 hplus
      (by simpa only [Fintype.card_fin] using htotal) hside

end BinPackingGap

end

namespace BinPackingGap

def completeFourGraph : GraphInput where
  n := 4
  edges := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
  ordered := by decide
  distinct := by decide

theorem completeFourGraph_edge_pos : 0 < completeFourGraph.edges.length := by decide

theorem completeFourGraph_cover_card {C : Finset completeFourGraph.Vertex}
    (hC : completeFourGraph.IsCover C) : 3 ≤ C.card := by
  classical
  change Finset (Fin 4) at C
  change 3 ≤ C.card
  change ∀ e : Fin 4 × Fin 4,
    e ∈ [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] →
      e.1 ∈ C ∨ e.2 ∈ C at hC
  have h01 : (0 : Fin 4) ∈ C ∨ (1 : Fin 4) ∈ C :=
    hC ((0 : Fin 4), (1 : Fin 4)) (by decide)
  have h02 : (0 : Fin 4) ∈ C ∨ (2 : Fin 4) ∈ C :=
    hC ((0 : Fin 4), (2 : Fin 4)) (by decide)
  have h03 : (0 : Fin 4) ∈ C ∨ (3 : Fin 4) ∈ C :=
    hC ((0 : Fin 4), (3 : Fin 4)) (by decide)
  have h12 : (1 : Fin 4) ∈ C ∨ (2 : Fin 4) ∈ C :=
    hC ((1 : Fin 4), (2 : Fin 4)) (by decide)
  have h13 : (1 : Fin 4) ∈ C ∨ (3 : Fin 4) ∈ C :=
    hC ((1 : Fin 4), (3 : Fin 4)) (by decide)
  have h23 : (2 : Fin 4) ∈ C ∨ (3 : Fin 4) ∈ C :=
    hC ((2 : Fin 4), (3 : Fin 4)) (by decide)
  have hsmall : (Finset.univ \ C).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hxC : x ∉ C := (Finset.mem_sdiff.mp hx).2
    have hyC : y ∉ C := (Finset.mem_sdiff.mp hy).2
    fin_cases x <;> fin_cases y <;> simp_all
  have htotal : (Finset.univ \ C).card + C.card = 4 := by
    simpa only [Finset.card_univ, Fintype.card_fin, completeFourGraph] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ C)
  omega

theorem completeFourGraph_cover_three : completeFourGraph.CoverAtMost 3 := by
  change ∃ C : Finset (Fin 4),
    (∀ e : Fin 4 × Fin 4,
      e ∈ [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] →
        e.1 ∈ C ∨ e.2 ∈ C) ∧ C.card ≤ 3
  exact ⟨{0, 1, 2}, by decide, by decide⟩

theorem completeFourGraph_no_small_cover :
    ¬ ∃ C : Finset completeFourGraph.Vertex,
      completeFourGraph.IsCover C ∧
        (C.card : ℝ) ≤ 2 + (1 / 8 : ℝ) * completeFourGraph.n := by
  rintro ⟨C, hC, hcard⟩
  have hthree : (3 : ℝ) ≤ C.card := by exact_mod_cast completeFourGraph_cover_card hC
  norm_num [completeFourGraph] at hcard
  linarith

end BinPackingGap

end

end OAI
