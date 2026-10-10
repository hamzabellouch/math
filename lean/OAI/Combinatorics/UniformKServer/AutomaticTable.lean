import Mathlib
import OAI.Combinatorics.UniformKServer.FiniteTable
import OAI.Combinatorics.UniformKServer.ExecutableDyadic

namespace OAI

namespace UniformKServer.AutomaticTable
open EffectiveLP

def assignment {n k H : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) :
    Fin (Fintype.card (Variable n k H)+1) → ℚ :=
  (FourierMotzkin.optimize (Fintype.card (Variable n k H)) (constraints d u)).getD (fun _ => 0)

def flow {n k H : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) :
    BoundedFlow n k H ℚ := ofAssignment (Form.recover (assignment d u))

def coefficient {n k : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) (H : ℕ) : ℚ :=
  FourierMotzkin.objective (assignment (H:=H) d u)

abbrev State (n k : ℕ) := List (Fin n) × Config n k

def qrow {n k : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) (H : ℕ)
    (s : State n k) (r : Fin n) (j : Fin k) : ℚ :=
  FiniteTable.row (flow (H:=H) d u) s.1 r s.2 j

def next {n k : ℕ} (s : State n k) (r : Fin n) (j : Fin k) : State n k :=
  (s.1 ++ [r], FiniteTable.next s.2 r j)

def charge {n k : ℕ} (d : RationalMetric n) (s : State n k) (r : Fin n) (j : Fin k) : ℚ :=
  d.distance (s.2.val j) r

def bitWidth (k H : ℕ) : ℕ := Nat.clog 2 (k * H^2)

def counts {n k : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) (H : ℕ)
    (s : State n k) (r : Fin n) (j : Fin k) : ℕ :=
  ExecutableDyadic.numerators (qrow d u H s r) (FiniteTable.fallback s.2 r) (2^(bitWidth k H)) j

theorem flow_valid {n k H : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) :
    Valid d u (flow (H:=H) d u) (coefficient d u H) ∧
    ∀ (F : BoundedFlow n k H ℝ) (a : ℝ), Valid d u F a →
      (coefficient d u H : ℝ) ≤ a := by
  obtain ⟨x,hx,hv,hm⟩ := unconditional_optimization (H:=H) d u
  simpa only [flow, coefficient, assignment, hx, Option.getD_some] using And.intro hv hm

theorem rationalCost_eq {n k : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k)
    (H : ℕ) (s : State n k) (w : List (Fin n)) :
    ExecutableDyadic.rationalCost (qrow d u H) next (charge d) s w =
      FiniteFlow.cost (FiniteTable.row (flow (H:=H) d u)) FiniteTable.next
        (FiniteTable.charge d) s.1 s.2 w := by
  induction w generalizing s with
  | nil => rfl
  | cons r w ih =>
    simp only [ExecutableDyadic.rationalCost, FiniteFlow.cost, ih]
    rfl

theorem row_facts {n k : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) (H : ℕ) :
    (∀ s r j, 0 ≤ qrow d u H s r j) ∧
    (∀ s r, ∑ j, qrow d u H s r j = 1) ∧
    (∀ s r j, j ∉ labels s.2 r → qrow d u H s r j = 0) ∧
    (∀ w : List (Fin n), w.length ≤ H →
      ExecutableDyadic.rationalCost (qrow d u H) next (charge d) ([],u) w ≤
        coefficient d u H * OfflineDynamic.optRat d u.val w) := by
  obtain ⟨hn,hs,hp,hc⟩ := FiniteTable.realize d u (flow (H:=H) d u)
    (coefficient d u H) (flow_valid d u).1
  refine ⟨fun s r j => hn s.1 r s.2 j, fun s r => hs s.1 r s.2,
    fun s r j => hp s.1 r s.2 j, ?_⟩
  intro w hw
  simpa only [rationalCost_eq] using hc w hw

theorem error_bound {k H h : ℕ} (hh : h ≤ H) (D : ℝ) (hD : 0 ≤ D) :
    (k : ℝ) * (h : ℝ)^2 / ((2^(bitWidth k H) : ℕ) : ℝ) * D ≤ D := by
  have hb : (0 : ℝ) < (2^(bitWidth k H) : ℕ) := by positivity
  have hle : k * h^2 ≤ 2^(bitWidth k H) :=
    (Nat.mul_le_mul_left k (Nat.pow_le_pow_left hh 2)).trans (Nat.le_pow_clog (by omega) _)
  have hle' : (k : ℝ) * (h : ℝ)^2 ≤ (2^(bitWidth k H) : ℕ) := by exact_mod_cast hle
  have := mul_le_mul_of_nonneg_right ((div_le_one hb).mpr hle') hD
  simpa using this

/-- Total deterministic construction, exact-bit legal realization, and the
finite-word inequality of source Proposition finite-table. The sharp coefficient
is deliberately exposed as optimization against real feasible flows, not assumed
from an unproved companion theorem. -/
theorem construct {n k : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k)
    (H : ℕ) (D : ℝ) (hD : 0 ≤ D) (hd : ∀ x y, (d.distance x y : ℝ) ≤ D) :
    0 ≤ coefficient d u H ∧
    (∀ (F : BoundedFlow n k H ℝ) (a : ℝ), Valid d u F a →
      (coefficient d u H : ℝ) ≤ a) ∧
    (k * H^2 ≤ 2^(bitWidth k H)) ∧
    (∀ b, k * H^2 ≤ 2^b → bitWidth k H ≤ b) ∧
    ∃ hN : ∀ s r, ∑ j, counts d u H s r j = 2^(bitWidth k H),
      (∀ s r coins, BitSampling.row (counts d u H s r) (hN s r) coins ∈ labels s.2 r) ∧
      (∀ w : List (Fin n), w.length ≤ H →
        BitSampling.mean (BitSampling.runCost (counts d u H) hN next
          (fun s r j => (charge d s r j : ℝ)) ([],u) w) ≤
          (coefficient d u H : ℝ) * offlineCost d u.val w + D) := by
  obtain ⟨hn,hs,hp,hc⟩ := row_facts d u H
  obtain ⟨hN,hz,he⟩ := ExecutableDyadic.finite_bit_perturbation (qrow d u H) hn hs
    (fun s r => FiniteTable.fallback s.2 r) (bitWidth k H) next (charge d)
    (fun s r j => d.nonneg (s.2.val j) r) D hD (fun s r j => hd (s.2.val j) r)
  refine ⟨(flow_valid d u).1.1, (flow_valid d u).2,
    Nat.le_pow_clog (by omega) _, fun b hb => (Nat.clog_le_iff_le_pow (by omega)).mpr hb,
    hN, ?_, ?_⟩
  · intro s r coins
    by_contra hbad
    have hj : BitSampling.row (counts d u H s r) (hN s r) coins ≠ FiniteTable.fallback s.2 r := by
      intro heq
      exact hbad (heq ▸ FiniteTable.fallback_mem s.2 r)
    have hzero := hz s r _ hj (hp s r _ hbad)
    have hpositive := (BitSampling.exact_row (counts d u H s r) (hN s r)).1 coins
    change 0 < ExecutableDyadic.numerators _ _ _ _ at hpositive
    rw [hzero] at hpositive
    omega
  · intro w hw
    have hce : (ExecutableDyadic.rationalCost (qrow d u H) next (charge d) ([],u) w : ℝ) ≤
        (coefficient d u H : ℝ) * (OfflineDynamic.optRat d u.val w : ℝ) := by
      exact_mod_cast hc w hw
    rw [OfflineDynamic.offline_eq_optRat]
    exact (he ([],u) w).trans (add_le_add hce (error_bound hw D hD))

end UniformKServer.AutomaticTable



end OAI
