import Mathlib
import OAI.Combinatorics.UniformKServer.BitPaths
import OAI.Combinatorics.UniformKServer.EpochShadow

namespace OAI

namespace UniformKServer.EpochExpectation
open EpochShadow

abbrev BState (n k : ℕ) := List (Fin n) × Configuration n k

def next {n k : ℕ} (s : BState n k) (r : Fin n) (j : Fin k) : BState n k :=
  (s.1 ++ [r], serve s.2 r j)

def charge {n k : ℕ} (d : RationalMetric n) (s : BState n k) (r : Fin n) (j : Fin k) : ℝ :=
  d.distance (s.2 j) r

def selector {n k b : ℕ} (N : BState n k → Fin n → Fin k → ℕ)
    (hN : ∀ s r, ∑ j, N s r j = 2^b) (coins : ℕ → Fin b → Bool) : Selector n k :=
  fun p c r => BitSampling.row (N (p,c) r) (hN (p,c) r) (coins p.length)

def extend {m b : ℕ} (coins : Fin m → Fin b → Bool) (t : ℕ) : Fin b → Bool :=
  if h : t < m then coins ⟨t,h⟩ else fun _ => false

/-- Exact finite product of the fresh bits assigned to the deterministic kept
word. Extra shadow bits after a switch are analytical only. -/
def epochTrace {n k b : ℕ} (hk : 0 < k) (M : ℕ)
    (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀ s r, ∑ j, N s r j = 2^b)
    (u : Configuration n k) (raw : List (Fin n))
    (coins : Fin (keptTail M (initial u) raw).length → Fin b → Bool) : History n k :=
  trace hk M (selector N hN (extend coins)) (initial u) ⟨u,0⟩ ∅ raw

theorem selector_lazy {n k b : ℕ} (N : BState n k → Fin n → Fin k → ℕ)
    (hN : ∀ s r, ∑ j, N s r j = 2^b)
    (hLazy : ∀ s r j, (∃ i, s.2 i = r) → s.2 j ≠ r → N s r j = 0)
    (coins : ℕ → Fin b → Bool) : StronglyLazy (selector N hN coins) := by
  intro p c r hc
  by_contra hn
  have hz := hLazy (p,c) r (selector N hN coins p c r) hc hn
  have hp := (BitSampling.exact_row (N (p,c) r) (hN (p,c) r)).1 (coins p.length)
  change 0 < N (p,c) r (selector N hN coins p c r) at hp
  omega

theorem shadow_cost {n k b : ℕ} (d : RationalMetric n)
    (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀ s r, ∑ j, N s r j = 2^b)
    (coins : ℕ → Fin b → Bool) (p : List (Fin n)) (c : Configuration n k)
    (w : List (Fin n)) :
    costAlong d c (shadowTrace (selector N hN coins) p c w) =
      BitSampling.runCost N hN next (charge d) (p,c) w
        (fun i => coins (p.length + i.val)) := by
  induction w generalizing p c with
  | nil => rfl
  | cons r w ih =>
    simp only [shadowTrace, costAlong, BitSampling.runCost, selector, Fin.val_zero,
      add_zero, next, charge, ih]
    congr 1
    congr 1
    funext i
    simp only [List.length_append, List.length_cons, List.length_nil, zero_add,
      Fin.tail, Fin.val_succ]
    congr 1
    omega

theorem shadow_full {n k b : ℕ} (d : RationalMetric n)
    (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀ s r, ∑ j, N s r j = 2^b)
    (c : Configuration n k) (w : List (Fin n)) (coins : Fin w.length → Fin b → Bool) :
    costAlong d c (shadowTrace (selector N hN (extend coins)) [] c w) =
      BitSampling.runCost N hN next (charge d) ([],c) w coins := by
  rw [shadow_cost]
  congr 1
  funext i
  simp [extend, i.isLt]

theorem kept_sublist {n k : ℕ} (M : ℕ) (f : FilterState n k) (w : List (Fin n)) :
    (keptTail M f w).Sublist w := by
  induction w generalizing f with
  | nil => exact List.Sublist.refl _
  | cons r w ih =>
    unfold keptTail
    split_ifs
    · exact (ih f).cons r
    · exact (ih _).cons_cons r

theorem mean_mono {A : Type*} [Fintype A] (f g : A → ℝ) (h : ∀ a, f a ≤ g a) :
    BitSampling.mean f ≤ BitSampling.mean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (by positivity)

theorem mean_mul {A : Type*} [Fintype A] (c : ℝ) (f : A → ℝ) :
    BitSampling.mean (fun a => c * f a) = c * BitSampling.mean f := by
  simp only [BitSampling.mean, ← Finset.mul_sum, mul_div_assoc]

                                                                          
                                                                         
                                                                               
theorem comparison {n k b : ℕ} (hk : 0 < k) (hk2 : 2 ≤ k) (d : RationalMetric n)
    (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀ s r, ∑ j, N s r j = 2^b)
    (hLazy : ∀ s r j, (∃ i, s.2 i = r) → s.2 j ≠ r → N s r j = 0)
    (u s c : Configuration n k) (hu : Function.Injective u) (M R : ℕ)
    (D δ a : ℝ) (hD : 0 ≤ D) (hδ : 0 ≤ δ) (ha : 0 ≤ a)
    (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (hcap : R * (k+1) * D ≤ (M+1) * δ)
    (hTable : ∀ w : List (Fin n), w.length ≤ horizon k M →
      BitSampling.mean (BitSampling.runCost N hN next (charge d) ([],u) w) ≤
        a * offlineCost d u w + D)
    (raw : List (Fin n)) (hR : blockCount (k:=k) ∅ raw ≤ R)
    (g : History n k) (hg : g.map Prod.fst = raw) :
    (∀ coins, (epochTrace hk M N hN u raw coins).map Prod.fst = raw) ∧
    BitSampling.mean (fun coins => costAlong d s (epochTrace hk M N hN u raw coins)) ≤
      2*a*costAlong d c g + (2*a+2)*k*D := by
  have hl := selector_lazy N hN hLazy
  refine ⟨fun coins => (epoch_virtual_bound hk d _ (hl _) u hu M R D δ hD hδ
    hdiam hsep hcap raw hR).1, ?_⟩
  let w := keptTail M (initial u) raw
  have hw : w.length ≤ horizon k M := by
    simpa only [w, kept_tail_full] using (filter_bounds M u raw).2.2
  have hsub : w.Sublist (g.map Prod.fst) := by
    rw [hg]; exact kept_sublist M (initial u) raw
  obtain ⟨g',hgg',hew⟩ := List.sublist_map_iff.mp hsub
  have hopt : offlineCost d u w ≤ costAlong d c g + k*D := by
    rw [hew]
    exact (subsequence_cost_transfer d u c g' g hgg' D hdiam).2.2
  have ht := hTable w hw
  have hb := mean_mono
    (fun coins => costAlong d s (epochTrace hk M N hN u raw coins))
    (fun coins => 2 * BitSampling.runCost N hN next (charge d) ([],u) w coins + k*D)
    (fun coins => by
      have hh := epoch_actual_bound hk d _ (hl (extend coins)) u s hu M R D δ hD hδ
        hdiam hsep hcap raw hR
      simpa only [epochTrace, shadow_full] using hh)
  rw [BitSampling.mean_add, mean_mul, BitSampling.mean_const] at hb
  have hmul := mul_le_mul_of_nonneg_left hopt ha
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hKD := mul_le_mul_of_nonneg_right hk' hD
  nlinarith

end UniformKServer.EpochExpectation



end OAI
