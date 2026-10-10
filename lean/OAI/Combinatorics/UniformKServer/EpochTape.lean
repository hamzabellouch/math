import Mathlib
import OAI.Combinatorics.UniformKServer.EpochExpectation

namespace OAI

noncomputable section
                                
section

namespace UniformKServer.EpochTape
open EpochShadow EpochExpectation

theorem mean_restrict {m H : ℕ} (h : m ≤ H) {A : Type*} [Fintype A] [Nonempty A]
    (f : (Fin m → A) → ℝ) :
    BitSampling.mean (fun g : Fin H → A => f (fun i => g (Fin.castLE h i))) =
      BitSampling.mean f := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
  have he := BitSampling.mean_equiv (Fin.appendEquiv (α:=A) m d)
    (fun g : Fin (m+d) → A => f (fun i => g (Fin.castLE (by omega) i)))
  have hh : (fun p : (Fin m → A) × (Fin d → A) =>
      f (fun i => Fin.append p.1 p.2 (Fin.castLE (by omega) i))) = fun p => f p.1 := by
    funext p
    congr 1
    funext i
    change Fin.append p.1 p.2 (Fin.castAdd d i) = p.1 i
    simp
  change BitSampling.mean (fun p : (Fin m → A) × (Fin d → A) =>
    f (fun i => Fin.append p.1 p.2 (Fin.castLE (by omega) i))) = _ at he
  rw [hh] at he
  rw [← he, BitSampling.mean_prod]
  simp only [BitSampling.mean_const]

theorem trace_congr {n k : ℕ} (hk : 0 < k) (M m : ℕ)
    (T U : Selector n k) (hTU : ∀p c r,p.length < m → T p c r=U p c r)
    (f : FilterState n k) (e : Entry n k) (seen : Finset (Fin n))
    (w : List (Fin n)) (hb : f.kept.length+(keptTail M f w).length ≤ m) :
    trace hk M T f e seen w = trace hk M U f e seen w := by
  induction w generalizing f e seen with
  | nil => rfl
  | cons r w ih =>
    by_cases hs : ∀ z ∈ f.live,Covers z r
    · simp only [trace,ite_eq_left hs]
      congr 1
      apply ih
      simpa only [keptTail,ite_eq_left hs] using hb
    · have hl : f.kept.length < m := by
        simp only [keptTail,ite_eq_right hs,List.length_cons] at hb
        omega
      have ht := hTU f.kept e.position r hl
      simp only [trace,ite_eq_right hs,ht]
      congr 1
      split_ifs
      · apply ih
        simp only [keptTail,ite_eq_right hs] at hb
        simpa only [UniformKServer.step,ite_eq_right hs,List.length_append,
          List.length_singleton,List.length_cons,List.length_nil,Nat.zero_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb
      · rfl

def fullTrace {n k b H : ℕ} (hk : 0 < k) (M : ℕ)
    (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀s r,∑j,N s r j=2^b)
    (u : Configuration n k) (w : List (Fin n)) (coins : Fin H → Fin b → Bool) : History n k :=
  trace hk M (selector N hN (extend coins)) (initial u) ⟨u,0⟩ ∅ w

theorem fullTrace_restrict {n k b H : ℕ} (hk : 0 < k) (M : ℕ)
    (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀s r,∑j,N s r j=2^b)
    (u : Configuration n k) (w : List (Fin n))
    (hb : (keptTail M (initial u) w).length ≤ H) (coins : Fin H → Fin b → Bool) :
    fullTrace hk M N hN u w coins =
      epochTrace hk M N hN u w (fun i => coins (Fin.castLE hb i)) := by
  apply trace_congr hk M (keptTail M (initial u) w).length
  · intro p c r hp
    have hpH : p.length < H := hp.trans_le hb
    simp only [selector,extend,dite_eq_left hp,dite_eq_left hpH]
    rfl
  · simp [initial]

theorem kept_bound {n k : ℕ} (M : ℕ) (u : Configuration n k) (w : List (Fin n)) :
    (keptTail M (initial u) w).length ≤ horizon k M := by
  rw [kept_tail_full]
  exact (filter_bounds M u w).2.2

theorem full_mean {n k b : ℕ} (hk : 0 < k) (M : ℕ)
    (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀s r,∑j,N s r j=2^b)
    (u : Configuration n k) (w : List (Fin n)) (f : History n k → ℝ) :
    BitSampling.mean (fun coins : Fin (horizon k M) → Fin b → Bool =>
      f (fullTrace hk M N hN u w coins)) =
    BitSampling.mean (fun coins => f (epochTrace hk M N hN u w coins)) := by
  simp_rw [fullTrace_restrict hk M N hN u w (kept_bound M u w)]
  exact mean_restrict (kept_bound M u w) (fun coins => f (epochTrace hk M N hN u w coins))

end UniformKServer.EpochTape

end


end

end OAI
