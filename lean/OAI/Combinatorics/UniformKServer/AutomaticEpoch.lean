import Mathlib
import OAI.Combinatorics.UniformKServer.AutomaticTable
import OAI.Combinatorics.UniformKServer.EpochExpectation

namespace OAI

namespace UniformKServer.AutomaticEpoch
open EffectiveLP

def baseLabel {n k : ℕ} [NeZero k] (c : Configuration n k) (r : Fin n) : Fin k :=
  Fallback.pick (NeZero.pos k) (Fallback.coverers c r)

def counts {n k : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) (H : ℕ)
    (s : EpochExpectation.BState n k) (r : Fin n) (j : Fin k) : ℕ :=
  if hc : Function.Injective s.2 then AutomaticTable.counts d u H (s.1,⟨s.2,hc⟩) r j
  else if j = baseLabel s.2 r then 2^(AutomaticTable.bitWidth k H) else 0

theorem base_covers {n k : ℕ} [NeZero k] (c : Configuration n k) (r : Fin n)
    (h : ∃ j, c j = r) : c (baseLabel c r) = r := by
  apply (Fallback.mem_coverers _ _ _).mp
  apply Fallback.pick_mem
  obtain ⟨j,hj⟩ := h
  exact ⟨j,(Fallback.mem_coverers _ _ _).mpr hj⟩

theorem total {n k : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) (H : ℕ) :
    ∀ s r, ∑ j, counts d u H s r j = 2^(AutomaticTable.bitWidth k H) := by
  intro s r
  by_cases hc : Function.Injective s.2
  · simp only [counts, dite_eq_left hc]
    exact ExecutableDyadic.numerators_sum _ ((AutomaticTable.row_facts d u H).1 _ _)
      ((AutomaticTable.row_facts d u H).2.1 _ _)
      (FiniteTable.fallback ⟨s.2,hc⟩ r) _ (by positivity)
  · simp [counts, hc]

theorem forbidden {n k : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) (H : ℕ) :
    ∀ s r j, (∃ i, s.2 i = r) → s.2 j ≠ r → counts d u H s r j = 0 := by
  intro s r j hhit hbad
  by_cases hc : Function.Injective s.2
  · have hj : j ∉ labels ⟨s.2,hc⟩ r := by simp [labels, hhit, hbad]
    have hres : j ≠ FiniteTable.fallback ⟨s.2,hc⟩ r := by
      intro he
      exact hj (he ▸ FiniteTable.fallback_mem ⟨s.2,hc⟩ r)
    have hq := (AutomaticTable.row_facts d u H).2.2.1 (s.1,⟨s.2,hc⟩) r j hj
    simp only [counts, dite_eq_left hc, AutomaticTable.counts, ExecutableDyadic.numerators,
      ite_eq_right hres, hq, mul_zero, Nat.floor_zero]
  · have hj : j ≠ baseLabel s.2 r := by
      intro he; exact hbad (he ▸ base_covers s.2 r hhit)
    simp [counts, hc, hj]

theorem runCost_eq {n k : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) (H : ℕ)
    (hA : ∀ s r, ∑ j, AutomaticTable.counts d u H s r j = 2^(AutomaticTable.bitWidth k H))
    (hlegal : ∀ s r coins,
      BitSampling.row (AutomaticTable.counts d u H s r) (hA s r) coins ∈ labels s.2 r)
    (p : List (Fin n)) (c : Config n k) (w : List (Fin n))
    (coins : Fin w.length → Fin (AutomaticTable.bitWidth k H) → Bool) :
    BitSampling.runCost (counts d u H) (total d u H) EpochExpectation.next
      (EpochExpectation.charge d) (p,c.val) w coins =
    BitSampling.runCost (AutomaticTable.counts d u H) hA AutomaticTable.next
      (fun s r j => (AutomaticTable.charge d s r j : ℝ)) (p,c) w coins := by
  induction w generalizing p c with
  | nil => rfl
  | cons r w ih =>
    have he : counts d u H (p,c.val) r = AutomaticTable.counts d u H (p,c) r := by
      funext j
      simp only [counts, dite_eq_left c.property]
      rfl
    have hr : BitSampling.row (counts d u H (p,c.val) r) (total d u H (p,c.val) r)
        (coins 0) = BitSampling.row (AutomaticTable.counts d u H (p,c) r)
          (hA (p,c) r) (coins 0) := by
      congr 1
    let j := BitSampling.row (AutomaticTable.counts d u H (p,c) r) (hA (p,c) r) (coins 0)
    have hj : j ∈ labels c r := hlegal (p,c) r (coins 0)
    have hv : (FiniteTable.next c r j).val = serve c.val r j := by
      unfold FiniteTable.next
      split
      · rfl
      · contradiction
    simp only [BitSampling.runCost, hr, EpochExpectation.next, AutomaticTable.next,
      EpochExpectation.charge, AutomaticTable.charge]
    change (d.distance (c.val j) r : ℝ) +
      BitSampling.runCost (counts d u H) (total d u H) EpochExpectation.next
        (EpochExpectation.charge d) (p++[r],serve c.val r j) w (Fin.tail coins) = _
    rw [← hv, ih]
    rfl

/-- The input is only the finite rational metric, parameters and canonical
virtual tuple. No existence theorem or policy oracle appears in this result. -/
theorem construct {n k : ℕ} [NeZero k] (hk2 : 2 ≤ k)
    (d : RationalMetric n) (u : Config n k) (M R : ℕ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 0 ≤ δ) (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (hcap : R * (k+1) * D ≤ (M+1) * δ) :
    ∃ hN : ∀ s r, ∑ j, counts d u (horizon k M) s r j =
        2^(AutomaticTable.bitWidth k (horizon k M)),
      ∀ (raw : List (Fin n)), EpochShadow.blockCount (k:=k) ∅ raw ≤ R →
        ∀ (s c : Configuration n k) (g : History n k), g.map Prod.fst = raw →
          (∀ coins, (EpochExpectation.epochTrace (NeZero.pos k) M
            (counts d u (horizon k M)) hN u.val raw coins).map Prod.fst = raw) ∧
          BitSampling.mean (fun coins => costAlong d s
            (EpochExpectation.epochTrace (NeZero.pos k) M (counts d u (horizon k M))
              hN u.val raw coins)) ≤
            2*(AutomaticTable.coefficient d u (horizon k M) : ℝ)*costAlong d c g +
              (2*(AutomaticTable.coefficient d u (horizon k M) : ℝ)+2)*k*D := by
  let H := horizon k M
  obtain ⟨ha,_,_,_,hA,hlegal,hcost⟩ := AutomaticTable.construct d u H D hD hdiam
  refine ⟨total d u H, ?_⟩
  intro raw hR s c g hg
  apply EpochExpectation.comparison (NeZero.pos k) hk2 d (counts d u H) (total d u H)
    (forbidden d u H) u.val s c u.property M R D δ
    (AutomaticTable.coefficient d u H : ℝ) hD hδ (by exact_mod_cast ha)
    hdiam hsep hcap ?_ raw hR g hg
  intro w hw
  have he : BitSampling.mean (BitSampling.runCost (counts d u H) (total d u H)
      EpochExpectation.next (EpochExpectation.charge d) ([],u.val) w) =
      BitSampling.mean (BitSampling.runCost (AutomaticTable.counts d u H) hA
        AutomaticTable.next (fun s r j => (AutomaticTable.charge d s r j : ℝ)) ([],u) w) := by
    congr 1
    funext coins
    exact runCost_eq d u H hA hlegal [] u w coins
  rw [he]
  exact hcost w hw

end UniformKServer.AutomaticEpoch


end OAI
