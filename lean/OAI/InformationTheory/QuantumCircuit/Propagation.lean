import OAI.InformationTheory.QuantumCircuit.PropagationAsymptotics

namespace OAI

/-! Low-degree transport along regular trajectories. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Filter

namespace QAC

theorem regular_layer_propagation
    (hpauli : PublishedPauliExpansion) (hspec : PublishedProductSpectralResolution)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (a : ∀ ν, AnalyticLayer (m ν)) (ψ : ∀ ν, State (m ν))
    (hψ : ∀ ν, ‖ψ ν‖ ≤ 1) (hreg : LayerRegular m a ψ)
    {k K : ℝ} (hk : 0 < k) (hkK : k < K) (hK : K < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ ν in atTop, ∀ E : Operator (m ν),
      HasDegreeLE E ((m ν : ℝ)^k) → ‖E‖ ≤ Real.exp ((m ν : ℝ)^k) →
      TransportOn (a ν).matrix (ψ ν) ((m ν : ℝ)^K) (Real.exp ((m ν : ℝ)^K))
        (ε * Real.exp (-((m ν : ℝ)^k))) E := by
  let Δ := K - k
  let q := k + Δ / 12
  let p₁ := k + Δ / 6
  let L := k + 5 * Δ / 6
  let r := k + 2 * Δ / 3
  let p₂ := k + 3 * Δ / 4
  have hΔ : 0 < Δ := sub_pos.mpr hkK
  have hkq : k < q := by dsimp [q]; linarith
  have hqp : q < p₁ := by dsimp [q, p₁]; linarith
  have hpr : p₁ < r := by dsimp [p₁, r]; linarith
  have hrp : r < p₂ := by dsimp [r, p₂]; linarith
  have hpL : p₂ < L := by dsimp [p₂, L]; linarith
  have hLK : L < K := by dsimp [L, Δ]; linarith
  have hrK := hrp.trans (hpL.trans hLK)
  have hqK := hqp.trans (hpr.trans hrK)
  have hkL := hkq.trans (hqp.trans (hpr.trans (hrp.trans hpL)))
  have hp₁ : 0 < p₁ := hk.trans (hkq.trans hqp)
  have hp₂ : 0 < p₂ := hp₁.trans (hpr.trans hrp)
  have hpoly : (p₁ + L) / 2 < r := by dsimp [p₁, L, r]; linarith
  have he₁ := hm.eventually (eventually_exp_power_gap (hkq.trans hqp) hqp hp₁
    1 (ε / 2) 1 1 (by norm_num) (by positivity))
  have he₂ := hm.eventually (eventually_exp_power_gap
    (hkq.trans (hqp.trans (hpr.trans hrp))) hrp hp₂
    2 (ε / 2) 1 2 (by norm_num) (by positivity))
  filter_upwards [hreg k L p₂ hk.le hkL (hLK.trans hK) hp₂ hpL,
    hm.eventually (polynomial_approximation hp₁ (hpr.trans (hrp.trans hpL)) hpoly),
    hm.eventually (eventually_propagationBudget hk.le (hkK.trans hK).le hkq),
    hm.eventually (eventually_two_powers_le hkK hrK),
    hm.eventually (eventually_two_powers_le hqK hrK),
    hm.eventually (eventually_ge_atTop 1), he₁, he₂]
    with ν ht hp hbudget hdegree hnorm hN he₁ he₂
  intro E hE hEn
  have hN1 : (1 : ℝ) ≤ m ν := by exact_mod_cast hN
  have hqr : (m ν : ℝ)^q ≤ (m ν : ℝ)^r :=
    Real.rpow_le_rpow_of_exponent_le hN1 (hqp.trans hpr).le
  have hkKpow : (m ν : ℝ)^k ≤ (m ν : ℝ)^K :=
    Real.rpow_le_rpow_of_exponent_le hN1 hkK.le
  cases ha : a ν with
  | «local» U =>
    have hu := localMatrix_unitary U
    refine ⟨conjugate (localMatrix U) E, (hE.local_conjugate U).mono hkKpow, ?_, ?_⟩
    · exact (norm_unitary_conjugate hu E).le.trans (hEn.trans (Real.exp_le_exp.mpr hkKpow))
    · have hx : act (localMatrix U) (act E (ψ ν)) =
          act (conjugate (localMatrix U) E) (act (localMatrix U) (ψ ν)) := by
        simp only [conjugate, ← act_mul, mul_assoc,
          Unitary.star_mul_self_of_mem hu, mul_one]
      change ‖act (localMatrix U) (act E (ψ ν)) -
        act (conjugate (localMatrix U) E) (act (localMatrix U) (ψ ν))‖ ≤ _
      rw [hx, sub_self, norm_zero]
      positivity
  | reflection R =>
    obtain ⟨p, hpd, hpw, hp0, hpa⟩ := hp
    let ell := ⌊(m ν : ℝ)^k⌋₊
    have hell : (ell : ℝ) ≤ (m ν : ℝ)^k := Nat.floor_le (by positivity)
    have hcut : ∀ x : ℕ, 1 ≤ x → (x : ℝ) < (m ν : ℝ)^L →
        |p.eval (x : ℝ)| ≤ Real.exp (-((m ν : ℝ)^p₁)) := by
      intro x hx hxr
      apply hpa x hx
      exact_mod_cast hxr.le.trans (Nat.le_ceil _)
    have htail : ∀ S : List (Count (m ν)), S.Sublist R.gates → S.length ≤ ell →
        ‖act ((jointTest S).high ((m ν : ℝ)^L)) (ψ ν)‖ ≤
          Real.exp (-((m ν : ℝ)^p₂)) := by
      intro S hS hs
      exact ht R ha S hS ((by exact_mod_cast hs : (S.length : ℝ) ≤ ell).trans hell)
    have hfin := low_degree_reflection_approximation hpauli hspec hN R (ψ ν) (hψ ν)
      E (hE.floor (by positivity)) p ((m ν : ℝ)^L)
      (Real.exp (-((m ν : ℝ)^p₁))) (Real.exp (-((m ν : ℝ)^p₂)))
      (Real.exp_pos _).le (Real.exp_pos _).le hp0 hcut htail
    have hmass : propagationBudget (m ν) ell * ‖E‖ ≤ Real.exp ((m ν : ℝ)^q) :=
      (mul_le_mul_of_nonneg_left hEn (propagationBudget_nonneg _ _)).trans
        (hbudget ell hell)
    have hn : propagationBudget (m ν) ell * ‖E‖ * weight (m ν) p ≤
        Real.exp ((m ν : ℝ)^K) := by
      calc
        _ ≤ Real.exp ((m ν : ℝ)^q) * Real.exp ((m ν : ℝ)^r) :=
          mul_le_mul hmass hpw (weight_nonneg (Nat.cast_nonneg _) p) (Real.exp_pos _).le
        _ = Real.exp ((m ν : ℝ)^q + (m ν : ℝ)^r) := (Real.exp_add ..).symm
        _ ≤ _ := Real.exp_le_exp.mpr hnorm
    have he : propagationBudget (m ν) ell * ‖E‖ *
        (Real.exp (-((m ν : ℝ)^p₁)) + (1 + weight (m ν) p) * Real.exp (-((m ν : ℝ)^p₂))) ≤
        ε * Real.exp (-((m ν : ℝ)^k)) := by
      have hw1 : 1 ≤ Real.exp ((m ν : ℝ)^r) := Real.one_le_exp (by positivity)
      calc
        _ ≤ Real.exp ((m ν : ℝ)^q) *
            (Real.exp (-((m ν : ℝ)^p₁)) +
              (2 * Real.exp ((m ν : ℝ)^r)) * Real.exp (-((m ν : ℝ)^p₂))) := by
          have hw0 : 0 ≤ weight (m ν) p := weight_nonneg (Nat.cast_nonneg _) p
          have hb : Real.exp (-((m ν : ℝ)^p₁)) +
              (1 + weight (m ν) p) * Real.exp (-((m ν : ℝ)^p₂)) ≤
              Real.exp (-((m ν : ℝ)^p₁)) +
              (2 * Real.exp ((m ν : ℝ)^r)) * Real.exp (-((m ν : ℝ)^p₂)) := by
            apply add_le_add le_rfl
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            linarith only [hpw, hw1]
          exact mul_le_mul hmass hb (by positivity) (Real.exp_pos _).le
        _ = Real.exp ((m ν : ℝ)^q - (m ν : ℝ)^p₁) +
            2 * Real.exp ((m ν : ℝ)^q + (m ν : ℝ)^r - (m ν : ℝ)^p₂) := by
          simp only [sub_eq_add_neg, Real.exp_add]
          ring
        _ ≤ Real.exp ((m ν : ℝ)^q - (m ν : ℝ)^p₁) +
            2 * Real.exp (2 * (m ν : ℝ)^r - (m ν : ℝ)^p₂) := by
          apply add_le_add le_rfl
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
          apply Real.exp_le_exp.mpr
          linarith only [hqr]
        _ ≤ (ε / 2) * Real.exp (-((m ν : ℝ)^k)) +
            (ε / 2) * Real.exp (-((m ν : ℝ)^k)) :=
          add_le_add (by simpa only [one_mul] using he₁) (by simpa only [one_mul] using he₂)
        _ = _ := by ring
    exact (hfin.mono ((add_le_add hell hpd).trans hdegree) hn he).transport
      (reflectionMatrix_unitary R)

end QAC

end

end OAI
