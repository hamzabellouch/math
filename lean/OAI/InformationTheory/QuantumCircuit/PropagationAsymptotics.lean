import OAI.InformationTheory.QuantumCircuit.ReflectionApproximation

namespace OAI

/-! Asymptotic estimates for propagation through reflection layers. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Filter

namespace QAC

lemma HasDegreeLE.floor {N : ℕ} {E : Operator N} {r : ℝ}
    (hE : HasDegreeLE E r) (hr : 0 ≤ r) : HasDegreeLE E (⌊r⌋₊ : ℝ) := by
  apply Submodule.span_mono ?_ hE
  rintro A ⟨J, hJ, hA⟩
  exact ⟨J, by exact_mod_cast (Nat.le_floor_iff hr).mpr hJ, hA⟩

lemma propagationBudget_log_bound {N ell : ℕ} {k : ℝ}
    (hN : 27 ≤ N) (hk : 0 ≤ k) (hk1 : k ≤ 1) (hell : (ell : ℝ) ≤ (N : ℝ)^k) :
    propagationBudget N ell ≤ Real.exp (4 * (N : ℝ)^k * Real.log N) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN27 : (27 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hx : 1 ≤ (N : ℝ)^k := Real.one_le_rpow hN1 hk
  have hxN : (N : ℝ)^k ≤ N := by
    simpa using Real.rpow_le_rpow_of_exponent_le hN1 hk1
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlogA : Real.log (ell + 1 : ℝ) ≤ 2 * Real.log N := by
    calc
      _ ≤ Real.log ((N : ℝ)^2) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; norm_num
  have hlogB : Real.log (27 * N : ℝ) ≤ 2 * Real.log N := by
    calc
      _ ≤ Real.log ((N : ℝ)^2) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; norm_num
  have heq : propagationBudget N ell =
      Real.exp (Real.log (ell + 1 : ℝ) + ell * Real.log (27 * N : ℝ)) := by
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by positivity),
      Real.exp_log (by positivity)]
    unfold propagationBudget
    push_cast
    rw [mul_assoc, ← mul_pow]
    congr 2
    ring
  rw [heq]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ 2 * Real.log N + (ell : ℝ) * (2 * Real.log N) :=
      add_le_add hlogA (mul_le_mul_of_nonneg_left hlogB (Nat.cast_nonneg ell))
    _ ≤ 4 * (N : ℝ)^k * Real.log N := by
      nlinarith [mul_le_mul_of_nonneg_right hell hlog,
        mul_le_mul_of_nonneg_right hx hlog]

lemma eventually_propagationBudget {k q : ℝ} (hk : 0 ≤ k) (hk1 : k ≤ 1) (hkq : k < q) :
    ∀ᶠ N : ℕ in atTop, ∀ ell : ℕ, (ell : ℝ) ≤ (N : ℝ)^k →
      propagationBudget N ell * Real.exp ((N : ℝ)^k) ≤ Real.exp ((N : ℝ)^q) := by
  filter_upwards [eventually_ge_atTop 27, eventually_power_log_le hkq 8,
    eventually_power_le hkq 2] with N hN hlog hpow
  intro ell hell
  calc
    _ ≤ Real.exp (4 * (N : ℝ)^k * Real.log N) * Real.exp ((N : ℝ)^k) :=
      mul_le_mul_of_nonneg_right (propagationBudget_log_bound hN hk hk1 hell) (Real.exp_nonneg _)
    _ = Real.exp (4 * (N : ℝ)^k * Real.log N + (N : ℝ)^k) := (Real.exp_add ..).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

def LayerRegular (m : ℕ → ℕ) (a : ∀ ν, AnalyticLayer (m ν))
    (ψ : ∀ ν, State (m ν)) : Prop :=
  ∀ b h p : ℝ, 0 ≤ b → b < h → h < 1 → 0 < p → p < h →
    ∀ᶠ ν in atTop, ∀ R, a ν = .reflection R →
      ∀ S : List (Count (m ν)), S.Sublist R.gates → (S.length : ℝ) ≤ (m ν : ℝ)^b →
        ‖act ((jointTest S).high ((m ν : ℝ)^h)) (ψ ν)‖ ≤ Real.exp (-((m ν : ℝ)^p))

def TransportOn {N : ℕ} (U : Operator N) (ψ : State N)
    (r C δ : ℝ) (E : Operator N) : Prop :=
  ∃ E' : Operator N, HasDegreeLE E' r ∧ ‖E'‖ ≤ C ∧
    ‖act U (act E ψ) - act E' (act U ψ)‖ ≤ δ

lemma ApproxOn.transport {N : ℕ} {U : Operator N} {ψ : State N}
    {r C δ : ℝ} {E : Operator N} (hU : U ∈ unitary (Operator N))
    (h : ApproxOn (act U ψ) r C δ (conjugate U E)) : TransportOn U ψ r C δ E := by
  obtain ⟨E', hd, hn, he⟩ := h
  refine ⟨E', hd, hn, ?_⟩
  have hid : act (conjugate U E) (act U ψ) = act U (act E ψ) := by
    simp only [conjugate, ← act_mul, mul_assoc,
      Unitary.star_mul_self_of_mem hU, mul_one]
  rwa [act_sub, hid] at he

end QAC

end

end OAI
