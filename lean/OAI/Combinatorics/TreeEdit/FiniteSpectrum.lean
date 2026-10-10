import OAI.Combinatorics.TreeEdit.FiniteShifts
import OAI.Combinatorics.TreeEdit.FiniteFourier

namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

namespace FiniteTree

noncomputable instance instStateFintype {m : ℕ} (p : ℕ → Fin m → ℕ)
    [∀ j i, NeZero (p j i)] (h q : ℕ) [NeZero q] : Fintype (State m p h q) :=
  stateFintype p (fun j i => Nat.pos_of_ne_zero (NeZero.ne (p j i))) h q
    (Nat.pos_of_ne_zero (NeZero.ne q))

noncomputable instance instSymbolFintype {m : ℕ} (p : ℕ → Fin m → ℕ)
    [∀ j i, NeZero (p j i)] (h q : ℕ) [NeZero q] : Fintype (Symbol m p h q) :=
  symbolFintype p (fun j i => Nat.pos_of_ne_zero (NeZero.ne (p j i))) h q
    (Nat.pos_of_ne_zero (NeZero.ne q))

open FiniteFourier

variable {m : ℕ} {p : ℕ → Fin m → ℕ} [∀ j i, NeZero (p j i)]

def SpectralBound (T h q : ℕ) [NeZero q] (H : AddChar (State m p h q) ℂ → ℝ) (C : ℝ) : Prop :=
  ∀ z b, (∀ x, (ed (word p T h q x).val (word p T h q (x + z)).val : ℝ) ≤ b) →
    energy H z ≤ C * b

lemma SpectralBound.child {T h q : ℕ} [NeZero q]
    {H : AddChar (State m p (h + 1) q) ℂ → ℝ} {C : ℝ}
    (hH : SpectralBound T (h + 1) q H C) (i : Fin m) :
    SpectralBound T h (q * p h i) (pushSpectrum H (embedChild p h q i)) (C * T) := by
  intro z b hb
  rw [energy_push]
  have hh := hH (embedChild p h q i z) (T * b) (child_cost i z b hb)
  simpa only [mul_assoc] using hh

noncomputable def activeChildren {h q : ℕ} (χ : AddChar (State m p (h + 1) q) ℂ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => χ (embedChild p h q i (w p h (q * p h i))) ≠ 1)

omit [∀ j i, NeZero (p j i)] in
lemma chi_u {h q : ℕ} (χ : AddChar (State m p (h + 1) q) ℂ) :
    χ (u p h q) = ∏ i, χ (embedChild p h q i (w p h (q * p h i))) := by
  have he : u p h q = ∑ i, embedChild p h q i (w p h (q * p h i)) := by
    exact (Finset.univ_sum_single _).symm
  rw [he]
  have hs : ∀ (s : Finset (Fin m)),
      χ (∑ i ∈ s, embedChild p h q i (w p h (q * p h i))) =
        ∏ i ∈ s, χ (embedChild p h q i (w p h (q * p h i))) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [ha, AddChar.map_add_eq_mul, ih]
  exact hs _

omit [∀ j i, NeZero (p j i)] in
lemma active_period {h q : ℕ} (χ : AddChar (State m p (h + 1) q) ℂ) :
    (χ (u p h q)) ^ (q * ∏ i ∈ activeChildren χ, p h i) = 1 := by
  classical
  rw [chi_u, ← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i _
  by_cases hi : i ∈ activeChildren χ
  · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (p h) hi
    have hp := w_period p h (q * p h i)
    have he : (χ (embedChild p h q i (w p h (q * p h i)))) ^ (q * p h i) = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, ← map_nsmul, hp, map_zero, AddChar.map_zero_eq_one]
    rw [hc, ← mul_assoc, pow_mul, he, one_pow]
  · have he : χ (embedChild p h q i (w p h (q * p h i))) = 1 := by
      simpa [activeChildren] using hi
    simp [he]

omit [∀ j i, NeZero (p j i)] in
lemma active_u_ne_one {h q : ℕ} (χ : AddChar (State m p (h + 1) q) ℂ)
    (hχ : χ (w p (h + 1) q) ≠ 1) : χ (u p h q) ≠ 1 := by
  intro he
  apply hχ
  change χ ((∏ i, p h i) • u p h q) = 1
  rw [AddChar.map_nsmul_eq_pow, he, one_pow]

omit [∀ j i, NeZero (p j i)] in
lemma sparse_period_bound {h q K U Qcap : ℕ} [NeZero q]
    (χ : AddChar (State m p (h + 1) q) ℂ)
    (hU : 1 ≤ U) (hp : ∀ i, p h i ≤ U)
    (hq : q * U ^ (h + 1) ≤ Qcap) (hsp : (activeChildren χ).card < K) :
    q * (∏ i ∈ activeChildren χ, p h i) ≤ Qcap * U ^ K := by
  have hq' : q ≤ Qcap := (Nat.le_mul_of_pos_right q (by positivity : 0 < U ^ (h + 1))).trans hq
  have hprod : (∏ i ∈ activeChildren χ, p h i) ≤ U ^ K := by
    calc
      _ ≤ ∏ _i ∈ activeChildren χ, U := Finset.prod_le_prod (fun i _ => hp i)
      _ = U ^ (activeChildren χ).card := by simp
      _ ≤ U ^ K := pow_le_pow_right₀ hU (le_of_lt hsp)
  exact Nat.mul_le_mul hq' hprod

end FiniteTree

namespace FiniteTree

open FiniteFourier
variable {m : ℕ} {p : ℕ → Fin m → ℕ} [∀ j i, NeZero (p j i)]

noncomputable def sparse {h q : ℕ} (K : ℕ) (χ : AddChar (State m p (h + 1) q) ℂ) : ℝ :=
  if χ (w p (h + 1) q) ≠ 1 ∧ (activeChildren χ).card < K then 1 else 0

noncomputable def sparseMass {h q : ℕ} [NeZero q]
    (K : ℕ) (H : AddChar (State m p (h + 1) q) ℂ → ℝ) : ℝ := ∑ χ, sparse K χ * H χ

omit [∀ j i, NeZero (p j i)] in
lemma sum_activeChildren {h q : ℕ} (χ : AddChar (State m p (h + 1) q) ℂ) :
    ∑ i, active χ (embedChild p h q i (w p h (q * p h i))) = (activeChildren χ).card := by
  classical
  simp only [active, activeChildren, ← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> norm_num
  contradiction

omit [∀ j i, NeZero (p j i)] in
lemma branch_pointwise {h q : ℕ} (K : ℕ) (χ : AddChar (State m p (h + 1) q) ℂ) :
    (K : ℝ) * active χ (w p (h + 1) q) ≤
      ∑ i, active χ (embedChild p h q i (w p h (q * p h i))) + K * sparse K χ := by
  rw [sum_activeChildren]
  by_cases hw : χ (w p (h + 1) q) = 1
  · simp [active, sparse, hw]
  · by_cases hc : (activeChildren χ).card < K
    · simp [active, sparse, hw, hc]
    · simpa [active, sparse, hw, hc] using (show (K : ℝ) ≤ (activeChildren χ).card by exact_mod_cast Nat.le_of_not_gt hc)

lemma branch_mass {h q : ℕ} [NeZero q] (K : ℕ)
    {H : AddChar (State m p (h + 1) q) ℂ → ℝ} (hH : ∀ χ, 0 ≤ H χ) :
    (K : ℝ) * activeMass H (w p (h + 1) q) ≤
      (∑ i, activeMass (pushSpectrum H (embedChild p h q i)) (w p h (q * p h i))) + K * sparseMass K H := by
  classical
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun χ _ =>
    mul_le_mul_of_nonneg_right (branch_pointwise K χ) (hH χ))
  have he : (∑ χ, (∑ i, active χ (embedChild p h q i (w p h (q * p h i)))) * H χ) =
      ∑ i, activeMass (pushSpectrum H (embedChild p h q i)) (w p h (q * p h i)) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [activeMass_push]
  simp only [add_mul, Finset.sum_add_distrib, he, mul_assoc, ← Finset.mul_sum] at hh
  exact hh

lemma sparse_estimate {T h q K U Qcap J : ℕ} [NeZero q]
    {H : AddChar (State m p (h + 1) q) ℂ → ℝ} {C : ℝ}
    (hH : ∀ χ, 0 ≤ H χ) (hbound : SpectralBound T (h + 1) q H C)
    (hU : 1 ≤ U) (hp : ∀ i, p h i ≤ U) (hq : q * U ^ (h + 1) ≤ Qcap)
    (hJ : 2 * (Qcap * U ^ K) ≤ J) (hJT : J ≤ T) (hJpos : 0 < J) :
    sparseMass K H ≤ C * (2 * J * (m * length m T h)) := by
  classical
  have hdetect (χ : AddChar (State m p (h + 1) q) ℂ) :
      (J : ℝ) * sparse K χ ≤ ∑ s ∈ Finset.range J, multiplier χ ((s + 1) • u p h q) := by
    by_cases hs : χ (w p (h + 1) q) ≠ 1 ∧ (activeChildren χ).card < K
    · rw [sparse, ite_eq_left hs, mul_one]
      apply period_detect χ (u p h q) (n := q * ∏ i ∈ activeChildren χ, p h i)
      · exact Nat.mul_pos (NeZero.pos q) (Finset.prod_pos (fun i _ => NeZero.pos (p h i)))
      · exact (Nat.mul_le_mul_left 2 (sparse_period_bound χ hU hp hq hs.2)).trans hJ
      · exact active_u_ne_one χ hs.1
      · exact active_period χ
    · simp only [sparse, ite_eq_right hs, mul_zero]
      exact Finset.sum_nonneg fun s _ => multiplier_nonneg χ _
  have hcost (s : ℕ) (hs : s ∈ Finset.range J) :
      energy H ((s + 1) • u p h q) ≤ C * (2 * J * (m * length m T h)) := by
    have hsJ : s + 1 ≤ J := Finset.mem_range.mp hs
    apply hbound
    intro x
    have hc := cycle_cost (hsJ.trans hJT) x (p := p)
    have hh := hc.trans (Nat.mul_le_mul_right (m * length m T h) (Nat.mul_le_mul_left 2 hsJ))
    exact_mod_cast hh
  have hh : (J : ℝ) * sparseMass K H ≤ J * (C * (2 * J * (m * length m T h))) := by
    calc
      _ ≤ ∑ χ, (∑ s ∈ Finset.range J, multiplier χ ((s + 1) • u p h q)) * H χ := by
        rw [sparseMass, Finset.mul_sum]
        exact Finset.sum_le_sum fun χ _ => by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hdetect χ) (hH χ)
      _ = ∑ s ∈ Finset.range J, energy H ((s + 1) • u p h q) := by
        simp only [energy, Finset.sum_mul]
        rw [Finset.sum_comm]
      _ ≤ ∑ _s ∈ Finset.range J, C * (2 * J * (m * length m T h)) := Finset.sum_le_sum hcost
      _ = _ := by simp
  exact (mul_le_mul_iff_right₀ (by exact_mod_cast hJpos : (0 : ℝ) < J)).mp hh

theorem mass_bound {T h q K U Qcap J : ℕ} [NeZero q]
    {H : AddChar (State m p h q) ℂ → ℝ} {C : ℝ}
    (hH : ∀ χ, 0 ≤ H χ) (hC : 0 ≤ C) (hbound : SpectralBound T h q H C)
    (hK : 1 ≤ K) (hU : 1 ≤ U) (hp : ∀ j, j < h → ∀ i, p j i ≤ U)
    (hq : q * U ^ h ≤ Qcap) (hJ : 2 * (Qcap * U ^ K) ≤ J)
    (hJT : J ≤ T) (hJpos : 0 < J) :
    activeMass H (w p h q) ≤ C * length m T h * ((K : ℝ)⁻¹ ^ h + 2 * h * J / T) := by
  have hTpos : 0 < T := hJpos.trans_le hJT
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hTr : (0 : ℝ) < T := by exact_mod_cast hTpos
  induction h generalizing q C with
  | zero =>
    have hb (z : State m p 0 q) : energy H z ≤ C := by
      have hh := hbound z 1 (fun x => by
        have hh := ed_le_of_script (substitution_script
          (x := (word p T 0 q x).val) (y := (word p T 0 q (x + z)).val)
          (by simp [(word p T 0 q x).property, (word p T 0 q (x + z)).property]))
        simpa [(word p T 0 q x).property, length] using hh)
      simpa using hh
    have hh := (twice_activeMass_le_average hH (w p 0 q)).trans (average_le hb)
    simpa [length] using (show activeMass H (w p 0 q) ≤ C by linarith [activeMass_nonneg hH (w p 0 q)])
  | succ h ih =>
    have hchild (i : Fin m) :
        activeMass (pushSpectrum H (embedChild p h q i)) (w p h (q * p h i)) ≤
          (C * T) * length m T h * ((K : ℝ)⁻¹ ^ h + 2 * h * J / T) := by
      apply ih (pushSpectrum_nonneg hH _) (mul_nonneg hC (Nat.cast_nonneg _)) (hbound.child i)
        (fun j hj => hp j (by omega))
      calc
        (q * p h i) * U ^ h = q * (p h i * U ^ h) := by ring
        _ ≤ q * (U * U ^ h) := Nat.mul_le_mul_left q (Nat.mul_le_mul_right _ (hp h (by omega) i))
        _ = q * U ^ (h + 1) := by rw [pow_succ]; ring
        _ ≤ Qcap := hq
    have hsp := sparse_estimate hH hbound hU (hp h (by omega)) hq hJ hJT hJpos
    have hb := branch_mass K hH
    have hc := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hchild i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hc
    have hmain : (K : ℝ) * activeMass H (w p (h + 1) q) ≤
      C * length m T (h + 1) * ((K : ℝ)⁻¹ ^ h + 2 * h * J / T) +
        K * (C * (2 * J * (m * length m T h))) := by
      calc
        _ ≤ _ := hb.trans (add_le_add hc (mul_le_mul_of_nonneg_left hsp (by positivity)))
        _ = _ := by simp only [length, Nat.cast_mul]; ring
    have he : (K : ℝ) * (C * length m T (h + 1) *
        ((K : ℝ)⁻¹ ^ (h + 1) + 2 * (h + 1) * J / T)) -
      (C * length m T (h + 1) * ((K : ℝ)⁻¹ ^ h + 2 * h * J / T) +
        K * (C * (2 * J * (m * length m T h)))) =
      C * (m * length m T h) * (2 * h * J) * (K - 1) := by
      simp only [length, Nat.cast_mul, pow_succ]
      field_simp
      ring
    have hn : 0 ≤ C * (m * length m T h) * (2 * (h : ℝ) * J) * ((K : ℝ) - 1) := by positivity
    have hf : (K : ℝ) * activeMass H (w p (h + 1) q) ≤
        K * (C * length m T (h + 1) * ((K : ℝ)⁻¹ ^ (h + 1) + 2 * (h + 1) * J / T)) := by linarith
    exact (mul_le_mul_iff_right₀ (by linarith : (0 : ℝ) < K)).mp (by simpa using hf)

end FiniteTree

end TreeEdit

end OAI
