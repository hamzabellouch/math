import OAI.Combinatorics.TreeEdit.CircleFourier

namespace OAI

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical TorusTree FiniteFourier FiniteProbability

noncomputable def high {M m : ℕ} [NeZero M] (h Q : ℕ) (χ : AddChar (State (ZMod M) m h) ℂ) : ℝ :=
  if (Q : ℝ) ≤ |(centered (summary h χ) : ℝ)| then 1 else 0

noncomputable def highMass {M m : ℕ} [NeZero M] (h Q : ℕ) (H : AddChar (State (ZMod M) m h) ℂ → ℝ) : ℝ :=
  ∑ χ, high h Q χ * H χ

lemma high_nonneg {M m : ℕ} [NeZero M] (h Q : ℕ) (χ : AddChar (State (ZMod M) m h) ℂ) : 0 ≤ high h Q χ := by
  unfold high; split_ifs <;> norm_num

lemma active_summary {M m : ℕ} [NeZero M] (h : ℕ) (χ : AddChar (State (ZMod M) m h) ℂ) :
    active χ (diagonal (A := ZMod M) (m := m) h 1) = if summary h χ = 0 then 0 else 1 := by
  have he : χ (diagonal (A := ZMod M) (m := m) h 1) = 1 ↔ summary h χ = 0 := character_one (summary h χ)
  unfold active
  simp only [he]

lemma branch_multiplier {I : Type} {g s L M b e K Q : ℕ} [NeZero M] (r : I → ℕ)
    (hr : ∀ i, Nat.Prime (r i)) (hinj : Function.Injective r) (j : Fin g ↪ I)
    (hb : 1 ≤ b) (hlower : ∀ i, b ≤ r i) (hQ : Q ≤ b^e) (hg : e+K ≤ g)
    (hM : (g*s+1)*Q < M) (h : ℕ) (C : Config I L (g*s) (h+1))
    (hPM : period r j C.1 ∣ M) (χ : AddChar (State (ZMod M) (g*s) (h+1)) ℂ) :
    (K : ℝ) * active χ (diagonal (A := ZMod M) (m := g*s) (h+1) 1) ≤
      (∑ i : Fin (g*s), active (χ.compAddMonoidHom (child (A := ZMod M) h i)) (diagonal (A := ZMod M) (m := g*s) h 1)) +
      K * (high (h+1) Q χ + (∑ i : Fin (g*s), high h Q (χ.compAddMonoidHom (child (A := ZMod M) h i))) +
        active χ (cycle (M := M) r j h C)) := by
  let S := ∑ i : Fin (g*s), active (χ.compAddMonoidHom (child (A := ZMod M) h i)) (diagonal (A := ZMod M) (m := g*s) h 1)
  let E := ∑ i : Fin (g*s), high h Q (χ.compAddMonoidHom (child (A := ZMod M) h i))
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => active_nonneg _ _
  have hE : 0 ≤ E := Finset.sum_nonneg fun i _ => high_nonneg _ _ _
  have hA := active_nonneg χ (cycle (M := M) r j h C)
  have hH := high_nonneg (h+1) Q χ
  change _ ≤ S + K * (high (h+1) Q χ + E + active χ (cycle (M := M) r j h C))
  rw [active_summary]
  split_ifs with hn
  · simp only [mul_zero]
    exact add_nonneg hS (mul_nonneg (Nat.cast_nonneg (α := ℝ) K) (add_nonneg (add_nonneg hH hE) hA))
  · simp only [mul_one]
    by_cases hp : (Q : ℝ) ≤ |(centered (summary (h+1) χ) : ℝ)|
    · rw [high, ite_eq_left hp]
      nlinarith [Nat.cast_nonneg (α := ℝ) K]
    by_cases hc : ∃ i : Fin (g*s), (Q : ℝ) ≤ |(centered (summary h (χ.compAddMonoidHom (child (A := ZMod M) h i))) : ℝ)|
    · obtain ⟨i, hi⟩ := hc
      have hei : 1 ≤ E := by
        calc
          1 = high h Q (χ.compAddMonoidHom (child (A := ZMod M) h i)) := by simp only [high, ite_eq_left hi]
          _ ≤ E := Finset.single_le_sum (f := fun v => high h Q (χ.compAddMonoidHom (child (A := ZMod M) h v))) (fun v _ => high_nonneg _ _ _) (Finset.mem_univ i)
      nlinarith [Nat.cast_nonneg (α := ℝ) K]
    by_cases hχ : χ (cycle (M := M) r j h C) = 1
    · have hh := branch_summaries r hr hinj j hb hlower hQ hg hM h C hPM χ (lt_of_not_ge hp)
        (fun i => lt_of_not_ge (fun hi => hc ⟨i,hi⟩)) hχ hn
      have hs : (K : ℝ) ≤ S := by
        dsimp [S]
        simp_rw [active_summary]
        have he : (∑ i : Fin (g*s), if summary h (χ.compAddMonoidHom (child (A := ZMod M) h i)) = 0 then (0 : ℝ) else 1) =
            ((Finset.univ.filter (fun i : Fin (g*s) => summary h (χ.compAddMonoidHom (child (A := ZMod M) h i)) ≠ 0)).card : ℝ) := by
          simpa only [ite_not] using (Finset.sum_boole (fun i : Fin (g*s) => summary h (χ.compAddMonoidHom (child (A := ZMod M) h i)) ≠ 0) Finset.univ)
        rw [he]
        exact_mod_cast hh
      nlinarith [Nat.cast_nonneg (α := ℝ) K]
    · rw [active, ite_eq_right hχ]
      nlinarith [Nat.cast_nonneg (α := ℝ) K]

lemma branch_mass {I : Type} {g s L M b e K Q : ℕ} [NeZero M] (r : I → ℕ)
    (hr : ∀ i, Nat.Prime (r i)) (hinj : Function.Injective r) (j : Fin g ↪ I)
    (hb : 1 ≤ b) (hlower : ∀ i, b ≤ r i) (hQ : Q ≤ b^e) (hg : e+K ≤ g)
    (hM : (g*s+1)*Q < M) (h : ℕ) (C : Config I L (g*s) (h+1))
    (hPM : period r j C.1 ∣ M) (H : AddChar (State (ZMod M) (g*s) (h+1)) ℂ → ℝ) (hH : ∀ χ, 0 ≤ H χ) :
    (K : ℝ) * activeMass H (diagonal (A := ZMod M) (m := g*s) (h+1) 1) ≤
      (∑ i : Fin (g*s), activeMass (pushSpectrum H (child (A := ZMod M) h i)) (diagonal (A := ZMod M) (m := g*s) h 1)) +
      K * (highMass (h+1) Q H + (∑ i : Fin (g*s), highMass h Q (pushSpectrum H (child (A := ZMod M) h i))) +
        activeMass H (cycle (M := M) r j h C)) := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun χ _ => mul_le_mul_of_nonneg_right
    (branch_multiplier r hr hinj j hb hlower hQ hg hM h C hPM χ) (hH χ))
  simp only [activeMass, highMass, pushSpectrum_sum] at hh ⊢
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc, ← Finset.mul_sum] at hh
  rw [Finset.sum_comm, Finset.sum_comm (f := fun χ i => high h Q (χ.compAddMonoidHom (child (A := ZMod M) h i)) * H χ)] at hh
  exact hh

def SpectralBound {I : Type} {g s L M R : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g → I) (T h : ℕ) (C : Config I L (g*s) h)
    (H : AddChar (State (ZMod M) (g*s) h) ℂ → ℝ) (D : ℝ) : Prop := ∀ z,
      energy H z ≤ D * mean (fun x : State (ZMod M) (g*s) h =>
        (ed (sampledWord r j T R h C x).val (sampledWord r j T R h C (x+z)).val : ℝ))

lemma SpectralBound.child {I : Type} {g s L M T R h : ℕ} [NeZero M] [NeZero R]
    {r : I → ℕ} {j : Fin g → I} (hr : ∀ i, 0 < r i)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M)
    {C : Config I L (g*s) (h+1)} {H : AddChar (State (ZMod M) (g*s) (h+1)) ℂ → ℝ} {D : ℝ}
    (hD : 0 ≤ D) (hb : SpectralBound (R := R) r j T (h+1) C H D) (i : Fin (g*s)) :
    SpectralBound (R := R) r j T h (C.2 i).2 (pushSpectrum H (child (A := ZMod M) h i)) (D*T) := by
  intro z
  rw [energy_push]
  exact (hb _).trans ((mul_le_mul_of_nonneg_left (sampledWord_child_mean r j hr hPM h C i z) hD).trans_eq (by ring))

lemma high_estimate {I : Type} {g s L M T R D Q J h : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g → I) (hr : ∀ i, 0 < r i)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M)
    (hD : 0 < D) (hQ : 0 < Q) (hMR : M = R*D) (hMQ : M = J*Q)
    (C : Config I L (g*s) h) (H : AddChar (State (ZMod M) (g*s) h) ℂ → ℝ) (a : ℝ)
    (hH : ∀ χ, 0 ≤ H χ) (ha : 0 ≤ a) (hb : SpectralBound (R := R) r j T h C H a) :
    highMass h Q H ≤ a * FiniteTree.length (g*s) T h * R / Q := by
  have hJ : 0 < J := by have := NeZero.pos M; nlinarith
  have hd (χ : AddChar (State (ZMod M) (g*s) h) ℂ) :
      (J : ℝ) * high h Q χ ≤ ∑ n ∈ Finset.range J, multiplier χ (diagonal (A := ZMod M) (m := g*s) h (n+1)) := by
    unfold high
    split_ifs with hc
    · simpa only [mul_one, multiplier_eq, summary, AddChar.compAddMonoidHom_apply] using sum_chord_detect hQ hMQ (summary h χ) hc
    · simp only [mul_zero]
      exact Finset.sum_nonneg fun n _ => multiplier_nonneg χ _
  have hcost (n : ℕ) (hn : n ∈ Finset.range J) :
      energy H (diagonal (A := ZMod M) (m := g*s) h (n+1)) ≤ a * FiniteTree.length (g*s) T h * R / Q := by
    apply (hb _).trans
    have ht := sampledWord_tiny (T := T) r j hr hPM hD hQ hMR hMQ h C (n+1) (Finset.mem_range.mp hn)
    exact (mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_add, Nat.cast_one] using ht) ha).trans_eq (by ring)
  have hh : (J : ℝ) * highMass h Q H ≤ J * (a * FiniteTree.length (g*s) T h * R / Q) := by
    calc
      _ ≤ ∑ χ, (∑ n ∈ Finset.range J, multiplier χ (diagonal (A := ZMod M) (m := g*s) h (n+1))) * H χ := by
        rw [highMass, Finset.mul_sum]
        exact Finset.sum_le_sum fun χ _ => by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hd χ) (hH χ)
      _ = ∑ n ∈ Finset.range J, energy H (diagonal (A := ZMod M) (m := g*s) h (n+1)) := by
        simp only [energy, Finset.sum_mul]
        rw [Finset.sum_comm]
      _ ≤ ∑ _n ∈ Finset.range J, (a * FiniteTree.length (g*s) T h * R / Q) := Finset.sum_le_sum hcost
      _ = _ := by simp
  exact (mul_le_mul_iff_right₀ (by exact_mod_cast hJ : (0 : ℝ) < J)).mp hh

end TreeEdit.TorusFourier

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical TorusTree FiniteFourier FiniteProbability

lemma cycle_estimate {I : Type} {g s L M T R V h : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g → I) (hr : ∀ i, 0 < r i)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M) (hPV : ∀ σ : Equiv.Perm I, period r j σ ≤ V) (hVT : V ≤ T)
    (C : Config I L (g*s) (h+1)) (H : AddChar (State (ZMod M) (g*s) (h+1)) ℂ → ℝ) (a : ℝ)
    (hH : ∀ χ, 0 ≤ H χ) (ha : 0 ≤ a) (hb : SpectralBound (R := R) r j T (h+1) C H a) :
    activeMass H (cycle (M := M) r j h C) ≤ a * FiniteTree.length (g*s) T (h+1) * (2 * V) / T := by
  let P := period r j C.1
  let v := cycle (M := M) r j h C
  have hP : 0 < P := period_pos hr j C.1
  have hT : 0 < T := hP.trans_le ((hPV C.1).trans hVT)
  have hd (χ : AddChar (State (ZMod M) (g*s) (h+1)) ℂ) :
      (P : ℝ) * active χ v ≤ ∑ n ∈ Finset.range P, multiplier χ ((n+1) • v) := by
    by_cases hc : χ v = 1
    · simp only [active, ite_eq_left hc, mul_zero]
      exact Finset.sum_nonneg fun n _ => multiplier_nonneg χ _
    · have hper : (χ v)^P = 1 := by
        rw [← AddChar.map_nsmul_eq_pow, cycle_period r j h C (hPM C.1), AddChar.map_zero_eq_one]
      rw [sum_multiplier_period χ v P hc hper, active, ite_eq_right hc]
      nlinarith [Nat.cast_nonneg (α := ℝ) P]
  have hcost (n : ℕ) (hn : n ∈ Finset.range P) : energy H ((n+1) • v) ≤ a * (2 * V * ((g*s) * FiniteTree.length (g*s) T h)) := by
    apply (hb _).trans
    apply mul_le_mul_of_nonneg_left _ ha
    apply (mean_le (fun x => show
        (ed (sampledWord r j T R (h+1) C x).val (sampledWord r j T R (h+1) C (x+(n+1) • v)).val : ℝ) ≤
        (2 * V * ((g*s) * FiniteTree.length (g*s) T h) : ℝ) from by
      have hnV : n+1 ≤ V := (Finset.mem_range.mp hn).trans_le (hPV C.1)
      have hh := sampledWord_cycle_cost (R := R) (T := T) r j hr hPM h C x (n+1) (hnV.trans hVT)
      exact_mod_cast hh.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hnV)))).trans_eq
    exact mean_const _
  have hh : (P : ℝ) * activeMass H v ≤ P * (a * (2 * V * ((g*s) * FiniteTree.length (g*s) T h))) := by
    calc
      _ ≤ ∑ χ, (∑ n ∈ Finset.range P, multiplier χ ((n+1) • v)) * H χ := by
        rw [activeMass, Finset.mul_sum]
        exact Finset.sum_le_sum fun χ _ => by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hd χ) (hH χ)
      _ = ∑ n ∈ Finset.range P, energy H ((n+1) • v) := by
        simp only [energy, Finset.sum_mul]
        rw [Finset.sum_comm]
      _ ≤ ∑ _n ∈ Finset.range P, a * (2 * V * ((g*s) * FiniteTree.length (g*s) T h)) := Finset.sum_le_sum hcost
      _ = _ := by simp
  have hc := (mul_le_mul_iff_right₀ (by exact_mod_cast hP : (0 : ℝ) < P)).mp hh
  apply hc.trans_eq
  simp only [FiniteTree.length, Nat.cast_mul]
  have hTr : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  field_simp

lemma mass_bound {I : Type} {g s L M T R D Q J V b e K h : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g ↪ I) (hr : ∀ i, Nat.Prime (r i)) (hinj : Function.Injective r)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M) (hPV : ∀ σ : Equiv.Perm I, period r j σ ≤ V) (hVT : V ≤ T)
    (hD : 0 < D) (hQ : 0 < Q) (hMR : M = R*D) (hMQ : M = J*Q)
    (hb : 1 ≤ b) (hlower : ∀ i, b ≤ r i) (hQpow : Q ≤ b^e) (hg : e+K ≤ g) (hK : 1 ≤ K)
    (hM : (g*s+1)*Q < M)
    (C : Config I L (g*s) h) (H : AddChar (State (ZMod M) (g*s) h) ℂ → ℝ) (a : ℝ)
    (hH : ∀ χ, 0 ≤ H χ) (ha : 0 ≤ a) (hbound : SpectralBound (R := R) r j T h C H a) :
    activeMass H (diagonal (A := ZMod M) (m := g*s) h 1) ≤
      a * FiniteTree.length (g*s) T h * ((K : ℝ)⁻¹^h + h * (2*(R : ℝ)/Q + 2*(V : ℝ)/T)) := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have herr : 0 ≤ 2*(R : ℝ)/Q + 2*(V : ℝ)/T := by positivity
  induction h generalizing a with
  | zero =>
    have hc (z : State (ZMod M) (g*s) 0) : energy H z ≤ a := by
      apply (hbound z).trans
      have hm : mean (fun x : State (ZMod M) (g*s) 0 =>
          (ed (sampledWord r j T R 0 C x).val (sampledWord r j T R 0 C (x+z)).val : ℝ)) ≤ 1 := by
        apply (mean_le (fun x => show
          (ed (sampledWord r j T R 0 C x).val (sampledWord r j T R 0 C (x+z)).val : ℝ) ≤ 1 from by
            have hh := ed_le_of_script (substitution_script
              (x := (sampledWord r j T R 0 C x).val) (y := (sampledWord r j T R 0 C (x+z)).val)
              (by simp [(sampledWord r j T R 0 C x).property, (sampledWord r j T R 0 C (x+z)).property]))
            simpa [(sampledWord r j T R 0 C x).property, FiniteTree.length] using (Nat.cast_le (α := ℝ)).mpr hh)).trans_eq
        exact mean_const 1
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hm ha
    have hh := (twice_activeMass_le_average hH (diagonal (A := ZMod M) (m := g*s) 0 1)).trans (average_le hc)
    simpa only [FiniteTree.length, Nat.cast_one, mul_one, pow_zero, Nat.cast_zero, zero_mul, add_zero] using
      (show activeMass H (diagonal (A := ZMod M) (m := g*s) 0 1) ≤ a by linarith [activeMass_nonneg hH (diagonal (A := ZMod M) (m := g*s) 0 1)])
  | succ h ih =>
    have hchild (i : Fin (g*s)) := ih (C.2 i).2 (pushSpectrum H (child (A := ZMod M) h i)) (a*T)
      (pushSpectrum_nonneg hH _) (mul_nonneg ha (Nat.cast_nonneg _)) (hbound.child (fun i => (hr i).pos) hPM ha i)
    have hs : (∑ i : Fin (g*s), activeMass (pushSpectrum H (child (A := ZMod M) h i))
        (diagonal (A := ZMod M) (m := g*s) h 1)) ≤
        a * FiniteTree.length (g*s) T (h+1) * ((K : ℝ)⁻¹^h + h * (2*(R : ℝ)/Q + 2*(V : ℝ)/T)) := by
      apply (Finset.sum_le_sum fun i _ => hchild i).trans_eq
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, FiniteTree.length, Nat.cast_mul]
      ring
    have hhi := high_estimate r j (fun i => (hr i).pos) hPM hD hQ hMR hMQ C H a hH ha hbound
    have hhis (i : Fin (g*s)) := high_estimate r j (fun i => (hr i).pos) hPM hD hQ hMR hMQ
      (C.2 i).2 (pushSpectrum H (child (A := ZMod M) h i)) (a*T) (pushSpectrum_nonneg hH _)
      (mul_nonneg ha (Nat.cast_nonneg _)) (hbound.child (fun i => (hr i).pos) hPM ha i)
    have hhs : (∑ i : Fin (g*s), highMass h Q (pushSpectrum H (child (A := ZMod M) h i))) ≤
        a * FiniteTree.length (g*s) T (h+1) * R / Q := by
      apply (Finset.sum_le_sum fun i _ => hhis i).trans_eq
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, FiniteTree.length, Nat.cast_mul]
      ring
    have hcy := cycle_estimate r j (fun i => (hr i).pos) hPM hPV hVT C H a hH ha hbound
    have hbr := branch_mass r hr hinj j hb hlower hQpow hg hM h C (hPM C.1) H hH
    have herror : highMass (h+1) Q H + (∑ i : Fin (g*s), highMass h Q (pushSpectrum H (child (A := ZMod M) h i))) +
        activeMass H (cycle (M := M) r j h C) ≤
      a * FiniteTree.length (g*s) T (h+1) * (2*(R : ℝ)/Q + 2*(V : ℝ)/T) := by
      calc
        _ ≤ a * FiniteTree.length (g*s) T (h+1) * R/Q + a * FiniteTree.length (g*s) T (h+1) * R/Q +
          a * FiniteTree.length (g*s) T (h+1) * (2*V)/T := add_le_add (add_le_add hhi hhs) hcy
        _ = _ := by ring
    have hmain := hbr.trans (add_le_add hs (mul_le_mul_of_nonneg_left herror hKpos.le))
    have hkn : 0 ≤ a * (FiniteTree.length (g*s) T (h+1) : ℝ) * h * (2*(R : ℝ)/Q + 2*(V : ℝ)/T) * ((K : ℝ)-1) := by positivity
    have he : (K : ℝ) * (a * FiniteTree.length (g*s) T (h+1) * ((K : ℝ)⁻¹^(h+1) + (h+1) * (2*(R : ℝ)/Q + 2*(V : ℝ)/T))) =
        (a * FiniteTree.length (g*s) T (h+1) * ((K : ℝ)⁻¹^h + h * (2*(R : ℝ)/Q + 2*(V : ℝ)/T)) +
          K * (a * FiniteTree.length (g*s) T (h+1) * (2*(R : ℝ)/Q + 2*(V : ℝ)/T))) +
        a * FiniteTree.length (g*s) T (h+1) * h * (2*(R : ℝ)/Q + 2*(V : ℝ)/T) * ((K : ℝ)-1) := by
      rw [pow_succ]
      field_simp
      ring
    apply (mul_le_mul_iff_right₀ hKpos).mp
    simp only [Nat.cast_add, Nat.cast_one]
    rw [he]
    linarith

lemma energy_diagonal_le_mass {M m h : ℕ} [NeZero M]
    (H : AddChar (State (ZMod M) m h) ℂ → ℝ) (hH : ∀ χ, 0 ≤ H χ) (a : ZMod M) :
    energy H (diagonal (A := ZMod M) (m := m) h a) ≤ 4 * activeMass H (diagonal (A := ZMod M) (m := m) h 1) := by
  rw [energy, activeMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro χ _
  rw [active_summary]
  split_ifs with hc
  · have he : χ (diagonal (A := ZMod M) (m := m) h a) = 1 := congrArg (fun η : AddChar (ZMod M) ℂ => η a) hc
    simp only [multiplier, he, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero, le_refl]
  · simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_right (multiplier_le_four χ _) (hH χ)

end TreeEdit.TorusFourier

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical TorusTree FiniteFourier FiniteProbability

theorem displacement_bound {I : Type} {g s L M T R D Q J V b e K h : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g ↪ I) (hr : ∀ i, Nat.Prime (r i)) (hinj : Function.Injective r)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M) (hPV : ∀ σ : Equiv.Perm I, period r j σ ≤ V) (hVT : V ≤ T)
    (hD : 0 < D) (hQ : 0 < Q) (hMR : M = R*D) (hMQ : M = J*Q)
    (hb : 1 ≤ b) (hlower : ∀ i, b ≤ r i) (hQpow : Q ≤ b^e) (hg : e+K ≤ g) (hK : 1 ≤ K)
    (hM : (g*s+1)*Q < M) (C : Config I L (g*s) h) (t : ZMod M)
    (F : State (ZMod M) (g*s) h → RealL1) (a : ℝ) (ha : 0 ≤ a)
    (hlip : ∀ x y, dist (F x) (F y) ≤ a * ed (sampledWord r j T R h C x).val (sampledWord r j T R h C y).val) :
    average (fun x => dist (F x) (F (x + diagonal (A := ZMod M) (m := g*s) h t))) ≤
      a * FiniteTree.length (g*s) T h * (4*((K : ℝ)⁻¹^h + h*(2*(R : ℝ)/Q + 2*(V : ℝ)/T))) := by
  obtain ⟨H, hH, _, he⟩ := l1_displacement_spectrum F
  have hbound : SpectralBound (R := R) r j T h C H a := by
    intro z
    rw [energy, ← he]
    have hh := average_mono (fun x => hlip x (x+z))
    simpa only [dist_comm, average, mean, ← Finset.mul_sum, mul_assoc, mul_left_comm] using hh
  have hh := mass_bound r j hr hinj hPM hPV hVT hD hQ hMR hMQ hb hlower hQpow hg hK hM C H a hH ha hbound
  calc
    _ = energy H (diagonal (A := ZMod M) (m := g*s) h t) := by simpa only [dist_comm, energy] using he (diagonal (A := ZMod M) (m := g*s) h t)
    _ ≤ 4*activeMass H (diagonal (A := ZMod M) (m := g*s) h 1) := energy_diagonal_le_mass H hH t
    _ ≤ 4*(a * FiniteTree.length (g*s) T h * ((K : ℝ)⁻¹^h + h*(2*(R : ℝ)/Q + 2*(V : ℝ)/T))) := by gcongr
    _ = _ := by ring

end TreeEdit.TorusFourier

end OAI
