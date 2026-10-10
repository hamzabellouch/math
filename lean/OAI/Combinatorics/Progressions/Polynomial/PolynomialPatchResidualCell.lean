import OAI.Combinatorics.Progressions.Lattices.TriangularIntegerLift

namespace OAI

section

namespace Erdos3.PolynomialSlots

open MvPolynomial

variable {σ : Type*} {D E : ℕ} {w : Fin (D + E) → ℕ}

def takePrefix (A : PolynomialSlots σ (D + E) w) :
    PolynomialSlots σ D (fun i => w (i.castAdd E)) where
  center i := A.center (i.castAdd E)
  degree i := A.degree (i.castAdd E)

theorem takePrefix_slots (A : PolynomialSlots σ (D + E) w) (t : σ → ℝ) :
    A.takePrefix.slots t = (A.slots t).takePrefix := by
  apply TriangularSlots.ext
  intro x i
  change aeval (Sum.elim t (fun j => x (earlierSlot i j))) (A.center (i.castAdd E)) =
    aeval (Sum.elim t (fun j => Fin.append x 0 (earlierSlot (i.castAdd E) j)))
      (A.center (i.castAdd E))
  apply congrArg (fun f : σ ⊕ Fin i.val → ℝ => aeval f (A.center (i.castAdd E)))
  funext v
  cases v with
  | inl a => rfl
  | inr j =>
    change x (earlierSlot i j) = Fin.append x 0 ((earlierSlot i j).castAdd E)
    exact (Fin.append_left _ _ _).symm

end Erdos3.PolynomialSlots

end

section

namespace Erdos3

open MvPolynomial

namespace PolynomialPatch

variable {s D E : ℕ}

theorem exists_freeze_of_residual_cell (A : PolynomialPatch Unit s (D + E))
    (g : ℕ → Fin D → ℤ) (z : Fin D → ℝ) {N : ℕ} {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 12)
    (hsmall : (2 : ℝ) ^ (s + 1) * ε < 1)
    (hz : ∀ i, |z i| ≤ 1 / 4)
    (hcell : ∀ n < N, ∀ i,
      ‖(A.form.slots (fun _ => (n : ℝ))).takePrefix.residual (g n) i - z i‖ ≤ ε) :
    ∃ F : PolynomialPatch Unit s E, F.kernel.lip = A.kernel.lip ∧
      ∀ n < N, dist (A.value (fun _ => (n : ℝ))) (F.value (fun _ => (n : ℝ))) ≤
        A.kernel.lip * ε := by
  have hthreshold (i : Fin D) : (2 : ℝ) ^ (A.weight (i.castAdd E) + 1) * ε < 1 := by
    apply lt_of_le_of_lt _ hsmall
    apply mul_le_mul_of_nonneg_right _ hε0
    exact pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right (A.weight_le _) 1)
  obtain ⟨I, hI, _, heq⟩ := A.form.takePrefix.exists_integer_lifts_of_small_residuals g z
    hthreshold (by simpa only [PolynomialSlots.takePrefix_slots] using hcell)
  refine ⟨A.freezePrefix I hI z, rfl, ?_⟩
  intro n hn
  apply A.freezePrefix_error I hI z (fun _ => (n : ℝ)) (g n) (heq n hn) hz hε
  apply (dist_pi_le_iff hε0).mpr
  intro i
  simpa only [dist_eq_norm] using hcell n hn i

end PolynomialPatch

namespace TriangularSlots

theorem takePrefix_zero {d : ℕ} (A : TriangularSlots d) :
    A.takePrefix (D := d) (E := 0) = A := by
  apply TriangularSlots.ext
  intro x i
  have happend : Fin.append x (0 : Fin 0 → ℝ) = x := by
    ext j
    exact Fin.append_left x (0 : Fin 0 → ℝ) j
  change A.center (Fin.append x (0 : Fin 0 → ℝ)) (i.castAdd 0) = A.center x i
  rw [happend]
  exact congrArg (A.center x) (Fin.ext rfl)

end TriangularSlots

namespace PolynomialPatch

theorem exists_constant_of_residual_cell {s d : ℕ} (A : PolynomialPatch Unit s d)
    (g : ℕ → Fin d → ℤ) (z : Fin d → ℝ) {N : ℕ} {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 12)
    (hsmall : (2 : ℝ) ^ (s + 1) * ε < 1)
    (hz : ∀ i, |z i| ≤ 1 / 4)
    (hcell : ∀ n < N, ∀ i,
      ‖(A.form.slots (fun _ => (n : ℝ))).residual (g n) i - z i‖ ≤ ε) :
    ∃ c ∈ Set.Icc (0 : ℝ) 1, ∀ n < N,
      dist (A.value (fun _ => (n : ℝ))) c ≤ A.kernel.lip * ε := by
  obtain ⟨F, _, hF⟩ := A.exists_freeze_of_residual_cell (D := d) (E := 0) g z
    hε0 hε hsmall hz (by simpa only [TriangularSlots.takePrefix_zero] using hcell)
  refine ⟨F.kernel.value 0, ⟨F.kernel.nonneg _, F.kernel.le_one _⟩, ?_⟩
  intro n hn
  simpa only [PolynomialPatch.value_rank_zero] using hF n hn

end PolynomialPatch
end Erdos3

end

end OAI
