import OAI.NumberTheory.EgyptianFractions.CollisionCounting

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- A collision-energy threshold, rather than a small-image hypothesis,
also permits the larger-sieve double count. The diagonal is removed before
using the bound on how many maps can identify two distinct inputs. -/
theorem large_collision_maps_card_le {ι α : Type*} {β : ι → Type*}
    [DecidableEq ι] [DecidableEq α] [∀ i, DecidableEq (β i)]
    (I : Finset ι) (A : Finset α) (f : ∀ i, α → β i)
    {H R : ℝ} (hH : 0 < H) (hR : 0 ≤ R)
    (hsize : 2 * H ≤ (A.card : ℝ))
    (henergy : ∀ i ∈ I,
      (A.card : ℝ) ^ 2 ≤ H * ((collisionPairs A (f i)).card : ℝ))
    (hpairs : ∀ p ∈ A.offDiag,
      ((I.filter (fun i => f i p.1 = f i p.2)).card : ℝ) ≤ R) :
    (I.card : ℝ) ≤ 2 * H * R := by
  classical
  have hlow : ∀ i ∈ I, (A.card : ℝ) ^ 2 / (2 * H) ≤
      ((A.offDiag.bipartiteAbove (fun i p => f i p.1 = f i p.2) i).card : ℝ) := by
    intro i hi
    have heq : A.offDiag.bipartiteAbove (fun i p => f i p.1 = f i p.2) i =
        strictCollisionPairs A (f i) := by
      ext p
      simp only [Finset.mem_bipartiteAbove, Finset.mem_offDiag,
        strictCollisionPairs, collisionPairs, Finset.mem_filter, Finset.mem_product]
      tauto
    rw [heq]
    have hdiag : ((collisionPairs A (f i)).card : ℝ) =
        ((strictCollisionPairs A (f i)).card : ℝ) + (A.card : ℝ) := by
      exact_mod_cast collision_card_eq_strict_add A (f i)
    have he := henergy i hi
    rw [hdiag] at he
    have hmul := mul_nonneg (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)
      (sub_nonneg.mpr hsize)
    apply (div_le_iff₀ (by positivity : 0 < 2 * H)).mpr
    nlinarith
  have hdouble := Finset.card_nsmul_le_card_nsmul
    (R := ℝ) (s := I) (t := A.offDiag)
    (m := (A.card : ℝ) ^ 2 / (2 * H)) (n := R)
    (fun (i : ι) (p : α × α) => f i p.1 = f i p.2) hlow hpairs
  simp only [nsmul_eq_mul] at hdouble
  have hoffnat : A.offDiag.card ≤ A.card ^ 2 := by
    calc
      A.offDiag.card ≤ (A ×ˢ A).card := Finset.card_le_card (by
        intro p hp
        exact Finset.mem_product.mpr ⟨(Finset.mem_offDiag.mp hp).1,
          (Finset.mem_offDiag.mp hp).2.1⟩)
      _ = A.card ^ 2 := by rw [Finset.card_product, pow_two]
  have hoff : (A.offDiag.card : ℝ) ≤ (A.card : ℝ) ^ 2 := by
    exact_mod_cast hoffnat
  have hbound := hdouble.trans (mul_le_mul_of_nonneg_right hoff hR)
  have hmain : (I.card : ℝ) * (A.card : ℝ) ^ 2 ≤
      (A.card : ℝ) ^ 2 * R * (2 * H) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * H)).mp
    simpa only [mul_div_assoc] using hbound
  have hN : 0 < (A.card : ℝ) := by linarith
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hN)).mp
  calc
    (I.card : ℝ) * (A.card : ℝ) ^ 2 ≤ (A.card : ℝ) ^ 2 * R * (2 * H) := hmain
    _ = (2 * H * R) * (A.card : ℝ) ^ 2 := by ring

/-- For arbitrary moduli, each off-diagonal collision gives a divisor of
a positive difference. The predicate `Q` can restrict the divisors to rough
integers; the difference itself need not be rough. -/
theorem moduli_energy_card_le_of_divisor_count
    (I A : Finset ℕ) (P : ℕ) (X : ℝ) (Q : ℕ → Prop) [DecidablePred Q]
    {H R : ℝ} (hH : 0 < H) (hR : 0 ≤ R)
    (hA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ P)
    (hI : ∀ q ∈ I, (q : ℝ) ≤ X ∧ Q q)
    (hsize : 2 * H ≤ (A.card : ℝ))
    (henergy : ∀ q ∈ I,
      (A.card : ℝ) ^ 2 ≤ H * ((collisionPairs A (fun a => a % q)).card : ℝ))
    (hdivisors : ∀ n : ℕ, 0 < n → n ≤ P →
      ((n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ X ∧ Q d)).card : ℝ) ≤ R) :
    (I.card : ℝ) ≤ 2 * H * R := by
  apply large_collision_maps_card_le I A (fun q a => a % q) hH hR hsize henergy
  intro p hp
  obtain ⟨hpa, hpb, hne⟩ := Finset.mem_offDiag.mp hp
  have hd : 0 < Nat.dist p.1 p.2 := Nat.dist_pos_of_ne hne
  have hdP : Nat.dist p.1 p.2 ≤ P := by
    have ha := hA p.1 hpa
    have hb := hA p.2 hpb
    unfold Nat.dist
    omega
  have hsub : I.filter (fun q => p.1 % q = p.2 % q) ⊆
      (Nat.dist p.1 p.2).divisors.filter (fun d : ℕ => (d : ℝ) ≤ X ∧ Q d) := by
    intro q hq
    obtain ⟨hqI, hmod⟩ := Finset.mem_filter.mp hq
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hd.ne'⟩, hI q hqI⟩
    have hm : Nat.ModEq q p.1 p.2 := hmod
    rcases le_total p.1 p.2 with hab | hba
    · rw [Nat.dist_eq_sub_of_le hab]
      exact (Nat.modEq_iff_dvd' hab).mp hm
    · rw [Nat.dist_eq_sub_of_le_right hba]
      exact (Nat.modEq_iff_dvd' hba).mp hm.symm
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (hdivisors _ hd hdP)

/-- A common divisor list on a modulus block turns a power-size collision
exception into a sparse set of moduli. This is applicable to every modulus,
not only primes, and retains the genuine restricted-divisor-count input. -/
theorem moduli_rpow_energy_card_le
    (I A : Finset ℕ) (P : ℕ) (X θ : ℝ) (Q : ℕ → Prop) [DecidablePred Q]
    {R : ℝ} (hX : 0 < X) (hθ : 0 ≤ θ) (hR : 0 ≤ R)
    (hA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ P)
    (hI : ∀ q ∈ I, (q : ℝ) ≤ X ∧ Q q)
    (hsize : 2 * X ^ θ ≤ (A.card : ℝ))
    (henergy : ∀ q ∈ I, (A.card : ℝ) ^ 2 ≤
      (q : ℝ) ^ θ * ((collisionPairs A (fun a => a % q)).card : ℝ))
    (hdivisors : ∀ n : ℕ, 0 < n → n ≤ P →
      ((n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ X ∧ Q d)).card : ℝ) ≤ R) :
    (I.card : ℝ) ≤ 2 * X ^ θ * R := by
  apply moduli_energy_card_le_of_divisor_count I A P X Q
    (Real.rpow_pos_of_pos hX θ) hR hA hI hsize ?_ hdivisors
  intro q hq
  exact (henergy q hq).trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (Nat.cast_nonneg q) (hI q hq).1 hθ) (by positivity))

end Problem337

end

end OAI
