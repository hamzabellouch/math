import OAI.NumberTheory.TwoPoint.Bounds.PositiveWeightComparison
import OAI.NumberTheory.TwoPoint.Bounds.PrimeCoordinates

namespace OAI

/-! Actual integer-origin transfer of one positive deletion cost. The
event is represented by its literal prime-residue circuit, and the
comparison uses the same CRT law as the graph estimates. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem BravermanDepth22Input.eventually_positive_prime_cost_comparison
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (S : Finset ℕ), S ⊆ data.P ∪ data.Q → (S.card : ℝ) ≤ L ^ 2 →
      ∀ (r ninput : ℕ), (r : ℝ) ≤ 100 * Real.log L →
      ∀ (literal : Fin ninput → ↥(data.P ∪ data.Q) × ℤ)
        (index : Fin (Fintype.card S) → Fin ninput) (site : ℤ),
      (∀ i, (literal (index i)).1.val = ((Fintype.equivFin S).symm i).val ∧
        (literal (index i)).2 = site) →
      ∀ (c : AC0Circuit ninput), c.depth ≤ 19 → (c.size : ℝ) ≤ Real.exp (L ^ 3) →
      ∀ (bad : ℤ → Prop),
      (∀ n, c.eval (fun i => decide (((literal i).1.val : ℤ) ∣ n + (literal i).2)) = true ↔
        bad n) →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let F := fun n : ℤ => (4 : ℝ) ^ r * positivePrimeWeight S (n + site) *
        if bad n then 1 else 0
      |uniformAverage (fun x : Fin N => F (a + x.val)) -
        (data.residueLaw B hB).average (fun x => F (data.residueOrigin x))| ≤
          Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_positive_weight_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb] with L hb
  intro h J M B data hB hpool hBL S hS hSL r ninput hr literal index site hindex
    c hc hsize bad hbad a N hN
  let primes := data.P ∪ data.Q
  let modulus := primeResidueModuli primes
  let (i : Fin (Fintype.card primes)) : NeZero (modulus i) :=
    ⟨(primeResidueModuli_prime primes (fun p hp => data.prime ⟨p, hp⟩) i).ne_zero⟩
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let p : Fin (Fintype.card S) → ℕ := fun i => (e i).val
  let F := fun z : ∀ i, ZMod (modulus i) =>
    let bits := residueCircuitInputs modulus (primeLiteralCoordinate primes literal)
      (primeLiteralTest primes literal) z
    positivePrimeTable p r (fun i => bits (index i)) * c.indicator bits
  let cost := fun n : ℤ => (4 : ℝ) ^ r * positivePrimeWeight S (n + site) *
    if bad n then 1 else 0
  have hp (i : Fin (Fintype.card S)) : 1 ≤ p i :=
    (data.prime ⟨p i, hS (e i).property⟩).one_lt.le
  have hcard : (Fintype.card primes : ℝ) ≤ Real.exp L := by
    have hh := primePool_card_bound primes (fun p hp => data.prime ⟨p, hp⟩) B hB
    have hh' : (primes.card : ℝ) ≤ B := by exact_mod_cast hh
    simpa only [Fintype.card_coe] using hh'.trans hBL
  have hm : 0 < Fintype.card primes := by
    simpa only [Fintype.card_coe] using card_pos.mpr hpool
  have hmod (i : Fin (Fintype.card primes)) : (modulus i : ℝ) ≤ Real.exp L :=
    primeResidueModuli_bound primes (Real.exp L)
      (fun p hp => (show (p : ℝ) ≤ B by exact_mod_cast hB p hp).trans hBL) i
  have hh := hb (Fintype.card primes) modulus hm (by linarith)
    (primeResidueModuli_coprime primes (fun p hp => data.prime ⟨p, hp⟩)) hmod
    (Fintype.card S) r ninput p hp (by simpa only [Fintype.card_coe] using hSL) hr
    (primeLiteralCoordinate primes literal) (primeLiteralTest primes literal) index c
    hc hsize a N hN
  change |uniformAverage (fun x : Fin N => F (fun i => (a + x.val : ZMod (modulus i)))) -
    uniformAverage F| ≤ Real.exp (-(L ^ 9)) at hh
  have hF (n : ℤ) : F (fun i => (n : ZMod (modulus i))) = cost n := by
    let bits := residueCircuitInputs modulus (primeLiteralCoordinate primes literal)
      (primeLiteralTest primes literal) (fun i => (n : ZMod (modulus i)))
    have hall : bits = fun i => decide (((literal i).1.val : ℤ) ∣ n + (literal i).2) := by
      funext i
      exact primeLiteral_integer_input primes literal n i
    have hbits (i : Fin (Fintype.card S)) : bits (index i) =
        decide ((p i : ℤ) ∣ n + site) := by
      rw [hall]
      simp only [(hindex i).1, (hindex i).2, p, e]
    have hgate : c.indicator bits = if bad n then 1 else 0 := by
      have heval : c.eval bits = true ↔ bad n := by
        simpa only [hall] using hbad n
      simp only [AC0Circuit.indicator, heval]
    change positivePrimeTable p r (fun i => bits (index i)) * c.indicator bits = cost n
    simp only [hbits, hgate]
    rw [positivePrimeTable_actual S e r (n + site)]
  have hmodel : (data.residueLaw B hB).average (fun x => cost (data.residueOrigin x)) =
      uniformAverage F := by
    rw [← data.residue_average_canonical hB F]
    apply congrArg (data.residueLaw B hB).average
    funext x
    rw [← hF, data.canonical_origin]
  dsimp only
  rw [hmodel]
  have hsample : (fun x : Fin N => cost (a + x.val)) =
      (fun x : Fin N => F (fun i => (a + x.val : ZMod (modulus i)))) := by
    funext x
    simpa only [Int.cast_add, Int.cast_natCast, Nat.cast_add] using (hF (a + x.val)).symm
  rw [hsample]
  exact hh

end TwoPointCorrelations

end OAI
