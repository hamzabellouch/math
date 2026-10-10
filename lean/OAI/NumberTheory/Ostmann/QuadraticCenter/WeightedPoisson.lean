import OAI.NumberTheory.Ostmann.QuadraticCenter.WeightedGauss

namespace OAI

namespace Ostmann.QuadraticCenter
open Ostmann.QuadraticSieve
open scoped BigOperators SchwartzMap FourierTransform

theorem divModEquiv_residue_cast {Q l : ℕ} [NeZero Q] (hl : l ∣ Q) (n : ℤ) :
    (((Int.divModEquiv Q n).2.val : ℕ) : ZMod l) = (n : ZMod l) := by
  have hr : (Int.divModEquiv Q n).1 * (Q : ℤ) +
      ((Int.divModEquiv Q n).2.val : ℤ) = n := (Int.divModEquiv Q).symm_apply_apply n
  have hQ : (Q : ZMod l) = 0 := (ZMod.natCast_eq_zero_iff Q l).mpr hl
  have hz := congrArg (fun z : ℤ => (z : ZMod l)) hr
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, hQ, mul_zero, zero_add] using hz

theorem weighted_translated_quadratic_poisson {q d : ℕ} [NeZero q] [NeZero d]
    (hqd : q.Coprime d) (hq : Odd q) (hsq : Squarefree q)
    (r s : ℤ) (hbez : (d : ℤ) * r + (q : ℤ) * s = 1)
    (X : ℝ) (hX : 0 < X) (t : ℤ) (G : ZMod d → ℂ) (f : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, (jacobiSym (n - t) q : ℂ) * G (n : ZMod d) * f ((n : ℝ) / X)) =
      ((X / (q * d) : ℝ) : ℂ) * gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar *
        ∑' u : ℤ, (jacobiSym (u * r) q : ℂ) *
          ZMod.stdAddChar (((u * r : ℤ) : ZMod q) * (t : ZMod q)) *
          ZMod.dft G (-((u * s : ℤ) : ZMod d)) * 𝓕 f ((u : ℝ) * X / (q * d)) := by
  have hin (n : ℤ) :
      (jacobiSym (((Int.divModEquiv (q * d) n).2.val : ℤ) - t) q : ℂ) *
        G ((Int.divModEquiv (q * d) n).2.val : ZMod d) =
      (jacobiSym (n - t) q : ℂ) * G (n : ZMod d) := by
    have hqmod := divModEquiv_residue_cast (dvd_mul_right q d) n
    have hdmod := divModEquiv_residue_cast (dvd_mul_left d q) n
    rw [hdmod]
    congr 1
    rw [← jacobiDirichletCharacter_intCast, ← jacobiDirichletCharacter_intCast]
    simp only [Int.cast_sub, Int.cast_natCast, hqmod]
  have hp := periodic_weighted_poisson_scaled (q * d) X hX
    (fun a : Fin (q * d) => (jacobiSym ((a.val : ℤ) - t) q : ℂ) * G (a.val : ZMod d)) f
  simp_rw [hin] at hp
  simp only [Nat.cast_mul] at hp
  simp_rw [finite_weighted_translated_gauss hqd hq hsq r s hbez] at hp
  calc
    _ = ∑' u : ℤ, ((X / (q * d) : ℝ) : ℂ) *
        ((ZMod.stdAddChar (((u * r : ℤ) : ZMod q) * (t : ZMod q)) *
          (jacobiSym (u * r) q : ℂ) * gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar) *
            ZMod.dft G (-((u * s : ℤ) : ZMod d))) *
        𝓕 f ((u : ℝ) * X / (q * d)) := hp
    _ = ∑' u : ℤ,
        (((X / (q * d) : ℝ) : ℂ) * gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar) *
        ((jacobiSym (u * r) q : ℂ) *
          ZMod.stdAddChar (((u * r : ℤ) : ZMod q) * (t : ZMod q)) *
          ZMod.dft G (-((u * s : ℤ) : ZMod d)) * 𝓕 f ((u : ℝ) * X / (q * d))) := by
      apply tsum_congr
      intro u
      ring
    _ = _ := tsum_mul_left

theorem exists_crt_bezout {q d : ℕ} (hqd : q.Coprime d) :
    ∃ r s : ℤ, (d : ℤ) * r + (q : ℤ) * s = 1 := by
  obtain ⟨r, s, hrs⟩ := hqd.symm.isCoprime
  exact ⟨r, s, by simpa only [mul_comm] using hrs⟩

end Ostmann.QuadraticCenter

end OAI
