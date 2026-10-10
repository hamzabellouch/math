import OAI.NumberTheory.Ostmann.QuadraticCenter.CRTPhase
import OAI.NumberTheory.Ostmann.QuadraticCenter.TranslatedPoisson

namespace OAI

namespace Ostmann.QuadraticCenter
open Ostmann.QuadraticSieve
open scoped BigOperators

theorem weighted_translated_gauss_crt {q d : ℕ} [NeZero q] [NeZero d]
    (hqd : q.Coprime d) (hq : Odd q) (hsq : Squarefree q)
    (r s : ℤ) (hbez : (d : ℤ) * r + (q : ℤ) * s = 1)
    (u t : ℤ) (G : ZMod d → ℂ) :
    (∑ x : ZMod (q * d), jacobiDirichletCharacter q
        ((ZMod.chineseRemainder hqd x).1 - (t : ZMod q)) *
      G (ZMod.chineseRemainder hqd x).2 * ZMod.stdAddChar ((u : ZMod (q * d)) * x)) =
    (ZMod.stdAddChar (((u * r : ℤ) : ZMod q) * (t : ZMod q)) *
      (jacobiSym (u * r) q : ℂ) * gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar) *
        ZMod.dft G (-((u * s : ℤ) : ZMod d)) := by
  rw [finite_crt_transform_bezout hqd r s hbez u
    (fun a => jacobiDirichletCharacter q (a - (t : ZMod q))) G,
    translated_jacobi_gauss_sum hq hsq]
  congr 1
  simp only [ZMod.dft_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [show -(b * -((u * s : ℤ) : ZMod d)) = ((u * s : ℤ) : ZMod d) * b by ring]
  ring

theorem finite_weighted_translated_gauss {q d : ℕ} [NeZero q] [NeZero d]
    (hqd : q.Coprime d) (hq : Odd q) (hsq : Squarefree q)
    (r s : ℤ) (hbez : (d : ℤ) * r + (q : ℤ) * s = 1)
    (u t : ℤ) (G : ZMod d → ℂ) :
    (∑ a : Fin (q * d), (jacobiSym ((a.val : ℤ) - t) q : ℂ) * G (a.val : ZMod d) *
      fourier u (((a.val : ℝ) / (q * d) : ℝ) : UnitAddCircle)) =
    (ZMod.stdAddChar (((u * r : ℤ) : ZMod q) * (t : ZMod q)) *
      (jacobiSym (u * r) q : ℂ) * gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar) *
        ZMod.dft G (-((u * s : ℤ) : ZMod d)) := by
  have hf (a : ℕ) :
      jacobiDirichletCharacter q ((ZMod.chineseRemainder hqd (a : ZMod (q * d))).1 -
          (t : ZMod q)) = (jacobiSym ((a : ℤ) - t) q : ℂ) := by
    have hp : ((a : ZMod q × ZMod d).1) = (a : ZMod q) :=
      map_natCast (RingHom.fst (ZMod q) (ZMod d)) a
    rw [map_natCast, hp]
    simpa only [Int.cast_sub, Int.cast_natCast] using
      jacobiDirichletCharacter_intCast q ((a : ℤ) - t)
  have hg (a : ℕ) : (ZMod.chineseRemainder hqd (a : ZMod (q * d))).2 = (a : ZMod d) := by
    rw [map_natCast]
    exact map_natCast (RingHom.snd (ZMod q) (ZMod d)) a
  calc
    _ = ∑ a : Fin (q * d), jacobiDirichletCharacter q
        ((ZMod.chineseRemainder hqd (a.val : ZMod (q * d))).1 - (t : ZMod q)) *
      G (ZMod.chineseRemainder hqd (a.val : ZMod (q * d))).2 *
        ZMod.stdAddChar ((u : ZMod (q * d)) * (a.val : ZMod (q * d))) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hf, hg]
      congr 1
      simpa only [Int.cast_natCast, Nat.cast_mul] using
        fourier_div_eq_stdAddChar_mul (q * d) u (a.val : ℤ)
    _ = ∑ x : ZMod (q * d), jacobiDirichletCharacter q
        ((ZMod.chineseRemainder hqd x).1 - (t : ZMod q)) *
      G (ZMod.chineseRemainder hqd x).2 * ZMod.stdAddChar ((u : ZMod (q * d)) * x) :=
      sum_fin_residues_eq_sum_zmod (q * d) (fun x => jacobiDirichletCharacter q
        ((ZMod.chineseRemainder hqd x).1 - (t : ZMod q)) *
          G (ZMod.chineseRemainder hqd x).2 * ZMod.stdAddChar ((u : ZMod (q * d)) * x))
    _ = _ := weighted_translated_gauss_crt hqd hq hsq r s hbez u t G

end Ostmann.QuadraticCenter

end OAI
