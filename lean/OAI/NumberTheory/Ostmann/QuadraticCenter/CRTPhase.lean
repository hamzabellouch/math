import OAI.NumberTheory.Ostmann.QuadraticSieveGauss

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem stdAddChar_product_bezout {q d : ℕ} [NeZero q] [NeZero d]
    (r s : ℤ) (hbez : (d : ℤ) * r + (q : ℤ) * s = 1) (u x : ℤ) :
    ZMod.stdAddChar (((u * x : ℤ) : ZMod (q * d))) =
      ZMod.stdAddChar (((u * r * x : ℤ) : ZMod q)) *
        ZMod.stdAddChar (((u * s * x : ℤ) : ZMod d)) := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ← Complex.exp_add]
  push_cast
  apply congrArg Complex.exp
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  have hb : (d : ℂ) * r + (q : ℂ) * s = 1 := by exact_mod_cast hbez
  have hf : (r : ℂ) / q + (s : ℂ) / d = 1 / ((q : ℂ) * d) := by
    field_simp
    linear_combination hb
  calc
    _ = (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ) * (x : ℂ)) *
        ((r : ℂ) / q + (s : ℂ) / d) := by rw [hf]; ring
    _ = _ := by ring

theorem stdAddChar_crt_bezout {q d : ℕ} [NeZero q] [NeZero d]
    (hqd : q.Coprime d) (r s : ℤ) (hbez : (d : ℤ) * r + (q : ℤ) * s = 1)
    (u : ℤ) (x : ZMod (q * d)) :
    ZMod.stdAddChar ((u : ZMod (q * d)) * x) =
      ZMod.stdAddChar (((u * r : ℤ) : ZMod q) * (ZMod.chineseRemainder hqd x).1) *
        ZMod.stdAddChar (((u * s : ℤ) : ZMod d) * (ZMod.chineseRemainder hqd x).2) := by
  obtain ⟨x, rfl⟩ := ZMod.intCast_surjective x
  have hf : ((x : ZMod q × ZMod d).1) = (x : ZMod q) :=
    map_intCast (RingHom.fst (ZMod q) (ZMod d)) x
  have hg : ((x : ZMod q × ZMod d).2) = (x : ZMod d) :=
    map_intCast (RingHom.snd (ZMod q) (ZMod d)) x
  simpa only [map_intCast, hf, hg, Int.cast_mul] using
    stdAddChar_product_bezout r s hbez u x

theorem finite_crt_transform_bezout {q d : ℕ} [NeZero q] [NeZero d]
    (hqd : q.Coprime d) (r s : ℤ) (hbez : (d : ℤ) * r + (q : ℤ) * s = 1)
    (u : ℤ) (F : ZMod q → ℂ) (G : ZMod d → ℂ) :
    (∑ x : ZMod (q * d), F (ZMod.chineseRemainder hqd x).1 *
      G (ZMod.chineseRemainder hqd x).2 * ZMod.stdAddChar ((u : ZMod (q * d)) * x)) =
    (∑ a : ZMod q, F a * ZMod.stdAddChar (((u * r : ℤ) : ZMod q) * a)) *
      (∑ b : ZMod d, G b * ZMod.stdAddChar (((u * s : ℤ) : ZMod d) * b)) := by
  simp_rw [stdAddChar_crt_bezout hqd r s hbez]
  rw [Fintype.sum_equiv (ZMod.chineseRemainder hqd).toEquiv
    (fun x => F (ZMod.chineseRemainder hqd x).1 * G (ZMod.chineseRemainder hqd x).2 *
      (ZMod.stdAddChar (((u * r : ℤ) : ZMod q) * (ZMod.chineseRemainder hqd x).1) *
        ZMod.stdAddChar (((u * s : ℤ) : ZMod d) * (ZMod.chineseRemainder hqd x).2)))
    (fun z : ZMod q × ZMod d => F z.1 * G z.2 *
      (ZMod.stdAddChar (((u * r : ℤ) : ZMod q) * z.1) *
        ZMod.stdAddChar (((u * s : ℤ) : ZMod d) * z.2))) (fun _ => rfl)]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

end Ostmann.QuadraticCenter

end OAI
