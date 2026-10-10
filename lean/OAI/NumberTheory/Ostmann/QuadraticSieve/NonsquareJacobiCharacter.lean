import Mathlib.NumberTheory.DirichletCharacter.Bounds
import OAI.NumberTheory.Ostmann.QuadraticSieve.PrimitiveKernelCharacter
import OAI.NumberTheory.Ostmann.QuadraticSieve.WeightedJacobiMoment

namespace OAI

/-! # The concrete character behind nonsquare Jacobi cancellation -/

namespace Ostmann

private theorem exists_squarefree_jacobi_level (s : ℕ) (hs : Squarefree s)
    (hs1 : 1 < s) :
    ∃ q : ℕ, 0 < q ∧ q ∣ 8 * s ∧ ∃ χ : DirichletCharacter ℝ q,
      χ ≠ 1 ∧ ∀ a : ℕ, Odd a → a.Coprime s →
        χ (a : ZMod q) = realJacobi s a := by
  rcases Nat.even_or_odd s with he | ho
  · obtain ⟨N, hN⟩ := he
    have hsN : s = 2 * N := by omega
    have hNp : 0 < N := by omega
    have hsf : Squarefree (2 * N) := hsN ▸ hs
    have hNo : Odd N := (Nat.coprime_of_squarefree_mul hsf).odd_of_left
    have hNs : Squarefree N := hsf.of_mul_right
    let : NeZero N := ⟨hNp.ne'⟩
    let : NeZero (Nat.lcm N 8) := ⟨Nat.lcm_ne_zero hNp.ne' (by decide)⟩
    let χ := signedEvenKernelCharacter N false
    have hχ : χ ≠ 1 := by
      by_cases hN1 : N = 1
      · subst N
        intro hc
        have hv := signedEvenKernelCharacter_value 1 false (by decide) 5 (by decide) (by decide)
        change χ (5 : ZMod (Nat.lcm 1 8)) = _ at hv
        have hu : IsUnit (5 : ZMod (Nat.lcm 1 8)) := (ZMod.isUnit_iff_coprime 5 _).mpr (by decide)
        rw [hc, MulChar.one_apply hu] at hv
        have hJ : jacobiSym 2 5 = -1 := by
          rw [jacobiSym.at_two (by decide)]
          norm_num [ZMod.χ₈_nat_eq_if_mod_eight]
        norm_num [hJ] at hv
      · exact character_ne_one_of_conductor_dvd χ (by omega)
          (signedEvenKernelCharacter_conductor_bounds N false hNs hNo).1
    refine ⟨Nat.lcm N 8, Nat.pos_of_ne_zero (NeZero.ne _), ?_, χ, hχ, ?_⟩
    · apply Nat.lcm_dvd
      · rw [hsN]
        exact dvd_mul_of_dvd_right (dvd_mul_left N 2) 8
      · exact dvd_mul_right 8 s
    · intro a hao hac
      have hacN := hac.of_dvd_right (hsN ▸ dvd_mul_left N 2)
      have hac8 : a.Coprime 8 := by simpa using hao.coprime_two_right.pow_right 3
      have hacq := (hacN.mul_right hac8).of_dvd_right (Nat.lcm_dvd_mul N 8)
      have hv := signedEvenKernelCharacter_value N false hNo a hacq hao
      simpa [χ, realJacobi, hsN, Nat.cast_mul] using hv
  · let : NeZero s := ⟨by omega⟩
    let : NeZero (Nat.lcm s 4) := ⟨Nat.lcm_ne_zero (NeZero.ne s) (by decide)⟩
    let χ := signedOddKernelCharacter s false
    refine ⟨Nat.lcm s 4, Nat.pos_of_ne_zero (NeZero.ne _), ?_, χ, ?_, ?_⟩
    · exact Nat.lcm_dvd (dvd_mul_left s 8) (dvd_mul_of_dvd_left (by decide : 4 ∣ 8) s)
    · exact character_ne_one_of_conductor_dvd χ hs1
        (signedOddKernelCharacter_conductor_bounds s false hs ho).1
    · intro a hao hac
      have hac4 : a.Coprime 4 := by simpa using hao.coprime_two_right.pow_right 2
      have hacq := (hac.mul_right hac4).of_dvd_right (Nat.lcm_dvd_mul s 4)
      simpa [χ, realJacobi] using signedOddKernelCharacter_value s false ho a hacq hao

/-- At level `8*n` the extra nonunit zeroes are exactly the even arguments
and the common factors with `n`. Induction from the nontrivial squarefree
kernel preserves nonprincipality. -/
theorem exists_nonsquare_jacobi_character (n : ℕ) (hn : 0 < n)
    (hns : ¬IsSquare n) :
    ∃ χ : DirichletCharacter ℝ (8 * n), χ ≠ 1 ∧
      ∀ a : ℕ, χ (a : ZMod (8 * n)) = if Odd a then realJacobi n a else 0 := by
  obtain ⟨s, w, hsp, hwp, he, hsf⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hs1 : 1 < s := by
    by_contra h
    have hs : s = 1 := by omega
    apply hns
    refine ⟨w, ?_⟩
    simpa [hs, pow_two] using he.symm
  obtain ⟨q, hqp, hqd, ψ, hψ, hvalue⟩ := exists_squarefree_jacobi_level s hsf hs1
  have hsn : s ∣ n := ⟨w ^ 2, by nlinarith [he]⟩
  have hqn : q ∣ 8 * n := hqd.trans (Nat.mul_dvd_mul_left 8 hsn)
  let : NeZero (8 * n) := ⟨by omega⟩
  let χ := ψ.changeLevel hqn
  refine ⟨χ, ?_, ?_⟩
  · exact fun hc => hψ ((DirichletCharacter.changeLevel_eq_one_iff hqn).mp hc)
  · intro a
    by_cases hao : Odd a
    · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hao))]
      by_cases hac : a.Coprime (8 * n)
      · have hasn : a.Coprime n := hac.of_dvd_right (dvd_mul_left n 8)
        have has : a.Coprime s := hasn.of_dvd_right hsn
        have hwan : w ∣ n := ⟨w * s, by nlinarith [he]⟩
        have hwc : w.Coprime a := (hasn.of_dvd_right hwan).symm
        have hcast : χ (a : ZMod (8 * n)) = ψ (a : ZMod q) := by
          rw [← Int.cast_natCast (R := ZMod (8 * n)),
            DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _
              (Nat.isCoprime_iff_coprime.mpr hac), Int.cast_natCast]
        rw [hcast, hvalue a hao has]
        unfold realJacobi
        congr 1
        rw [← he, Nat.cast_mul, Nat.cast_pow, jacobiSym.mul_left,
          jacobiSym.pow_left, jacobiSym.sq_one (by simpa using hwc), one_mul]
      · have hnotu : ¬IsUnit (a : ZMod (8 * n)) := by
          simpa only [ZMod.isUnit_iff_coprime] using hac
        rw [MulChar.map_nonunit χ hnotu]
        have hasn : ¬a.Coprime n := by
          intro han
          have ha8 : a.Coprime 8 := by simpa using hao.coprime_two_right.pow_right 3
          exact hac (ha8.mul_right han)
        have ha0 : a ≠ 0 := by intro h; subst a; norm_num at hao
        let : NeZero a := ⟨ha0⟩
        have hj : jacobiSym (n : ℤ) a = 0 :=
          jacobiSym.eq_zero_iff_not_coprime.mpr (by simpa [Nat.coprime_comm] using hasn)
        simp [realJacobi, hj]
    · rw [ite_eq_right_iff.mpr (fun h => False.elim (hao h))]
      apply MulChar.map_nonunit
      intro hu
      have hc := (ZMod.isUnit_iff_coprime a (8 * n)).mp hu
      have hc2 : a.Coprime 2 := hc.of_dvd_right (dvd_mul_of_dvd_left (by decide : 2 ∣ 8) n)
      exact hao hc2.odd_of_right

end Ostmann

end OAI
