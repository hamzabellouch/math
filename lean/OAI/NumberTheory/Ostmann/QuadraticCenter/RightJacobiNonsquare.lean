import OAI.NumberTheory.Ostmann.QuadraticCenter.RightJacobiWitness

namespace OAI

namespace Ostmann.QuadraticCenter

theorem exists_nonsquare_right_nonresidue {n : ℕ} (hn : 0 < n) (hns : ¬ IsSquare n) :
    ∃ a : ℕ, a.Coprime (4 * n) ∧ rightJacobi n a = -1 := by
  obtain ⟨u, t, hu, ht, hnu, hsq⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hu1 : u ≠ 1 := by
    intro he
    subst u
    apply hns
    refine ⟨t, ?_⟩
    simpa only [mul_one, pow_two] using hnu.symm
  obtain ⟨b, hbc, hbo, hbj⟩ := exists_squarefree_right_nonresidue hsq hu1
  have hudvd : u ∣ n := ⟨t ^ 2, by simpa only [mul_comm] using hnu.symm⟩
  obtain ⟨a, hac, hab⟩ := exists_coprime_lift (M := 8 * n) (d := 8 * u)
    (by omega) (mul_dvd_mul_left 8 hudvd) hbc
  have hac4 : a.Coprime (4 * n) := hac.of_dvd_right ⟨2, by ring⟩
  have haodd : Odd a := Nat.coprime_two_right.mp (hac.of_dvd_right ⟨4 * n, by ring⟩)
  have hab4 : Nat.ModEq (4 * u) a b := hab.of_dvd ⟨2, by ring⟩
  have hju : rightJacobi u a = rightJacobi u b := by
    rw [rightJacobi_mod u a, rightJacobi_mod u b]
    exact congrArg (rightJacobi u) hab4
  have hjua : jacobiSym (u : ℤ) a = -1 := by
    simpa only [rightJacobi, haodd, hbo, ite_eq_left, hbj] using hju
  have htdvd : t ∣ n := ⟨t * u, by nlinarith [hnu]⟩
  have hta : t.Coprime a := (hac.of_dvd_right (htdvd.trans (dvd_mul_left n 8))).symm
  have htagcd : Int.gcd (t : ℤ) (a : ℤ) = 1 := by
    simpa only [Int.gcd_natCast_natCast] using hta
  refine ⟨a, hac4, ?_⟩
  simp only [rightJacobi, haodd, ite_eq_left]
  rw [← hnu, Nat.cast_mul, Nat.cast_pow, jacobiSym.mul_left,
    jacobiSym.sq_one' htagcd, hjua, one_mul]

end Ostmann.QuadraticCenter

end OAI
