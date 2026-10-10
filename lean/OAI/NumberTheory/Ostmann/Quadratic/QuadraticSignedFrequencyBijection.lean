import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSignedFrequency

namespace OAI

/-! # Unique signed squarefree coordinates, with exact finite reindexing -/

namespace Ostmann

open scoped Classical BigOperators

private theorem signed_frequency_abs (a : ℤ) (ha : a ∈ ({1, -1, 2, -2} : Finset ℤ)) :
    a.natAbs = 1 ∨ a.natAbs = 2 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> norm_num

private theorem signed_odd_kernel_squarefree {a : ℤ} {b : ℕ}
    (ha : a ∈ ({1, -1, 2, -2} : Finset ℤ)) (hb : Odd b) (hs : Squarefree b) :
    Squarefree (a.natAbs * b) := by
  rcases signed_frequency_abs a ha with hh | hh
  · simpa only [hh, one_mul] using hs
  · rw [hh]
    exact (Nat.squarefree_mul (Nat.coprime_two_left.mpr hb)).mpr
      ⟨Nat.prime_two.squarefree, hs⟩

theorem quadratic_signed_coordinates_injective {a d : ℤ} {c e b f : ℕ}
    (ha : a ∈ ({1, -1, 2, -2} : Finset ℤ))
    (hd : d ∈ ({1, -1, 2, -2} : Finset ℤ))
    (hc : 0 < c) (he : 0 < e) (hb : Odd b) (hf : Odd f)
    (hsb : Squarefree b) (hsf : Squarefree f)
    (hh : a * (c : ℤ) ^ 2 * b = d * (e : ℤ) ^ 2 * f) :
    a = d ∧ c = e ∧ b = f := by
  have habs := congrArg Int.natAbs hh
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at habs
  have hfactor : c ^ 2 * (a.natAbs * b) = e ^ 2 * (d.natAbs * f) := by
    calc
      _ = a.natAbs * c ^ 2 * b := by ring
      _ = d.natAbs * e ^ 2 * f := habs
      _ = _ := by ring
  obtain ⟨hce, hkernel⟩ := quadratic_squarefree_factor_unique hc.ne' he.ne'
    (signed_odd_kernel_squarefree ha hb hsb) (signed_odd_kernel_squarefree hd hf hsf) hfactor
  have hbf : b = f := by
    obtain ⟨r, hr⟩ := hb
    obtain ⟨s, hs⟩ := hf
    rcases signed_frequency_abs a ha with ha' | ha' <;>
      rcases signed_frequency_abs d hd with hd' | hd' <;>
      simp only [ha', hd', one_mul] at hkernel <;> omega
  refine ⟨?_, hce, hbf⟩
  rw [hce, hbf] at hh
  have heZ : (e : ℤ) ≠ 0 := by exact_mod_cast he.ne'
  have hfZ : (f : ℤ) ≠ 0 := by exact_mod_cast hsf.ne_zero
  exact mul_right_cancel₀ (pow_ne_zero 2 heZ) (mul_right_cancel₀ hfZ hh)

theorem quadratic_frequency_coordinates_injOn (H : ℕ) :
    Set.InjOn (fun z : (ℤ × ℕ) × ℕ => z.1.1 * (z.1.2 : ℤ) ^ 2 * (z.2 : ℤ))
      (quadraticFrequencyTriples H) := by
  intro z hz w hw heq
  obtain ⟨hz, _⟩ := Finset.mem_filter.mp hz
  obtain ⟨hw, _⟩ := Finset.mem_filter.mp hw
  obtain ⟨hzac, hzb⟩ := Finset.mem_product.mp hz
  obtain ⟨hwac, hwb⟩ := Finset.mem_product.mp hw
  obtain ⟨hza, hzc⟩ := Finset.mem_product.mp hzac
  obtain ⟨hwa, hwc⟩ := Finset.mem_product.mp hwac
  obtain ⟨_, hzbo, hzbs⟩ := Finset.mem_filter.mp hzb
  obtain ⟨_, hwbo, hwbs⟩ := Finset.mem_filter.mp hwb
  obtain ⟨ha, hc, hb⟩ := quadratic_signed_coordinates_injective hza hwa
    (Finset.mem_Icc.mp hzc).1 (Finset.mem_Icc.mp hwc).1 hzbo hwbo hzbs hwbs heq
  exact Prod.ext (Prod.ext ha hc) hb

theorem quadratic_frequency_sum_exact {R : Type*} [AddCommMonoid R] (H : ℕ) (F : ℤ → R) :
    (∑ h ∈ quadraticNonzeroFrequencies H, F h) =
      ∑ z ∈ quadraticFrequencyTriples H, F (z.1.1 * (z.1.2 : ℤ) ^ 2 * (z.2 : ℤ)) := by
  rw [← quadratic_frequency_image]
  exact Finset.sum_image (quadratic_frequency_coordinates_injOn H)

end Ostmann

end OAI
