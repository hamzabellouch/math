import OAI.NumberTheory.PrimeGaps.MultiplicativeSieve

namespace OAI

namespace Ostmann.HybridSieve
open LargePrimeGaps
open scoped ComplexConjugate Classical

noncomputable def shiftedCharacterSum (A : ℕ) {q N : ℕ}
    (a : Fin N → ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n : Fin N, a n * χ ((A + (n : ℕ) : ℕ) : ZMod q)

noncomputable def shiftedFourierSum (A : ℕ) {q N : ℕ} [NeZero q]
    (a : Fin N → ℂ) (u : ZMod q) : ℂ :=
  ∑ n : Fin N, a n * ZMod.stdAddChar (((A + (n : ℕ) : ℕ) : ZMod q) * u)

variable (A : ℕ)

theorem shifted_primitive_gauss_expansion {q N : ℕ} [NeZero q]
    (a : Fin N→ℂ) {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    gaussSum (χ⁻¹) ZMod.stdAddChar*shiftedCharacterSum A a χ=
      ∑ u:(ZMod q)ˣ,shiftedFourierSum A (q:=q) a (u:ZMod q)*(χ⁻¹) u := by
  have hg (n:Fin N) := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar
    (primitive_inverse hχ) (((A+(n:ℕ):ℕ):ZMod q))
  simp only [inv_inv] at hg
  unfold shiftedCharacterSum
  rw [Finset.mul_sum]
  calc
    _ = ∑ n:Fin N,a n*gaussSum (χ⁻¹) (ZMod.stdAddChar.mulShift (((A+(n:ℕ):ℕ):ZMod q))) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [hg]
      ring
    _ = ∑ x:ZMod q,(χ⁻¹) x*shiftedFourierSum A a x := by
      simp only [gaussSum,AddChar.mulShift_apply,Finset.mul_sum,shiftedFourierSum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = ∑ u:(ZMod q)ˣ,(χ⁻¹) u*shiftedFourierSum A (q:=q) a (u:ZMod q) := multiply_sum_units _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u _
      rw [mul_comm]

theorem shifted_primitive_energy_le {q N : ℕ} [NeZero q] (a : Fin N→ℂ) :
    (q:ℝ)/(q.totient:ℝ)*
        (∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖shiftedCharacterSum A a χ‖^2)≤
      ∑ u:(ZMod q)ˣ,‖shiftedFourierSum A (q:=q) a (u:ZMod q)‖^2 := by
  classical
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hs : (q:ℝ)*
        (∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖shiftedCharacterSum A a χ‖^2)≤
      (q.totient:ℝ)*(∑ u:(ZMod q)ˣ,‖shiftedFourierSum A (q:=q) a (u:ZMod q)‖^2) := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ u:(ZMod q)ˣ,shiftedFourierSum A (q:=q) a (u:ZMod q)*(χ⁻¹) u‖^2 := by
        apply Finset.sum_congr rfl
        intro χ hχ
        have hp := (Finset.mem_filter.mp hχ).2
        have h := congrArg (fun z:ℂ => ‖z‖^2) (shifted_primitive_gauss_expansion A a hp)
        rwa [norm_mul,mul_pow,primitive_gauss_norm_sq (primitive_inverse hp)] at h
      _ ≤ ∑ χ:DirichletCharacter ℂ q,‖∑ u:(ZMod q)ˣ,shiftedFourierSum A (q:=q) a (u:ZMod q)*(χ⁻¹) u‖^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
      _ = ∑ χ:DirichletCharacter ℂ q,‖∑ u:(ZMod q)ˣ,shiftedFourierSum A (q:=q) a (u:ZMod q)*χ u‖^2 := by
        exact Fintype.sum_bijective (fun χ : DirichletCharacter ℂ q => χ⁻¹)
          inv_involutive.bijective _ _ (fun _ => rfl)
      _ ≤ _ := character_transform_bound _
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hφ).mpr (by simpa only [mul_comm] using hs)

theorem shiftedFourierSum_factor {q N : ℕ} [NeZero q]
    (a : Fin N → ℂ) (u : ZMod q) :
    shiftedFourierSum A a u =
      ZMod.stdAddChar ((A : ZMod q) * u) * modularFourierSum a u := by
  simp only [shiftedFourierSum, modularFourierSum, Nat.cast_add, add_mul,
    AddChar.map_add_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem norm_shiftedFourierSum {q N : ℕ} [NeZero q]
    (a : Fin N → ℂ) (u : ZMod q) :
    ‖shiftedFourierSum A a u‖ = ‖modularFourierSum a u‖ := by
  rw [shiftedFourierSum_factor, norm_mul, ZMod.stdAddChar_apply]
  simp

end Ostmann.HybridSieve

end OAI
