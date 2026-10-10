import OAI.Combinatorics.Sidorenko.LocalMoments

namespace OAI


section

namespace SidorenkoCounterexample
open scoped BigOperators
open Module
section Gauss
variable {K V : Type*} [Field K] [Fintype K]
  [AddCommGroup V] [Module K V] [Fintype V]

 theorem char_conj (ψ : AddChar K ℂ) (a : K) :
    star (ψ a) = (ψ a)⁻¹ := (Complex.inv_eq_conj (ψ.norm_apply a)).symm

omit [Module K V] in
 theorem character_differencing (ψ : AddChar K ℂ) (f : V → K) :
    ‖∑ x, ψ (f x)‖ ^ 2 = ‖∑ u, ∑ z, ψ (f (z+u) - f z)‖ := by
  classical
  have h : (∑ u, ∑ z, ψ (f (z+u) - f z)) =
      (∑ x, ψ (f x)) * star (∑ x, ψ (f x)) := by
    simp only [AddChar.map_sub_eq_div, div_eq_mul_inv, ← char_conj]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    have ht (z : V) : (∑ u, ψ (f (z+u))) = ∑ x, ψ (f x) :=
      Fintype.sum_equiv (Equiv.addLeft z) _ _ (fun _ => rfl)
    simp only [ht, ← Finset.mul_sum, star_sum]
  rw [h, norm_mul, norm_star, pow_two]

omit [Fintype K] in
 theorem linear_character_sum_zero (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (f : V →ₗ[K] K) (hf : f ≠ 0) : ∑ x, ψ (f x) = 0 := by
  classical
  have hsurj : Function.Surjective f := by
    have hex : ∃ x, f x ≠ 0 := by
      by_contra! h
      exact hf (LinearMap.ext h)
    obtain ⟨x, hx⟩ := hex
    intro a
    refine ⟨(a / f x) • x, ?_⟩
    simp [hx]
  change ∑ x, (ψ.compAddMonoidHom f.toAddMonoidHom) x = 0
  apply AddChar.sum_eq_zero_iff_ne_zero.mpr
  intro heq
  apply hψ
  ext a
  obtain ⟨x, rfl⟩ := hsurj a
  exact congrArg (fun χ : AddChar V ℂ => χ x) heq

omit [Fintype K] [Fintype V] in
/-- Exact one-step differencing for a symmetric quadratic polynomial. -/
 theorem quadratic_difference (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (l : V →ₗ[K] K) (c : K) (z u : V) :
    (B (z+u) (z+u) + l (z+u) + c) - (B z z + l z + c) =
      B u u + l u + (2 : K) * B u z := by
  simp only [map_add, LinearMap.add_apply, hB.eq z u]
  ring

/-- The raw quadratic Gauss bound, with arbitrary linear and constant terms.
Its right side is exactly |V| times the size of the radical. -/
 theorem quadratic_gauss_bound (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (hodd : (2 : K) ≠ 0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (l : V →ₗ[K] K) (c : K) :
    ‖∑ x, ψ (B x x + l x + c)‖ ^ 2 ≤
      (Fintype.card V : ℝ) * Nat.card B.ker := by
  classical
  rw [character_differencing]
  simp only [quadratic_difference B hB, AddChar.map_add_eq_mul]
  have hi (u : V) : (∑ z, ψ ((2:K) * B u z)) =
      if u ∈ B.ker then (Fintype.card V : ℂ) else 0 := by
    by_cases hu : u ∈ B.ker
    · have hz : B u = 0 := LinearMap.mem_ker.mp hu
      simp [hu, hz]
    · rw [ite_eq_right hu]
      exact linear_character_sum_zero ψ hψ ((2:K) • B u) (by
        intro heq
        apply hu
        apply LinearMap.mem_ker.mpr
        exact (smul_eq_zero.mp heq).resolve_left hodd)
  simp only [← Finset.mul_sum, hi]
  calc
    ‖∑ u, ψ (B u u) * ψ (l u) *
        (if u ∈ B.ker then (Fintype.card V : ℂ) else 0)‖ ≤
        ∑ u, ‖ψ (B u u) * ψ (l u) *
        (if u ∈ B.ker then (Fintype.card V : ℂ) else 0)‖ := norm_sum_le _ _
    _ = (Fintype.card V : ℝ) * Nat.card B.ker := by
      simp only [norm_mul, AddChar.norm_apply, one_mul]
      simp only [apply_ite norm, Complex.norm_natCast, norm_zero]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const, nsmul_eq_mul]
      rw [mul_comm]
      congr 1
      rw [Nat.card_eq_fintype_card]
      simp [Fintype.card_subtype]



 theorem normalized_quadratic_gauss_bound (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (hodd : (2 : K) ≠ 0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (l : V →ₗ[K] K) (c : K) :
    ‖(Fintype.card V : ℂ)⁻¹ * ∑ x, ψ (B x x + l x + c)‖ ^ 2 ≤
      1 / (Fintype.card K : ℝ) ^ finrank K B.range := by
  classical
  have h := quadratic_gauss_bound ψ hψ hodd B hB l c
  have hv : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hk : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hc : (Fintype.card V : ℝ) =
      (Fintype.card K : ℝ) ^ finrank K B.range * Nat.card B.ker := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K) (V := V),
      Module.card_eq_pow_finrank (K := K) (V := B.ker)]
    push_cast
    rw [← pow_add, B.finrank_range_add_finrank_ker]
  simp only [norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
  calc
    (Fintype.card V : ℝ)⁻¹ ^ 2 * ‖∑ x, ψ (B x x + l x + c)‖ ^ 2 ≤
      (Fintype.card V : ℝ)⁻¹ ^ 2 *
        ((Fintype.card V : ℝ) * Nat.card B.ker) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = 1 / (Fintype.card K : ℝ) ^ finrank K B.range := by
      have hp := pow_pos hk (finrank K B.range)
      field_simp
      nlinarith [hc]

end Gauss
section Fourier
variable {K ι : Type*} [Field K] [Fintype K] [Fintype ι] [DecidableEq ι] [DecidableEq K]

noncomputable def coordinatePairing (v : ι → K) : (ι → K) →ₗ[K] K where
  toFun t := t ⬝ᵥ v
  map_add' := fun _ _ => add_dotProduct _ _ _
  map_smul' := fun _ _ => smul_dotProduct _ _ _

 theorem coordinate_character_sum (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (v : ι → K) :
    ∑ t : ι → K, ψ (t ⬝ᵥ v) = if v = 0 then (Fintype.card (ι → K) : ℂ) else 0 := by
  classical
  split_ifs with hv
  · simp [hv]
  · apply linear_character_sum_zero ψ hψ (coordinatePairing v)
    intro h
    apply hv
    apply dotProduct_eq_zero_iff.mp
    intro t
    simpa [coordinatePairing, dotProduct_comm] using
      congrArg (fun f : (ι → K) →ₗ[K] K => f t) h

noncomputable def finiteFourier (ψ : AddChar K ℂ) (μ : (ι → K) → ℝ)
    (t : ι → K) : ℂ := ∑ x, (μ x : ℂ) * ψ (t ⬝ᵥ x)

 theorem finite_parseval (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (μ : (ι → K) → ℝ) :
    ∑ t, ‖finiteFourier ψ μ t‖ ^ 2 =
      (Fintype.card (ι → K) : ℝ) * ∑ x, (μ x)^2 := by
  classical
  apply Complex.ofReal_injective
  have hn (z : ℂ) : ((‖z‖^2 : ℝ) : ℂ) = z * star z := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]; rfl
  have hs (x : ℝ) : star (x : ℂ) = x := by simp
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, hn, finiteFourier,
    star_sum, star_mul, hs,
    char_conj, Finset.sum_mul, Finset.mul_sum]
  have he (x y : ι → K) :
      (∑ t, (μ x : ℂ) * ψ (t ⬝ᵥ x) * ((ψ (t ⬝ᵥ y))⁻¹ * μ y)) =
      (μ x : ℂ) * μ y * (if x = y then (Fintype.card (ι → K) : ℂ) else 0) := by
    calc
      _ = (μ x : ℂ) * μ y * ∑ t, ψ (t ⬝ᵥ (x-y)) := by
        simp only [dotProduct_sub, AddChar.map_sub_eq_div, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        ring
      _ = _ := by rw [coordinate_character_sum ψ hψ]; simp only [sub_eq_zero]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, x]; rw [Finset.sum_comm]
  simp only [he]
  simp [Finset.sum_ite_eq', pow_two, mul_comm, mul_assoc]

 theorem finiteFourier_sub_uniform (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (μ : (ι → K) → ℝ) (hμ : ∑ x, μ x = 1) (t : ι → K) :
    finiteFourier ψ (fun x => μ x - (Fintype.card (ι → K) : ℝ)⁻¹) t =
      if t = 0 then 0 else finiteFourier ψ μ t := by
  classical
  have hc : (Fintype.card (ι → K) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [finiteFourier, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Complex.ofReal_inv, Complex.ofReal_natCast]
  have hs : ∑ x : ι → K, ψ (t ⬝ᵥ x) =
      if t = 0 then (Fintype.card (ι → K) : ℂ) else 0 := by
    simpa only [dotProduct_comm] using coordinate_character_sum ψ hψ t
  rw [hs]
  split_ifs with ht
  · simp [ht, ← Complex.ofReal_sum, hμ]
  · simp



 theorem finite_fourier_l1_bound (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (μ : (ι → K) → ℝ) (hμ : ∑ x, μ x = 1) :
    (∑ x, |μ x - (Fintype.card (ι → K) : ℝ)⁻¹|)^2 ≤
      ∑ t, if t = 0 then 0 else ‖finiteFourier ψ μ t‖^2 := by
  classical
  have hp := finite_parseval ψ hψ (fun x => μ x - (Fintype.card (ι → K) : ℝ)⁻¹)
  simp only [finiteFourier_sub_uniform ψ hψ μ hμ] at hp
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : ι → K => (1:ℝ))
    (fun x => |μ x - (Fintype.card (ι → K) : ℝ)⁻¹|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, sq_abs] at hs
  rw [← hp] at hs
  simpa only [apply_ite norm, norm_zero, ite_pow, zero_pow (by decide : 2 ≠ 0)] using hs

 theorem finite_fourier_l1_of_uniform_bound (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (μ : (ι → K) → ℝ) (hμ : ∑ x, μ x = 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hf : ∀ t ≠ 0, ‖finiteFourier ψ μ t‖ ^ 2 ≤ ε) :
    (∑ x, |μ x - (Fintype.card (ι → K) : ℝ)⁻¹|)^2 ≤
      (Fintype.card (ι → K) : ℝ) * ε := by
  classical
  refine (finite_fourier_l1_bound ψ hψ μ hμ).trans ?_
  calc
    _ ≤ ∑ _t : ι → K, ε := by
      apply Finset.sum_le_sum
      intro t _
      split_ifs with ht
      · exact hε
      · exact hf t ht
    _ = _ := by simp


variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

noncomputable def uniformLaw (f : Ω → ι → K) (x : ι → K) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ * ∑ v, if f v = x then 1 else 0

omit [Field K] in
 theorem uniformLaw_sum (f : Ω → ι → K) : ∑ x, uniformLaw f x = 1 := by
  classical
  simp only [uniformLaw, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp

omit [Field K] [Nonempty Ω] in
 theorem uniformLaw_average (f : Ω → ι → K) (g : (ι → K) → ℝ) :
    ∑ x, uniformLaw f x * g x = (Fintype.card Ω : ℝ)⁻¹ * ∑ v, g (f v) := by
  classical
  simp only [uniformLaw, mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  simp

omit [Nonempty Ω] in
 theorem finiteFourier_uniformLaw (ψ : AddChar K ℂ) (f : Ω → ι → K) (t : ι → K) :
    finiteFourier ψ (uniformLaw f) t =
      (Fintype.card Ω : ℂ)⁻¹ * ∑ v, ψ (t ⬝ᵥ f v) := by
  classical
  simp only [finiteFourier, uniformLaw, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_natCast, Complex.ofReal_sum, mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  simp only [apply_ite, Complex.ofReal_one, Complex.ofReal_zero, ite_mul, one_mul, zero_mul]
  simp

variable {V : Type*} [AddCommGroup V] [Module K V] [Fintype V]

noncomputable def quadraticMap (B : ι → LinearMap.BilinForm K V)
    (l : ι → V →ₗ[K] K) (c : ι → K) (v : V) (i : ι) : K :=
  B i v v + l i v + c i

omit [Fintype K] [DecidableEq ι] [DecidableEq K] [Fintype V] in
 theorem quadraticMap_frequency (B : ι → LinearMap.BilinForm K V)
    (l : ι → V →ₗ[K] K) (c t : ι → K) (v : V) :
    t ⬝ᵥ quadraticMap B l c v =
      (∑ i, t i • B i) v v + (∑ i, t i • l i) v + ∑ i, t i * c i := by
  simp [dotProduct, quadraticMap, Finset.sum_add_distrib, mul_add]

 theorem quadraticMap_fourier_bound (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (hodd : (2:K) ≠ 0) (B : ι → LinearMap.BilinForm K V)
    (hB : ∀ i, (B i).IsSymm) (l : ι → V →ₗ[K] K) (c t : ι → K) :
    ‖finiteFourier ψ (uniformLaw (quadraticMap B l c)) t‖^2 ≤
      1 / (Fintype.card K : ℝ) ^ finrank K (∑ i, t i • B i).range := by
  rw [finiteFourier_uniformLaw]
  simp only [quadraticMap_frequency]
  apply normalized_quadratic_gauss_bound ψ hψ hodd
  constructor
  intro x y
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [(hB i).eq]




 theorem quadraticMap_joint_l1_bound (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (hodd : (2:K) ≠ 0) (B : ι → LinearMap.BilinForm K V)
    (hB : ∀ i, (B i).IsSymm) (l : ι → V →ₗ[K] K) (c : ι → K)
    (hrank : ∀ t : ι → K, t ≠ 0 →
      Fintype.card ι + 1 ≤ finrank K (∑ i, t i • B i).range) :
    (∑ x, |uniformLaw (quadraticMap B l c) x -
      (Fintype.card (ι → K) : ℝ)⁻¹|)^2 ≤ 1 / (Fintype.card K : ℝ) := by
  have hq : (1:ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
  have hf (t : ι → K) (ht : t ≠ 0) :
      ‖finiteFourier ψ (uniformLaw (quadraticMap B l c)) t‖^2 ≤
        1 / (Fintype.card K : ℝ)^(Fintype.card ι+1) := by
    refine (quadraticMap_fourier_bound ψ hψ hodd B hB l c t).trans ?_
    exact one_div_le_one_div_of_le (pow_pos (by linarith) _)
      (pow_le_pow_right₀ hq (hrank t ht))
  have hh := finite_fourier_l1_of_uniform_bound ψ hψ _
    (uniformLaw_sum (quadraticMap B l c)) _ (by positivity) hf
  convert hh using 1
  rw [Fintype.card_fun, Nat.cast_pow, pow_succ]
  have hq0 : (Fintype.card K : ℝ) ≠ 0 := by linarith
  field_simp

end Fourier
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open scoped BigOperators
open Module
section SignMoments
variable {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Fintype ι] [DecidableEq ι]

noncomputable def characterProduct (x : ι → K) : ℝ := ∏ i, (quadraticChar K (x i) : ℝ)

omit [DecidableEq ι] in
 theorem characterProduct_abs_le (x : ι → K) : |characterProduct x| ≤ 1 := by
  rw [characterProduct, Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun i _ => by
    have h := quadraticChar_dichotomy (F := K) (a := x i)
    by_cases hx : x i = 0
    · simp [hx]
    · rcases h hx with h | h <;> simp [h])

 theorem characterProduct_sum [Nonempty ι] (hodd : ringChar K ≠ 2) :
    ∑ x : ι → K, characterProduct x = 0 := by
  rw [show (∑ x : ι → K, characterProduct x) =
    ∏ _i : ι, ∑ a : K, (quadraticChar K a : ℝ) from (Fintype.prod_sum (fun (_i : ι) (a : K) => (quadraticChar K a : ℝ))).symm]
  have hz : ∑ a : K, (quadraticChar K a : ℝ) = 0 := by
    exact_mod_cast quadraticChar_sum_zero hodd
  rw [hz]
  simp

omit [Field K] [DecidableEq K] in
 theorem bounded_test_l1 (μ ν : (ι → K) → ℝ) (g : (ι → K) → ℝ)
    (hg : ∀ x, |g x| ≤ 1) :
    |(∑ x, μ x * g x) - ∑ x, ν x * g x| ≤ ∑ x, |μ x-ν x| := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro x _
  rw [← sub_mul, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hg x)

variable {V : Type*} [AddCommGroup V] [Module K V] [Fintype V]



 theorem quadraticMap_character_moment [Nonempty ι]
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 0) (hodd : (2:K) ≠ 0)
    (B : ι → LinearMap.BilinForm K V) (hB : ∀ i, (B i).IsSymm)
    (l : ι → V →ₗ[K] K) (c : ι → K)
    (hrank : ∀ t : ι → K, t ≠ 0 →
      Fintype.card ι + 1 ≤ finrank K (∑ i, t i • B i).range) :
    ((Fintype.card V : ℝ)⁻¹ * ∑ v, characterProduct (quadraticMap B l c v))^2 ≤
      1 / (Fintype.card K : ℝ) := by
  have hc : ringChar K ≠ 2 := by
    intro h
    apply hodd
    simpa using (ringChar.spec K 2).mpr (by rw [h])
  have hz : ∑ x : ι → K, (Fintype.card (ι → K) : ℝ)⁻¹ * characterProduct x = 0 := by
    rw [← Finset.mul_sum, characterProduct_sum hc, mul_zero]
  have hb := bounded_test_l1 (uniformLaw (quadraticMap B l c))
    (fun _ => (Fintype.card (ι → K) : ℝ)⁻¹) characterProduct characterProduct_abs_le
  rw [uniformLaw_average, hz, sub_zero] at hb
  have hf := quadraticMap_joint_l1_bound ψ hψ hodd B hB l c hrank
  have hh := ((sq_le_sq₀ (abs_nonneg _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).mpr hb).trans hf
  simpa only [sq_abs] using hh

end SignMoments
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix BigOperators
section Mom
variable {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Fintype ι] [DecidableEq ι] [Nonempty ι] {N : ℕ}

omit [Fintype K] [DecidableEq K] in
theorem matrix_form_rank (M : Matrix (Fin N) (Fin N) K) :
    finrank K M.toBilin'.range=M.rank := by
  rw [←matrix_radical_quotient_rank]
  exact M.toBilin'.quotKerEquivRange.finrank_eq.symm

omit [Fintype K] [DecidableEq K] in
theorem schur_polynomial (M : SymMatrix K N) (z w : Fin N → K) (a : K) :
    a-(z-w) ⬝ᵥ M.val⁻¹.mulVec (z-w) =
      (-M.val⁻¹.toBilin') z z + (2 • (M.val⁻¹.toBilin' w)) z +
        (a-M.val⁻¹.toBilin' w w) := by
  have hs := Matrix.isSymm_toBilin'_iff_isSymm.mpr M.property.inv
  have he : (z-w) ⬝ᵥ M.val⁻¹.mulVec (z-w) = M.val⁻¹.toBilin' (z-w) (z-w) := by
    rw [matrix_bilin_eval,M.property.inv,dotProduct_comm]
  rw [he]
  simp only [map_sub,LinearMap.sub_apply,LinearMap.neg_apply,LinearMap.smul_apply]
  rw [hs.eq z w]
  ring

omit [Fintype K] [DecidableEq K] [DecidableEq ι] [Nonempty ι] in
theorem inverse_form_span_rank (M : ι → SymMatrix K N) (t : ι → K) :
    finrank K (∑ i, t i • (-((M i).val⁻¹.toBilin'))).range =
      (∑ i, t i • (M i).val⁻¹).rank := by
  have he : (∑ i, t i • (-((M i).val⁻¹.toBilin'))) =
      (-(∑ i, t i • (M i).val⁻¹)).toBilin' := by
    simp only [map_neg,map_sum,map_smul]
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp
  rw [he,matrix_form_rank,matrix_rank_neg]

theorem schur_sign_moment (hodd : ringChar K≠2)
    (M : ι → SymMatrix K N) (hM : ∀ i, (M i).val.det≠0)
    (w : ι → Fin N → K) (a : ι → K)
    (hrank : ∀ t : ι → K, t≠0 →
      Fintype.card ι+1≤(∑ i, t i • (M i).val⁻¹).rank) :
    (uniformMean (fun z : Fin N → K =>
      ∏ i, (quadraticChar K (symmetricBorder (M i) (z-w i) (a i)).val.det : ℝ)))^2 ≤
      1/(Fintype.card K : ℝ) := by
  obtain ⟨ψ,hψ⟩ := (AddChar.exists_apply_ne_zero (a := (1 : K))).mpr one_ne_zero
  have hp : ψ≠0 := by intro h; apply hψ; simp [h]
  have htwo : (2 : K)≠0 := by
    exact Ring.two_ne_zero hodd
  let B : ι → LinearMap.BilinForm K (Fin N → K) := fun i => -(M i).val⁻¹.toBilin'
  let l : ι → (Fin N → K) →ₗ[K] K := fun i => 2 • ((M i).val⁻¹.toBilin' (w i))
  let c : ι → K := fun i => a i-(M i).val⁻¹.toBilin' (w i) (w i)
  have hB : ∀ i, (B i).IsSymm := fun i =>
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr (M i).property.inv).neg
  have hb := quadraticMap_character_moment ψ hp htwo B hB l c (fun t ht => by
    rw [inverse_form_span_rank M t]; exact hrank t ht)
  have hb' : (uniformMean (fun z => characterProduct (quadraticMap B l c z)))^2 ≤
      1/(Fintype.card K : ℝ) := by
    simpa only [uniformMean,div_eq_mul_inv,mul_comm] using hb
  have he (z : Fin N → K) : (∏ i, (quadraticChar K
      (symmetricBorder (M i) (z-w i) (a i)).val.det : ℝ)) =
      characterProduct (fun i => (M i).val.det) * characterProduct (quadraticMap B l c z) := by
    unfold characterProduct
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [symmetricBorder_det _ _ _ (hM i),map_mul,Int.cast_mul,schur_polynomial]
    rfl
  simp_rw [he]
  rw [uniformMean_mul,mul_pow]
  have hc := characterProduct_abs_le (fun i => (M i).val.det)
  have hc2 : characterProduct (fun i => (M i).val.det)^2≤1 := by
    simpa only [sq_abs,one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr hc
  exact (mul_le_of_le_one_left (sq_nonneg _) hc2).trans hb'
end Mom
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module Classical
open scoped Matrix BigOperators
section Span
variable {K I : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] {N : ℕ}

omit [Fintype K] [DecidableEq K] [DecidableEq I] in
theorem matrix_combination_form_rank (t : I → K) (Q : I → SymMatrix K N) :
    finrank K (weightedCombination t (fun i => matrixFormEquiv N (Q i))).val.range =
      (∑ i, t i • (Q i).val).rank := by
  have he : (weightedCombination t (fun i => matrixFormEquiv N (Q i))).val =
      (∑ i, t i • (Q i).val).toBilin' := by
    simp only [weightedCombination, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply]
    change (symmetricFormSubmodule (K := K) (V := Fin N → K)).subtype
      (∑ i, t i • matrixFormEquiv N (Q i)) = _
    calc
      _ = ∑ i, (symmetricFormSubmodule (K := K) (V := Fin N → K)).subtype
          (t i • matrixFormEquiv N (Q i)) := map_sum _ _ _
      _ = _ := by
        simp only [map_sum,map_smul]
        apply Finset.sum_congr rfl
        intro i _
        exact map_smul (symmetricFormSubmodule (K := K) (V := Fin N → K)).subtype (t i) (matrixFormEquiv N (Q i))
  rw [he,matrix_form_rank]

theorem matrix_low_rank_span_bound (s : ℕ) (hs : s ≤ N) :
    uniformMean (fun Q : I → SymMatrix K N => if ∃ t : I → K, t≠0 ∧
      (∑ i, t i • (Q i).val).rank ≤ s then 1 else 0)  ≤ 
      (Fintype.card K : ℝ)^(Fintype.card I) *
        (2^(N-s)/(Fintype.card K : ℝ)^((N-s+1).choose 2)) := by
  classical
  let e : (I → SymMatrix K N) ≃ (I → SymForm K (Fin N → K)) :=
    Equiv.piCongrRight (fun _ => matrixFormEquiv N)
  have hp (Q : I → SymMatrix K N) : (∃ t : I → K, t≠0 ∧
      (∑ i, t i • (Q i).val).rank ≤ s) ↔
      ∃ t : I → K, t≠0 ∧ finrank K (weightedCombination t (e Q)).val.range ≤ s := by
    apply exists_congr
    intro t
    rw [show finrank K (weightedCombination t (e Q)).val.range =
      (∑ i, t i • (Q i).val).rank from matrix_combination_form_rank t Q]
  simp_rw [hp]
  rw [←Function.comp_def (fun Q : I → SymForm K (Fin N → K) => if ∃ t : I → K, t≠0 ∧
    finrank K (weightedCombination t Q).val.range ≤ s then (1 : ℝ) else 0) e,
    uniformMean_equiv e,uniformMean_indicator]
  simpa only [Nat.card_eq_fintype_card,Module.finrank_fin_fun] using
    (symmetric_low_rank_span_bound (K := K) (V := Fin N → K) (ι := I) s (by simpa using hs))

noncomputable def goodMinors (M : I → SymMatrix K N) : Prop :=
  (∀ i, (M i).val.det≠0) ∧ ∀ t : I → K, t≠0 →
    Fintype.card I+1 ≤ (∑ i, t i • (M i).val⁻¹).rank

noncomputable def minorBadBound (N s : ℕ) (q : ℝ) : ℝ :=
  (s : ℝ)*N/q + q^s*(2^(N-s)/q^((N-s+1).choose 2))

theorem badMinors_bound (hN : Fintype.card I ≤ N) :
    uniformMean (fun M : I → SymMatrix K N => if goodMinors M then 0 else 1)  ≤ 
      minorBadBound N (Fintype.card I) (Fintype.card K) := by
  classical
  let P (Q : I → SymMatrix K N) : Prop := ∃ t : I → K, t≠0 ∧
    (∑ i, t i • (Q i).val).rank ≤ Fintype.card I
  let e : (I → SymMatrix K N) ≃ (I → SymMatrix K N) :=
    Equiv.piCongrRight (fun _ => symmetricInverseEquiv N)
  have he (M : I → SymMatrix K N) (hM : ∀ i, (M i).val.det≠0) (i : I) :
      (e M i).val=(M i).val⁻¹ := by simp [e,symmetricInverseEquiv,symmetricInverse,hM i]
  have hp (M : I → SymMatrix K N) :
      (if goodMinors M then (0 : ℝ) else 1)  ≤ 
        (∑ i, if (M i).val.det=0 then 1 else 0)+(if P (e M) then 1 else 0) := by
    by_cases hg : goodMinors M
    · simp only [ite_eq_left hg]; positivity
    · simp only [ite_eq_right hg]
      by_cases hM : ∀ i, (M i).val.det≠0
      · have hr : P (e M) := by
          simp only [goodMinors,not_and,not_forall] at hg
          obtain ⟨t,ht⟩ := hg hM
          obtain ⟨htt1,htt2⟩ := ht
          refine ⟨t,htt1,?_⟩
          simp only [he M hM]
          omega
        simp only [ite_eq_left hr]
        have : (0 : ℝ) ≤ ∑ i, if (M i).val.det=0 then (1 : ℝ) else 0 := by positivity
        linarith
      · push Not at hM
        obtain ⟨i,hi⟩ := hM
        have hb : (1 : ℝ) ≤ ∑ j, if (M j).val.det=0 then (1 : ℝ) else 0 := by
          simpa only [hi,ite_true] using Finset.single_le_sum
            (fun j (_ : j ∈ Finset.univ) => by positivity : ∀ j ∈ Finset.univ, 0 ≤ (if (M j).val.det=0 then (1 : ℝ) else 0))
            (Finset.mem_univ i)
        exact hb.trans (le_add_of_nonneg_right (by positivity))
  apply (uniformMean_mono hp).trans
  rw [uniformMean_add,uniformMean_sum]
  have hs (i : I) : uniformMean (fun M : I → SymMatrix K N => if (M i).val.det=0 then (1 : ℝ) else 0)  ≤ 
      (N : ℝ)/(Fintype.card K : ℝ) := by
    rw [uniformMean_coordinate i (fun A : SymMatrix K N => if A.val.det = 0 then (1 : ℝ) else 0)]
    exact symmetricSingularProb_bound (K := K) N
  have hb : uniformMean (fun M => if P (e M) then (1 : ℝ) else 0)  ≤ 
      (Fintype.card K : ℝ)^(Fintype.card I) *
        (2^(N-Fintype.card I)/(Fintype.card K : ℝ)^((N-Fintype.card I+1).choose 2)) := by
    rw [←Function.comp_def (fun M => if P M then (1 : ℝ) else 0) e,uniformMean_equiv]
    exact matrix_low_rank_span_bound (Fintype.card I) hN
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hs i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  unfold minorBadBound
  rw [←mul_div_assoc] at hsum
  exact add_le_add hsum hb
end Span
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section Star
variable {K I J W : Type*} [Field K] [AddCommGroup W] [Module K W]

def starDifference (v : I) (k : J → I) : (I → W) →ₗ[K] (J → W) where
  toFun X j := X v-X (k j)
  map_add' X Y := by ext j; simp only [Pi.add_apply]; abel
  map_smul' c X := by ext j; simp only [Pi.smul_apply,RingHom.id_apply,smul_sub]

theorem starDifference_surjective (v : I) (k : J → I) (hk : Function.Injective k)
    (hv : ∀ j, k j≠v) : Function.Surjective (starDifference (K := K) (W := W) v k) := by
  intro M
  refine ⟨Function.extend k (fun j => -M j) (fun _ => 0),?_⟩
  ext j
  change Function.extend k (fun j => -M j) (fun _ => (0 : W)) v-
    Function.extend k (fun j => -M j) (fun _ => (0 : W)) (k j)=M j
  rw [hk.extend_apply,Function.extend_apply' _ _ v (by simpa using hv)]
  simp

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype W]
include K in
theorem uniformMean_starDifference (v : I) (k : J → I) (hk : Function.Injective k)
    (hv : ∀ j, k j≠v) (f : (J → W) → ℝ) :
    uniformMean (fun X : I → W => f (fun j => X v-X (k j)))=uniformMean f :=
  uniformMean_surjective_linear (starDifference (K := K) v k)
    (starDifference_surjective v k hk hv) f
end Star
section Border
variable {K I : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]

omit [Fintype K] [DecidableEq K] in
theorem symmetricBorder_sub {N : ℕ} (W V : SymMatrix K N) (z w : Fin N → K) (a b : K) :
    symmetricBorder W z a-symmetricBorder V w b=symmetricBorder (W-V) (z-w) (a-b) := by
  apply Subtype.ext
  ext i j
  change borderRaw W.val z a (borderIndex N i) (borderIndex N j)-
    borderRaw V.val w b (borderIndex N i) (borderIndex N j)=
      borderRaw (W-V).val (z-w) (a-b) (borderIndex N i) (borderIndex N j)
  cases borderIndex N i <;> cases borderIndex N j <;> rfl

theorem uniformMean_pi_prod {A B : Type*} [Fintype A] [Fintype B]
    (f : (I → A × B) → ℝ) :
    uniformMean f=uniformMean fun a : I → A => uniformMean fun b : I → B => f (fun i => (a i,b i)) := by
  rw [←uniformMean_equiv (Equiv.arrowProdEquivProdArrow I (fun _ => A) (fun _ => B)).symm,
    uniformMean_prod]
  rfl

omit [DecidableEq K] in
theorem uniformMean_bordered (N : ℕ) (f : (I → SymMatrix K (N+1)) → ℝ) :
    uniformMean f=uniformMean (fun W : I → SymMatrix K N =>
      uniformMean (fun z : I → (Fin N → K) => uniformMean (fun a : I → K =>
        f (fun i => symmetricBorder (W i) (z i) (a i))))) := by
  rw [←uniformMean_equiv (Equiv.piCongrRight (fun _ : I => (symmetricBorderEquiv (K := K) N).symm))]
  rw [uniformMean_pi_prod]
  apply uniformMean_congr
  intro W
  rw [uniformMean_pi_prod]
  rfl
end Border
end SidorenkoCounterexample

end

end OAI
