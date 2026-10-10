import OAI.NumberTheory.CubicMoment.Estimates.DivisorDispersion

namespace OAI

/-!
# The exact cube frequencies after square-divisor sieving

For a squarefree divisor `d`, the frequencies with `d*h` a cube are
precisely `d²*j³`. Every nonzero such frequency has three preimages.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Squarefreeness forces the full `d²` factor in a principal frequency. -/
theorem squarefree_mul_cube_iff {d h : Eisenstein} (hd : d ≠ 0) (hs : Squarefree d) :
    (∃ j : Eisenstein, d*h = j^3) ↔ ∃ j : Eisenstein, h = d^2*j^3 := by
  constructor
  · rintro ⟨j,hj⟩
    have hdj : d ∣ j := (hs.dvd_pow_iff_dvd (by norm_num : (3:ℕ) ≠ 0)).mp
      (hj ▸ dvd_mul_right d h)
    obtain ⟨k,rfl⟩ := hdj
    refine ⟨k,mul_left_cancel₀ hd ?_⟩
    calc
      d*h = (d*k)^3 := hj
      _ = d*(d^2*k^3) := by ring
  · rintro ⟨j,rfl⟩
    exact ⟨d*j,by ring⟩

lemma cube_eq_iff {x y : Eisenstein} :
    x^3 = y^3 ↔ x = y ∨ x = omegaE*y ∨ x = omegaE^2*y := by
  have hω : omegaE^2+omegaE+1 = 0 := Subtype.ext omega_quadratic
  have hfactor : x^3-y^3 = (x-y)*(x-omegaE*y)*(x-omegaE^2*y) := by
    linear_combination (x^2*y-x*y^2)*hω + (y^3-x*y^2)*(omegaE_cube)
  constructor
  · intro h
    have hz : (x-y)*(x-omegaE*y)*(x-omegaE^2*y) = 0 := by rw [← hfactor,h,sub_self]
    rcases mul_eq_zero.mp hz with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (sub_eq_zero.mp h))
  · rintro (rfl | rfl | rfl)
    · rfl
    · rw [mul_pow,omegaE_cube,one_mul]
    · rw [mul_pow,← pow_mul,show (2:ℕ)*3 = 3*2 by norm_num,pow_mul,omegaE_cube,one_pow,one_mul]

/-- The three roots differ exactly by the cube roots of unity. -/
theorem cube_fiber_eq {y : Eisenstein} :
    {x : Eisenstein | x^3 = y^3} = {y,omegaE*y,omegaE^2*y} := by
  ext x
  simp only [Set.mem_ofPred_eq,Set.mem_insert_iff,Set.mem_singleton_iff,cube_eq_iff]

/-- Every Eisenstein cube is a rational integer modulo three. -/
theorem cube_eq_integer_mod_three (j : Eisenstein) :
    ∃ n : ℤ, (3 : Eisenstein) ∣ j^3-(n : Eisenstein) := by
  obtain ⟨⟨a,b⟩,rfl⟩ := ofCoords_surjective j
  refine ⟨a^3+b^3-3*a*b^2,⟨((a*b*(a-b) : ℤ) : Eisenstein)*omegaE,?_⟩⟩
  have hω : omegaE^2+omegaE+1 = 0 := Subtype.ext omega_quadratic
  dsimp only [ofCoords]
  push_cast
  linear_combination (b : Eisenstein)^3*omegaE_cube +
    (3*(a : Eisenstein)*(b : Eisenstein)^2)*hω

lemma tracePhase_rational_mod_three {h : Eisenstein}
    (hh : ∃ n : ℤ, (3 : Eisenstein) ∣ h-(n : Eisenstein)) :
    (Real.fourierChar (tracePair (h : ℂ) (1/(3*traceLambda))) : ℂ) = 1 := by
  obtain ⟨n,k,hk⟩ := hh
  have he : (h : ℂ) = (n : ℂ)+3*(k : ℂ) := by
    have he' : h = (n : Eisenstein)+3*k := by linear_combination hk
    have hc := congrArg (eisensteinRing.val : Eisenstein → ℂ) he'
    simpa only [map_add,map_mul,map_ofNat,map_intCast,Subalgebra.val_apply] using hc
  have hz : tracePair (h : ℂ) (1/(3*traceLambda)) =
      tracePair (k : ℂ) (1/traceLambda) := by
    rw [he]
    have hpair : ((n : ℂ)+3*(k : ℂ))*(1/(3*traceLambda)) =
        (n : ℂ)/(3*traceLambda)+(k : ℂ)/traceLambda := by
      field_simp
    unfold tracePair
    rw [hpair,Complex.add_re]
    have hn : ((n : ℂ)/(3*traceLambda)).re = 0 := by
      rw [traceLambda_eq]
      simp [Complex.div_re,Complex.mul_re,Complex.mul_im]
    rw [hn,zero_add,div_eq_mul_inv,one_div]
  rw [hz,tracePhase_div_lambda_one]

/-- The additive phase in the Poisson formula is one on every principal
frequency produced by the squarefree majorant. -/
theorem squarefree_cube_frequency_phase {d : Eisenstein} (hd : primary d)
    (j : Eisenstein) :
    (Real.fourierChar (tracePair ((d^2*j^3 : Eisenstein) : ℂ)
      (1/(3*traceLambda))) : ℂ) = 1 := by
  obtain ⟨n,hn⟩ := cube_eq_integer_mod_three j
  apply tracePhase_rational_mod_three
  refine ⟨n,?_⟩
  have hd2 : (3 : Eisenstein) ∣ d^2-1 := by
    have h := primary_mul hd hd
    simpa only [primary,pow_two] using h
  have hs := dvd_add (dvd_mul_of_dvd_left hd2 (j^3)) hn
  convert hs using 1
  ring

lemma omegaE_mul_injective {y : Eisenstein} (hy : y ≠ 0) :
    Function.Injective (fun i : Fin 3 => omegaE^(i : ℕ)*y) := by
  intro i j hij
  apply Fin.ext
  exact omegaE_primitive.pow_inj i.isLt j.isLt (mul_right_cancel₀ hy hij)

/-- The factor `1/3` in the cube-lattice sum is the exact fiber size,
including all three units whose cubes are one. -/
theorem cube_fiber_card {y : Eisenstein} (hy : y ≠ 0) :
    {x : Eisenstein | x^3 = y^3}.ncard = 3 := by
  have he : {x : Eisenstein | x^3 = y^3} =
      Set.range (fun i : Fin 3 => omegaE^(i : ℕ)*y) := by
    ext x
    rw [Set.mem_ofPred_eq,cube_eq_iff,Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨0,by simp⟩
      · exact ⟨1,by simp⟩
      · exact ⟨2,by simp⟩
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
  rw [he,Set.ncard_range_of_injective (omegaE_mul_injective hy)]
  simp

end CubicFirstMoment

end

end OAI
