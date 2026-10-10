import OAI.NumberTheory.DirichletL.Hecke.LogarithmicActual

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeReciprocalGrowth
open HeckeFamily HeckeLogarithmic HeckeDeletionBounds

def presentationComplexity (χ : Character) (t : ℝ) : ℝ :=
  ((radical χ.modulus).absNorm : ℝ)*complexity χ t

theorem reciprocal_subpower (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ D : ℝ, 0<D ∧ ∀ (χ : Character) (s : ℂ),
      HeckeZeroSupremum.beta+8*e ≤ s.re →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ D*(presentationComplexity χ s.im)^ε := by
  obtain ⟨Dp,hDp,hpbound⟩ := HeckeLogarithmicActual.primitive_reciprocal_subpower e ε he he' hε
  obtain ⟨Cd,hCd,hreduce⟩ := HeckeDeletionReciprocal.exists_primitive_reciprocal_reduction
    (HeckeZeroSupremum.beta+8*e) ε (by linarith [HeckeZeroSupremum.half_le_beta]) hε
  refine ⟨Cd*Dp, mul_pos hCd hDp, ?_⟩
  intro χ s hs
  obtain ⟨ψ,hp,hn,_,hr⟩ := hreduce χ
  have hc : complexity ψ s.im ≤ complexity χ s.im := by
    unfold complexity
    have hn' : (ψ.modulus.absNorm : ℝ) ≤ χ.modulus.absNorm := by exact_mod_cast hn
    gcongr
  have hc0 : 0 ≤ complexity ψ s.im :=
    (Real.exp_pos 1).le.trans (complexity_ge_exp ψ s.im)
  have hr0 : 0 ≤ ((radical χ.modulus).absNorm : ℝ) := by positivity
  apply (hr s hs).trans
  calc
    _ ≤ Cd*((radical χ.modulus).absNorm : ℝ)^ε * (Dp*(complexity ψ s.im)^ε) :=
      mul_le_mul_of_nonneg_left (hpbound ψ hp s hs) (by positivity)
    _ = (Cd*Dp)*(((radical χ.modulus).absNorm : ℝ)*complexity ψ s.im)^ε := by
      rw [Real.mul_rpow hr0 hc0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hr0 hc0) (mul_le_mul_of_nonneg_left hc hr0) hε.le)
      (mul_pos hCd hDp).le

theorem polynomial_reciprocal_bound (χ : Character) (a : ℝ)
    (hβ : HeckeZeroSupremum.beta < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2) := by
  let e : ℝ := min (1/2000) ((a-HeckeZeroSupremum.beta)/16)
  have he : 0<e := lt_min (by norm_num) (by linarith)
  have he' : e<1/1000 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hmargin : HeckeZeroSupremum.beta+8*e ≤ a := by
    have hh := min_le_right (1/2000 : ℝ) ((a-HeckeZeroSupremum.beta)/16)
    change e ≤ (a-HeckeZeroSupremum.beta)/16 at hh
    linarith
  obtain ⟨C,hC,hbound⟩ := reciprocal_subpower e 1 he he' (by norm_num)
  let K : ℝ := C*((radical χ.modulus).absNorm : ℝ)*(2*(χ.modulus.absNorm : ℝ))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨18*K, by positivity, ?_⟩
  intro s hs
  have h := hbound χ s (hmargin.trans hs)
  have hheight : (3+|s.im|)^2 ≤ 18*(1+|s.im|^2) := by
    nlinarith [sq_nonneg (|s.im|-1), sq_nonneg |s.im|]
  rw [Real.rpow_one] at h
  calc
    _ ≤ K*(3+|s.im|)^2 := by
      convert h using 1 ; unfold K presentationComplexity complexity ; ring
    _ ≤ K*(18*(1+|s.im|^2)) := mul_le_mul_of_nonneg_left hheight hK
    _ = _ := by ring

end SevenEighths.HeckeReciprocalGrowth

end

end OAI
