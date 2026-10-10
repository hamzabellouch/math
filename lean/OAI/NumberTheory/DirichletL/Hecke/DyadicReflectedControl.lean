import OAI.NumberTheory.DirichletL.Hecke.DyadicReflectedFamily

namespace OAI

noncomputable section
open scoped Classical Topology ComplexConjugate
open Complex Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeReciprocalGrowth HeckeDeletionBounds HeckeDyadicReflection

theorem radical_norm_ge_one (M : Ideal O) : 1≤((radical M).absNorm : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero M))

theorem buffered_reflected_line_control (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (s : ℂ), s.re=1-a-6*e → |s.im|≤(3*i+2 : ℕ)*T →
      ‖LFunction (χ j) s‖≤C*((χ j).modulus.absNorm : ℝ)^(a-1/2+6*e)*
        ((radical (χ j).modulus).absNorm : ℝ)^(6*e+2*ε)*
        (3+(3*i+2 : ℕ)*T)^2*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε := by
  obtain ⟨Cg,hCg,hreflect⟩ := original_reflected_subpower ε hε
  obtain ⟨Cb,hCb,hrect⟩ := buffered_rectangle_control e ε he he' hε
  refine ⟨Cg*Cb,mul_pos hCg hCb,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j s hs him
  have hwre : (1-conj s).re=a+6*e := by simp; linarith
  have hwim : (1-conj s).im=s.im := by simp
  have hw := hrect χ hχ T a i hT ha ha' hmax j (1-conj s)
    (by rw [hwre]) (by rw [hwre]; linarith) (by rwa [hwim])
  have hL : ‖LFunction (χ j) (1-conj s)‖≤
      Cb*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans hw.2
  have href := hreflect (χ j) (hχ j) s (by rw [hs]; linarith) (by rw [hs]; linarith)
  have hexp : 1/2-s.re=a-1/2+6*e := by rw [hs]; ring
  rw [hexp] at href
  have hR : ((radical (χ j).modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε)≤
      ((radical (χ j).modulus).absNorm : ℝ)^(6*e+2*ε) := by
    apply Real.rpow_le_rpow_of_exponent_le (radical_norm_ge_one _)
    have hm : max (-s.re) 0≤6*e := max_le (by rw [hs]; linarith) (by positivity)
    linarith
  calc
    _ ≤ Cg*((χ j).modulus.absNorm : ℝ)^(a-1/2+6*e)*
        ((radical (χ j).modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε)*
        (3+|s.im|)^2*‖LFunction (χ j) (1-conj s)‖ := href
    _ ≤ Cg*((χ j).modulus.absNorm : ℝ)^(a-1/2+6*e)*
        ((radical (χ j).modulus).absNorm : ℝ)^(6*e+2*ε)*
        (3+(3*i+2 : ℕ)*T)^2*(Cb*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε) := by
      gcongr
    _ = _ := by ring

theorem original_upper_strip (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ χ : Character, χ.residue≠1 → ∀ s : ℂ,
      -(1/10 : ℝ)≤s.re →
      ‖LFunction χ s‖≤C*(χ.modulus.absNorm : ℝ)^(3/5 : ℝ)*
        ((radical χ.modulus).absNorm : ℝ)^(1/10+ε)*(3+|s.im|)^2 := by
  obtain ⟨Cd,hCd,hdel⟩ := factors_any_re_subpower_bound ε hε
  refine ⟨(1+HeckeLogarithmicInput.uniformConstant)*Cd,
    mul_pos (by linarith [HeckeLogarithmicInput.uniformConstant_nonneg]) hCd,?_⟩
  intro χ hχ s hs
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue≠1 := fun h => hχ ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr h)
  have hg := HeckeLogarithmicInput.regular_right_growth ψ hp hs
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal ψ hψ] at hg
  have hQ' : (ψ.modulus.absNorm : ℝ)^(3/5 : ℝ)≤(χ.modulus.absNorm : ℝ)^(3/5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQ) (by norm_num)
  have hd : ‖HeckeFiniteDeletion.factors χ.modulus ψ s‖≤
      Cd*((radical χ.modulus).absNorm : ℝ)^(1/10+ε) := by
    apply (hdel χ.modulus ψ s).trans
    apply mul_le_mul_of_nonneg_left _ hCd.le
    apply Real.rpow_le_rpow_of_exponent_le (radical_norm_ge_one _)
    have hm : max (-s.re) 0≤1/10 := max_le (by linarith) (by norm_num)
    linarith
  have hU := HeckeLogarithmicInput.uniformConstant_nonneg
  rw [LFunction_eq_of_mask_entire χ ψ hχ hmask,norm_mul]
  calc
    _ ≤ (HeckeLogarithmicInput.uniformConstant*(ψ.modulus.absNorm : ℝ)^(3/5 : ℝ)*(3+|s.im|)^2)*
        (Cd*((radical χ.modulus).absNorm : ℝ)^(1/10+ε)) :=
      mul_le_mul hg hd (norm_nonneg _) (by positivity)
    _ ≤ ((1+HeckeLogarithmicInput.uniformConstant)*(χ.modulus.absNorm : ℝ)^(3/5 : ℝ)*(3+|s.im|)^2)*
        (Cd*((radical χ.modulus).absNorm : ℝ)^(1/10+ε)) := by
      gcongr
      linarith
    _ = _ := by ring

end SevenEighths.HeckeDyadic

end

end OAI
