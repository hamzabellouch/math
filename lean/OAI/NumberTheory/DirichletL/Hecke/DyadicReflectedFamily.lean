import OAI.NumberTheory.DirichletL.Hecke.DyadicReflection
import OAI.NumberTheory.DirichletL.Hecke.Conjugation
import OAI.NumberTheory.DirichletL.Hecke.DeletionBounds

namespace OAI

noncomputable section
open scoped Classical Topology ComplexConjugate
open Complex Set
namespace SevenEighths.HeckeDyadicReflection
open HeckeFamily HeckePresentation HeckeFiniteDeletion

theorem family_reflected_bound : ∃ C : ℝ, 0<C ∧ ∀ η : Character,
    FiniteFourier.IsPrimitiveOnIdeals η.residue → η.residue≠1 →
    ∀ s : ℂ, -(1/10 : ℝ)≤s.re → s.re≤1/2 →
    ‖LFunction η s‖≤C*(η.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
      ‖LFunction η (1-conj s)‖ := by
  obtain ⟨C,hC,hbound⟩ := primitive_reflected_bound
  refine ⟨C,hC,?_⟩
  intro η hp hη s hl hr
  have h := hbound (generator η) (principalResidue η) (principalResidue_unit η)
    (principalResidue_primitive η hp) (principalResidue_ne_one η hη) s hl hr
  have hi : HeckePrimitive.character (generator η) (principalResidue η)⁻¹
      (HeckePrimitive.inverse_unit_trivial (generator η) (principalResidue η) (principalResidue_unit η)) =
      (principalCharacter η).inverse := rfl
  rw [hi,LFunction_inverse_conj (principalCharacter η) (principalResidue_ne_one η hη),
    norm_conj,map_sub,map_one] at h
  change ‖LFunction (principalCharacter η) s‖≤_ at h
  rw [LFunction_principalCharacter η hη,LFunction_principalCharacter η hη] at h
  simpa only [HeckeStripActual.conductor,span_generator] using h

theorem LFunction_eq_of_mask_entire (χ ψ : Character) (hχ : χ.residue≠1)
    (hmask : ∀ J : Ideal O, idealCoeff χ J=
      if IsCoprime J χ.modulus then idealCoeff ψ J else 0) (s : ℂ) :
    LFunction χ s=LFunction ψ s*factors χ.modulus ψ s := by
  have hψ : ψ.residue≠1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have ha := LFunction_entire_nonprincipal χ hχ
  have hb : Differentiable ℂ (fun z => LFunction ψ z*factors χ.modulus ψ z) :=
    (LFunction_entire_nonprincipal ψ hψ).mul (factors_differentiable _ _)
  have he : LFunction χ=(fun z => LFunction ψ z*factors χ.modulus ψ z) := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr ha).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hb) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ)<(2 : ℂ).re)] with z hz
    exact LFunction_eq_of_mask_right χ ψ hmask hz
  exact congr_fun he s

theorem original_reflected_bound : ∃ C : ℝ, 0<C ∧ ∀ χ ψ : Character,
    FiniteFourier.IsPrimitiveOnIdeals ψ.residue → χ.residue≠1 →
    (∀ J : Ideal O, idealCoeff χ J=
      if IsCoprime J χ.modulus then idealCoeff ψ J else 0) →
    ∀ s : ℂ, -(1/10 : ℝ)≤s.re → s.re≤1/2 →
    ‖LFunction χ s‖≤C*(ψ.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
      ‖LFunction χ (1-conj s)‖*
      (‖factors χ.modulus ψ s‖*‖(factors χ.modulus ψ (1-conj s))⁻¹‖) := by
  obtain ⟨C,hC,hbound⟩ := family_reflected_bound
  refine ⟨C,hC,?_⟩
  intro χ ψ hp hχ hmask s hl hr
  have hψ : ψ.residue≠1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have h := hbound ψ hp hψ s hl hr
  have hd : factors χ.modulus ψ (1-conj s)≠0 := factors_ne_zero _ _ (by simp; linarith)
  have he : LFunction ψ (1-conj s)=LFunction χ (1-conj s)*(factors χ.modulus ψ (1-conj s))⁻¹ := by
    rw [LFunction_eq_of_mask_entire χ ψ hχ hmask]
    field_simp
  rw [he,norm_mul] at h
  rw [LFunction_eq_of_mask_entire χ ψ hχ hmask,norm_mul]
  calc
    _ ≤ (C*(ψ.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
        (‖LFunction χ (1-conj s)‖*‖(factors χ.modulus ψ (1-conj s))⁻¹‖))*
          ‖factors χ.modulus ψ s‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = _ := by ring

theorem original_reflected_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ χ : Character, χ.residue≠1 →
    ∀ s : ℂ, -(1/10 : ℝ)≤s.re → s.re≤1/2 →
    ‖LFunction χ s‖≤C*(χ.modulus.absNorm : ℝ)^(1/2-s.re)*
      ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε)*
      (3+|s.im|)^2*‖LFunction χ (1-conj s)‖ := by
  obtain ⟨Cg,hCg,hreflect⟩ := original_reflected_bound
  obtain ⟨Cl,hCl,hleft⟩ := HeckeDeletionBounds.factors_any_re_subpower_bound ε hε
  obtain ⟨Cr,hCr,hright⟩ := HeckeDeletionBounds.factors_radical_subpower_bound (1/2) ε (by norm_num) hε
  refine ⟨Cg*Cl*Cr,by positivity,?_⟩
  intro χ hχ s hl hr
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hR : 0<((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (HeckeDeletionBounds.radical_ne_zero χ.modulus))
  have hd₁ := hleft χ.modulus ψ s
  have hd₂ : ‖(factors χ.modulus ψ (1-conj s))⁻¹‖≤
      Cr*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε := by
    have h := hright χ.modulus ψ (1-conj s) (by simp; linarith)
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans h
  have hd : ‖factors χ.modulus ψ s‖*‖(factors χ.modulus ψ (1-conj s))⁻¹‖≤
      (Cl*Cr)*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε) := by
    calc
      _ ≤ (Cl*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+ε))*
          (Cr*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε) :=
        mul_le_mul hd₁ hd₂ (norm_nonneg _) (mul_nonneg hCl.le (Real.rpow_nonneg hR.le _))
      _ = _ := by
        have he : ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+ε)*
            ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε =
            ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε) := by
          rw [←Real.rpow_add hR]
          congr 1
          ring
        calc
          _ = (Cl*Cr)*(((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+ε)*
              ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε) := by ring
          _ = _ := by rw [he]
  have hQ' : (ψ.modulus.absNorm : ℝ)^(1/2-s.re)≤(χ.modulus.absNorm : ℝ)^(1/2-s.re) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQ) (by linarith)
  calc
    _ ≤ Cg*(ψ.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
        ‖LFunction χ (1-conj s)‖*
        (‖factors χ.modulus ψ s‖*‖(factors χ.modulus ψ (1-conj s))⁻¹‖) :=
      hreflect χ ψ hp hχ hmask s hl hr
    _ ≤ Cg*(χ.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
        ‖LFunction χ (1-conj s)‖*
        ((Cl*Cr)*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε)) := by
      apply mul_le_mul _ hd (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
      gcongr
    _ = _ := by ring

end SevenEighths.HeckeDyadicReflection

end

end OAI
