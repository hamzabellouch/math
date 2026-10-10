import OAI.Probability.SignedSweeps.Imprimitivity
import OAI.Probability.SignedSweeps.InjectionRestriction

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G E : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E) (P : E →ₗ[ℂ] E)
    (hP : P * P = P) (hcomm : ∀ g, ρ g * P = P * ρ g)

omit [Fintype G] [FiniteDimensional ℂ E] in
lemma projectionSubrepresentation_norm (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (g : G) (x : (projectionSubrepresentation ρ P hcomm).toSubmodule) :
    ‖(projectionSubrepresentation ρ P hcomm).toRepresentation g x‖ = ‖x‖ := hρ g x

include hP in

omit [Fintype G] [FiniteDimensional ℂ E] in
lemma projectionSubrepresentation_fixed (x : (projectionSubrepresentation ρ P hcomm).toSubmodule) :
    P (x : E) = x := by
  obtain ⟨y,hy⟩ := x.property
  change P y = (x : E) at hy
  rw [← hy]
  exact LinearMap.congr_fun hP y

include hP in

lemma projectionSubrepresentation_trace (f : G → ℂ) :
    LinearMap.trace ℂ E (P * coefficientAction ρ f) =
      LinearMap.trace ℂ (projectionSubrepresentation ρ P hcomm).toSubmodule
        (coefficientAction (projectionSubrepresentation ρ P hcomm).toRepresentation f) := by
  let S := (projectionSubrepresentation ρ P hcomm).toSubmodule
  let j : S →ₗ[ℂ] E := S.subtype
  let q : E →ₗ[ℂ] S := P.rangeRestrict
  have he : P * coefficientAction ρ f = j ∘ₗ (q ∘ₗ coefficientAction ρ f) := rfl
  rw [he, LinearMap.trace_comp_comm']
  congr 1
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change P (coefficientAction ρ f (x : E)) = _
  simp only [coefficientAction, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    Submodule.coe_sum, Submodule.coe_smul]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  exact projectionSubrepresentation_fixed ρ P hP hcomm
    ((projectionSubrepresentation ρ P hcomm).toRepresentation g x)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma specht_dimension_expansion {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) :
    finrank ℂ E = ∑ lam : Partition n,
      finrank ℂ (Representation.IntertwiningMap (spechtRepresentation lam) ρ) * spechtDimension lam := by
  have ht := character_specht_expansion ρ 1
  simp only [Representation.char_one] at ht
  exact_mod_cast ht

lemma exists_nonzero_of_multiplicity_ne_zero {G E F : Type*} [Monoid G]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
    (hm : finrank ℂ (Representation.IntertwiningMap ρ σ) ≠ 0) :
    ∃ f : Representation.IntertwiningMap ρ σ, f ≠ 0 := by
  by_contra hn
  push Not at hn
  exact hm (finrank_zero_iff_forall_zero.mpr hn)

theorem sector_positive_restriction {p n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (SymmetricGroup p) E)
    (i : SymmetricGroup p →* SymmetricGroup n) (hi : Function.Injective i)
    (f : SymmetricGroup n → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive)
    (D T : ℝ) (hD : 0 < D) (hT : 0 ≤ T)
    (hdegree : ∀ mu : Partition p,
      (∃ k : Representation.IntertwiningMap (spechtRepresentation mu) ρ, k ≠ 0) →
        D ≤ spechtDimension mu)
    (hambient : ∀ mu : Partition p,
      (∃ k : Representation.IntertwiningMap (spechtRepresentation mu) ρ, k ≠ 0) →
      ∀ lam : Partition n,
        (∃ k : Representation.IntertwiningMap (spechtRepresentation mu)
          ((spechtRepresentation lam).comp i), k ≠ 0) →
        (spechtDimension lam : ℝ) *
          (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) f)).re ≤ T) :
    (LinearMap.trace ℂ E (coefficientAction ρ (fun g => f (i g)))).re ≤
      (finrank ℂ E : ℝ) *
        (((p.factorial : ℝ) / n.factorial) * (Fintype.card (Partition n) : ℝ) * T) / D^2 := by
  let R := ((p.factorial : ℝ) / n.factorial) * (Fintype.card (Partition n) : ℝ) * T
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hterm (mu : Partition p)
      (hm : finrank ℂ (Representation.IntertwiningMap (spechtRepresentation mu) ρ) ≠ 0) :
      (LinearMap.trace ℂ (Specht mu)
        (coefficientAction (spechtRepresentation mu) (fun g => f (i g)))).re ≤
        (spechtDimension mu : ℝ) * R / D^2 := by
    have he := exists_nonzero_of_multiplicity_ne_zero _ _ hm
    let := specht_irreducible mu
    have ht := positive_injective_restriction (spechtRepresentation mu)
      (spechtRepresentation_norm mu) i hi f hf
    have hs : (∑ lam : Partition n, if
        (∃ k : Representation.IntertwiningMap (spechtRepresentation mu)
          ((spechtRepresentation lam).comp i), k ≠ 0) then
          (spechtDimension lam : ℝ) *
            (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) f)).re
        else 0) ≤ (Fintype.card (Partition n) : ℝ) * T := by
      calc
        _ ≤ ∑ _lam : Partition n, T := by
          apply Finset.sum_le_sum
          intro lam _
          split_ifs with hh
          · exact hambient mu he lam hh
          · exact hT
        _ = _ := by simp
    have hb : (spechtDimension mu : ℝ) *
        (LinearMap.trace ℂ (Specht mu)
          (coefficientAction (spechtRepresentation mu) (fun g => f (i g)))).re ≤ R := by
      have hb := ht.2.trans (mul_le_mul_of_nonneg_left hs (by positivity))
      simpa only [spechtDimension, SymmetricGroup, Fintype.card_perm, Fintype.card_fin, mul_assoc, R] using hb
    have hdmu : D ≤ (spechtDimension mu : ℝ) := hdegree mu he
    have hdsq : D^2 ≤ (spechtDimension mu : ℝ)^2 := sq_le_sq₀ hD.le (Nat.cast_nonneg _) |>.mpr hdmu
    apply (le_div_iff₀ (sq_pos_of_pos hD)).mpr
    calc
      _ = D^2 * (LinearMap.trace ℂ (Specht mu)
          (coefficientAction (spechtRepresentation mu) (fun g => f (i g)))).re := mul_comm _ _
      _ ≤ (spechtDimension mu : ℝ)^2 * (LinearMap.trace ℂ (Specht mu)
          (coefficientAction (spechtRepresentation mu) (fun g => f (i g)))).re :=
        mul_le_mul_of_nonneg_right hdsq ht.1
      _ = (spechtDimension mu : ℝ) * ((spechtDimension mu : ℝ) *
          (LinearMap.trace ℂ (Specht mu)
            (coefficientAction (spechtRepresentation mu) (fun g => f (i g)))).re) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
  rw [trace_specht_expansion, Complex.re_sum]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  calc
    _ ≤ ∑ mu : Partition p,
        (finrank ℂ (Representation.IntertwiningMap (spechtRepresentation mu) ρ) : ℝ) *
          ((spechtDimension mu : ℝ) * R / D^2) := by
      apply Finset.sum_le_sum
      intro mu _
      by_cases hm : finrank ℂ (Representation.IntertwiningMap (spechtRepresentation mu) ρ) = 0
      · simp [hm]
      · exact mul_le_mul_of_nonneg_left (hterm mu hm) (Nat.cast_nonneg _)
    _ = _ := by
      change (∑ mu : Partition p,
        (finrank ℂ (Representation.IntertwiningMap (spechtRepresentation mu) ρ) : ℝ) *
          ((spechtDimension mu : ℝ) * R / D^2)) = (finrank ℂ E : ℝ) * R / D^2
      have hd : (∑ mu : Partition p,
          (finrank ℂ (Representation.IntertwiningMap (spechtRepresentation mu) ρ) : ℝ) *
            (spechtDimension mu : ℝ)) = (finrank ℂ E : ℝ) := by
        exact_mod_cast (specht_dimension_expansion ρ).symm
      simp_rw [mul_div_assoc, ← mul_assoc]
      rw [← Finset.sum_mul, hd]

end SignedSweeps
end

end OAI
