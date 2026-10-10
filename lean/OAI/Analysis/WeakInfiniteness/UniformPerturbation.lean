import Mathlib
import OAI.Analysis.WeakInfiniteness.PerturbationRows
import OAI.Analysis.WeakInfiniteness.SupportedSeparation
import OAI.Analysis.WeakInfiniteness.UniformGap

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra ComplexOrder

variable {A : Type 1} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local instance matrixRealModuleUniform {m : Type*} [Fintype m] :
    Module ℝ (CStarMatrix m m A) := Module.complexToReal _

theorem uniform_perturbation_of_gap_one
    {γ σ : ℝ} (hσ : 0 ≤ σ) (hσγ : 2*σ ≤ γ)
    (hgap : ∀ (B : Type 1) [CStarAlgebra B] (v : B), ‖v‖ ≤ 1 → Exact B →
      ¬ FiniteContractionModels B v γ)
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A, 0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (p q h k c : A) (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1)
    (hh : 0 ≤ h) (hk : 0 ≤ k) (hc : 0 ≤ c)
    (hph : star p*p*h=h) (hqk : q*star q*k=k)
    (hch : CuntzSubequiv (diagonalCopies n c) (diagonalCopies 1 h))
    (hck : CuntzSubequiv (diagonalCopies n c) (diagonalCopies 1 k))
    (T : A) {η α : ℝ} (hη : 0 < η) (hα : 0 < α) :
    ∃ y : A, ‖y‖ ≤ 1 ∧
      ∀ (H : ComplexHilbert.{1}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        α ≤ ‖π c‖ → σ*η ≤ ‖π (T+(η : ℂ) • (p*y*q))‖ := by
  obtain ⟨R,hR,hRh,hRn⟩ := exists_fixed_comparison_row c h hc hh hch hα
  obtain ⟨S,hS,hSk,hSn⟩ := exists_fixed_comparison_row c k hc hk hck hα
  obtain ⟨U,hU,_,_⟩ := exists_fixed_comparison_row c h hc hh hch (α := α/4) (by positivity)
  let E := diagonalCopies n (cfcₙ (spectralRamp (α/4)) c)
  let e := diagonalCopies n (cfcₙ (spectralRamp (α/16)) c)
  have he : IsSelfAdjoint e := by
    have hcself : IsSelfAdjoint (cfcₙ (spectralRamp (α/16)) c) := cfcₙ_predicate _ _
    exact hcself.map (diagonalHom n)
  have hUe : U.conjTranspose*U=e := by
    have hd : α/4/4=α/16 := by ring
    simpa only [hd] using hU
  let P := diagonalCopies 1 p
  let Q := diagonalCopies 1 q
  let X := diagonalCopies 1 T
  let L := R.conjTranspose*star P
  let K := star Q*S
  have hPR : star P*P*R=R := by
    change (star (diagonalHom 1 p)*diagonalHom 1 p)*R=R
    rw [← map_star,← map_mul]
    exact fixed_row_partial_isometry p h hh hph R hRh
  have hQS : Q*star Q*S=S := by
    have hhq : star (star q)*star q*k=k := by simpa only [star_star] using hqk
    change diagonalHom 1 q*star (diagonalHom 1 q)*S=S
    rw [← map_star,← map_mul]
    rw [show diagonalHom 1 (q*star q)=diagonalCopies 1 (q*star q) from rfl]
    simpa only [star_star] using fixed_row_partial_isometry (star q) k hk hhq S hSk
  have hLPR : L*P*R=E := by
    dsimp only [L]
    rw [rectangular_mul_assoc, rectangular_mul_assoc, ← rectangular_mul_assoc (star P), hPR]
    exact hR
  have hSQK : S.conjTranspose*Q*K=E := by
    dsimp only [K]
    rw [rectangular_mul_assoc, ← rectangular_mul_assoc Q, hQS]
    exact hS
  have hLn : ‖L‖ ≤ 1 := by
    calc
      ‖L‖ ≤ ‖R.conjTranspose‖*‖star P‖ := rectangular_norm_mul_le _ _
      _ = ‖R‖*‖P‖ := by rw [rectangular_norm_conjTranspose,norm_star]
      _ ≤ 1*1 := by gcongr; exact (norm_diagonalCopies_le 1 p).trans hp
      _ = 1 := one_mul _
  have hKn : ‖K‖ ≤ 1 := by
    calc
      ‖K‖ ≤ ‖star Q‖*‖S‖ := rectangular_norm_mul_le _ _
      _ = ‖Q‖*‖S‖ := by rw [norm_star]
      _ ≤ 1*1 := by gcongr; exact (norm_diagonalCopies_le 1 q).trans hq
      _ = 1 := one_mul _
  let Vval := (η : ℂ)⁻¹ • (R.conjTranspose*(star P*X*star Q)*S)
  let V : supportedAlgebra e he := ⟨Vval,supported_testing_element c hα R S hR hS _ _⟩
  obtain ⟨w,hwn,hEw,hsep⟩ := exists_separated_supported_model_one hσ hσγ hgap hA hn hpi c hc hα e he U hUe V
  let y := matrixSingletonHom (-(R*w*S.conjTranspose))
  have hyn : ‖y‖ ≤ 1 := norm_row_test_le R S w hRn hSn hwn
  have hy : diagonalCopies 1 y= -(R*w*S.conjTranspose) := diagonal_singleton _
  have hcompy : L*(P*(diagonalCopies 1 y)*Q)*K= -w := by
    rw [hy]
    exact compress_row_test L K R S P Q E w hLPR hSQK hEw
  have hcη : (η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hη)
  have hηV : (η : ℂ) • Vval=L*X*K := by
    dsimp only [Vval]
    rw [smul_smul, mul_inv_cancel₀ hcη, one_smul]
    dsimp only [L,K]
    simp only [rectangular_mul_assoc]
  have hcomp : L*diagonalCopies 1 (T+(η : ℂ) • (p*y*q))*K=(η : ℂ) • (Vval-w) := by
    change L*(diagonalHom 1 (T+(η : ℂ) • (p*y*q)))*K= _
    rw [map_add,map_smul,map_mul,map_mul]
    change L*(X+(η : ℂ) • (P*diagonalCopies 1 y*Q))*K= _
    rw [rectangular_mul_add_support,rectangular_add_mul_support,
      rectangular_mul_smul_support,rectangular_smul_mul_support,hcompy,
      smul_sub,hηV,smul_neg,sub_eq_add_neg]
  refine ⟨y,hyn,?_⟩
  intro H π hπc
  have hs := hsep H π hπc
  have hb := norm_representation_compression_le π L K
    (diagonalCopies 1 (T+(η : ℂ) • (p*y*q))) hLn hKn
  rw [hcomp,map_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hη,
    singleton_diagonal] at hb
  exact (by nlinarith : σ*η ≤ η*‖matrixRepresentation π (Fin n) (Vval-w)‖).trans hb

theorem exists_uniform_perturbation_constant_one :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧
      ∀ (A : Type 1) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A],
      Exact A → ∀ n : ℕ, 1 ≤ n →
      (∀ a : A, 0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a)) →
      ∀ p q h k c : A, ‖p‖ ≤ 1 → ‖q‖ ≤ 1 → 0 ≤ h → 0 ≤ k → 0 ≤ c →
      star p*p*h=h → q*star q*k=k →
      CuntzSubequiv (diagonalCopies n c) (diagonalCopies 1 h) →
      CuntzSubequiv (diagonalCopies n c) (diagonalCopies 1 k) →
      ∀ (T : A) (η α : ℝ), 0 < η → 0 < α →
      ∃ y : A, ‖y‖ ≤ 1 ∧
        ∀ (H : ComplexHilbert.{1}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
          α ≤ ‖π c‖ → σ*η ≤ ‖π (T+(η : ℂ) • (p*y*q))‖ := by
  obtain ⟨γ,hγ,hgap⟩ := exists_uniform_gap_one
  let σ := min (1/2) (γ/3)
  have hσ : 0 < σ := lt_min (by norm_num) (by positivity)
  have hσ1 : σ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hσγ : 2*σ ≤ γ := by have := min_le_right (1/2 : ℝ) (γ/3); dsimp [σ]; linarith
  refine ⟨σ,hσ,hσ1,?_⟩
  intro A _ _ _ hA n hn hpi p q h k c hp hq hh hk hc hph hqk hch hck T η α hη hα
  exact uniform_perturbation_of_gap_one hσ.le hσγ hgap hA hn hpi p q h k c hp hq
    hh hk hc hph hqk hch hck T hη hα

end

end WeakPureInfiniteness
end

end OAI
