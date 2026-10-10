import Mathlib
import OAI.Analysis.WeakInfiniteness.CompatiblePerturbations
import OAI.Analysis.WeakInfiniteness.QuantitativeAssembly
import OAI.Analysis.WeakInfiniteness.SeparationColumnBounds
import OAI.Analysis.WeakInfiniteness.SeparationPreassembly
import OAI.Analysis.WeakInfiniteness.SeparationSupport
import OAI.Analysis.WeakInfiniteness.SeparationTransferredCoverage

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

open scoped CStarAlgebra

section

variable {A : Type 1} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma separatingPositives_of_four_columns
    (a b x₀ x₁ y₀ y₁ : A) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {r l σ : ℝ} (hr : 0 < r) (hl : 0 < l) (hl1 : l < 1/10)
    (hσ : 0 < σ) (hσ1 : σ < 1)
    (hx₀mem : x₀ ∈ principalRightIdeal a) (hx₁mem : x₁ ∈ principalRightIdeal a)
    (hy₀mem : y₀ ∈ principalRightIdeal b) (hy₁mem : y₁ ∈ principalRightIdeal b)
    (h00 : ‖star x₀*y₀‖ ≤ 8*l) (h10 : ‖star x₁*y₀‖ ≤ 6*Real.sqrt l)
    (h01 : ‖star x₀*y₁‖ ≤ 6*Real.sqrt l) (h11 : star x₁*y₁=0)
    (hcoverage₁ : ∀ (H : ComplexHilbert.{1}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
      r ≤ ‖π a‖ → r*(σ/16)/8 ≤ max ‖π x₀‖ ‖π x₁‖)
    (hcoverage₂ : ∀ (H : ComplexHilbert.{1}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
      r ≤ ‖π b‖ → r*(σ^2/128)/8 ≤ max ‖π y₀‖ ‖π y₁‖) :
    ∃ Q R : A,0 ≤ Q ∧ 0 ≤ R ∧
      Q ∈ hereditarySubalgebra a ha.isSelfAdjoint ∧
      R ∈ hereditarySubalgebra b hb.isSelfAdjoint ∧
      (∀ (H : ComplexHilbert.{1}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        NonUnitalRepresentationIrreducible π →
        (r ≤ ‖π a‖ → r*σ^2/1024 ≤ ‖π Q‖) ∧
        (r ≤ ‖π b‖ → r*σ^2/1024 ≤ ‖π R‖)) ∧ ‖Q*R‖ ≤ 20*Real.sqrt l := by
  let Q : A := CFC.sqrt (x₀*star x₀+x₁*star x₁)
  let R : A := CFC.sqrt (y₀*star y₀+y₁*star y₁)
  have hQQ : 0 ≤ x₀*star x₀+x₁*star x₁ := add_nonneg (mul_star_self_nonneg x₀) (mul_star_self_nonneg x₁)
  have hRR : 0 ≤ y₀*star y₀+y₁*star y₁ := add_nonneg (mul_star_self_nonneg y₀) (mul_star_self_nonneg y₁)
  refine ⟨Q,R,CFC.sqrt_nonneg _,CFC.sqrt_nonneg _,?_,?_,?_,?_⟩
  · exact sqrt_mem_hereditary a _ ha.isSelfAdjoint ((hereditarySubalgebra a ha.isSelfAdjoint).add_mem
      (rightIdeal_square_mem_hereditary a x₀ ha.isSelfAdjoint hx₀mem)
      (rightIdeal_square_mem_hereditary a x₁ ha.isSelfAdjoint hx₁mem)) hQQ
  · exact sqrt_mem_hereditary b _ hb.isSelfAdjoint ((hereditarySubalgebra b hb.isSelfAdjoint).add_mem
      (rightIdeal_square_mem_hereditary b y₀ hb.isSelfAdjoint hy₀mem)
      (rightIdeal_square_mem_hereditary b y₁ hb.isSelfAdjoint hy₁mem)) hRR
  · intro H π _
    constructor
    · intro hπ
      have h := hcoverage₁ H π hπ
      obtain ⟨hx,hy⟩ := norm_sqrt_sum_representation π x₀ x₁
      have hm := max_le hx hy
      have hs : σ^2 ≤ 8*σ := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left hs hr.le
      exact (by nlinarith : r*σ^2/1024 ≤ r*(σ/16)/8).trans (h.trans hm)
    · intro hπ
      have h := hcoverage₂ H π hπ
      obtain ⟨hx,hy⟩ := norm_sqrt_sum_representation π y₀ y₁
      have hm := max_le hx hy
      have heq : r*(σ^2/128)/8 = r*σ^2/1024 := by ring
      rw [heq] at h
      exact h.trans hm
  · have hn := norm_two_sqrt_sums_le x₀ x₁ y₀ y₁
    rw [h11,norm_zero] at hn
    have hls : l ≤ Real.sqrt l := by nlinarith [Real.sq_sqrt hl.le,Real.sqrt_nonneg l]
    change ‖CFC.sqrt (x₀*star x₀+x₁*star x₁)*CFC.sqrt (y₀*star y₀+y₁*star y₁)‖ ≤ _
    linarith

theorem quantitative_separatingPositives_one
    (hpi : ∀ a : A,0 ≤ a → ProperlyInfinite (diagonalCopies 1 a))
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (hpert : UniformPerturbationOne A σ) :
    QuantitativeSeparatingPositives A σ := by
  intro a b ha hb han hbn r l hr _ hl hl1
  let B := Unitization ℂ A
  let X : A := a*b
  let Xu : B := X
  let T : B := star Xu*Xu
  let S : B := Xu*star Xu
  let V : B := cfc (separationV l) T
  let R₀ : B := cfc (separationR l) T
  let g₀ : A := cfcₙ (separationG l) (star X*X)
  let N₀ : A := cfcₙ (separationN l) (star X*X)
  let g : B := cfc (separationG l) T
  let N : B := cfc (separationN l) T
  let Lₛ : B := cfc (separationL l) S
  let Lₜ : B := cfc (separationL l) T
  let C₁ : A := unitizedRight a (Xu*V)
  let C₂ : A := unitizedRight b R₀
  have hg₀ : (g₀ : B)=g := inr_separationG X hl
  have hN₀ : (N₀ : B)=N := inr_separationN X hl
  have hC₁ : (C₁ : B)=(a : B)*Xu*V := by rw [inr_unitizedRight]; simp only [mul_assoc]
  have hC₂ : (C₂ : B)=(b : B)*R₀ := inr_unitizedRight b R₀
  have hXu : Xu=(a : B)*(b : B) := by simp only [Xu,X,Unitization.inr_mul]
  have hXn : ‖Xu‖ ≤ 1 := by
    rw [show Xu=(X : B) from rfl,Unitization.norm_inr]
    exact (norm_mul_le a b).trans (by nlinarith [norm_nonneg a,norm_nonneg b])
  obtain ⟨e,f,k₁,k₂,he,hf,hk₁,hk₂,hen,hfn,hef,hek₁,hfk₂,hge,hgf,hkdet⟩ :=
    exists_separation_cores hpi X hl
  have hgeu : g*(e : B)=(e : B) := by
    rw [← hg₀,← Unitization.inr_mul,hge]
  have hgfu : g*(f : B)=(f : B) := by
    rw [← hg₀,← Unitization.inr_mul,hgf]
  let τ : ℝ := r*Real.sqrt l/8
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  let D₁ : A := C₁*g₀
  let D₂ : A := C₂*g₀
  let h₁ : A := cfcₙ (columnCoreFunction τ) (star D₁*D₁)
  let h₂ : A := cfcₙ (columnCoreFunction τ) (star D₂*D₂)
  let d₁ : A := cfcₙ (columnCoreFunction (2*τ)) (star (C₁*N₀)*(C₁*N₀))
  let d₂ : A := cfcₙ (columnCoreFunction (2*τ)) (star (C₂*N₀)*(C₂*N₀))
  let F₁ : B := cfc (columnMetricFunction τ) ((D₁ : B)*star (D₁ : B))
  let F₂ : B := cfc (columnMetricFunction τ) ((D₂ : B)*star (D₂ : B))
  obtain ⟨p₁,hp₁eq,hF₁,hp₁,hh₁,hph₁⟩ := nonunital_column_left_normalization D₁ hτ
  obtain ⟨p₂,hp₂eq,hF₂,hp₂,hh₂,hph₂⟩ := nonunital_column_left_normalization D₂ hτ
  have hFC₁ : F₁*(C₁ : B)*g=(p₁ : B) := by
    rw [mul_assoc,← hg₀,← Unitization.inr_mul]
    exact hp₁eq
  have hFC₂ : F₂*(C₂ : B)*g=(p₂ : B) := by
    rw [mul_assoc,← hg₀,← Unitization.inr_mul]
    exact hp₂eq
  have hd₁ : 0 ≤ d₁ := cfcₙ_nonneg (fun s _ => le_max_right _ _)
  have hd₂ : 0 ≤ d₂ := cfcₙ_nonneg (fun s _ => le_max_right _ _)
  obtain ⟨hdh₁,hdk₁⟩ := separation_core_comparisons hpi X C₁ k₁ hk₁ hl hτ
    (fun H π hπ => (hkdet H π hπ).1)
  obtain ⟨hdh₂,hdk₂⟩ := separation_core_comparisons hpi X C₂ k₂ hk₂ hl hτ
    (fun H π hπ => (hkdet H π hπ).2)
  obtain ⟨Z,W,z,w,hZfact,hWfact,hZW,hZn,hWn,htest₁,htest₂⟩ :=
    exists_compatible_metric_perturbations hσ hσ1 hτ hpert g F₁ F₂ (C₁ : B) (C₂ : B)
      (norm_separationG Xu l) (cfc_predicate _ _) p₁ p₂ e f h₁ h₂ k₁ k₂ d₁ d₂
      hp₁ hp₂ hen hfn hh₁ hh₂ hk₁ hk₂ hd₁ hd₂ hph₁ hph₂ hek₁ hfk₂
      hdh₁ hdh₂ hdk₁ hdk₂ hgeu hgfu hFC₁ hFC₂
  let s : ℂ := (((Real.sqrt l)⁻¹ : ℝ) : ℂ)
  let x₀ : A := unitizedRight a Lₛ
  let y₀ : A := unitizedRight b Lₜ
  let x₁ : A := s • unitizedRight C₁ (Z*(e : B))
  let y₁ : A := s • unitizedRight C₂ (W*(f : B))
  have hx₀ : (x₀ : B)=(a : B)*Lₛ := inr_unitizedRight a Lₛ
  have hy₀ : (y₀ : B)=(b : B)*Lₜ := inr_unitizedRight b Lₜ
  have hx₁ : (x₁ : B)=s • ((C₁ : B)*Z*(e : B)) := by
    rw [Unitization.inr_smul,inr_unitizedRight]
    simp only [mul_assoc]
  have hy₁ : (y₁ : B)=s • ((C₂ : B)*W*(f : B)) := by
    rw [Unitization.inr_smul,inr_unitizedRight]
    simp only [mul_assoc]
  have hx₀mem : x₀ ∈ principalRightIdeal a := inr_factor_mem_principal ha Lₛ hx₀
  have hy₀mem : y₀ ∈ principalRightIdeal b := inr_factor_mem_principal hb Lₜ hy₀
  have hx₁mem : x₁ ∈ principalRightIdeal a := by
    apply inr_factor_mem_principal ha (s • (Xu*V*Z*(e : B)))
    rw [hx₁,hC₁,mul_smul_comm]
    simp only [mul_assoc]
  have hy₁mem : y₁ ∈ principalRightIdeal b := by
    apply inr_factor_mem_principal hb (s • (R₀*W*(f : B)))
    rw [hy₁,hC₂,mul_smul_comm]
    simp only [mul_assoc]
  have haU : 0 ≤ (a : B) := Unitization.inr_nonneg_iff.mpr ha
  have heU : 0 ≤ (e : B) := Unitization.inr_nonneg_iff.mpr he
  have hefU : (e : B)*(f : B)=0 := by rw [← Unitization.inr_mul,hef,Unitization.inr_zero]
  have hcols := separation_four_column_bounds (a : B) (b : B) (e : B) (f : B) Z W w haU heU hefU hl
    (by simpa only [Unitization.norm_inr] using hen) (by simpa only [Unitization.norm_inr] using hfn)
    hZn hWn (by simpa only [← hXu] using hgfu) (by simpa only [← hXu] using hWfact) hZW
  have h00 : ‖star x₀*y₀‖ ≤ 8*l := by
    rw [← Unitization.norm_inr (𝕜 := ℂ) (star x₀*y₀),Unitization.inr_mul,Unitization.inr_star,hx₀,hy₀]
    simpa only [← hXu] using hcols.1
  have h10 : ‖star x₁*y₀‖ ≤ 6*Real.sqrt l := by
    rw [← Unitization.norm_inr (𝕜 := ℂ) (star x₁*y₀),Unitization.inr_mul,Unitization.inr_star,hx₁,hy₀,hC₁]
    simpa only [← hXu] using hcols.2.1
  have h01 : ‖star x₀*y₁‖ ≤ 6*Real.sqrt l := by
    rw [← Unitization.norm_inr (𝕜 := ℂ) (star x₀*y₁),Unitization.inr_mul,Unitization.inr_star,hx₀,hy₁,hC₂]
    simpa only [← hXu] using hcols.2.2.1
  have h11 : star x₁*y₁=0 := by
    apply Unitization.inr_injective (R := ℂ)
    rw [Unitization.inr_mul,Unitization.inr_star,hx₁,hy₁,hC₁,hC₂,Unitization.inr_zero]
    simpa only [← hXu] using hcols.2.2.2
  let K₁ : B := star (Xu*cfc (separationK l) T)
  let K₂ : B := cfc (separationJ l) T
  have hK₁ : ‖K₁‖ ≤ (Real.sqrt l)⁻¹ := by
    rw [norm_star]
    exact norm_separation_coverage_factor Xu hXn hl
  have hK₂ : ‖K₂‖ ≤ (Real.sqrt l)⁻¹ := norm_separationJ Xu hXn hl (by linarith)
  have haeq : (a : B)=(x₀ : B)+((C₁ : B)*(N₀ : B))*K₁ := by
    rw [hx₀,hC₁,hN₀]
    rw [separation_first_coverage_identity (a : B) Xu hl]
    exact separation_LN_decomposition (a : B) S (IsSelfAdjoint.mul_star_self Xu) l
  have hbeq : (b : B)=(y₀ : B)+((C₂ : B)*(N₀ : B))*K₂ := by
    rw [hy₀,hC₂,hN₀]
    rw [separation_second_coverage_identity (b : B) Xu hl]
    exact separation_LN_decomposition (b : B) T (IsSelfAdjoint.star_mul_self Xu) l
  have hcoverage₁ := separation_transferred_coverage a x₀ x₁ C₁ N₀ K₁ F₁ ((C₁ : B)*Z*(e : B))
    hr hl (rfl : τ=r*Real.sqrt l/8) (by linarith : σ/16 ≤ 4) haeq hx₁ hK₁ hF₁
    (fun H π hπ => by
      have ht := htest₁ H π hπ
      simpa only [mul_assoc] using ht)
  have hcoverage₂ := separation_transferred_coverage b y₀ y₁ C₂ N₀ K₂ F₂ ((C₂ : B)*W*(f : B))
    hr hl (rfl : τ=r*Real.sqrt l/8) (by nlinarith : σ^2/128 ≤ 4) hbeq hy₁ hK₂ hF₂
    (fun H π hπ => by
      have ht := htest₂ H π hπ
      simpa only [mul_assoc] using ht)
  exact separatingPositives_of_four_columns a b x₀ x₁ y₀ y₁ ha hb hr hl hl1 hσ hσ1
    hx₀mem hx₁mem hy₀mem hy₁mem h00 h10 h01 h11 hcoverage₁ hcoverage₂

theorem exists_quantitative_separatingPositives_one (hA : Exact A)
    (hpi : ∀ a : A,0 ≤ a → ProperlyInfinite (diagonalCopies 1 a)) :
    ∃ σ : ℝ,0 < σ ∧ σ < 1 ∧ QuantitativeSeparatingPositives A σ := by
  obtain ⟨σ,hσ,hσ1,hpert⟩ := exists_uniformPerturbationOne A hA hpi
  exact ⟨σ,hσ,hσ1,quantitative_separatingPositives_one hpi hσ hσ1 hpert⟩

end

end

end WeakPureInfiniteness
end

end OAI
