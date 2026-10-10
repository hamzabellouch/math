import Mathlib
import OAI.Probability.SKGap.Gaussian.ConditionalGramTail
import OAI.Probability.SKGap.Localization.ConditionalRankAlgebra

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real
open scoped BigOperators Matrix.Norms.Frobenius

theorem goe_scalar_tail {n : ℕ} (hn : 0 < n) {j U ε : ℝ}
    (hj : 0 < j) (hU : 0 ≤ U) (hε : 0 ≤ ε)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ ≤ U) :
    (Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)).real
      {g | ε ≤ |matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u|} ≤
      2*exp (-(n:ℝ)*ε^2/(π^2*(2*(U+1)^2)^2*j)) := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have h := goe_bilinear_concentration hj (by norm_num : (0:ℝ)≤1) hU
    (by norm_num : (0:ℝ)≤0) hε (fun M => M) (fun _ _ _ => rfl)
    (fun M N => by simp) 0 (by intro i; simp [goeEntry_integral]) u u hu hu
  have hz : (diagonal (0 : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ)=0 := by
    ext i k; simp [Matrix.diagonal]
  rw [hz] at h
  simpa only [Fintype.card_fin,zero_mul,zero_add,sub_zero,
    show (1:ℝ)+1=2 by norm_num] using h
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

def conditionalBase {n : ℕ} (j : ℝ) (a : Fin n → ℝ)
    (g : MatrixCoordinates (Fin n) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1-pathDiagonal a 1*(goeMatrix (j/(n:ℝ)) g-((j/(n:ℝ))*∑ i,a i) • 1)*pathDiagonal a 1

def conditionalUpdateColumns {n : ℕ} (j : ℝ) (a : Fin n → ℝ)
    (p : Fin 3 → EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin n))
    (g : MatrixCoordinates (Fin n) → ℝ) : Matrix (Fin n) ((Fin 3) ⊕ Unit) ℝ :=
  extendColumns (fun r => (p r).ofLp)
    (residualGramVector (j/(n:ℝ)*∑ i,a i) (goeMatrix (j/(n:ℝ)) g) u.ofLp)

theorem compact_conditional_fixed_tail {α : Type*} [TopologicalSpace α] [CompactSpace α]
    {j A U : ℝ} (hj : 0 < j) (hj1 : j < 1) (hA : 0 < A)
    (hsub : sqrt j*A < 1) (hU : 0 ≤ U)
    (b e s q κ : α → ℝ) (hb : Continuous b) (he : Continuous e)
    (hs : Continuous s) (hq : Continuous q) (hk : Continuous κ)
    (hb0 : ∀ x,0 < b x) (hb1 : ∀ x,b x ≤ 1) (he0 : ∀ x,0 ≤ e x)
    (hs0 : ∀ x,0 < s x) (hq0 : ∀ x,0 < q x)
    (hkq : ∀ x,κ x^2=1-j*q x/s x) :
    ∃ δ ρ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < ρ ∧
    ∀ ε τ : ℝ, 0 < ε → 0 < τ → ∃ c : ℝ, ∃ N : ℕ, 0 < c ∧ 0 < N ∧
    ∀ n, N ≤ n → ∀ a : Fin n → ℝ, (∀ i,0 ≤ a i) → (∀ i,a i ≤ A) →
    0 < j/(n:ℝ)*∑ i,a i →
    augmentedGramTolerance (j/(n:ℝ)*∑ i,a i) ε < ρ/2 →
    ∀ p : Fin 3 → EuclideanSpace ℝ (Fin n), ∀ u : EuclideanSpace ℝ (Fin n),
    (∀ r,‖p r‖ ≤ U) → ‖u‖ ≤ U → u.ofLp⬝ᵥu.ofLp=1 →
    ∀ x (C E : Matrix ((Fin 3) ⊕ Unit) ((Fin 3) ⊕ Unit) ℝ),
    C.IsHermitian → E.IsHermitian → τ*‖E‖ < ρ/2 →
    ‖diagonalAugmentedGram a p-augmentedGram (ν := Unit) (limitingGram (b x) (e x) (s x))‖ < ρ/2 →
    ‖C-conditionalCoefficient j ((2*j*q x+2*(j*b x)*(κ x-1))/q x)
      j ((κ x-1)*√(j*b x)/√(q x))‖ < ρ/2 →
    (Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)).real
      {g | ¬(conditionalBase j a g-
        pathDiagonal a 1*conditionalUpdateColumns j a p u g*
        (C+matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u • E)*
        (conditionalUpdateColumns j a p u g)ᵀ*pathDiagonal a 1-
        (δ*((1-sqrt j*A)^2/4)) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef} ≤
      101*exp (-c*(n:ℝ)) := by
  obtain ⟨δ,ρ,hδ,hδ1,hρ,hcrit⟩ := compact_conditional_rank_criterion hj hj1 b e s q κ
    hb he hs hq hk hb0 hb1 he0 hs0 hq0 hkq
  refine ⟨δ,ρ,hδ,hδ1,hρ,?_⟩
  intro ε τ hε hτ
  obtain ⟨c₀,N,hc₀,hN,hgram⟩ := conditional_augmented_gram_tail hj hA hsub hU hε
  let c₁ := τ^2/(π^2*(2*(U+1)^2)^2*j)
  have hc₁ : 0 < c₁ := by dsimp [c₁]; positivity
  refine ⟨min c₀ c₁,N,lt_min hc₀ hc₁,hN,?_⟩
  intro n hn a ha haA hB heps p u hp hu hunit x C E hC hE hEbound hdiag hcoef
  let μ := Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)
  let badG := {g | ¬bilinearPathGood j A a g ∨
    augmentedGramTolerance (j/(n:ℝ)*∑ i,a i) ε <
      ‖actualAugmentedGram j a p u g-diagonalAugmentedGram a p‖}
  let badS := {g | τ ≤ |matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u|}
  have hnpos := hN.trans_le hn
  have hgprob : μ.real badG ≤ 99*exp (-c₀*(n:ℝ)) := hgram n hn a ha haA hB p u hp hu hunit
  have hsprob : μ.real badS ≤ 2*exp (-c₁*(n:ℝ)) := by
    have hh := goe_scalar_tail hnpos hj hU hτ.le u hu
    convert hh using 1
    congr 2
    dsimp [c₁]
    ring
  have hsubsets : {g | ¬(conditionalBase j a g-
        pathDiagonal a 1*conditionalUpdateColumns j a p u g*
        (C+matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u • E)*
        (conditionalUpdateColumns j a p u g)ᵀ*pathDiagonal a 1-
        (δ*((1-sqrt j*A)^2/4)) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef} ⊆ badG ∪ badS := by
    intro g hg
    by_contra hbad
    have hgG : g ∉ badG := fun hh => hbad (Or.inl hh)
    have hgS : g ∉ badS := fun hh => hbad (Or.inr hh)
    simp only [badG,mem_ofPred_eq,not_or,not_lt] at hgG
    have hgS' : |matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u| < τ := lt_of_not_ge hgS
    let D := pathDiagonal a 1
    let S := conditionalBase j a g
    let V := conditionalUpdateColumns j a p u g
    let Cg := C+matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u • E
    let lo := (1-sqrt j*A)^2/4
    have hmargin : (S-lo • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef :=
      bilinearPathGood_margin a g (not_not.mp hgG.1)
    have hlo : 0 ≤ lo := by dsimp [lo]; positivity
    have hSpos : S.PosDef := by
      have hh := hmargin.add_posSemidef ((Matrix.PosSemidef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosSemidef).smul hlo)
      convert hh using 1; abel
    have hD : D.IsHermitian := isHermitian_diagonal_iff.mpr
      (fun i => isSelfAdjoint_iff.mpr (star_trivial _))
    have hCg : Cg.IsHermitian := hC.add (hE.smul (R := ℝ)
      (isSelfAdjoint_iff.mpr (star_trivial _)))
    have hG : ‖Vᵀ*D*S⁻¹*D*V-augmentedGram (ν := Unit) (limitingGram (b x) (e x) (s x))‖ < ρ := by
      have hh := norm_sub_le_norm_sub_add_norm_sub (actualAugmentedGram j a p u g) (diagonalAugmentedGram a p)
        (augmentedGram (ν := Unit) (limitingGram (b x) (e x) (s x)))
      have heq : Vᵀ*D*S⁻¹*D*V=actualAugmentedGram j a p u g := by
        simp only [V,D,S,conditionalUpdateColumns,conditionalBase,actualAugmentedGram,
          exactG,Fintype.card_fin,Matrix.mul_assoc]
      rw [heq]
      exact hh.trans_lt (by linarith [hgG.2])
    have hCgclose : ‖Cg-conditionalCoefficient j ((2*j*q x+2*(j*b x)*(κ x-1))/q x)
        j ((κ x-1)*√(j*b x)/√(q x))‖ < ρ := by
      have hn : ‖matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u • E‖ ≤ τ*‖E‖ := by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hgS'.le (norm_nonneg _)
      have hh := norm_add_le (C-conditionalCoefficient j ((2*j*q x+2*(j*b x)*(κ x-1))/q x)
        j ((κ x-1)*√(j*b x)/√(q x))) (matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u • E)
      have heq : Cg-conditionalCoefficient j ((2*j*q x+2*(j*b x)*(κ x-1))/q x)
          j ((κ x-1)*√(j*b x)/√(q x))=
          (C-conditionalCoefficient j ((2*j*q x+2*(j*b x)*(κ x-1))/q x)
          j ((κ x-1)*√(j*b x)/√(q x)))+matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u • E := by
        dsimp [Cg]; abel
      rw [heq]
      exact hh.trans_lt (by linarith)
    exact hg (hcrit x (Fin n) S D V Cg lo hSpos hD hCg hmargin.posSemidef hG hCgclose)
  apply (measureReal_mono hsubsets (measure_ne_top _ _)).trans
  apply (measureReal_union_le badG badS).trans
  apply (add_le_add hgprob hsprob).trans
  have he₀ : exp (-c₀*(n:ℝ)) ≤ exp (-min c₀ c₁*(n:ℝ)) := by
    apply exp_le_exp.mpr; simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left c₀ c₁) (Nat.cast_nonneg n : (0:ℝ) ≤ n))
  have he₁ : exp (-c₁*(n:ℝ)) ≤ exp (-min c₀ c₁*(n:ℝ)) := by
    apply exp_le_exp.mpr; simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right c₀ c₁) (Nat.cast_nonneg n : (0:ℝ) ≤ n))
  nlinarith
end SKGap
end
end

end OAI
