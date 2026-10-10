import OAI.Analysis.TracialSplitting.TraceConvexity

namespace OAI


section

noncomputable section

open scoped ComplexOrder

open CurrentMain Pureness

namespace NuclearTrace

section Normalization

variable {A I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [Fintype I] [DecidableEq I]

lemma scalarMix_trace_sq_le (τ : TracialState A) (a : I → A)
    (T : CStarMatrix I I ℂ) (hT : ‖T‖ ≤ 1) :
    (∑ i, traceTwoNorm τ (scalarMix (CStarMatrix.ofMatrix.symm T) a i)^2) ≤
      ∑ i, traceTwoNorm τ (a i)^2 := by
  obtain ⟨S,hS⟩ := scalar_contraction_dilation T hT
  have h := scalarMix_dilation_covariance T S hS a 1
  have ht := congrArg (fun x : A => (τ.functional x).re) h
  simp only [mul_one,map_add,map_sum,Complex.add_re,Complex.re_sum,
    ← traceTwoNorm_sq] at ht
  have hn : 0 ≤ ∑ i, traceTwoNorm τ (scalarMix (CStarMatrix.ofMatrix.symm S) a i)^2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

omit [PartialOrder A] [StarOrderedRing A] [DecidableEq I] in
lemma matrixSynthesis_eq_mix (a : I → A) (T : CStarMatrix I I ℂ) :
    matrixSynthesis a T = ∑ i, star (a i)*scalarMix (CStarMatrix.ofMatrix.symm T) a i := by
  change (∑ i, ∑ j, T i j • (star (a i)*a j)) = _
  simp only [scalarMix,Finset.mul_sum,mul_smul_comm,CStarMatrix.ofMatrix_symm_apply]

omit [PartialOrder A] [StarOrderedRing A] [DecidableEq I] in
lemma scalarMix_sub (T : CStarMatrix I I ℂ) (a b : I → A) (i : I) :
    scalarMix (CStarMatrix.ofMatrix.symm T) (fun j => a j-b j) i =
      scalarMix (CStarMatrix.ofMatrix.symm T) a i -
      scalarMix (CStarMatrix.ofMatrix.symm T) b i := by
  simp only [scalarMix,smul_sub,Finset.sum_sub_distrib]

omit [DecidableEq I] in
lemma trace_pairing_sum_bound (τ : TracialState A) (u : A) (hu : ‖u‖ ≤ 1)
    (a b : I → A) :
    ‖τ.functional (u*(∑ i, star (a i)*b i))‖^2 ≤
      (∑ i, traceTwoNorm τ (a i)^2)*(∑ i, traceTwoNorm τ (b i)^2) := by
  have hb (i : I) : ‖τ.functional (u*(star (a i)*b i))‖ ≤
      traceTwoNorm τ (a i)*traceTwoNorm τ (b i) := by
    rw [← mul_assoc]
    exact (trace_norm_mul_le τ _ _).trans (by
      apply mul_le_mul_of_nonneg_right _ (traceTwoNorm_nonneg τ _)
      exact (traceTwoNorm_mul_left τ _ _).trans (by
        rw [traceTwoNorm_star]
        exact (mul_le_mul_of_nonneg_right hu (traceTwoNorm_nonneg τ _)).trans_eq (one_mul _)))
  have he : ‖τ.functional (u*(∑ i, star (a i)*b i))‖ ≤
      ∑ i, traceTwoNorm τ (a i)*traceTwoNorm τ (b i) := by
    rw [Finset.mul_sum,map_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hb i)
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun i _ =>
    mul_nonneg (traceTwoNorm_nonneg τ _) (traceTwoNorm_nonneg τ _))).mpr he |>.trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i _; exact sq_nonneg _
  · intro i _; exact sq_nonneg _
  · intro i _; rw [mul_pow]

lemma matrixSynthesis_difference_pairing (τ : TracialState A) (a b : I → A)
    (T : CStarMatrix I I ℂ) (hT : ‖T‖ ≤ 1) (u : A) (hu : ‖u‖ ≤ 1) :
    ‖τ.functional (u*(matrixSynthesis a T-matrixSynthesis b T))‖^2 ≤
      2*((∑ i, traceTwoNorm τ (a i)^2)+(∑ i, traceTwoNorm τ (b i)^2))*
        (∑ i, traceTwoNorm τ (a i-b i)^2) := by
  let d : I → A := fun i => a i-b i
  let ma := scalarMix (CStarMatrix.ofMatrix.symm T) a
  let md := scalarMix (CStarMatrix.ofMatrix.symm T) d
  have he : matrixSynthesis a T-matrixSynthesis b T =
      (∑ i, star (d i)*ma i)+(∑ i, star (b i)*md i) := by
    rw [matrixSynthesis_eq_mix,matrixSynthesis_eq_mix,← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [d,ma,md]
    rw [scalarMix_sub,star_sub]
    noncomm_ring
  have h1 := trace_pairing_sum_bound τ u hu d ma
  have h2 := trace_pairing_sum_bound τ u hu b md
  have hm1 := scalarMix_trace_sq_le τ a T hT
  have hm2 := scalarMix_trace_sq_le τ d T hT
  have hd0 : 0 ≤ ∑ i, traceTwoNorm τ (d i)^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hb0 : 0 ≤ ∑ i, traceTwoNorm τ (b i)^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hb1 := h1.trans (mul_le_mul_of_nonneg_left hm1 hd0)
  have hb2 := h2.trans (mul_le_mul_of_nonneg_left hm2 hb0)
  rw [he,mul_add,map_add]
  have hn := norm_add_le (τ.functional (u*∑ i, star (d i)*ma i))
    (τ.functional (u*∑ i, star (b i)*md i))
  have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
  dsimp [d] at hb1 hb2
  nlinarith [sq_nonneg (‖τ.functional (u*∑ i, star (d i)*ma i)‖-
    ‖τ.functional (u*∑ i, star (b i)*md i)‖)]

omit [DecidableEq I] in
lemma row_mass_nonneg (a : I → A) : 0 ≤ ∑ i, star (a i)*a i :=
  Finset.sum_nonneg fun i _ => star_mul_self_nonneg (a i)

omit [DecidableEq I] in
lemma rowNormalizer_mass (a : I → A) :
    (∑ i, star (a i*rowNormalizer (∑ j, star (a j)*a j)) *
      (a i*rowNormalizer (∑ j, star (a j)*a j))) =
    rowNormalizer (∑ j, star (a j)*a j)*(∑ j, star (a j)*a j)*
      rowNormalizer (∑ j, star (a j)*a j) := by
  have hs := (rowNormalizer_nonneg (∑ j, star (a j)*a j)).isSelfAdjoint.star_eq
  simp only [star_mul,hs,Finset.mul_sum,Finset.sum_mul,mul_assoc]

omit [DecidableEq I] in
lemma rowNormalizer_error_mass (a : I → A) :
    (∑ i, star (a i-a i*rowNormalizer (∑ j, star (a j)*a j)) *
      (a i-a i*rowNormalizer (∑ j, star (a j)*a j))) =
    (1-rowNormalizer (∑ j, star (a j)*a j))*(∑ j, star (a j)*a j)*
      (1-rowNormalizer (∑ j, star (a j)*a j)) := by
  have hs := (IsSelfAdjoint.one A).sub
    (rowNormalizer_nonneg (∑ j, star (a j)*a j)).isSelfAdjoint
  simp only [show ∀ i, a i-a i*rowNormalizer (∑ j, star (a j)*a j) =
    a i*(1-rowNormalizer (∑ j, star (a j)*a j)) from fun i => by noncomm_ring,
    star_mul,hs.star_eq,Finset.mul_sum,Finset.sum_mul,mul_assoc]

theorem rowNormalizer_pairing_bound (τ : TracialState A) (a : I → A)
    (T : CStarMatrix I I ℂ) (hT : ‖T‖ ≤ 1) (u : A) (hu : ‖u‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hmass : (τ.functional (∑ i, star (a i)*a i)).re ≤ 1+δ)
    (herr : (τ.functional (CFC.abs ((∑ i, star (a i)*a i)-1))).re ≤ δ) :
    ‖τ.functional (u*(matrixSynthesis a T-
      matrixSynthesis (fun i => a i*rowNormalizer (∑ j, star (a j)*a j)) T))‖^2 ≤
        2*(2+δ)*δ := by
  let b : A := ∑ i, star (a i)*a i
  let c := rowNormalizer b
  have hclip := rowNormalizer_bounds (row_mass_nonneg a)
  have hbc : (τ.functional (c*b*c)).re ≤ 1 := by
    have h := τ.functional.monotone (show c*b*c ≤ 1 from sub_nonneg.mp hclip.1)
    exact (Complex.le_def.mp h).1.trans_eq (by change (τ.functional 1).re = 1; rw [τ.normalized]; rfl)
  have hbd : (τ.functional ((1-c)*b*(1-c))).re ≤ δ :=
    ((Complex.le_def.mp (τ.functional.monotone hclip.2.2)).1).trans herr
  have hs1 : (∑ i, traceTwoNorm τ (a i)^2) ≤ 1+δ := by
    simpa only [traceTwoNorm_sq,← Complex.re_sum,← map_sum] using hmass
  have hs2 : (∑ i, traceTwoNorm τ (a i*c)^2) ≤ 1 := by
    simpa only [c,b,traceTwoNorm_sq,← Complex.re_sum,← map_sum,rowNormalizer_mass] using hbc
  have hs3 : (∑ i, traceTwoNorm τ (a i-a i*c)^2) ≤ δ := by
    simpa only [c,b,traceTwoNorm_sq,← Complex.re_sum,← map_sum,rowNormalizer_error_mass] using hbd
  have h := matrixSynthesis_difference_pairing τ a (fun i => a i*c) T hT u hu
  apply h.trans
  have hnon : 0 ≤ (∑ i, traceTwoNorm τ (a i)^2)+(∑ i, traceTwoNorm τ (a i*c)^2) :=
    add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)
      (Finset.sum_nonneg fun i _ => sq_nonneg _)
  apply mul_le_mul
  · linarith
  · exact hs3
  · exact Finset.sum_nonneg fun i _ => sq_nonneg _
  · positivity

end Normalization

end NuclearTrace

end

end

end OAI
