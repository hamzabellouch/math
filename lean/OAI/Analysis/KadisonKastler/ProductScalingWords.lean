import OAI.Analysis.KadisonKastler.StateScalingCoisometry

namespace OAI

/-! # Finite product words as state-scaling partial isometries

All scale ratios here come from the actual two fixed site families.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

def matrixSiteBlockScale (ν : TwoRatioSite → ℝ) :
    (l : List TwoRatioSite) → MatrixSiteBlockIndex l → MatrixSiteBlockIndex l → ℝ
  | [], _, _ => 1
  | i :: l, a, b => (twoSiteWeight (ν i) b.1 / twoSiteWeight (ν i) a.1) *
      matrixSiteBlockScale ν l a.2 b.2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω twoRatioSiteParameter)

include S

theorem site_weight_pos (i : TwoRatioSite) (a : Fin 2) :
    0 < twoSiteWeight (twoRatioSiteParameter i) a := by
  have hp := (S.valid i).1
  unfold twoSiteWeight
  split_ifs <;> positivity

theorem site_entry_mem (i : TwoRatioSite) (a b : Fin 2) : (S.site i).entry a b ∈ M := by
  have hm := subset_generatedVonNeumannAlgebra _
    ((le_iSup (fun j => (S.site j).algebra) i) ((S.site i).entry_mem a b))
  exact Eq.mpr (congrArg (fun N : VonNeumannAlgebra H =>
    (S.site i).entry a b ∈ N) S.generates) hm

theorem site_entry_scales (i : TwoRatioSite) (a b : Fin 2) :
    StateScales M Ω (twoSiteWeight (twoRatioSiteParameter i) b /
      twoSiteWeight (twoRatioSiteParameter i) a) ((S.site i).entry a b) := by
  intro x hx
  have hh := S.twoRatio_site_balance i a b x hx
  have hw : (twoSiteWeight (twoRatioSiteParameter i) a : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (S.site_weight_pos i a).ne'
  rw [Complex.ofReal_div]
  apply mul_left_cancel₀ hw
  calc
    _ = (twoSiteWeight (twoRatioSiteParameter i) b : ℂ)*
        productVectorState Ω ((S.site i).entry a b*x) := hh.symm
    _ = _ := by field_simp

theorem blockEntry_scales (l : List TwoRatioSite) (hl : l.Nodup)
    (a b : MatrixSiteBlockIndex l) :
    StateScales M Ω (matrixSiteBlockScale twoRatioSiteParameter l a b)
      (S.blockEntry l a b) := by
  induction l with
  | nil => intro x hx; simp [blockEntry,matrixSiteBlockScale]
  | cons i l ih =>
    exact (S.site_entry_scales i a.1 b.1).mul
      (ih (List.nodup_cons.mp hl).2 a.2 b.2) (S.site_entry_mem i a.1 b.1)
      (S.finiteBlock_le l (List.nodup_cons.mp hl).2
        ((S.finiteBlock l (List.nodup_cons.mp hl).2).entry_mem a.2 b.2))

theorem block_diagonal_weight_ne_zero (l : List TwoRatioSite)
    (a : MatrixSiteBlockIndex l) :
    matrixSiteBlockWeight twoRatioSiteParameter l a a ≠ 0 := by
  induction l with
  | nil => exact one_ne_zero
  | cons i l ih =>
    change (if a.1=a.1 then (twoSiteWeight (twoRatioSiteParameter i) a.1 : ℂ) else 0)*
      matrixSiteBlockWeight twoRatioSiteParameter l a.2 a.2 ≠ 0
    simp only [↓reduceIte]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (S.site_weight_pos i a.1).ne') (ih a.2)

def blockScalingPartialIsometry (l : List TwoRatioSite) (hl : l.Nodup)
    (a b : MatrixSiteBlockIndex l) : PartialIsometry M := by
  let E := S.finiteBlock l hl
  let e (r c : MatrixSiteBlockIndex l) : Algebra M :=
    ⟨E.entry r c,S.finiteBlock_le l hl (E.entry_mem r c)⟩
  refine ⟨⟨e b b,?_,?_⟩,e a b,?_⟩
  · exact Subtype.ext (E.diagonal_projection b).isIdempotentElem.eq
  · exact Subtype.ext (E.diagonal_projection b).isSelfAdjoint.star_eq
  · apply Subtype.ext
    change star (E.entry a b)*E.entry a b=E.entry b b
    simp only [E.star_entry,E.mul_entry,↓reduceIte]

theorem blockScalingPartialIsometry_nonzero (l : List TwoRatioSite) (hl : l.Nodup)
    (a b : MatrixSiteBlockIndex l) : (S.blockScalingPartialIsometry l hl a b).val ≠ 0 := by
  intro hz
  have hh := (S.blockScalingPartialIsometry l hl a b).initial
  rw [hz,star_zero,zero_mul] at hh
  have he : S.blockEntry l b b=0 := (congrArg (fun x : Algebra M => x.val) hh).symm
  have ht := S.blockEntry_moment l hl b b
  rw [he,zero_apply,inner_zero_right] at ht
  exact S.block_diagonal_weight_ne_zero l b ht.symm

theorem block_coisometry (l : List TwoRatioSite) (hl : l.Nodup)
    (a b : MatrixSiteBlockIndex l)
    (hr : 0 < matrixSiteBlockScale twoRatioSiteParameter l a b)
    (hr1 : matrixSiteBlockScale twoRatioSiteParameter l a b ≤ 1) :
    ∃ w : Algebra M, w*star w=1 ∧
      StateScales M Ω (matrixSiteBlockScale twoRatioSiteParameter l a b) w.val :=
  exists_state_scaling_coisometry S.unit_vector S.separating S.twoRatio_centralizer_scalarCenter
    S.twoRatio_centralizer_diffuse hr hr1 (S.blockScalingPartialIsometry l hl a b)
    (S.blockEntry_scales l hl a b) (S.blockScalingPartialIsometry_nonzero l hl a b)

end PointedMatrixSites

end

end KadisonKastler

end OAI
