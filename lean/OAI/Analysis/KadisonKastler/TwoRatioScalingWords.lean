import OAI.Analysis.KadisonKastler.ProductScalingWords

namespace OAI

/-! # Integer powers of the two fixed state-scaling ratios

Distinct finite sites realize each ratio `lambda^k * mu^l` exactly.
-/

namespace KadisonKastler

noncomputable section

def signedSiteRow (k : ℤ) : Fin 2 := if k < 0 then 1 else 0
def signedSiteColumn (k : ℤ) : Fin 2 := if k < 0 then 0 else 1
def signedSiteScale (ν : ℝ) (k : ℤ) : ℝ := if k < 0 then ν⁻¹ else ν

theorem signed_site_weight_ratio {ν : ℝ} (hν : 0 < ν) (k : ℤ) :
    twoSiteWeight ν (signedSiteColumn k) / twoSiteWeight ν (signedSiteRow k) =
      signedSiteScale ν k := by
  have hden : 1+ν ≠ 0 := ne_of_gt (by linarith)
  by_cases hk : k < 0
  · simp only [signedSiteRow,signedSiteColumn,signedSiteScale,hk,↓reduceIte,twoSiteWeight]
    norm_num
    field_simp
  · simp only [signedSiteRow,signedSiteColumn,signedSiteScale,hk,↓reduceIte,twoSiteWeight]
    norm_num
    field_simp

theorem signed_site_scale_pow (ν : ℝ) (k : ℤ) :
    signedSiteScale ν k ^ k.natAbs = ν^k := by
  cases k with
  | ofNat n => simp [signedSiteScale]
  | negSucc n => simp [signedSiteScale,zpow_negSucc,inv_pow]

def twoRatioScalingSites (k l : ℤ) : List TwoRatioSite :=
  (List.range k.natAbs).map Sum.inl ++ (List.range l.natAbs).map Sum.inr

theorem twoRatioScalingSites_nodup (k l : ℤ) : (twoRatioScalingSites k l).Nodup := by
  apply List.Nodup.append
  · exact List.nodup_range.map Sum.inl_injective
  · exact List.nodup_range.map Sum.inr_injective
  · apply List.disjoint_left.mpr
    intro i hi hj
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hi
    simp at hj

def twoRatioScalingRow (k l : ℤ) : TwoRatioSite → Fin 2 :=
  Sum.elim (fun _ => signedSiteRow k) (fun _ => signedSiteRow l)

def twoRatioScalingColumn (k l : ℤ) : TwoRatioSite → Fin 2 :=
  Sum.elim (fun _ => signedSiteColumn k) (fun _ => signedSiteColumn l)

theorem matrixSiteBlockScale_ofFunction (ν : TwoRatioSite → ℝ) (l : List TwoRatioSite)
    (a b : TwoRatioSite → Fin 2) :
    matrixSiteBlockScale ν l (matrixSiteBlockIndexOfFunction l a)
      (matrixSiteBlockIndexOfFunction l b) =
      (l.map fun i => twoSiteWeight (ν i) (b i) / twoSiteWeight (ν i) (a i)).prod := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change _*matrixSiteBlockScale ν l (matrixSiteBlockIndexOfFunction l a)
      (matrixSiteBlockIndexOfFunction l b) = _
    rw [ih]
    rfl

theorem twoRatioScalingWords_scale (k l : ℤ) :
    matrixSiteBlockScale twoRatioSiteParameter (twoRatioScalingSites k l)
      (matrixSiteBlockIndexOfFunction _ (twoRatioScalingRow k l))
      (matrixSiteBlockIndexOfFunction _ (twoRatioScalingColumn k l)) =
      fixedProductLambda^k * fixedProductMu^l := by
  rw [matrixSiteBlockScale_ofFunction]
  simp only [twoRatioScalingSites,List.map_append,List.prod_append,List.map_map]
  change ((List.range k.natAbs).map (fun _ =>
    twoSiteWeight fixedProductLambda (signedSiteColumn k) /
      twoSiteWeight fixedProductLambda (signedSiteRow k))).prod *
    ((List.range l.natAbs).map (fun _ =>
    twoSiteWeight fixedProductMu (signedSiteColumn l) /
      twoSiteWeight fixedProductMu (signedSiteRow l))).prod = _
  simp_rw [signed_site_weight_ratio fixedProductLambda_pos,
    signed_site_weight_ratio fixedProductMu_pos]
  simp only [List.map_const',List.length_range,List.prod_replicate]
  rw [signed_site_scale_pow,signed_site_scale_pow]

open Generator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

theorem PointedMatrixSites.exists_twoRatio_scaling_coisometry
    (S : PointedMatrixSites M Ω twoRatioSiteParameter) (k l : ℤ)
    (hsmall : fixedProductLambda^k * fixedProductMu^l ≤ 1) :
    ∃ w : Algebra M, w*star w=1 ∧
      StateScales M Ω (fixedProductLambda^k * fixedProductMu^l) w.val := by
  have hr : 0 < fixedProductLambda^k * fixedProductMu^l :=
    mul_pos (zpow_pos fixedProductLambda_pos k) (zpow_pos fixedProductMu_pos l)
  have h := S.block_coisometry (twoRatioScalingSites k l) (twoRatioScalingSites_nodup k l)
    (matrixSiteBlockIndexOfFunction _ (twoRatioScalingRow k l))
    (matrixSiteBlockIndexOfFunction _ (twoRatioScalingColumn k l))
  rw [twoRatioScalingWords_scale] at h
  exact h hr hsmall

end

end KadisonKastler

end OAI
