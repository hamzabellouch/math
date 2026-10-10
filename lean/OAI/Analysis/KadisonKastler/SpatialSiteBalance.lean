import OAI.Analysis.KadisonKastler.ModularSiteEigen
import OAI.Analysis.KadisonKastler.SpatialProductState

namespace OAI

/-! # Modular site eigenoperators on the second spatial tensor leg

Only the two site eigenoperators needed in the factor proof are transported.
No general tensor-product formula for modular groups is assumed.
-/

namespace KadisonKastler

open UnitalTomsWinter Generator

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem spatialRight_weightedStateBalance
    (hK : PublishedKaplanskyDensity.{u}) (M : VonNeumannAlgebra H)
    (P : ProductMatrixStages (H := K)) (Ω : H) (u : K →L[ℂ] K) (r : ℂ)
    (hbal : ∀ b ∈ P.algebra, productVectorState P.vector (b * u) =
      r * productVectorState P.vector (u * b)) :
    ∀ x ∈ spatialProductAlgebra M P.algebra,
      productVectorState (tensorVector P.vector Ω) (x * spatialRight u) =
        r * productVectorState (tensorVector P.vector Ω) (spatialRight u * x) := by
  rw [show P.algebra = generatedVonNeumannAlgebra (⨆ n, (P.matrix n).algebra) from rfl,
    ← generated_spatialMatrixAlgebra_eq_product M P.matrix hK P.increasing]
  intro x hx
  have h := weighted_productState_generated (⨆ n, spatialMatrixAlgebra M (P.matrix n))
    (tensorVector P.vector Ω) (spatialRight u) r 1 ?_ x hx
  · simpa only [one_mul] using h.symm
  intro y hy
  have hmono : Monotone (fun n => spatialMatrixAlgebra M (P.matrix n)) :=
    fun i j hij => spatialMatrixAlgebra_mono M _ _ (P.increasing hij)
  have hym : y ∈ ⋃ n, (spatialMatrixAlgebra M (P.matrix n) : Set _) := by
    rw [← StarSubalgebra.coe_iSup_of_directed hmono.directed_le]
    exact hy
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hym
  obtain ⟨X, rfl⟩ := hn
  let φ := productVectorLinear (tensorVector P.vector Ω)
  change r * φ (spatialRight u * spatialMatrixAlgebraHom M (P.matrix n) X) =
    1 * φ (spatialMatrixAlgebraHom M (P.matrix n) X * spatialRight u)
  rw [spatialMatrixAlgebraHom_apply]
  simp only [Finset.mul_sum, Finset.sum_mul, map_sum, one_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change r * productVectorState (tensorVector P.vector Ω)
      (spatialTensorOp 1 u * spatialTensorOp (X i j).val ((P.matrix n).entry i j)) =
    productVectorState (tensorVector P.vector Ω)
      (spatialTensorOp (X i j).val ((P.matrix n).entry i j) * spatialTensorOp 1 u)
  rw [← spatialTensorOp_mul, ← spatialTensorOp_mul, one_mul, mul_one,
    productVectorState_spatialTensor, productVectorState_spatialTensor,
    hbal _ (P.local_le n ((P.matrix n).entry_mem i j))]
  ring

theorem PointedMatrixSites.twoRatio_site_spatial_modular_star_eigen
    (hK : PublishedKaplanskyDensity.{u}) (M : VonNeumannAlgebra H)
    (P : ProductMatrixStages (H := K)) (Ω : H)
    (S : PointedMatrixSites P.algebra P.vector twoRatioSiteParameter)
    (hsep : Function.Injective (algebraVectorMap (spatialProductAlgebra M P.algebra)
      (tensorVector P.vector Ω)))
    (m : ModularSpectralResolution (spatialProductAlgebra M P.algebra) (tensorVector P.vector Ω))
    (i : TwoRatioSite) (t : ℝ) :
    unitaryConj (star (m.group (Multiplicative.ofAdd t)))
        (spatialRight (H := H) ((S.site i).entry 0 1)) =
      regularCharacterScalar (Real.log (twoRatioSiteParameter i)) t •
        spatialRight (H := H) ((S.site i).entry 0 1) := by
  have hν := S.valid i
  have hb : ∀ y ∈ P.algebra, productVectorState P.vector (y * (S.site i).entry 0 1) =
      (twoRatioSiteParameter i : ℂ) * productVectorState P.vector ((S.site i).entry 0 1 * y) := by
    intro y hy
    have h := S.twoRatio_site_balance i 0 1 y hy
    have hw : (twoSiteWeight (twoRatioSiteParameter i) 0 : ℂ) ≠ 0 := by
      apply Complex.ofReal_ne_zero.mpr
      simp only [twoSiteWeight, ite_true, ne_eq, inv_eq_zero]
      linarith [hν.1]
    have hw₁ : (twoSiteWeight (twoRatioSiteParameter i) 1 : ℂ) =
        (twoRatioSiteParameter i : ℂ) * (twoSiteWeight (twoRatioSiteParameter i) 0 : ℂ) := by
      simp [twoSiteWeight, div_eq_mul_inv]
    rw [hw₁] at h
    apply mul_left_cancel₀ hw
    calc
      _ = ((twoRatioSiteParameter i : ℂ) * (twoSiteWeight (twoRatioSiteParameter i) 0 : ℂ)) *
          productVectorState P.vector ((S.site i).entry 0 1 * y) := h.symm
      _ = _ := by ring
  have hsp := spatialRight_weightedStateBalance hK M P Ω ((S.site i).entry 0 1) _ hb
  have hx := spatialRight_mem_product M P.algebra
    (S.twoRatio_site_algebra_le i ((S.site i).entry_mem 0 1))
  have he := modular_eigen_of_state_balance m hsep _ hx (-Real.log (twoRatioSiteParameter i))
    (neg_nonneg.mpr (Real.log_nonpos hν.1.le hν.2.le))
    (by simpa only [neg_neg, Real.exp_log hν.1] using hsp) (-t)
  rw [regularGroup_star_eq]
  convert he using 1
  congr 2
  rw [regularCharacterScalar, Circle.coe_exp]
  congr 1
  push_cast
  ring

end

end KadisonKastler

end OAI
