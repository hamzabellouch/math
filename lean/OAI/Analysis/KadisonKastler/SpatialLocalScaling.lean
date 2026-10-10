import OAI.Analysis.KadisonKastler.LocalScalingCentrality
import OAI.Analysis.KadisonKastler.SpatialRightScaling
import OAI.Analysis.KadisonKastler.PointedMatrixSum

namespace OAI

/-! # Remote scaling in an arbitrary spatial product

Finite matrix stages are used only in the second leg. The first algebra
is arbitrary and retains its original cyclic separating representation.
-/

namespace KadisonKastler

open Generator UnitalTomsWinter Filter
open scoped Topology BigOperators

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def spatialRightAlgebraHom (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K) :
    Algebra N →⋆ₐ[ℂ] Algebra (spatialProductAlgebra M N) :=
  (spatialRight.comp N.toStarSubalgebra.subtype).codRestrict _
    (fun a => spatialRight_mem_product M N a.property)

theorem spatialMatrix_commutes_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : VonNeumannAlgebra H) (E : MatrixUnitSystem ι (K →L[ℂ] K))
    (v : K →L[ℂ] K) (hv : ∀ i j, Commute (E.entry i j) v)
    (b : spatialMatrixAlgebra M E) : Commute b.val (spatialRight (H := H) v) := by
  obtain ⟨X,hX⟩ := b.property
  change Commute b.val (spatialTensorOp 1 v)
  rw [← hX]
  change Commute (spatialMatrixAlgebraHom M E X) (spatialTensorOp 1 v)
  rw [spatialMatrixAlgebraHom_apply]
  apply Commute.sum_left
  intro i _
  apply Commute.sum_left
  intro j _
  change spatialTensorOp (X i j).val (E.entry i j)*spatialTensorOp 1 v =
    spatialTensorOp 1 v*spatialTensorOp (X i j).val (E.entry i j)
  rw [← spatialTensorOp_mul,← spatialTensorOp_mul,mul_one,one_mul,(hv i j).eq]

namespace PointedMatrixSites

variable {N : VonNeumannAlgebra K} {ξ : K}
  (S : PointedMatrixSites N ξ twoRatioSiteParameter)
  (M : VonNeumannAlgebra H) (Ω : H)

theorem spatialMatrix_reference_approximation (a : Algebra (spatialProductAlgebra M N))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k, ∃ b : spatialMatrixAlgebra M (S.twoRatioMatrix k),
      ‖a.val (tensorVector ξ Ω)-b.val (tensorVector ξ Ω)‖ < ε := by
  let B (n : ℕ) := spatialMatrixAlgebra M (S.twoRatioMatrix n)
  have hmono : Monotone B := fun i j hij =>
    spatialMatrixAlgebra_mono M _ _ (S.twoRatioMatrix_increasing hij)
  have hgen : generatedVonNeumannAlgebra (⨆ n, B n)=spatialProductAlgebra M N := by
    rw [generated_spatialMatrixAlgebra_eq_product M S.twoRatioMatrix
      publishedKaplanskyDensity S.twoRatioMatrix_increasing,S.twoRatioMatrix_generates]
  have ham : a.val ∈ Set.centralizer (Set.centralizer
      ((⨆ n, B n : StarSubalgebra ℂ (SpatialHilbert H K →L[ℂ] SpatialHilbert H K)) : Set _)) := by
    rw [← generatedVonNeumannAlgebra_coe,hgen]
    exact a.property
  obtain ⟨b,hb⟩ := Generator.bicommutant_finite_strong_approximation
    (⨆ n, B n) a.val ham {tensorVector ξ Ω} ε hε
  have hbm : b.val ∈ ⋃ n, (B n : Set _) := by
    rw [← StarSubalgebra.coe_iSup_of_directed hmono.directed_le]
    exact b.property
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hbm
  refine ⟨n,⟨b.val,hn⟩,?_⟩
  simpa only [norm_sub_rev] using hb (tensorVector ξ Ω) (Finset.mem_singleton_self _)

theorem spatial_remote_commutator_tendsto
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (s : ℕ → ℝ) (v : ℕ → Algebra N)
    (hv : ∀ n, v n*star (v n)=1)
    (hs : ∀ n, StateScales N ξ (s n) (v n).val) (hs1 : ∀ n, s n ≤ 1)
    (a : Algebra (spatialProductAlgebra M N)) (η : SpatialHilbert H K) :
    Tendsto (fun n =>
      (a*spatialRightAlgebraHom M N (S.remoteCopy n (v n))-
        spatialRightAlgebraHom M N (S.remoteCopy n (v n))*a).val η) atTop (𝓝 0) := by
  let w (n : ℕ) := spatialRightAlgebraHom M N (S.remoteCopy n (v n))
  have hw (n : ℕ) : w n*star (w n)=1 := by
    simp only [w,← map_star,← map_mul,hv,map_one]
  apply local_scaling_commutator_tendsto
    (separating_spatialProduct_vector_of_separating M N Ω ξ hsep S.separating)
    (fun n => spatialMatrixAlgebra M (S.twoRatioMatrix n))
    (fun n => spatialMatrixAlgebra_le_product M N (S.twoRatioMatrix n)
      (fun i j => S.twoRatioMatrix_le n ((S.twoRatioMatrix n).entry_mem i j)))
    (fun a ε hε => S.spatialMatrix_reference_approximation M Ω a hε)
    s w hw (fun n => (S.remoteCopy_scales n (v n) (hs n)).spatialRight) hs1
    ?_ a η
  intro k b n hkn
  apply spatialMatrix_commutes_right
  intro i j
  exact S.remoteCopy_commutes_stage n (v n) ((S.twoRatioMatrix k).entry i j)
    (S.twoRatioMatrix_increasing hkn ((S.twoRatioMatrix k).entry_mem i j))

theorem spatial_remote_adjoint_commutator_tendsto
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (d : ModularConjugationData (spatialProductAlgebra M N) (tensorVector ξ Ω))
    (s : ℕ → ℝ) (v : ℕ → Algebra N)
    (hv : ∀ n, v n*star (v n)=1)
    (hs : ∀ n, StateScales N ξ (s n) (v n).val)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hcs : ∀ᶠ n in atTop, c ≤ s n)
    (a : Algebra (spatialProductAlgebra M N)) (η : SpatialHilbert H K) :
    Tendsto (fun n =>
      (a*star (spatialRightAlgebraHom M N (S.remoteCopy n (v n)))-
        star (spatialRightAlgebraHom M N (S.remoteCopy n (v n)))*a).val η)
      atTop (𝓝 0) := by
  let w (n : ℕ) := spatialRightAlgebraHom M N (S.remoteCopy n (v n))
  have hw (n : ℕ) : w n*star (w n)=1 := by
    simp only [w,← map_star,← map_mul,hv,map_one]
  apply local_scaling_adjoint_commutator_tendsto d
    (separating_spatialProduct_vector_of_separating M N Ω ξ hsep S.separating)
    (fun n => spatialMatrixAlgebra M (S.twoRatioMatrix n))
    (fun n => spatialMatrixAlgebra_le_product M N (S.twoRatioMatrix n)
      (fun i j => S.twoRatioMatrix_le n ((S.twoRatioMatrix n).entry_mem i j)))
    (fun a ε hε => S.spatialMatrix_reference_approximation M Ω a hε)
    s w hw (fun n => (S.remoteCopy_scales n (v n) (hs n)).spatialRight)
    ?_ hc hc1 hcs a η
  intro k b n hkn
  apply spatialMatrix_commutes_right
  intro i j
  exact S.remoteCopy_commutes_stage n (v n) ((S.twoRatioMatrix k).entry i j)
    (S.twoRatioMatrix_increasing hkn ((S.twoRatioMatrix k).entry_mem i j))

end PointedMatrixSites

end

end KadisonKastler

end OAI
