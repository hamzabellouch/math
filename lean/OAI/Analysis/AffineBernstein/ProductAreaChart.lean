import Mathlib
import OAI.Analysis.AffineBernstein.GlobalFlatAreaLIntegral
import OAI.Analysis.AffineBernstein.FlatProductCoordinates

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section ProductAreaChart
variable {S E F : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Actual graph-area change of variables in a full flat projective chart,
expressed in the true product Haar measure on base times angular plane. -/
theorem affineEpigraph_product_area_chart {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bS : OrthonormalBasis ι ℝ S) (bF : OrthonormalBasis κ ℝ F)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (e : Fin n ≃ ι ⊕ κ) :
    let Z := flatProductCoordinates bS bF e
    let bE := flatProductFiberBasis bF f
    let eA := (Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc ι κ Unit)
    let b := (bS.toBasis.prod bE.toBasis).reindex eA.symm
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    ∃ φ : OpenPartialHomeomorph (Space n) (Space n),
      φ.source = {x | (Z x).1 ∈ D} ∧ φ.target ⊆ Ω ∧
      (∀ x ∈ φ.source, a+L ((Z x).1,
        gaussPoint {y | ((Z x).1,y) ∈ affineEpigraphPullback Ω u a L}
          (f (WithLp.toLp 2 ((Z x).2,(1:ℝ))))) = (φ x,u (φ x))) ∧
      ∀ {Q : Set S}, MeasurableSet Q → Q ⊆ D →
        ENNReal.ofReal (Real.rpow |b.det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
          ((n:ℝ)/((n:ℝ)+2))) *
          (∫⁻ y in φ '' (Z ⁻¹' (Q ×ˢ Set.univ)), ENNReal.ofReal (affineAreaDensity u y)) =
        (∫⁻ q : S × F, ENNReal.ofReal (tubeAreaDensity
          (tubeBaseMatrix H (q.1,f (WithLp.toLp 2 (q.2,(1:ℝ)))) bS.toBasis)
          (tubeRadiusMatrix H (q.1,f (WithLp.toLp 2 (q.2,(1:ℝ)))) bE)
          (1/((Fintype.card ι:ℝ)+Fintype.card κ+2))) ∂(volume.restrict Q).prod volume) := by
  let Z := flatProductCoordinates bS bF e
  let bE := flatProductFiberBasis bF f
  let J := (flatProductEmbedding (S:=S) f).comp Z.toContinuousLinearMap
  let q₀ : S × E := (0,f (WithLp.toLp 2 (0,(1:ℝ))))
  have hq (x : Space n) : q₀+J x = ((Z x).1,f (WithLp.toLp 2 ((Z x).2,(1:ℝ)))) :=
    flatProductEmbedding_affine f (Z x)
  have hd : inner ℝ q₀.2 (bE (Sum.inr ())) = 1 := by
    simp only [q₀,bE,flatProductFiberBasis_last,f.inner_map_map]
    simp
  have hJ : Function.Injective J := (flatProductEmbedding_injective f).comp Z.injective
  have hJvert (x : Space n) : inner ℝ (J x).2 (bE (Sum.inr ())) = 0 :=
    flatProductEmbedding_vertical bF f (Z x)
  have hJe (i : Fin n) : J (coordinateVector n i) = tubeTangent bS.toBasis bE (e i) := by
    change flatProductEmbedding f (Z (coordinateVector n i)) = _
    rw [flatProductCoordinates_basis]
    rcases e i with j | j <;> simp [tubeTangent,bE]
  obtain ⟨φ,hsource,ht,hφ,hψ,heφ,harea⟩ := affineEpigraph_flat_chart_global_area_lintegral
    hΩ hcv hu hp a L hD hK hzero q₀ bS.toBasis bE hd J hJ hJvert e hJe
  dsimp only
  refine ⟨φ,?_,ht,?_,?_⟩
  · simpa only [hq] using hsource
  · intro x hx
    simpa only [supportParam,hq] using heφ x hx
  · intro Q hQ hQD
    let T : Set (S × F) := Q ×ˢ univ
    have hT : MeasurableSet T := hQ.prod MeasurableSet.univ
    have hZT : MeasurableSet (Z ⁻¹' T) := hT.preimage Z.continuous.measurable
    have hZsource : Z ⁻¹' T ⊆ φ.source := by
      intro x hx
      rw [hsource]
      change (q₀+J x).1 ∈ D
      rw [hq]
      exact hQD hx.1
    have heq := harea (Z ⁻¹' T) hZT hZsource (fun _ => 1)
    simp only [mul_one,hq] at heq
    rw [Measure.restrict_prod_eq_prod_univ,← Measure.volume_eq_prod S F]
    rw [← (flatProductCoordinates_measurePreserving bS bF e).setLIntegral_comp_preimage_emb
      Z.toHomeomorph.measurableEmbedding]
    exact heq.symm

end ProductAreaChart

-- FiniteProjectiveCharts

end
end AffineBernstein
end

end OAI
