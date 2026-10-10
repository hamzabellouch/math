import Mathlib
import OAI.Analysis.AffineBernstein.TargetCapLIntegral
import OAI.Analysis.AffineBernstein.GlobalFlatInverseLIntegral
import OAI.Analysis.AffineBernstein.FixedBasisCoordinates

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [FiniteDimensional ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Uniform inverse-energy bound on the actual entire flat support chart. It is produced
by stationarity of the original graph, not by an assumed stationarity equation on the tube.
The constant precedes, and is independent of, the varying affine normalization `L`.
All cap-containment inputs are geometric and have their literal original-graph meanings. -/
theorem affineMaximal_uniform_flat_cap_lintegral_bound {n : ℕ}
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (e : Fin n ≃ ι ⊕ κ) {ε r R : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hR : 0 ≤ R) (t₀ t₁ c₀ : ℝ) :
    ∃ C > 0, ∀ {Ω : Set (Space n)}, IsOpen Ω → Convex ℝ Ω →
    ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω →
    (∀ x ∈ Ω, (hessian u x).PosDef) → AffineMaximalOn Ω u →
    ∀ (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
      {B : Set S}, IsOpen B →
    (∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) →
    (∀ s ∈ B, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) →
    ∀ (q₀ : S × E), inner ℝ q₀.2 (bE (Sum.inr ())) = 1 →
    ∀ (J : Space n →L[ℝ] (S × E)), Function.Injective J →
    (∀ v, inner ℝ (J v).2 (bE (Sum.inr ())) = 0) →
    (∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i)) →
    ∀ (ℓ : S →L[ℝ] ℝ) (o : Space n) (c : ℝ),
    Metric.closedBall (L.symm ((o,c)-a)) r ⊆
      (fun p => L.symm (p-a)) '' sourceEpigraph Ω u →
    ℓ (L.symm ((o,c)-a)).1 = c₀ →
    ∀ {K : Set (Space n)}, IsCompact K → K ⊆ Ω →
    (∀ x ∈ Ω, x ∉ K → t₁+ε ≤ pulledBaseGraphFunction u a L ℓ x) →
    (∀ x ∈ K, pulledBaseGraphFunction u a L ℓ x ∈ Icc t₀ (t₁+ε)) →
    (∀ x ∈ K, ‖L.symm ((x,u x)-a)‖ ≤ R) →
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    ∃ φ : OpenPartialHomeomorph (Space n) (Space n),
      φ.source = {x | (q₀+J x).1 ∈ B} ∧ φ.target ⊆ Ω ∧
      ContDiffOn ℝ ∞ φ φ.source ∧ ContDiffOn ℝ ∞ φ.symm φ.target ∧
      (∀ x ∈ φ.source, a+L (supportParam Y (q₀+J x)) = (φ x,u (φ x))) ∧
      ∀ {Q : Set (Space n)}, MeasurableSet Q → Q ⊆ φ.source →
        (∀ x ∈ Q, ℓ (q₀+J x).1 ≤ t₁-ε) →
        (∫⁻ x in Q, ENNReal.ofReal (tubeAreaDensity (tubeBaseMatrix H (q₀+J x) bS)
          (tubeRadiusMatrix H (q₀+J x) bE) (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))) *
          ENNReal.ofReal (‖supportConormal H (q₀+J x)‖ *
            inverseMatrixPair (tubeBaseMatrix H (q₀+J x) bS)
              (fun i => ℓ (bS i)) (fun i => ℓ (bS i)))) ≤ ENNReal.ofReal C := by
  let eA := (Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc ι κ Unit)
  let b := (bS.prod bE.toBasis).reindex eA.symm
  obtain ⟨C,hC,hcap⟩ := affineMaximal_uniform_target_cap_lintegral_bound n
    (targetBasisCoordinates b) hε hr hR t₀ t₁ c₀
  refine ⟨C,hC,?_⟩
  intro Ω hΩ hcv u hu hp hm a L B hB hKfib hzero q₀ hd J hi hJ hJe ℓ o c hball hcenter
    K hK hKΩ houtside hheight hbound
  let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  obtain ⟨α,β,d,hcoeff,hamb⟩ := pulledBaseGraphFunction_coefficients u a L ℓ
  obtain ⟨φ,hsource,ht,hφ,hψ,heφ,harea⟩ := affineEpigraph_flat_chart_global_inverseArea_lintegral
    hΩ hcv hu hp a L hB hKfib hzero q₀ bS bE hd J hi hJ e hJe ℓ
  change ∃ φ, _
  refine ⟨φ,hsource,ht,hφ,hψ,heφ,?_⟩
  intro Q hQ hQφ hqQ
  have hQi : MeasurableSet (φ '' Q) :=
    hQ.image_of_continuousOn_injOn (φ.continuousOn.mono hQφ) (φ.injOn.mono hQφ)
  have hpull (x : Space n) (hx : x ∈ φ.source) :
      L.symm ((φ x,u (φ x))-a) = supportParam Y (q₀+J x) := by
    apply L.injective
    rw [L.apply_symm_apply,← heφ x hx]
    abel
  have hq (x : Space n) (hx : x ∈ φ.source) :
      graphAffineFunction u α β d (φ x) = ℓ (q₀+J x).1 := by
    rw [← hcoeff]
    change ℓ (L.symm ((φ x,u (φ x))-a)).1 = _
    rw [hpull x hx]
    rfl
  have hQiΩ : φ '' Q ⊆ Ω := fun y hy => by
    obtain ⟨x,hx,rfl⟩ := hy
    exact ht (φ.map_source (hQφ hx))
  have hQiK : φ '' Q ⊆ K := by
    rintro _ ⟨x,hx,rfl⟩
    by_contra hn
    have hlo := houtside (φ x) (hQiΩ ⟨x,hx,rfl⟩) hn
    rw [hcoeff,hq x (hQφ hx)] at hlo
    linarith [hqQ x hx]
  have hbnd := hcap hΩ hcv hu hp hm L a o c α β d hball
    ((hamb (o,c)).symm.trans hcenter) hK hKΩ hQi hQiK
    (fun x hx hn => by simpa only [← hcoeff] using houtside x hx hn)
    (fun x hx => by simpa only [← hcoeff] using hheight x hx)
    (by rintro _ ⟨x,hx,rfl⟩; rw [hq x (hQφ hx)]; exact hqQ x hx)
    hbound
  rw [targetBasisCoordinates_det] at hbnd
  rw [harea Q hQ hQφ]
  convert hbnd using 1
  congr 1
  apply setLIntegral_congr_fun hQi
  intro y hy
  dsimp only
  rw [hcoeff,inverseMatrixPair_graphAffineFunction]
  change ENNReal.ofReal (affineAreaDensity u y) * ENNReal.ofReal
      (‖targetGraphConormal u L y‖ * graphInverseMetric u α β d y) = _
  exact (ENNReal.ofReal_mul (Real.rpow_nonneg (hp y (hQiΩ hy)).det_pos.le _)).symm

end AffineBernstein
end

end OAI
