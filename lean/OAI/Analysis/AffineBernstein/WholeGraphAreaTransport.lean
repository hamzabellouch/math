import Mathlib
import OAI.Analysis.AffineBernstein.AffineGaussSurjectivity
import OAI.Analysis.AffineBernstein.SphericalAreaContinuity
import OAI.Analysis.AffineBernstein.ProductAreaChart
import OAI.Analysis.AffineBernstein.FlatGraphCoverage

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section WholeGraphAreaTransport
variable {S E F : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Full graph-area transport above a regular fiber base. The loss is a fixed
finite chart multiplicity, chosen before every varying epigraph and affine map.
No surjectivity or area transport law is assumed. -/
theorem affineEpigraph_whole_graph_area_bound {n : ℕ}
    (bS : OrthonormalBasis ι ℝ S) (bF : OrthonormalBasis κ ℝ F)
    (bRef : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (e : Fin n ≃ ι ⊕ κ) :
    ∃ C > 0, ∀ {Ω : Set (Space n)}, IsOpen Ω → Convex ℝ Ω →
    ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω →
    (∀ x ∈ Ω, (hessian u x).PosDef) →
    ∀ (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
      {D : Set S}, IsOpen D →
    (∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) →
    (∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) →
    ∀ {Q : Set S}, MeasurableSet Q → Q ⊆ D →
    ∀ {K : Set (Space n)}, K ⊆ Ω →
    (∀ x ∈ K, (L.symm ((x,u x)-a)).1 ∈ Q) →
    let eA := (Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc ι κ Unit)
    let b := (bS.toBasis.prod bRef.toBasis).reindex eA.symm
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
    ENNReal.ofReal (Real.rpow |b.det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
      ((n:ℝ)/((n:ℝ)+2))) *
        (∫⁻ x in K, ENNReal.ofReal (affineAreaDensity u x)) ≤
    ENNReal.ofReal C * (∫⁻ s in Q, ∫⁻ v : Metric.sphere (0:E) 1,
      ENNReal.ofReal (Real.rpow (tubeBaseMatrix H (s,v) bS.toBasis).det δ *
        Real.rpow (tubeAngularDensity H (s,v) bRef) (1-δ)) ∂volume.toSphere) := by
  let J := (κ ⊕ Unit) × Bool
  let frame : J → WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E := signedProjectiveFrame bRef f
  let eA := (Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc ι κ Unit)
  let b := (bS.toBasis.prod bRef.toBasis).reindex eA.symm
  let bj (j : J) := (bS.toBasis.prod (flatProductFiberBasis bF (frame j)).toBasis).reindex eA.symm
  let d (j : J) : ℝ := Real.rpow |b.det (bj j)| ((n:ℝ)/((n:ℝ)+2))
  let C : ℝ := 1 + ∑ j, d j
  have hd (j : J) : 0 ≤ d j := Real.rpow_nonneg (abs_nonneg _) _
  have hC : 0 < C := by
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun j _ => hd j))
  refine ⟨C,hC,?_⟩
  intro Ω hΩ hcv u hu hp a L D hD hK hzero Q hQ hQD K hKO hKQ
  dsimp only
  let Z := flatProductCoordinates bS bF e
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
  let A : ℝ≥0∞ := ∫⁻ s in Q, ∫⁻ v : Metric.sphere (0:E) 1,
    ENNReal.ofReal (Real.rpow (tubeBaseMatrix H (s,v) bS.toBasis).det δ *
      Real.rpow (tubeAngularDensity H (s,v) bRef) (1-δ)) ∂volume.toSphere
  let Dref : ℝ := Real.rpow |b.det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
    ((n:ℝ)/((n:ℝ)+2))
  let Dj (j : J) : ℝ := Real.rpow |(bj j).det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
    ((n:ℝ)/((n:ℝ)+2))
  have hdet (j : J) : Dref = d j * Dj j := by
    dsimp only [Dref,d,Dj]
    rw [← b.det_mul_det (bj j),abs_mul]
    simp only [Real.rpow_eq_pow]
    exact Real.mul_rpow (abs_nonneg _) (abs_nonneg _)
  choose φ hsource htarget hφ harea using fun j : J =>
    affineEpigraph_product_area_chart hΩ hcv hu hp a L hD hK hzero bS bF (frame j) e
  let T (j : J) := φ j '' (Z ⁻¹' (Q ×ˢ Set.univ))
  have hcover : K ⊆ ⋃ j, T j := by
    intro x hx
    let p := L.symm ((x,u x)-a)
    have hpa : a+L p = (x,u x) := by simp [p]
    have hpD : p.1 ∈ D := hQD (hKQ x hx)
    have hpΩ : (a+L (p.1,p.2)).1 ∈ Ω := by rw [Prod.mk.eta,hpa]; exact hKO hx
    have hpF : affineDefining u a L (p.1,p.2) = 0 := by
      change u (a+L p).1 - (a+L p).2 = 0
      rw [hpa]; simp
    have hg := affineEpigraph_gauss_surjective hΩ hcv hu hp a L hD hK hzero hpD hpΩ hpF
    dsimp only at hg
    obtain ⟨j,hj⟩ := signedProjectiveFrame_cover bRef f hg.1
    apply Set.mem_iUnion.mpr
    refine ⟨j,?_⟩
    have hh := flatGraphChart_covers_direction Ω u a L bS bF (frame j) e (φ j)
      (hsource j) (hφ j) hQD (hKQ x hx) hg.2 hj
    change (a+L p).1 ∈ T j at hh
    rw [hpa] at hh
    exact hh
  have hchart (j : J) : ENNReal.ofReal (Dj j) *
      (∫⁻ x in T j, ENNReal.ofReal (affineAreaDensity u x)) ≤ A := by
    rw [harea j hQ hQD]
    refine (lintegral_prod_le _).trans ?_
    apply setLIntegral_mono_ae' hQ
    filter_upwards with s hs
    have he := affineEpigraph_sphere_area_two_flat_lintegral hΩ hcv hu hp a L hD hK hzero
      (hQD hs) bS.toBasis bF bRef (frame j)
    exact (he.symm ▸ le_add_right le_rfl)
  have hchart' (j : J) : ENNReal.ofReal Dref *
      (∫⁻ x in T j, ENNReal.ofReal (affineAreaDensity u x)) ≤ ENNReal.ofReal (d j)*A := by
    rw [hdet j,ENNReal.ofReal_mul (hd j),mul_assoc]
    exact mul_le_mul_right (hchart j) _
  change ENNReal.ofReal Dref * (∫⁻ x in K, ENNReal.ofReal (affineAreaDensity u x)) ≤ ENNReal.ofReal C*A
  calc
    _ ≤ ENNReal.ofReal Dref * (∫⁻ x in ⋃ j, T j, ENNReal.ofReal (affineAreaDensity u x)) :=
      mul_le_mul_right (lintegral_mono_set hcover) _
    _ ≤ ENNReal.ofReal Dref * ∑ j, ∫⁻ x in T j, ENNReal.ofReal (affineAreaDensity u x) := by
      apply mul_le_mul_right
      simpa only [tsum_fintype] using lintegral_iUnion_le T (fun x => ENNReal.ofReal (affineAreaDensity u x))
    _ = ∑ j, ENNReal.ofReal Dref * ∫⁻ x in T j, ENNReal.ofReal (affineAreaDensity u x) := by rw [Finset.mul_sum]
    _ ≤ ∑ j, ENNReal.ofReal (d j)*A := Finset.sum_le_sum (fun j _ => hchart' j)
    _ = (∑ j, ENNReal.ofReal (d j))*A := by rw [Finset.sum_mul]
    _ ≤ ENNReal.ofReal C*A := by
      apply mul_le_mul_left
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hd j)]
      exact ENNReal.ofReal_le_ofReal (by dsimp only [C]; linarith)
end WholeGraphAreaTransport

-- ActualAreaMass

end
end AffineBernstein
end

end OAI
