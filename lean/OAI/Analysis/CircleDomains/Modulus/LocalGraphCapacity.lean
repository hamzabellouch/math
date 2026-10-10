import OAI.Analysis.CircleDomains.Modulus.UnitGraphCapacity
import OAI.Analysis.CircleDomains.Selection.ScaledGraphCover
import OAI.Analysis.CircleDomains.Sobolev.RescaledBandEnergy

namespace OAI

/-! An actual compact Sobolev graph has a small-diameter local cover.
Its cost is paid by the original energy in the enlarged graph cylinder. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma local_graph_capacity_cover {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (hsu : HasCompactSupport u)
    (a : EuclideanPlane) (t : ℝ) {s : ℝ} (hs : 0 < s)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y, ‖deriv scalarCapacityBump y‖ ≤ C)
    (hηd : ∀ y, ‖fderiv ℝ spatialCapacityBump y‖ ≤ C)
    {A : Set (ℝ × ℝ)} (hA : A ⊆ closedBall 0 1)
    (hband : ∀ p ∈ A, |u (a+s • euclideanPlaneCoordinates.symm p)-t| ≤ s) :
    ∃ (U : Set (ℝ × ℝ)) (N : U → ℕ)
      (T : (x : U) → Fin (N x) → Set ((ℝ × ℝ) × ℝ)),
      U.Countable ∧
      (fun p => (euclideanPlaneCoordinates (a+s • euclideanPlaneCoordinates.symm p),
        u (a+s • euclideanPlaneCoordinates.symm p))) '' A ⊆ ⋃ x : U, ⋃ j, T x j ∧
      (∀ x j, ediam (T x j) ≤ ENNReal.ofReal (8*s)) ∧
      (∑' x : U, ∑' j : Fin (N x), ediam (T x j)^2) ≤
        4194304 * ENNReal.ofReal (1+8*C^2) *
          ∫⁻ y in {y : EuclideanPlane | ‖y-a‖ ≤ 4*s ∧ |u y-t| ≤ 2*s},
            ENNReal.ofReal (1+(|W.weakGrad y 0|+|W.weakGrad y 1|)^2) := by
  let w := fun x => spatialCapacityBump x * scalarCapacityBump ((u (a+s • x)-t)/s)
  let Q := rescaledBandWitness hu W hsu a t hs hC
  have hw : Continuous w := spatialCapacityBump.continuous.mul
    (scalarCapacityBump.continuous.comp
      ((hu.comp (planarAffineHomeomorph a s hs.ne').continuous).sub continuous_const |>.div_const s))
  have hwLp : MemLp (fun p => w (euclideanPlaneCoordinates.symm p)) 2 volume :=
    (show MemLp w 2 volume by simpa only [Measure.restrict_univ] using Q.memLp).comp_measurePreserving
      euclideanPlaneCoordinates_symm_measurePreserving
  let f := fun p => (u (a+s • euclideanPlaneCoordinates.symm p)-t)/s
  have hone (p) (hp : p ∈ A) : 1 ≤ w (euclideanPlaneCoordinates.symm p) := by
    have h := rescaledBandWitness_one a t hs (by simpa using hA hp) (hband p hp)
    exact le_of_eq h.symm
  have hfb (p) (hp : p ∈ A) : f p ∈ Icc (0-1) (0+1) := by
    have habs : |f p| ≤ 1 := by
      rw [abs_div,abs_of_pos hs,div_le_one hs]
      exact hband p hp
    simpa only [mem_Icc, zero_sub, zero_add] using abs_le.mp habs
  have hQLp (R : ℝ) (i : Fin 2) : MemLp (fun x => Q.weakGrad x i) 2 (volume.restrict (ball 0 R)) :=
    (show MemLp (fun x => Q.weakGrad x i) 2 volume by
      simpa only [Measure.restrict_univ] using Q.weakGrad_component_memLp i).restrict _
  obtain ⟨U,N,T,hU,hcover,hdiam,hcost⟩ := unit_graph_capacity_cover hw Q.isWeakGrad hQLp
    hwLp hA hone f 0 hfb
  have : Countable U := hU.to_subtype
  let S : (Σ x : U, Fin (N x)) → Set ((ℝ × ℝ) × ℝ) := fun p => T p.1 p.2
  have hcoverS : (fun p => (p,f p)) '' A ⊆ ⋃ j, S j := by
    simpa only [S, iUnion_sigma] using hcover
  obtain ⟨hc,hd,hcst⟩ := scaled_graph_cover (D := 8) S (euclideanPlaneCoordinates a) t hs
    (by simpa using fun p : Σ x : U, Fin (N x) => hdiam p.1 p.2) hcoverS
  refine ⟨U,N,fun x j => graphAffine (euclideanPlaneCoordinates a) t s '' T x j,hU,?_,?_,?_⟩
  · have himage : (fun p => (euclideanPlaneCoordinates (a+s • euclideanPlaneCoordinates.symm p),
        u (a+s • euclideanPlaneCoordinates.symm p))) '' A =
      graphAffine (euclideanPlaneCoordinates a) t s '' ((fun p => (p,f p)) '' A) := by
      rw [image_image]
      congr 1
      funext p
      apply Prod.ext
      · simp only [graphAffine, map_add, map_smul, ContinuousLinearEquiv.apply_symm_apply]
      · dsimp only [graphAffine,comp_apply,f]
        field_simp [hs.ne']
        ring
    rw [himage]
    simpa only [S,iUnion_sigma] using hc
  · intro x j
    have h := hd ⟨x,j⟩
    simpa only [S,mul_comm s 8] using h
  · have hcst' := hcst
    rw [ENNReal.tsum_sigma', ENNReal.tsum_sigma'] at hcst'
    calc
      _ ≤ ENNReal.ofReal (s^2) * ∑' x : U, ∑' j : Fin (N x), ediam (T x j)^2 := hcst'
      _ ≤ ENNReal.ofReal (s^2) * (4194304 *
          (ENNReal.ofReal (∫ p, (w (euclideanPlaneCoordinates.symm p))^2) +
            coordinateSobolevEnergy Q.weakGrad univ)) := mul_le_mul' le_rfl hcost
      _ = 4194304 * (ENNReal.ofReal (s^2) *
          (ENNReal.ofReal (∫ p, (w (euclideanPlaneCoordinates.symm p))^2) +
            coordinateSobolevEnergy Q.weakGrad univ)) := by ring
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul' (show (4194304:ℝ≥0∞) ≤ 4194304 from le_rfl)
          (rescaled_band_energy_payment hu W hsu a t hs hC0 hC hηd)

end CircleDomainRigidity

end

end OAI
