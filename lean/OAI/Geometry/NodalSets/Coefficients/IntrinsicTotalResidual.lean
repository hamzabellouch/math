import OAI.Geometry.NodalSets.Coefficients.PlacedTotalResidual
import OAI.Geometry.NodalSets.Elliptic.SeedDeviationCoordinates

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Yau.Probability Set Metric Filter
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section

theorem intrinsic_placed_total_residual
    (A : IntrinsicTensor) (hAs : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hrs : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    {r a : ℝ} {K : Set Base} {T : ℝ}
    (d : PlacedEnvelopeData (intrinsicSeedCoordMetric A rho) r a (seedDeviationCoordinates K) T)
    (ha : 0 ≤ a) (hK : IsCompact K)
    (hchart : K ⊆ (extChartAt (𝓡 4) seedPoint).source)
    (hA : ∀ x ∉ K, ∀ v w : AmbientBase,
      ⟪(x:AmbientBase),v⟫ = 0 → ⟪(x:AmbientBase),w⟫ = 0 →
      A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) = ⟪v,w⟫)
    (hr : ∀ x ∉ K, rho x = 1) (k0 K' : ℕ) :
    ∃ b : LocalCompactWaveData (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) d.S (closure d.U)
        (3*(K'+3)+4*k0+6) ((K'+3)+k0+1) (K'+3) k0,
      b.E ⊆ d.V ∧ ∃ C > 0, ∃ Q : Set Coord,
        IsCompact Q ∧ Q ⊆ d.Ω ∧ closure d.U ⊆ interior Q ∧ seedDeviationCoordinates K ⊆ interior Q ∧
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid d.U n),
          letI := hfin
          ∀ coeff : ((SourceGrid d.U n × Fin 3) × Fin 2) → ℝ,
            let v := gaussianWaveField
              (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff
            let u := fun x ↦ seedCoordinateField n x+v x
            let R := realSourceResidual (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) (seedEigenvalue n)
            ContDiff ℝ ∞ u ∧ ContDiff ℝ ∞ (R u) ∧
            R u = (fun x ↦ R (seedCoordinateField n) x+R v x) ∧
            tsupport (R u) ⊆ Q ∧
            (∀ x ∉ Q, ∀ k : ℕ, iteratedFDeriv ℝ k (R u) x = 0) ∧
            (coeff ∈ coefficientEvent (n:ℝ) → ∀ x : Coord,
              DerivativeBound k0 (R u) x
                (C*(n:ℝ)^(-(K':ℝ))*Real.exp ((n:ℝ)*d.S x))) := by
  have hreg := intrinsicSeedCoordMetric_regular A hAs hs hp rho hrs hrp
  have hweight := seedCoordWeight_smooth rho hrs
  have hweightp := seedCoordWeight_pos rho hrp
  have hsupport (n : ℕ) : tsupport
      (realSourceResidual (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho)
        (seedEigenvalue n) (seedCoordinateField n)) ⊆ seedDeviationCoordinates K :=
    intrinsicSeedCoord_residual_tsupport A hAs hs hp rho hrp hK.isClosed hA hr n
  obtain ⟨b,hb,C,hC,Q,hQ,hQΩ,hUQ,hKQ,hbound⟩ :=
    d.seeded_residual_of_seed_support ha (seedDeviationCoordinates_compact hK hchart)
      hreg.1.contDiffOn (fun x _ ↦ hreg.2.1 x) (fun x _ ↦ hreg.2.2 x)
      (seedCoordWeight rho) hweight.contDiffOn (fun x _ ↦ hweightp x) hsupport k0 K'
  refine ⟨b,hb,C,hC,Q,hQ,hQΩ,hUQ,hKQ,?_⟩
  filter_upwards [hbound] with n hn
  obtain ⟨hfin,hn⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro coeff
  have h := hn coeff
  refine ⟨h.1,?_,h.2⟩
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact realSourceResidual_smoothAt isOpen_univ _ hreg.1.contDiffOn
    (fun x _ ↦ hreg.2.1 x) (fun x _ ↦ hreg.2.2 x)
    _ hweight.contDiffOn (fun x _ ↦ hweightp x) _ _ h.1 (mem_univ x)

lemma derivativeBound_seed_majorant {f : Coord → ℂ} {S : Coord → ℝ} {x : Coord}
    {n k K' : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (h : DerivativeBound k f x (C*(n:ℝ)^(-(K':ℝ))*Real.exp ((n:ℝ)*S x))) :
    DerivativeBound k f x (C*(n:ℝ)^(-(K':ℝ))*
      max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*seedCoordReal x))) := by
  intro j hj
  exact (h j hj).trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity))

end
end Yau.Target

end OAI
