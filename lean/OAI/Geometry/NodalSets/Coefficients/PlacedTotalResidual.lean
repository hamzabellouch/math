import OAI.Geometry.NodalSets.Charts.FixedChartSeedSupport
import OAI.Geometry.NodalSets.Coefficients.PlacedRandomResidual
import OAI.Geometry.NodalSets.Coefficients.PlacedSeedResidual

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Yau.Probability Set Metric Filter
open scoped ContDiff Topology
noncomputable section

theorem PlacedEnvelopeData.seeded_residual_of_seed_support {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ}
    {r a : ℝ} {K : Set Coord} {T : ℝ} (d : PlacedEnvelopeData g r a K T)
    (ha : 0 ≤ a) (hK : IsCompact K)
    (hg : ContDiffOn ℝ ∞ g seedCoordBranch)
    (hs : ∀ x ∈ seedCoordBranch, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ seedCoordBranch, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : Coord → ℝ) (hw : ContDiffOn ℝ ∞ w seedCoordBranch)
    (hwp : ∀ x ∈ seedCoordBranch, 0 < w x)
    (hseedSupport : ∀ n, tsupport (realSourceResidual g w (seedEigenvalue n)
      (seedCoordinateField n)) ⊆ K) (k0 K' : ℕ) :
    ∃ b : LocalCompactWaveData g w d.S (closure d.U)
        (3*(K'+3)+4*k0+6) ((K'+3)+k0+1) (K'+3) k0,
      b.E ⊆ d.V ∧ ∃ C > 0, ∃ Q : Set Coord,
        IsCompact Q ∧ Q ⊆ d.Ω ∧ closure d.U ⊆ interior Q ∧ K ⊆ interior Q ∧
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid d.U n),
          letI := hfin
          ∀ coeff : ((SourceGrid d.U n × Fin 3) × Fin 2) → ℝ,
            let v := gaussianWaveField
              (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff
            let u := fun x ↦ seedCoordinateField n x+v x
            let R := realSourceResidual g w (seedEigenvalue n)
            ContDiff ℝ ∞ u ∧
            R u = (fun x ↦ R (seedCoordinateField n) x+R v x) ∧
            tsupport (R u) ⊆ Q ∧
            (∀ x ∉ Q, ∀ k : ℕ, iteratedFDeriv ℝ k (R u) x = 0) ∧
            (coeff ∈ coefficientEvent (n:ℝ) → ∀ x : Coord,
              DerivativeBound k0 (R u) x
                (C*(n:ℝ)^(-(K':ℝ))*Real.exp ((n:ℝ)*d.S x))) := by
  obtain ⟨b,hb,C,hC,Q,hQ,hQΩ,hUQ,hrandom⟩ := d.random_residual ha hg hs hp w hw hwp k0 K'
  have hKU : K ⊆ closure d.U := fun x hx ↦ subset_closure (d.C_U (d.inner_C (Or.inr hx)))
  have hKB : K ⊆ seedCoordBranch := hKU.trans d.closure_U_branch
  have hQB : Q ⊆ seedCoordBranch := hQΩ.trans (subset_closure.trans
    (d.closure_Ω_patch.trans (subset_closure.trans (d.patch_V.trans d.V_branch))))
  have hseed := d.seed_residual ha hK hg hs hp w hw hwp k0 K' (show (0:ℝ)<1 by norm_num)
  refine ⟨b,hb,1+C,by linarith,Q,hQ,hQΩ,hUQ,hKU.trans hUQ,?_⟩
  filter_upwards [hrandom,hseed,b.estimates] with n hn hsn hbn
  obtain ⟨hfin,hn⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro coeff
  let V := fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2
  let v := gaussianWaveField V coeff
  let u := fun x ↦ seedCoordinateField n x+v x
  let R := realSourceResidual g w (seedEigenvalue n)
  have hV (i : SourceGrid d.U n × Fin 3) : ContDiff ℝ ∞ (V i) :=
    (hbn (latticeFrame b.cover subset_closure n i.1,i.2)).1
  have hv : ContDiff ℝ ∞ v := gaussianWaveField_contDiff V coeff hV
  have hsmooth := seedCoordinateField_smooth n
  have hlam : (seedEigenvalue n:ℂ) = (4:ℂ)*(n:ℂ)^2+6*(n:ℂ) := by
    simp [seedEigenvalue]
  have hr := hn coeff
  have hvs : tsupport v ⊆ Q := hr.1
  have he : R u = fun x ↦ R (seedCoordinateField n) x+R v x :=
    realSourceResidual_add_supported seedCoordBranch_open g hg hs hp w hw hwp
      (seedEigenvalue n) _ v hsmooth hv (hvs.trans hQB)
  have hRs : tsupport (R (seedCoordinateField n)) ⊆ Q :=
    (hseedSupport n).trans (hKU.trans (hUQ.trans interior_subset))
  have hRv : tsupport (R v) ⊆ Q := by
    dsimp only [R]
    unfold realSourceResidual
    simpa only [← hlam] using hr.2.1
  have htotal : tsupport (R u) ⊆ Q := by
    apply closure_minimal _ hQ.isClosed
    intro x hx
    by_contra hxQ
    apply hx
    simp only [he]
    rw [image_eq_zero_of_notMem_tsupport (fun hz ↦ hxQ (hRs hz)),
      image_eq_zero_of_notMem_tsupport (fun hz ↦ hxQ (hRv hz)),add_zero]
  change ContDiff ℝ ∞ u ∧ _
  refine ⟨hsmooth.add hv,he,htotal,?_,?_⟩
  · intro x hx k
    exact iteratedFDeriv_zero_off_tsupport htotal hx k
  · intro hc x
    by_cases hx : x ∈ K
    ·
      have hsb : DerivativeBound k0 (R (seedCoordinateField n)) x
          ((n:ℝ)^(-(K':ℝ))*Real.exp ((n:ℝ)*d.S x)) := by
        dsimp only [R]
        unfold realSourceResidual
        simpa only [one_mul] using hsn x hx
      have hrb : DerivativeBound k0 (R v) x
          (C*(n:ℝ)^(-(K':ℝ))*Real.exp ((n:ℝ)*d.S x)) := by
        dsimp only [R]
        unfold realSourceResidual
        simpa only [← hlam] using (hr.2.2.2 hc).2 x
      have h := realSourceResidual_add_bound seedCoordBranch_open g hg hs hp w hw hwp
        (seedEigenvalue n) _ v hsmooth hv (hvs.trans hQB) (hKB hx) k0 _ _ hsb hrb
      convert h using 1
      first | rfl | ring
    · have hz : R (seedCoordinateField n) =ᶠ[𝓝 x] (fun _ ↦ 0) :=
        notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hx (hseedSupport n h))
      have heq : R u =ᶠ[𝓝 x] R v := by
        filter_upwards [hz] with z hz
        simp only [he,hz,zero_add]
      have hrb : DerivativeBound k0 (R v) x
          (C*(n:ℝ)^(-(K':ℝ))*Real.exp ((n:ℝ)*d.S x)) := by
        dsimp only [R]
        unfold realSourceResidual
        simpa only [← hlam] using (hr.2.2.2 hc).2 x
      intro j hj
      rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
      apply (hrb j hj).trans
      gcongr
      linarith

end
end Yau.Target

end OAI
