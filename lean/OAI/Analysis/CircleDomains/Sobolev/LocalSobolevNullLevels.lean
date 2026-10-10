import OAI.Analysis.CircleDomains.Sobolev.SobolevNullLevels
import OAI.Analysis.CircleDomains.Sobolev.LocalSobolevSmoothing
import Mathlib.Topology.Compactness.SigmaCompact

namespace OAI

/-! The zero-gradient conclusion on scalar null values is local on any
open source domain. Compact cutoffs reduce it to planar
coarea; an exhaustion covers the entire domain. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem local_sobolev_gradient_zero_on_null_values_compact
    (hcoarea : PlanarSobolevCoarea)
    {U K : Set EuclideanPlane} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (W : DeGiorgi.MemW1pWitness 2 u U)
    {N : Set ℝ} (hN : MeasurableSet N) (hNz : volume N = 0) :
    ∀ᵐ p ∂volume.restrict (K ∩ u ⁻¹' N), W.weakGrad p = 0 := by
  obtain ⟨η, V, hη, hsη, _, hsub, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK hU hKU
  have hVU : V ⊆ U := by
    intro p hp
    apply hsub
    apply subset_tsupport η
    change η p ≠ 0
    rw [hone p hp]
    exact one_ne_zero
  let w := fun p => η p*u p
  obtain ⟨Ww⟩ := exists_global_compact_cutoff_witness hU W.memW1p hη hsη hsub
  have hwK : EqOn w u K := fun p hp => by dsimp only [w]; rw [hone p (hKV hp), one_mul]
  have hsame : K ∩ w ⁻¹' N = K ∩ u ⁻¹' N := by
    ext p
    constructor <;> intro hp
    · exact ⟨hp.1, by change u p ∈ N; rw [← hwK hp.1]; exact hp.2⟩
    · exact ⟨hp.1, by change w p ∈ N; rw [hwK hp.1]; exact hp.2⟩
  have hWL (i : Fin 2) : MemLp (fun p => Ww.weakGrad p i) 2 volume := by
    simpa only [Measure.restrict_univ] using Ww.weakGrad_component_memLp i
  have hz := sobolev_gradient_zero_on_null_values hcoarea (hη.continuous.mul hu) Ww.isWeakGrad
    (fun R i => (hWL i).restrict (Metric.ball 0 R)) hK.measurableSet hK.isBounded hN hNz
  change ∀ᵐ p ∂volume.restrict (K ∩ w ⁻¹' N), Ww.weakGrad p = 0 at hz
  rw [hsame] at hz
  have hg (i : Fin 2) : (fun p => Ww.weakGrad p i) =ᵐ[volume.restrict (K ∩ u ⁻¹' N)]
      fun p => W.weakGrad p i :=
    (weakGrad_eq_on_cutoff_plateau hV hVU W Ww hone i).filter_mono
      (ae_mono (Measure.restrict_mono (inter_subset_left.trans hKV) le_rfl))
  filter_upwards [hz, hg 0, hg 1] with p hp hp0 hp1
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  funext i
  fin_cases i
  · simpa [hp] using hp0.symm
  · simpa [hp] using hp1.symm

 theorem local_sobolev_gradient_zero_on_null_values
    (hcoarea : PlanarSobolevCoarea)
    {U : Set EuclideanPlane} (hU : IsOpen U)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (W : DeGiorgi.MemW1pWitness 2 u U)
    {N : Set ℝ} (hN : MeasurableSet N) (hNz : volume N = 0) :
    ∀ᵐ p ∂volume.restrict (U ∩ u ⁻¹' N), W.weakGrad p = 0 := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let K := CompactExhaustion.choice U
  let L : ℕ → Set EuclideanPlane := fun n => Subtype.val '' K n
  have hL (n : ℕ) : IsCompact (L n) := (K.isCompact n).image continuous_subtype_val
  have hLU (n : ℕ) : L n ⊆ U := by rintro p ⟨q, _, rfl⟩; exact q.property
  have hn (n : ℕ) : ∀ᵐ p ∂volume, p ∈ L n ∩ u ⁻¹' N → W.weakGrad p = 0 :=
    (ae_restrict_iff' ((hL n).measurableSet.inter (hu.measurable hN))).mp
      (local_sobolev_gradient_zero_on_null_values_compact hcoarea hU (hL n) (hLU n) hu W hN hNz)
  rw [ae_restrict_iff' (hU.measurableSet.inter (hu.measurable hN))]
  filter_upwards [ae_all_iff.mpr hn] with p hp hpU
  obtain ⟨n, hn⟩ := K.exists_mem (⟨p, hpU.1⟩ : U)
  exact hp n ⟨⟨⟨p, hpU.1⟩, hn, rfl⟩, hpU.2⟩

end CircleDomainRigidity

end

end OAI
