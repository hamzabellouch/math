import OAI.Geometry.NodalSets.Elliptic.RealL2Convolution
import OAI.Geometry.NodalSets.Elliptic.RealMollifierSupport

namespace OAI

namespace Yau
open MeasureTheory Set Filter
open scoped ContDiff Convolution Topology
noncomputable section

def realSmoothCompactL2 {n : ℕ} (v : Coord n → ℝ)
    (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v) : RealEuclideanL2 n :=
  (real_compact_continuous_memLp v hv.continuous hc).toLp v

theorem realSmoothCompactL2_ae {n : ℕ} (v : Coord n → ℝ)
    (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v) :
    (realSmoothCompactL2 v hv hc : Coord n → ℝ) =ᵐ[volume] v :=
  (real_compact_continuous_memLp v hv.continuous hc).coeFn_toLp

theorem real_compact_memLp_integrable {n : ℕ} (u : Coord n → ℝ)
    (hu : MemLp u 2 volume) (hc : HasCompactSupport u) : Integrable u := by
  let : IsFiniteMeasure (volume.restrict (tsupport u)) :=
    isFiniteMeasure_restrict.mpr hc.measure_ne_top
  apply (integrableOn_iff_integrable_of_support_subset (subset_tsupport u)).mp
  exact (hu.restrict _).integrable (by norm_num)

theorem real_compact_convolution_L2_tendsto {n : ℕ} (u : Coord n → ℝ)
    (hu : MemLp u 2 volume) (hc : HasCompactSupport u)
    (b : ℕ → ContDiffBump (0 : Coord n))
    (hb : Tendsto (fun m ↦ (b m).rOut) atTop (𝓝 0)) :
    Tendsto (fun m ↦ realSmoothCompactL2 (u ⋆ (b m).normed volume)
      ((b m).hasCompactSupport_normed.contDiff_convolution_right
        (ContinuousLinearMap.lsmul ℝ ℝ) (hu.locallyIntegrable (by norm_num)) (b m).contDiff_normed)
      (hc.convolution (ContinuousLinearMap.lsmul ℝ ℝ) (b m).hasCompactSupport_normed))
      atTop (𝓝 (hu.toLp u)) := by
  have ht := realL2Convolution_normed_tendsto b hb (hu.toLp u)
  convert ht using 1
  funext m
  exact (realL2Convolution_eq_toLp u _ (real_compact_memLp_integrable u hu hc) hu
    (b m).contDiff_normed (b m).hasCompactSupport_normed _).symm

theorem real_compact_weak_H1_smooth_approximation {n : ℕ} {K L : Set (Coord n)}
    (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ interior L)
    (u : Coord n → ℝ) (g : Fin n → Coord n → ℝ)
    (hu : MemLp u 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hsu : ∀ x, x ∉ K → u x=0) (hsg : ∀ i x, x ∉ K → g i x=0)
    (hw : ∀ i, ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      (∫ x, u x*coordPartial psi x i)=-(∫ x, g i x*psi x)) :
    ∃ v : ℕ → Coord n → ℝ, ∃ hv : ∀ m, ContDiff ℝ ∞ (v m),
      ∃ hc : ∀ m, HasCompactSupport (v m),
      (∀ m, tsupport (v m) ⊆ L) ∧
      Tendsto (fun m ↦ realSmoothCompactL2 (v m) (hv m) (hc m)) atTop (𝓝 (hu.toLp u)) ∧
      ∀ i, Tendsto (fun m ↦ realSmoothCompactL2 (fun x ↦ coordPartial (v m) x i)
        (real_coordPartial_smooth (v m) (hv m) i) ((hc m).fderiv_apply ℝ (Pi.single i 1)))
        atTop (𝓝 ((hg i).toLp (g i))) := by
  have hs : tsupport u ⊆ K := closure_minimal (fun x hx ↦ by
    by_contra hn; exact hx (hsu x hn)) hK.isClosed
  have hgs (i : Fin n) : tsupport (g i) ⊆ K := closure_minimal (fun x hx ↦ by
    by_contra hn; exact hx (hsg i x hn)) hK.isClosed
  have huc : HasCompactSupport u := hK.of_isClosed_subset (isClosed_tsupport u) hs
  have hgc (i : Fin n) : HasCompactSupport (g i) :=
    hK.of_isClosed_subset (isClosed_tsupport (g i)) (hgs i)
  obtain ⟨r,hr,hsupport⟩ := real_compact_mollifier_support hK hKL
  let b : ℕ → ContDiffBump (0 : Coord n) := realMollifierBump r hr
  have hb : Tendsto (fun m ↦ (b m).rOut) atTop (𝓝 0) := realMollifierBump_radius_tendsto r hr
  let v : ℕ → Coord n → ℝ := fun m ↦ u ⋆ (b m).normed volume
  have hv (m : ℕ) : ContDiff ℝ ∞ (v m) :=
    (b m).hasCompactSupport_normed.contDiff_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ) (hu.locallyIntegrable (by norm_num)) (b m).contDiff_normed
  have hc (m : ℕ) : HasCompactSupport (v m) :=
    hL.of_isClosed_subset (isClosed_tsupport (v m)) (hsupport u hs m)
  refine ⟨v,hv,hc,hsupport u hs,real_compact_convolution_L2_tendsto u hu huc b hb,?_⟩
  intro i
  have ht := real_compact_convolution_L2_tendsto (g i) (hg i) (hgc i) b hb
  convert ht using 1
  funext m
  apply Lp.ext
  refine (realSmoothCompactL2_ae _ _ _).trans ?_
  rw [real_weak_convolution_derivative u (g i) ((b m).normed volume)
    (hu.locallyIntegrable (by norm_num)) (b m).contDiff_normed (b m).hasCompactSupport_normed i (hw i)]
  exact (realSmoothCompactL2_ae _ _ _).symm

end
end Yau

end OAI
