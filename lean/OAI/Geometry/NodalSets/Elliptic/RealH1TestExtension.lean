import OAI.Geometry.NodalSets.Elliptic.RealCompactH1Approximation
import OAI.Geometry.NodalSets.Elliptic.RealL2ZeroExtension

namespace OAI

namespace Yau
open MeasureTheory Set Filter
open scoped ContDiff Topology
noncomputable section

theorem real_L2_strong_pairing_tendsto {n : ℕ} (a u : Coord n → ℝ)
    (ha : MemLp a 2 volume) (hu : MemLp u 2 volume)
    (v : ℕ → Coord n → ℝ) (hv : ∀ m, MemLp (v m) 2 volume)
    (ht : Tendsto (fun m ↦ (hv m).toLp (v m)) atTop (𝓝 (hu.toLp u))) :
    Tendsto (fun m ↦ ∫ x, a x*v m x) atTop (𝓝 (∫ x, a x*u x)) := by
  have h := (tendsto_const_nhds (x := ha.toLp a)).inner (𝕜 := ℝ) ht
  simpa only [real_toLp_inner] using h

theorem real_L2_restricted_strong_pairing_tendsto {n : ℕ} {L : Set (Coord n)}
    (hL : MeasurableSet L) (a u : Coord n → ℝ)
    (ha : MemLp a 2 (volume.restrict L)) (hu : MemLp u 2 volume)
    (v : ℕ → Coord n → ℝ) (hv : ∀ m, MemLp (v m) 2 volume)
    (ht : Tendsto (fun m ↦ (hv m).toLp (v m)) atTop (𝓝 (hu.toLp u))) :
    Tendsto (fun m ↦ ∫ x in L, a x*v m x) atTop (𝓝 (∫ x in L, a x*u x)) := by
  have hi := (memLp_indicator_iff_restrict hL).mpr ha
  have h := real_L2_strong_pairing_tendsto (L.indicator a) u hi hu v hv ht
  simpa only [← indicator_mul_left,integral_indicator hL] using h

theorem real_local_divergence_H1_test {n : ℕ} {K L : Set (Coord n)}
    (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ interior L)
    (A G : Fin n → Coord n → ℝ) (F : Coord n → ℝ)
    (hA : ∀ j, MemLp (A j) 2 (volume.restrict L))
    (hG : ∀ j, MemLp (G j) 2 (volume.restrict L))
    (hF : MemLp F 2 (volume.restrict L))
    (heq : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ L →
      (∑ j, ∫ x in L, A j x*coordPartial psi x j) =
        (∫ x in L, F x*psi x)-(∑ j, ∫ x in L, G j x*coordPartial psi x j))
    (u : Coord n → ℝ) (g : Fin n → Coord n → ℝ)
    (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (g j) 2 volume)
    (hsu : ∀ x, x ∉ K → u x=0) (hsg : ∀ j x, x ∉ K → g j x=0)
    (hw : ∀ j, ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      (∫ x, u x*coordPartial psi x j)=-(∫ x, g j x*psi x)) :
    (∀ j, IntegrableOn (fun x ↦ A j x*g j x) L ∧ IntegrableOn (fun x ↦ G j x*g j x) L) ∧
    IntegrableOn (fun x ↦ F x*u x) L ∧
    (∑ j, ∫ x in L, A j x*g j x) =
      (∫ x in L, F x*u x)-(∑ j, ∫ x in L, G j x*g j x) := by
  obtain ⟨v,hv,hc,hs,ht,hdt⟩ :=
    real_compact_weak_H1_smooth_approximation hK hL hKL u g hu hg hsu hsg hw
  have hvLp (m : ℕ) := real_compact_continuous_memLp (v m) (hv m).continuous (hc m)
  have hdLp (j : Fin n) (m : ℕ) := real_compact_continuous_memLp _
    (real_coordPartial_smooth (v m) (hv m) j).continuous ((hc m).fderiv_apply ℝ (Pi.single j 1))
  have hleft := tendsto_finsetSum Finset.univ (fun j _ ↦
    real_L2_restricted_strong_pairing_tendsto hL.measurableSet (A j) (g j) (hA j) (hg j)
      (fun m x ↦ coordPartial (v m) x j) (hdLp j) (hdt j))
  have hdiv := tendsto_finsetSum Finset.univ (fun j _ ↦
    real_L2_restricted_strong_pairing_tendsto hL.measurableSet (G j) (g j) (hG j) (hg j)
      (fun m x ↦ coordPartial (v m) x j) (hdLp j) (hdt j))
  have hscalar := real_L2_restricted_strong_pairing_tendsto hL.measurableSet F u hF hu v hvLp ht
  refine ⟨fun j ↦ ⟨(hA j).integrable_mul ((hg j).restrict L),
    (hG j).integrable_mul ((hg j).restrict L)⟩,hF.integrable_mul (hu.restrict L),?_⟩
  exact tendsto_nhds_unique hleft ((hscalar.sub hdiv).congr
    (fun m ↦ (heq (v m) (hv m) (hc m) (hs m)).symm))

end
end Yau

end OAI
