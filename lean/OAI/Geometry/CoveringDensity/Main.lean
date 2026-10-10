import OAI.Geometry.CoveringDensity.EuclideanTransport
import OAI.Geometry.TranslativeCovering.Main

namespace OAI

namespace CoveringOrder
open Set MeasureTheory
open scoped ENNReal

theorem euclideanVolume_eq_volume (n : ℕ) : euclideanVolume n = volume :=
  (PiLp.volume_preserving_toLp (Fin n)).map_eq

theorem euclideanCovolume_eq_ofReal {n : ℕ} (lattice : Submodule ℤ (Space n))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice] :
    euclideanCovolume lattice = ENNReal.ofReal (ZLattice.covolume lattice volume) := by
  rw [euclideanCovolume, euclideanVolume_eq_volume, ZLattice.covolume]
  apply (ENNReal.ofReal_toReal ?_).symm
  intro htop
  apply ZLattice.covolume_ne_zero lattice volume
  simp only [ZLattice.covolume, htop, ENNReal.toReal_top]

theorem latticeDensity_eq_volume_div_covolume {n : ℕ} {K : Set (Space n)}
    (cover : LatticeCover K) :
    latticeDensity cover = volume K / ENNReal.ofReal (ZLattice.covolume cover.lattice volume) := by
  let := cover.discrete
  let := cover.fullrank
  simp only [latticeDensity, euclideanVolume_eq_volume, euclideanCovolume_eq_ofReal]

/-- The infimum of actual lattice densities agrees with indexing by bundled covers. -/
theorem thetaL_eq_iInf_latticeCover {n : ℕ} (K : Set (Space n)) :
    thetaL K = ⨅ P : LatticeCover K,
      volume K / ENNReal.ofReal (ZLattice.covolume P.lattice volume) := by
  unfold thetaL
  exact iInf_congr latticeDensity_eq_volume_div_covolume

/-- A single lattice is a one-coset periodic covering. -/
def LatticeCover.toPeriodic {n : ℕ} {K : Set (Space n)} (P : LatticeCover K) :
    TranslativeCovering.PeriodicCover K where
  lattice := P.lattice
  discrete := P.discrete
  fullrank := P.fullrank
  m := 1
  offsets := fun _ => 0
  covers := by
    intro y
    obtain ⟨l, hl⟩ := P.covers y
    exact ⟨0, l, by simpa using hl⟩

/-- Full periodization, followed by restriction to one-coset coverings. -/
theorem thetaT_le_thetaL {n : ℕ} {K : Set (Space n)}
    (hK : TranslativeCovering.ConvexBody K) :
    TranslativeCovering.thetaT K ≤ thetaL K := by
  rw [thetaL_eq_iInf_latticeCover, TranslativeCovering.periodization_exact hK,
    ← TranslativeCovering.listed_eq_distinct K]
  apply le_iInf
  intro P
  have h := iInf_le
    (fun Q : TranslativeCovering.PeriodicCover K => volume K * Q.intensity)
    P.toPeriodic
  simpa only [TranslativeCovering.thetaPerListed,
    TranslativeCovering.PeriodicCover.intensity, LatticeCover.toPeriodic,
    Nat.cast_one, one_div, div_eq_mul_inv, one_mul] using h

/-- The transported upper theorem bounds the actual lattice-density infimum. -/
theorem uniform_lattice_density_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ K : Set (Space n),
      TranslativeCovering.ConvexBody K →
      thetaL K ≤ ENNReal.ofReal (C * (n : ℝ) * Real.log (n : ℝ)) := by
  obtain ⟨C, hC, h⟩ := euclidean_lattice_upper
  refine ⟨C, hC, ?_⟩
  intro n hn K hK
  obtain ⟨L, hd, hf, hc, hb⟩ := h n hn K hK
  let P : LatticeCover K := ⟨L, hd, hf, hc⟩
  rw [thetaL_eq_iInf_latticeCover]
  exact (iInf_le (fun Q : LatticeCover K =>
    volume K / ENNReal.ofReal (ZLattice.covolume Q.lattice volume)) P).trans hb

/-- All four density suprema have order `n * log n` with common absolute constants. -/
theorem optimal_order : OptimalOrder := by
  obtain ⟨c, hc, n₀, hlower⟩ := TranslativeCovering.main
  obtain ⟨C, hC, hupper⟩ := uniform_lattice_density_upper
  refine ⟨c, C, hc, hC, max n₀ 2, ?_⟩
  intro n hn
  have hn₀ : n₀ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : 2 ≤ n := (le_max_right _ _).trans hn
  obtain ⟨K, hK, hsym, hlow⟩ := hlower n hn₀
  let B : Body n := ⟨K, hK⟩
  let S : SymmetricBody n := ⟨B, hsym⟩
  have t_upper (A : Body n) :
      TranslativeCovering.thetaT A.val ≤
        ENNReal.ofReal (C * (n : ℝ) * Real.log (n : ℝ)) :=
    (thetaT_le_thetaL A.property).trans (hupper n hn₂ A.val A.property)
  have l_upper (A : Body n) :
      thetaL A.val ≤ ENNReal.ofReal (C * (n : ℝ) * Real.log (n : ℝ)) :=
    hupper n hn₂ A.val A.property
  have tl : ENNReal.ofReal (c * (n : ℝ) * Real.log (n : ℝ)) ≤
      TranslativeCovering.thetaT K := hlow.le
  have ll : ENNReal.ofReal (c * (n : ℝ) * Real.log (n : ℝ)) ≤ thetaL K :=
    tl.trans (thetaT_le_thetaL hK)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact tl.trans (le_iSup (fun A : Body n => TranslativeCovering.thetaT A.val) B)
  · exact iSup_le t_upper
  · exact tl.trans (le_iSup
      (fun A : SymmetricBody n => TranslativeCovering.thetaT A.val.val) S)
  · exact iSup_le (fun A : SymmetricBody n => t_upper A.val)
  · exact ll.trans (le_iSup (fun A : Body n => thetaL A.val) B)
  · exact iSup_le l_upper
  · exact ll.trans (le_iSup (fun A : SymmetricBody n => thetaL A.val.val) S)
  · exact iSup_le (fun A : SymmetricBody n => l_upper A.val)

end CoveringOrder

end OAI
