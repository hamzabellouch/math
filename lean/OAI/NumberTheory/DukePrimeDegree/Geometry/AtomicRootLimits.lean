import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootOrbitRebase
import OAI.NumberTheory.DukePrimeDegree.Dynamics.CompactFlowReturns
import OAI.NumberTheory.DukePrimeDegree.Dynamics.DiagonalFlowMaximal
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingCollision

namespace OAI

/-!
# Atomic root leaves exclude nonzero diagonal limits

Compact simultaneous recurrence converts any root limit of diagonal
conjugates into two points on one root orbit in an atomic transversal.
Consequently the root parameter must vanish. Only invariance under the
diagonal group and atomicity of the specified root are used.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_nullset_atomic_root_limit
    (d : ℕ) {a b : Fin (d + 1)} (hab : a ≠ b)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hatom : ∀ᵐ x ∂μ, intrinsicRootLeaf hab μ x = Measure.dirac 0)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ r, ell r = 0) :
    ∃ M : Set (X (d + 1)), MeasurableSet M ∧ μ M = 0 ∧
      ∀ x ∉ M, ∀ y ∉ M, ∀ g : G (d + 1), rightAction x g = y → ∀ c : ℝ,
        Tendsto (fun t : ℝ => diagonalOneParameter ell hell t * g *
          diagonalOneParameter ell hell (-t)) atTop
          (𝓝 (Matrix.SpecialLinearGroup.transvection hab c)) → c = 0 := by
  obtain ⟨N, hN, hNzero, htrans⟩ := exists_nullset_atomic_root_transversal d hab μ hA hatom
  let Φ : ℝ → X (d + 1) → X (d + 1) :=
    fun t x => rightAction x (diagonalOneParameter ell hell (-t))
  have hcont : Continuous (fun p : X (d + 1) × ℝ => Φ p.2 p.1) := by
    exact (continuous_rightAction_uncurry (d + 1)).comp
      (continuous_fst.prodMk ((continuous_diagonalOneParameter ell hell).comp continuous_snd.neg))
  have hzero (x : X (d + 1)) : Φ 0 x = x := by
    simp [Φ, diagonalOneParameter_zero]
  have hadd (s t : ℝ) (x : X (d + 1)) : Φ (s + t) x = Φ s (Φ t x) := by
    dsimp [Φ]
    rw [rightAction_mul, ← diagonalOneParameter_add]
    congr 2
    ring
  have hpres (t : ℝ) : MeasurePreserving (Φ t) μ μ := by
    refine ⟨(continuous_rightAction _).measurable, ?_⟩
    dsimp only [Φ]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  obtain ⟨M, hM, hMzero, hreturns⟩ := exists_conull_simultaneous_compact_returns
    μ hcont.measurable hzero hadd hpres N hN hNzero
  refine ⟨M, hM, hMzero, ?_⟩
  intro x hx y hy g hxy c hlim
  obtain ⟨K, hK, hKN, hret⟩ := hreturns x hx y hy
  have hseq (m : ℕ) : ∃ t : ℝ, (m : ℝ) < t ∧ Φ t x ∈ K ∧ Φ t y ∈ K := hret m
  choose t ht htx hty using hseq
  have htop : Tendsto t atTop atTop :=
    tendsto_atTop_mono (fun m => (ht m).le) tendsto_natCast_atTop_atTop
  let H : ℕ → G (d + 1) := fun m => diagonalOneParameter ell hell (t m) * g *
    diagonalOneParameter ell hell (-t m)
  have hpair (m : ℕ) : rightAction (Φ (t m) x) (H m) = Φ (t m) y := by
    rw [← hxy]
    dsimp only [Φ, H]
    rw [rightAction_mul, rightAction_mul]
    congr 1
    rw [diagonalOneParameter_neg]
    group
  obtain ⟨z, hz, hzc, _⟩ := compact_equal_data_orbit_limit K hK (fun _ => ())
    continuous_const.continuousOn (fun m => Φ (t m) x) H
    (Matrix.SpecialLinearGroup.transvection hab c) htx
    (fun m => by rw [hpair]; exact hty m) (fun _ => rfl) (hlim.comp htop)
  exact htrans z (hKN hz) c (hKN hzc)

end DukePrimeDegree

end

end OAI
