import OAI.GroupTheory.PolycyclicRecognition.Lattices.UniformLatticeMetric
import OAI.GroupTheory.PolycyclicRecognition.Analysis.LinearMetricChains
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricQuasiEquivalence

namespace OAI

/-! # Linear metric chains on a uniform lattice -/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G] {Λ : Subgroup G}

omit [IsTopologicalGroup G] in
/-- Rounding an ambient chain to a uniformly close lattice section keeps
the linear length bound and enlarges only the step size. -/
theorem IsUniformLattice.nonempty_linearMetricChains
    (hΛ : IsUniformLattice Λ) (C : LinearMetricChains G) :
    Nonempty (LinearMetricChains Λ) := by
  classical
  obtain ⟨r, R, hR, hr, _⟩ := hΛ.exists_metric_section
  let s : G → Λ := fun x => if h : x ∈ Λ then ⟨x, h⟩ else r x
  have hs (x : G) : dist x (s x : G) ≤ R := by
    dsimp [s]
    split
    · simpa using hR
    · exact hr x
  have hfix (x : Λ) : s x = x := by simp [s]
  refine ⟨{
    step := C.step + (R + R)
    step_pos := by linarith [C.step_pos]
    slope := C.slope
    slope_nonneg := C.slope_nonneg
    error := C.error
    error_nonneg := C.error_nonneg
    chain := ?_ }⟩
  intro x y
  obtain ⟨n, p, h0, hn, hlen, hstep⟩ := C.chain (x : G) (y : G)
  refine ⟨n, s ∘ p, by simpa only [Function.comp_apply, h0] using hfix x,
    by simpa only [Function.comp_apply, hn] using hfix y, hlen, ?_⟩
  intro i hi
  change dist (s (p i) : G) (s (p (i + 1)) : G) ≤ _
  calc
    _ ≤ dist (s (p i) : G) (p i) + dist (p i) (p (i + 1)) +
        dist (p (i + 1)) (s (p (i + 1)) : G) := dist_triangle4 _ _ _ _
    _ ≤ R + C.step + R := add_le_add (add_le_add
      ((dist_comm _ _).trans_le (hs _)) (hstep i hi)) (hs _)
    _ = C.step + (R + R) := by ring

omit [IsTopologicalGroup G] in
/-- Inclusion and a bounded section are metric quasi-inverses. -/
theorem IsUniformLattice.nonempty_metricQuasiEquivalence
    (hΛ : IsUniformLattice Λ) : Nonempty (MetricQuasiEquivalence Λ G) := by
  obtain ⟨r, R, hR, hr, hrlip⟩ := hΛ.exists_metric_section
  refine ⟨{
    toFun := Subtype.val
    invFun := r
    toFun_control := ⟨1, 0, by norm_num, by norm_num, fun x y => by
      change dist (x : G) (y : G) ≤ 1 * dist (x : G) (y : G) + 0
      simp⟩
    invFun_control := ⟨1, R + R, by norm_num, add_nonneg hR hR,
      fun x y => by simpa using hrlip x y⟩
    left_close := ⟨R, hR, fun x => hr x⟩
    right_close := ⟨R, hR, hr⟩ }⟩

end PolycyclicRecognition

end

end OAI
