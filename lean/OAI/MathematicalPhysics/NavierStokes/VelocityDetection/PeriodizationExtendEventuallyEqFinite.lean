import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SpatialSlices
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Periodization

namespace OAI

noncomputable section
namespace VelocityDetection.Periodization
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open SpatialCalculus JointCalculus

theorem extend_eventuallyEq_finite {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → Coord n → E} {C : ℝ}
    (hs : ∀ t X, f t X ≠ 0 → ∀ i, |X i| ≤ C)
    (p : ℝ × Coord n) : ∃ N : ℕ,
    uncurry (extend f) =ᶠ[𝓝 p] (fun q => ∑ k ∈ box (n := n) N, f q.1 (q.2-lattice k)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (‖p.2‖+C)
  refine ⟨N,?_⟩
  have hv : ∀ᶠ q : ℝ × Coord n in 𝓝 p, ‖q.2‖+C < N :=
    (isOpen_lt (continuous_snd.norm.add_const C) continuous_const).mem_nhds hN
  exact hv.mono (fun q hq => extend_finite hs hq q.1)

theorem divergence_congr_nhds {n : ℕ} {a b : VectorField n}
    (ha : ContDiff ℝ ∞ (uncurry a)) (hb : ContDiff ℝ ∞ (uncurry b))
    {t : ℝ} {X : Coord n} (he : uncurry a =ᶠ[𝓝 (t,X)] uncurry b) :
    divergence a t X = divergence b t X := by
  apply Finset.sum_congr rfl
  intro i _
  have hai : ContDiff ℝ ∞ (uncurry (fun t X => a t X i)) := (contDiff_apply ℝ ℝ i).comp ha
  have hbi : ContDiff ℝ ∞ (uncurry (fun t X => b t X i)) := (contDiff_apply ℝ ℝ i).comp hb
  rw [spatialD_eq hai,spatialD_eq hbi]
  exact ((eventuallyEq_dAlong (0,Pi.single i 1)
    (he.mono (fun q h => congrFun h i))).eq_of_nhds)

theorem divergence_extend {a : VectorField 2} {C : ℝ}
    (ha : ContDiff ℝ ∞ (uncurry a))
    (hs : ∀ t X, a t X ≠ 0 → ∀ i, |X i| ≤ C)
    (hdiv : ∀ t X, divergence a t X = 0) (t : ℝ) (X : Coord 2) :
    divergence (extend a) t X = 0 := by
  classical
  obtain ⟨N,hN⟩ := extend_eventuallyEq_finite hs (t,X)
  let v : (Fin 2 → ℤ) → VectorField 2 := fun k s Y => a s (Y-lattice k)
  have hv (k : Fin 2 → ℤ) : ContDiff ℝ ∞ (uncurry (v k)) :=
    ha.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const))
  have hvsum : ContDiff ℝ ∞ (uncurry (fun s Y => ∑ k ∈ box (n := 2) N, v k s Y)) :=
    ContDiff.sum (fun k _ => hv k)
  rw [divergence_congr_nhds (contDiff_extend ha hs) hvsum hN,
    divergence_sum (box (n := 2) N) v (fun k _ s => contDiff_slice (hv k) s)]
  apply Finset.sum_eq_zero
  intro k _
  change (∑ i : Fin 2, spatialD i (fun s Y => a s (Y-lattice k) i) t X) = 0
  have he (i : Fin 2) : spatialD i (fun s Y => a s (Y-lattice k) i) t X =
      spatialD i (fun s Y => a s Y i) t (X-lattice k) :=
    congrFun (congrFun (spatialD_translate i (fun s Y => a s Y i) (fun _ => lattice k)) t) X
  simp_rw [he]
  exact hdiv t (X-lattice k)

end VelocityDetection.Periodization
end

end OAI
