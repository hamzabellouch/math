import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildTruncation

namespace OAI

/-! A common spatially smooth function represented by compatible finite-jet mild solutions. -/

noncomputable section
namespace ForcedComputation.PlaneScalarMild

open Set ShearFlows MeasureTheory
open scoped Topology ContDiff Interval BigOperators

/-- The uniquely determined continuous solution at a fixed finite jet order. -/
def mildSolution {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k : ℕ) (b : Fin 3 → C(Icc (0 : ℝ) T, Jet k))
    (a : WeaklySingular.Path (Jet k) T) : WeaklySingular.Path (Jet k) T :=
  Classical.choose (exists_unique_mild hT hν k b a)

theorem mildSolution_spec {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k : ℕ) (b : Fin 3 → C(Icc (0 : ℝ) T, Jet k))
    (a : WeaklySingular.Path (Jet k) T) :
    ∀ t : Icc (0 : ℝ) T, mildSolution hT hν k b a t = a t +
      ∑ i, ∫ s in 0..t.val, rawKernels hν k i (t.val-s)
        (multiplication k (b i (projIcc 0 T hT s))
          (WeaklySingular.extendPath (Jet k) hT (mildSolution hT hν k b a) s)) :=
  (Classical.choose_spec (exists_unique_mild hT hν k b a)).1

theorem mildSolution_truncate {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k n : ℕ) (hkn : k ≤ n)
    (b : Fin 3 → C(Icc (0 : ℝ) T, Jet n))
    (c : Fin 3 → C(Icc (0 : ℝ) T, Jet k))
    (hbc : ∀ i t, BoundedSpatialJets.truncateCLM Plane ℝ k n hkn (b i t) = c i t)
    (a : WeaklySingular.Path (Jet n) T) :
    truncatePath k n hkn T (mildSolution hT hν n b a) =
      mildSolution hT hν k c (truncatePath k n hkn T a) :=
  mild_solutions_compatible hT hν k n hkn b c hbc a _ _
    (mildSolution_spec hT hν n b a) (mildSolution_spec hT hν k c (truncatePath k n hkn T a))

variable {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
  (b : ∀ k, Fin 3 → C(Icc (0 : ℝ) T, Jet k))
  (a : ∀ k, WeaklySingular.Path (Jet k) T)

/-- The common scalar function is read from the uniquely determined zeroth-order path. -/
def commonFunction (t : Icc (0 : ℝ) T) (x : Plane) : ℝ :=
  BoundedSpatialJets.function Plane ℝ 0 (mildSolution hT hν 0 (b 0) (a 0) t) x

variable
  (hb : ∀ k n (hkn : k ≤ n) i t,
    BoundedSpatialJets.truncateCLM Plane ℝ k n hkn (b n i t) = b k i t)
  (ha : ∀ k n (hkn : k ≤ n), truncatePath k n hkn T (a n) = a k)

include hb ha in
theorem commonFunction_eq (k : ℕ) (t : Icc (0 : ℝ) T) (x : Plane) :
    commonFunction hT hν b a t x =
      BoundedSpatialJets.function Plane ℝ k (mildSolution hT hν k (b k) (a k) t) x := by
  have he := mildSolution_truncate hT hν 0 k (Nat.zero_le k) (b k) (b 0)
    (hb 0 k (Nat.zero_le k)) (a k)
  rw [ha 0 k (Nat.zero_le k)] at he
  have hp := congrArg (fun u : WeaklySingular.Path (Jet 0) T =>
    BoundedSpatialJets.function Plane ℝ 0 (u t) x) he
  change BoundedSpatialJets.function Plane ℝ 0
    (BoundedSpatialJets.truncate Plane ℝ 0 k (Nat.zero_le k)
      (mildSolution hT hν k (b k) (a k) t)) x = commonFunction hT hν b a t x at hp
  rw [BoundedSpatialJets.function_truncate] at hp
  exact hp.symm

include hb ha in
/-- Every finite-order solution represents the same spatially smooth scalar function. -/
theorem commonFunction_smooth (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (commonFunction hT hν b a t) := by
  apply contDiff_infty.mpr
  intro k
  have he : commonFunction hT hν b a t =
      BoundedSpatialJets.function Plane ℝ k (mildSolution hT hν k (b k) (a k) t) := by
    funext x
    exact commonFunction_eq hT hν b a hb ha k t x
  rw [he]
  exact BoundedSpatialJets.function_contDiff Plane ℝ k _

include hb ha in
/-- On the compact time interval every spatial derivative is uniformly bounded. -/
theorem commonFunction_spatial_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : Icc (0 : ℝ) T, ∀ x : Plane,
      ‖iteratedFDeriv ℝ k (commonFunction hT hν b a t) x‖ ≤ C := by
  let u := mildSolution hT hν k (b k) (a k)
  refine ⟨‖u‖, norm_nonneg _, ?_⟩
  intro t x
  have he : commonFunction hT hν b a t = BoundedSpatialJets.function Plane ℝ k (u t) := by
    funext y
    exact commonFunction_eq hT hν b a hb ha k t y
  rw [he]
  exact (BoundedSpatialJets.norm_iteratedFDeriv_le Plane ℝ k (u t) k le_rfl x).trans
    (((WeaklySingular.pathEquiv (Jet k) T u).norm_coe_le_norm t).trans_eq
      ((WeaklySingular.pathEquiv (Jet k) T).norm_map u))

include hb ha in
/-- Every spatial derivative of the common function varies jointly continuously. -/
theorem commonFunction_spatial_continuous (k : ℕ) :
    Continuous (fun p : Icc (0 : ℝ) T × Plane =>
      iteratedFDeriv ℝ k (commonFunction hT hν b a p.1) p.2) := by
  let u := mildSolution hT hν k (b k) (a k)
  let i : Fin (k+1) := ⟨k, Nat.lt_succ_self k⟩
  have hc : Continuous (fun t : Icc (0 : ℝ) T => (u t).val i) :=
    (BoundedSpatialJets.projection Plane ℝ k i).continuous.comp
      (WeaklySingular.pathEquiv (Jet k) T u).continuous
  have he (t : Icc (0 : ℝ) T) : commonFunction hT hν b a t =
      BoundedSpatialJets.function Plane ℝ k (u t) := by
    funext x
    exact commonFunction_eq hT hν b a hb ha k t x
  have hj : (fun p : Icc (0 : ℝ) T × Plane =>
      iteratedFDeriv ℝ k (commonFunction hT hν b a p.1) p.2) =
      (fun p => (u p.1).val i p.2) := by
    funext p
    rw [he p.1]
    exact congrFun (BoundedSpatialJets.iteratedFDeriv_function Plane ℝ k (u p.1) k le_rfl) p.2
  rw [hj]
  exact (hc.comp continuous_fst).eval continuous_snd

/-- Continuity in time is in the uniform norm, so evaluation is jointly continuous. -/
theorem commonFunction_continuous :
    Continuous (fun p : Icc (0 : ℝ) T × Plane => commonFunction hT hν b a p.1 p.2) := by
  have hc : Continuous (fun t : Icc (0 : ℝ) T => BoundedSpatialJets.function Plane ℝ 0
      (mildSolution hT hν 0 (b 0) (a 0) t)) :=
    (BoundedSpatialJets.functionMap Plane ℝ 0).continuous.comp
      (WeaklySingular.pathEquiv (Jet 0) T (mildSolution hT hν 0 (b 0) (a 0))).continuous
  exact (hc.comp continuous_fst).eval continuous_snd

end ForcedComputation.PlaneScalarMild

end

end OAI
