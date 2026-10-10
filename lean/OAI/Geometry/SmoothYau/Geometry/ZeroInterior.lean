import Mathlib
import OAI.Geometry.SmoothYau.Estimates.LocalZeroAcrossLevel

namespace OAI

noncomputable section
namespace YauCounterexamples
open MeasureTheory TopologicalSpace Filter Set Metric
open scoped Distributions ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def zeroInterior (u : SmoothScalar E) : Set E := {x | (u : E → ℝ) =ᶠ[𝓝 x] 0}
lemma zeroInterior_open (u : SmoothScalar E) : IsOpen (zeroInterior u) :=
  isOpen_setOfPred_eventually_nhds
lemma zero_of_mem_zeroInterior (u : SmoothScalar E) {x : E} (hx : x ∈ zeroInterior u) : u x = 0 :=
  hx.eq_of_nhds

def ballPhase (y : E) (r : ℝ) : SmoothScalar E :=
  algebraMap ℝ (SmoothScalar E) (r^2) - distanceSquare y
@[simp] lemma ballPhase_apply (y x : E) (r : ℝ) : ballPhase y r x = r^2-‖x-y‖^2 := rfl
lemma ballPhase_positive_iff (y x : E) (r : ℝ) (hr : 0 < r) :
    0 < ballPhase y r x ↔ x ∈ ball y r := by
  rw [ballPhase_apply, mem_ball, dist_eq_norm]
  constructor <;> intro h <;> nlinarith [norm_nonneg (x-y)]
lemma ballPhase_zero_of_dist (y x : E) (r : ℝ) (h : dist x y = r) : ballPhase y r x = 0 := by
  rw [ballPhase_apply, ← dist_eq_norm, h, sub_self]
lemma distanceSquare_directional (y x v : E) :
    SmoothScalar.directional v (distanceSquare y) x = 2*⟪x-y,v⟫ := by
  have hd := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const y).norm_sq
  simp only [id_eq] at hd
  change fderiv ℝ (fun x : E => ‖x-y‖^2) x v = _
  rw [hd.fderiv]
  simp [inner_sub_left]
lemma ballPhase_directional (y x v : E) (r : ℝ) :
    SmoothScalar.directional v (ballPhase y r) x = -2*⟪x-y,v⟫ := by
  rw [ballPhase, map_sub]
  change SmoothScalar.directional v (algebraMap ℝ (SmoothScalar E) (r^2)) x -
    SmoothScalar.directional v (distanceSquare y) x = _
  rw [distanceSquare_directional]
  have hc : SmoothScalar.directional v (algebraMap ℝ (SmoothScalar E) (r^2)) x = 0 := by
    change fderiv ℝ (fun _ : E => r^2) x v = 0
    rw [fderiv_const_apply, _root_.zero_apply]
  rw [hc]; ring
omit [Fintype ι] in
lemma ballPhase_gradient_ne_zero (e : Module.Basis ι ℝ E) (y x : E) (r : ℝ)
    (hxy : x ≠ y) : (fun i => SmoothScalar.directional (e i) (ballPhase y r) x) ≠ 0 := by
  intro h
  have hf : (innerSL ℝ (x-y)).toLinearMap = 0 := by
    apply e.ext
    intro i
    change ⟪x-y,e i⟫ = 0
    have hi := congrFun h i
    rw [ballPhase_directional] at hi
    simp only [Pi.zero_apply] at hi
    linarith
  have hz : x-y = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp
    (congrArg (fun f : E →ₗ[ℝ] ℝ => f (x-y)) hf)
  exact hxy (sub_eq_zero.mp hz)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma zero_near_tangent_ball (e : Module.Basis ι ℝ E) (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (V u : SmoothScalar E)
    (O : Set E) (hO : IsOpen O) (y x : E) (r : ℝ) (hr : 0 < r)
    (hx : x ∈ O) (hxy : dist x y = r) (hpos : Matrix.PosDef (fun i j => a i j x))
    (hsol : ∀ z ∈ O, coefficientSchrodinger e a V u z = 0)
    (hz : ∀ z ∈ ball y r, u z = 0) : x ∈ zeroInterior u := by
  apply local_zero_across_level e a ha V (ballPhase y r) u x
    (ballPhase_zero_of_dist y x r hxy) hpos
    (ballPhase_gradient_ne_zero e y x r (by intro heq; simp [heq] at hxy; linarith)) O hO hx hsol
  intro z _ hzφ
  exact hz z ((ballPhase_positive_iff y z r hr).mp hzφ)

theorem weak_unique_continuation (e : Module.Basis ι ℝ E) (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (V u : SmoothScalar E)
    (O : Set E) (hO : IsOpen O) (hconn : IsPreconnected O)
    (hpos : ∀ x ∈ O, Matrix.PosDef (fun i j => a i j x))
    (hsol : ∀ x ∈ O, coefficientSchrodinger e a V u x = 0)
    (hz : (O ∩ zeroInterior u).Nonempty) : ∀ x ∈ O, u x = 0 := by
  have hclosed : closure (zeroInterior u) ∩ O ⊆ zeroInterior u := by
    intro x hx
    by_contra hxn
    obtain ⟨R,hR,hsub⟩ := Metric.isOpen_iff.mp hO x hx.2
    obtain ⟨y,hy,hyx⟩ := Metric.mem_closure_iff.mp hx.1 (R/4) (by positivity)
    have hne : (zeroInterior u)ᶜ.Nonempty := ⟨x,hxn⟩
    have hc := (zeroInterior_open u).isClosed_compl
    obtain ⟨z,hz,hzd⟩ := hc.exists_infDist_eq_dist hne y
    let r := infDist y (zeroInterior u)ᶜ
    have hr : 0 < r := hc.notMem_iff_infDist_pos hne |>.mp (by simpa using hy)
    have hrbound : r ≤ dist y x := infDist_le_dist_of_mem hxn
    have hzO : z ∈ O := by
      apply hsub
      change dist z x < R
      have ht := dist_triangle z y x
      rw [dist_comm z y, ← hzd] at ht
      rw [dist_comm x y] at hyx
      dsimp [r] at hrbound
      linarith
    have hball : ∀ w ∈ ball y r, u w = 0 := by
      intro w hw
      apply zero_of_mem_zeroInterior u
      by_contra hwn
      have dd : r ≤ dist y w := infDist_le_dist_of_mem hwn
      exact (lt_of_lt_of_le (by simpa only [mem_ball, dist_comm] using hw) dd).false
    have hznear := zero_near_tangent_ball e a ha V u O hO y z r hr hzO
      (by rw [dist_comm, ← hzd]) (hpos z hzO) hsol hball
    exact hz hznear
  have hsub := hconn.subset_of_closure_inter_subset (zeroInterior_open u) hz hclosed
  intro x hx
  exact zero_of_mem_zeroInterior u (hsub hx)

end YauCounterexamples


end

end OAI
