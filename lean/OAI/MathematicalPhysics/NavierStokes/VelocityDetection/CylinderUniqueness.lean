import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Stacks
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.CylinderEnergy

namespace OAI

noncomputable section
namespace VelocityDetection.Cylinder
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty

@[simp] theorem split_join (x : Space) : split (join x) = x := by
  ext i
  · fin_cases i <;> simp [split, join, horizontal]
  · simp [split, join]

@[simp] theorem join_split (y : Coord 3) : join (split y) = y := by
  ext i
  fin_cases i <;> simp [join, split, horizontal]

theorem split_update (y : Coord 3) (i : Fin 3) (s : ℝ) :
    split (Function.update y i s) = split y + (s - y i) • frame i := by
  fin_cases i
  all_goals
    ext j
    · fin_cases j <;> simp [split, horizontal, frame]
    · simp [split, horizontal, frame]

theorem spatialD_flatten {F : ℝ → Space → ℝ} {t : ℝ}
    (hf : Differentiable ℝ (F t)) (i : Fin 3) (y : Coord 3) :
    spatialD i (fun s z => F s (split z)) t y = D i (F t) (split y) := by
  have ha : HasDerivAt (fun s : ℝ => split y + (s - y i) • frame i) (frame i) (y i) := by
    simpa only [one_smul, id_eq] using (((hasDerivAt_id (y i)).sub_const (y i)).smul_const (frame i)).const_add (split y)
  have hp : HasFDerivAt (F t) (fderiv ℝ (F t) (split y))
      (split y + (y i - y i) • frame i) := by
    simpa only [sub_self, zero_smul, add_zero] using (hf (split y)).hasFDerivAt
  have hh := hp.comp_hasDerivAt (y i) ha
  simpa only [spatialD, split_update, D, Function.comp_def] using hh.deriv

theorem second_spatialD_flatten {F : ℝ → Space → ℝ} {t : ℝ}
    (hf : ContDiff ℝ 2 (F t)) (i k : Fin 3) (y : Coord 3) :
    spatialD i (spatialD k (fun s z => F s (split z))) t y =
      D i (D k (F t)) (split y) := by
  change deriv (fun s => spatialD k (fun r z => F r (split z)) t (Function.update y i s)) (y i) = _
  simp_rw [spatialD_flatten (hf.differentiable (by norm_num))]
  exact spatialD_flatten (F := fun _ => D k (F t)) (t := t) ((contDiff_D hf k).differentiable (by norm_num)) i y

theorem laplacian_flatten {F : ℝ → Space → ℝ} {t : ℝ}
    (hf : ContDiff ℝ 2 (F t)) (y : Coord 3) :
    laplacian (fun s z => F s (split z)) t y = lap (F t) (split y) := by
  simp only [laplacian, lap, second_spatialD_flatten hf]

theorem navierStokes_flatten_iff
    {ν : ℝ} {f u : ℝ → Space → Vect} {p : ℝ → Space → ℝ}
    (hu : ∀ t ≥ 0, ∀ i, ContDiff ℝ 2 (fun x => u t x i))
    (hp : ∀ t ≥ 0, Differentiable ℝ (p t)) :
    NavierStokes ν (fun t y => u t (split y)) (fun t y => p t (split y))
      (fun t y => f t (split y)) ↔ navierStokes ν f u p := by
  have hdiv (t : ℝ) (ht : 0 ≤ t) (y : Coord 3) :
      divergence (fun s z => u s (split z)) t y = div (u t) (split y) := by
    unfold divergence div
    apply Finset.sum_congr rfl
    intro i _
    exact spatialD_flatten (F := fun s x => u s x i) (t := t) ((hu t ht i).differentiable (by norm_num)) i y
  have hadv (t : ℝ) (ht : 0 ≤ t) (y : Coord 3) (i : Fin 3) :
      advection (fun s z => u s (split z)) (fun s z => u s (split z) i) t y =
        ∑ k, u t (split y) k * D k (fun x => u t x i) (split y) := by
    unfold advection
    simp_rw [spatialD_flatten (F := fun s x => u s x i) (t := t) ((hu t ht i).differentiable (by norm_num))]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro t ht x
      simpa only [hdiv t ht, split_join] using h.2.1 t ht (join x)
    · intro t ht x i
      have hh := h.1 t ht (join x) i
      simpa only [hadv t ht, spatialD_flatten (hp t ht), laplacian_flatten (F := fun s x => u s x i) (t := t) (hu t ht i),
        timeD, dt, split_join] using hh
    · intro x
      simpa only [split_join] using h.2.2 (join x)
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro t ht y i
      simpa only [hadv t ht, spatialD_flatten (hp t ht), laplacian_flatten (F := fun s x => u s x i) (t := t) (hu t ht i),
        timeD, dt] using h.2.1 t ht (split y) i
    · intro t ht y
      simpa only [hdiv t ht] using h.1 t ht (split y)
    · intro y
      exact h.2.2 (split y)

theorem comparison_unique_coordinates
    {ν : ℝ} {f u v : VectorField 3} {p q : ScalarField 3}
    (hν : 0 ≤ ν)
    (hu : ComparisonClass (fun t x => u t (join x)) (fun t x => p t (join x)))
    (hv : ComparisonClass (fun t x => v t (join x)) (fun t x => q t (join x)))
    (H : NavierStokes ν u p f) (G : NavierStokes ν v q f) :
    ∀ t ≥ 0, (∀ x, v t x = u t x) ∧ (∀ x, q t x = p t x) := by
  have hU (t : ℝ) (ht : 0 ≤ t) : SliceH2 (fun x => u t (join x)) :=
    (hu.velocity_H2 (t+1) (by linarith only [ht])).1 t ⟨ht, by linarith⟩
  have hV (t : ℝ) (ht : 0 ≤ t) : SliceH2 (fun x => v t (join x)) :=
    (hv.velocity_H2 (t+1) (by linarith only [ht])).1 t ⟨ht, by linarith⟩
  have hP (t : ℝ) (ht : 0 ≤ t) : PressureH1 (fun x => p t (join x)) :=
    (hu.pressure_H1 (t+1) (by linarith only [ht])).1 t ⟨ht, by linarith⟩
  have hQ (t : ℝ) (ht : 0 ≤ t) : PressureH1 (fun x => q t (join x)) :=
    (hv.pressure_H1 (t+1) (by linarith only [ht])).1 t ⟨ht, by linarith⟩
  have HU : navierStokes ν (fun t x => f t (join x)) (fun t x => u t (join x))
      (fun t x => p t (join x)) :=
    (navierStokes_flatten_iff (fun t ht => (hU t ht).smooth)
      (fun t ht => (hP t ht).smooth.differentiable (by norm_num))).mp (by simpa only [join_split] using H)
  have HV : navierStokes ν (fun t x => f t (join x)) (fun t x => v t (join x))
      (fun t x => q t (join x)) :=
    (navierStokes_flatten_iff (fun t ht => (hV t ht).smooth)
      (fun t ht => (hQ t ht).smooth.differentiable (by norm_num))).mp (by simpa only [join_split] using G)
  intro t ht
  have hh := comparison_unique hν hu hv HU HV t ht
  exact ⟨fun y => by simpa only [join_split] using hh.1 (split y),
    fun y => by simpa only [join_split] using hh.2 (split y)⟩

end VelocityDetection.Cylinder
end

end OAI
