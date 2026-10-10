import Mathlib

namespace OAI

noncomputable section

namespace Problem340
namespace RadialOrbit

open NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def direction (e : E) (x : E) : E := by
  classical
  exact if x = 0 then e else normalize x

theorem norm_direction {e : E} (he : ‖e‖ = 1) (x : E) :
    ‖direction e x‖ = 1 := by
  by_cases hx : x = 0
  · simpa [direction, hx] using he
  · simp [direction, hx]

theorem norm_smul_direction (e x : E) : ‖x‖ • direction e x = x := by
  by_cases hx : x = 0
  · simp [direction, hx]
  · simp [direction, hx]

def radialMap (R : ℝ → ℝ) (x : E) : E := R ‖x‖ • normalize x

@[simp] theorem radialMap_zero (R : ℝ → ℝ) : radialMap R (0 : E) = 0 := by
  simp [radialMap]

theorem radialMap_polar {R : ℝ → ℝ} (hR0 : R 0 = 0)
    {r : ℝ} (hr : 0 ≤ r) {u : E} (hu : ‖u‖ = 1) :
    radialMap R (r • u) = R r • u := by
  rcases eq_or_lt_of_le hr with hr0 | hrpos
  · subst r
    simp [hR0]
  · simp [radialMap, norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, hu,
      normalize_smul_of_pos hrpos, normalize_eq_self_of_norm_eq_one hu]

theorem iterate_radialMap_polar {R : ℝ → ℝ} {A r : ℝ}
    (hR0 : R 0 = 0) (hR : Set.MapsTo R (Set.Icc 0 A) (Set.Icc 0 A))
    (hr : r ∈ Set.Icc 0 A) {u : E} (hu : ‖u‖ = 1) (n : ℕ) :
    (radialMap R)^[n] (r • u) = (R^[n] r) • u := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact radialMap_polar hR0 ((hR.iterate n) hr).1 hu

theorem iterate_radialMap_eq {R : ℝ → ℝ} {A : ℝ} {e : E} (he : ‖e‖ = 1)
    (hR0 : R 0 = 0) (hR : Set.MapsTo R (Set.Icc 0 A) (Set.Icc 0 A))
    {x : E} (hx : ‖x‖ ≤ A) (n : ℕ) :
    (radialMap R)^[n] x = (R^[n] ‖x‖) • direction e x := by
  conv_lhs => rw [← norm_smul_direction e x]
  exact iterate_radialMap_polar hR0 hR ⟨norm_nonneg x, hx⟩ (norm_direction he x) n

def polarMap (A : ℝ) (x : Set.Icc (0 : ℝ) A × Metric.sphere (0 : E) 1) : E :=
  (x.1 : ℝ) • (x.2 : E)

theorem continuous_polarMap (A : ℝ) : Continuous (polarMap (E := E) A) := by
  unfold polarMap
  fun_prop

theorem range_polarMap (A : ℝ) {e : E} (he : ‖e‖ = 1) :
    Set.range (polarMap (E := E) A) = Metric.closedBall (0 : E) A := by
  ext x
  constructor
  · rintro ⟨⟨r, u⟩, rfl⟩
    have hu : ‖(u : E)‖ = 1 := norm_eq_of_mem_sphere u
    simp only [Metric.mem_closedBall, dist_zero_right, polarMap, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg r.property.1, hu, mul_one]
    exact r.property.2
  · intro hx
    have hx' : ‖x‖ ≤ A := by simpa using hx
    refine ⟨(⟨‖x‖, norm_nonneg x, hx'⟩,
      ⟨direction e x, ?_⟩), ?_⟩
    · simpa using norm_direction he x
    · exact norm_smul_direction e x

theorem polarMap_semiconj {A : ℝ} {R : ℝ → ℝ}
    (hR0 : R 0 = 0) (hR : Set.MapsTo R (Set.Icc 0 A) (Set.Icc 0 A)) :
    Function.Semiconj (polarMap (E := E) A)
      (fun x : Set.Icc (0 : ℝ) A × Metric.sphere (0 : E) 1 =>
        (hR.restrict R _ _ x.1, x.2)) (radialMap R) := by
  intro x
  have hu : ‖(x.2 : E)‖ = 1 := norm_eq_of_mem_sphere x.2
  exact (radialMap_polar hR0 x.1.property.1 hu).symm

def polarMapPi {ι : Type*} (A : ℝ)
    (x : ι → Set.Icc (0 : ℝ) A × Metric.sphere (0 : E) 1) : ι → E :=
  fun i => polarMap A (x i)

theorem continuous_polarMapPi {ι : Type*} (A : ℝ) :
    Continuous (polarMapPi (E := E) (ι := ι) A) := by
  unfold polarMapPi
  exact continuous_pi fun i => (continuous_polarMap A).comp (continuous_apply i)

theorem range_polarMapPi {ι : Type*} (A : ℝ) {e : E} (he : ‖e‖ = 1) :
    Set.range (polarMapPi (E := E) (ι := ι) A) =
      Set.pi Set.univ (fun _ : ι => Metric.closedBall (0 : E) A) := by
  classical
  ext x
  constructor
  · rintro ⟨u, rfl⟩ i _
    change polarMap A (u i) ∈ Metric.closedBall (0 : E) A
    rw [← range_polarMap A he]
    exact Set.mem_range_self (u i)
  · intro hx
    have hex (i : ι) : ∃ u : Set.Icc (0 : ℝ) A × Metric.sphere (0 : E) 1,
        polarMap A u = x i := by
      change x i ∈ Set.range (polarMap A)
      rw [range_polarMap A he]
      exact hx i (Set.mem_univ i)
    choose u hu using hex
    exact ⟨u, funext hu⟩

theorem polarMapPi_semiconj {ι : Type*} {A : ℝ} {R : ℝ → ℝ}
    (hR0 : R 0 = 0) (hR : Set.MapsTo R (Set.Icc 0 A) (Set.Icc 0 A)) :
    Function.Semiconj (polarMapPi (E := E) (ι := ι) A)
      (fun x : ι → Set.Icc (0 : ℝ) A × Metric.sphere (0 : E) 1 =>
        fun i => (hR.restrict R _ _ (x i).1, (x i).2))
      (fun x : ι → E => fun i => radialMap R (x i)) := by
  intro x
  funext i
  exact polarMap_semiconj hR0 hR (x i)

theorem complex_polar_representation (z : ℂ) :
    ‖direction (1 : ℂ) z‖ = 1 ∧ ‖z‖ • direction (1 : ℂ) z = z :=
  ⟨norm_direction (by simp) z, norm_smul_direction 1 z⟩

end RadialOrbit
end Problem340

end

end OAI
