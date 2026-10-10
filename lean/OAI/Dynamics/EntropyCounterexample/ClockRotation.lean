import OAI.Dynamics.EntropyCounterexample.Clock
import OAI.Dynamics.EntropyCounterexample.Embedding

namespace OAI

noncomputable section

namespace Problem340.Clock

def rotate (x : ClockAmbient) (a : ℝ) : ClockAmbient :=
  WithLp.toLp 2 ![x 0 * Real.cos a - x 1 * Real.sin a,
    x 0 * Real.sin a + x 1 * Real.cos a]

@[simp] lemma rotate_zero_apply (x : ClockAmbient) (a : ℝ) :
    rotate x a 0 = x 0 * Real.cos a - x 1 * Real.sin a := rfl

@[simp] lemma rotate_one_apply (x : ClockAmbient) (a : ℝ) :
    rotate x a 1 = x 0 * Real.sin a + x 1 * Real.cos a := rfl

lemma norm_rotate (x : ClockAmbient) (a : ℝ) : ‖rotate x a‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, rotate_zero_apply, rotate_one_apply]
  have hc := Real.sin_sq_add_cos_sq a
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

lemma contDiff_rotate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞} {x : E → ClockAmbient} {a : E → ℝ}
    (hx : ContDiff ℝ n x) (ha : ContDiff ℝ n a) :
    ContDiff ℝ n (fun y => rotate (x y) (a y)) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp hx).mul ha.cos).sub
      (((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp hx).mul ha.sin)
  · exact (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp hx).mul ha.sin).add
      (((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp hx).mul ha.cos)

def parametrization (t : ℝ) : ClockAmbient :=
  WithLp.toLp 2 ![Real.cos (2 * Real.pi * t / 100), Real.sin (2 * Real.pi * t / 100)]

@[simp] lemma parametrization_zero (t : ℝ) :
    parametrization t 0 = Real.cos (2 * Real.pi * t / 100) := rfl

@[simp] lemma parametrization_one (t : ℝ) :
    parametrization t 1 = Real.sin (2 * Real.pi * t / 100) := rfl

lemma norm_parametrization (t : ℝ) : ‖parametrization t‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, parametrization_zero, parametrization_one, one_pow]
  nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * t / 100)]

lemma rotate_parametrization (t h : ℝ) :
    rotate (parametrization t) (2 * Real.pi * h / 100) = parametrization (t + h) := by
  ext i
  fin_cases i
  · change Real.cos (2 * Real.pi * t / 100) * Real.cos (2 * Real.pi * h / 100) -
        Real.sin (2 * Real.pi * t / 100) * Real.sin (2 * Real.pi * h / 100) =
      Real.cos (2 * Real.pi * (t + h) / 100)
    rw [show 2 * Real.pi * (t + h) / 100 =
        2 * Real.pi * t / 100 + 2 * Real.pi * h / 100 by ring, Real.cos_add]
  · change Real.cos (2 * Real.pi * t / 100) * Real.sin (2 * Real.pi * h / 100) +
        Real.sin (2 * Real.pi * t / 100) * Real.cos (2 * Real.pi * h / 100) =
      Real.sin (2 * Real.pi * (t + h) / 100)
    rw [show 2 * Real.pi * (t + h) / 100 =
        2 * Real.pi * t / 100 + 2 * Real.pi * h / 100 by ring, Real.sin_add]
    ring

def advance (x : StandardClock) (h : ℝ) : StandardClock :=
  ⟨rotate x.1 (2 * Real.pi * h / 100), by
    rw [Metric.mem_sphere, dist_zero_right, norm_rotate]
    simp⟩

def ambientIncrement (x : ClockAmbient) (e : ℝ) : ℝ :=
  ambientBarrier x + (1 - ambientBarrier x) * e

lemma ambientIncrement_mem_Icc (x : ClockAmbient) (hx : ‖x‖ ≤ 1)
    {e : ℝ} (he : e ∈ Set.Icc (0 : ℝ) 1) :
    ambientIncrement x e ∈ Set.Icc (0 : ℝ) 1 := by
  have hb := ambientBarrier_mem_Icc x hx
  have hp : 0 ≤ (1 - ambientBarrier x) * e := mul_nonneg (by linarith [hb.2]) he.1
  have hp' := mul_le_mul_of_nonneg_left he.2 (show 0 ≤ 1 - ambientBarrier x by linarith [hb.2])
  unfold ambientIncrement
  constructor <;> linarith [hb.1]

lemma ambientBarrier_le_ambientIncrement (x : ClockAmbient) (hx : ‖x‖ ≤ 1)
    {e : ℝ} (he : 0 ≤ e) : ambientBarrier x ≤ ambientIncrement x e := by
  have hb := (ambientBarrier_mem_Icc x hx).2
  have hp : 0 ≤ (1 - ambientBarrier x) * e := mul_nonneg (by linarith) he
  unfold ambientIncrement
  linarith

@[simp] lemma ambientIncrement_one (x : ClockAmbient) : ambientIncrement x 1 = 1 := by
  simp [ambientIncrement]

@[simp] lemma ambientIncrement_zero (x : ClockAmbient) : ambientIncrement x 0 = ambientBarrier x := by
  simp [ambientIncrement]

lemma contDiff_ambientIncrement {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞} {x : E → ClockAmbient} {e : E → ℝ}
    (hx : ContDiff ℝ n x) (he : ContDiff ℝ n e) :
    ContDiff ℝ n (fun y => ambientIncrement (x y) (e y)) := by
  exact (contDiff_ambientBarrier.comp hx).add
    ((contDiff_const.sub (contDiff_ambientBarrier.comp hx)).mul he)

lemma ambientIncrement_parametrization (t e : ℝ) :
    ambientIncrement (parametrization t) e = increment t e := by
  simp only [ambientIncrement, increment,
    ambientBarrier_on_circle t (parametrization t) (parametrization_zero t)]

def ambientUpdate (x : ClockAmbient) (e : ℝ) : ClockAmbient :=
  rotate x (2 * Real.pi * ambientIncrement x e / 100)

lemma contDiff_ambientUpdate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞} {x : E → ClockAmbient} {e : E → ℝ}
    (hx : ContDiff ℝ n x) (he : ContDiff ℝ n e) :
    ContDiff ℝ n (fun y => ambientUpdate (x y) (e y)) := by
  apply contDiff_rotate hx
  exact (contDiff_const.mul (contDiff_ambientIncrement hx he)).div_const 100

lemma ambientUpdate_parametrization (t e : ℝ) :
    ambientUpdate (parametrization t) e = parametrization (t + increment t e) := by
  rw [ambientUpdate, ambientIncrement_parametrization, rotate_parametrization]

lemma norm_ambientUpdate (x : ClockAmbient) (e : ℝ) : ‖ambientUpdate x e‖ = ‖x‖ :=
  norm_rotate _ _

def update (x : StandardClock) (e : ℝ) : StandardClock :=
  ⟨ambientUpdate x.1 e, by
    rw [Metric.mem_sphere, dist_zero_right, norm_ambientUpdate]
    simp⟩

lemma continuous_update : Continuous (fun p : StandardClock × ℝ => update p.1 p.2) := by
  apply Continuous.subtype_mk
  have hc : Continuous (fun p : ClockAmbient × ℝ => ambientUpdate p.1 p.2) :=
    (contDiff_ambientUpdate (n := 1) contDiff_fst contDiff_snd).continuous
  exact hc.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

def clockStep (q : ℕ) (e : CounterexampleAmbient q → ℝ)
    (x : CounterexampleManifold q) : CounterexampleManifold q :=
  (update x.1 (e (standardEmbedding q x)), x.2)

lemma isC1SelfMap_clockStep (q : ℕ) (e : CounterexampleAmbient q → ℝ)
    (he : ContDiff ℝ 1 e) : IsC1SelfMap q (clockStep q e) := by
  apply isC1SelfMap_of_contDiff (clockStep q e)
    (fun p : CounterexampleAmbient q => (ambientUpdate p.1 (e p), p.2))
  · exact (contDiff_ambientUpdate contDiff_fst he).prodMk contDiff_snd
  · intro y
    rfl

end Problem340.Clock

end

end OAI
