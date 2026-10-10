import OAI.Dynamics.EntropyCounterexample.Definitions

namespace OAI

noncomputable section

namespace Problem340
namespace SphereTranslation

def denom (c : ℂ) (x : SphereAmbient) : ℝ :=
  2 + 2 * c.re * x 0 + 2 * c.im * x 1 +
    (c.re ^ 2 + c.im ^ 2) * (1 - x 2)

def ambient (c : ℂ) (x : SphereAmbient) : SphereAmbient :=
  WithLp.toLp 2 ![2 * (x 0 + c.re * (1 - x 2)) / denom c x,
    2 * (x 1 + c.im * (1 - x 2)) / denom c x,
    1 - 2 * (1 - x 2) / denom c x]

lemma sphere_coordinates (x : StandardSphere2) :
    x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2 = 1 := by
  have hx : ‖x.1‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.2
  have he := EuclideanSpace.real_norm_sq_eq x.1
  rw [hx] at he
  simpa [Fin.sum_univ_succ, add_assoc] using he.symm

lemma denom_pos (c : ℂ) (x : StandardSphere2) : 0 < denom c x.1 := by
  have hx := sphere_coordinates x
  have hz : x.1 2 ≤ 1 := by nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1)]
  by_cases htop : x.1 2 = 1
  · have hzero : x.1 0 = 0 ∧ x.1 1 = 0 := by
      rw [htop] at hx
      constructor <;> nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1)]
    simp [denom, htop, hzero.1, hzero.2]
  · have ht : 0 < 1 - x.1 2 := sub_pos.mpr (lt_of_le_of_ne hz htop)
    have hid : denom c x.1 * (1 - x.1 2) =
        (x.1 0 + c.re * (1 - x.1 2)) ^ 2 +
        (x.1 1 + c.im * (1 - x.1 2)) ^ 2 +
        (1 - x.1 2) ^ 2 := by
      dsimp [denom]
      nlinarith [hx]
    have hp : 0 < denom c x.1 * (1 - x.1 2) := by
      rw [hid]
      positivity
    exact (mul_pos_iff_of_pos_right ht).mp hp

lemma ambient_mem_sphere (c : ℂ) (x : StandardSphere2) :
    ambient c x.1 ∈ Metric.sphere (0 : SphereAmbient) 1 := by
  have hd : denom c x.1 ≠ 0 := ne_of_gt (denom_pos c x)
  have hx := sphere_coordinates x
  have hid : ‖ambient c x.1‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rw [Fin.sum_univ_three]
    change (2 * (x.1 0 + c.re * (1 - x.1 2)) / denom c x.1) ^ 2 +
      (2 * (x.1 1 + c.im * (1 - x.1 2)) / denom c x.1) ^ 2 +
      (1 - 2 * (1 - x.1 2) / denom c x.1) ^ 2 = 1
    field_simp [hd]
    dsimp [denom]
    nlinarith [hx]
  rw [Metric.mem_sphere, dist_zero_right]
  nlinarith [norm_nonneg (ambient c x.1)]

def translate (c : ℂ) (x : StandardSphere2) : StandardSphere2 :=
  ⟨ambient c x.1, ambient_mem_sphere c x⟩

@[simp] lemma ambient_zero (x : SphereAmbient) : ambient 0 x = x := by
  ext i
  fin_cases i <;> simp [ambient, denom]

@[simp] lemma translate_zero (x : StandardSphere2) : translate 0 x = x := by
  apply Subtype.ext
  exact ambient_zero x.1

def domain : Set (ℂ × SphereAmbient) := {p | denom p.1 p.2 ≠ 0}

@[fun_prop] lemma contDiff_complex_re (n : WithTop ℕ∞) :
    ContDiff ℝ n Complex.re := Complex.reCLM.contDiff

@[fun_prop] lemma contDiff_complex_im (n : WithTop ℕ∞) :
    ContDiff ℝ n Complex.im := Complex.imCLM.contDiff

@[fun_prop] lemma contDiff_denom (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun p : ℂ × SphereAmbient => denom p.1 p.2) := by
  unfold denom
  fun_prop

lemma isOpen_domain : IsOpen domain := by
  exact isOpen_ne_fun (contDiff_denom 0).continuous continuous_const

lemma contDiffOn_ambient (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (fun p : ℂ × SphereAmbient => ambient p.1 p.2) domain := by
  have hd := (contDiff_denom n).contDiffOn (s := domain)
  have hn : ∀ p ∈ domain, denom p.1 p.2 ≠ 0 := fun p hp => hp
  apply contDiffOn_euclidean.mpr
  intro i
  fin_cases i
  · change ContDiffOn ℝ n
      (fun p : ℂ × SphereAmbient => 2 * (p.2 0 + p.1.re * (1 - p.2 2)) /
        denom p.1 p.2) domain
    apply ContDiffOn.div _ hd hn
    fun_prop
  · change ContDiffOn ℝ n
      (fun p : ℂ × SphereAmbient => 2 * (p.2 1 + p.1.im * (1 - p.2 2)) /
        denom p.1 p.2) domain
    apply ContDiffOn.div _ hd hn
    fun_prop
  · change ContDiffOn ℝ n
      (fun p : ℂ × SphereAmbient => 1 - 2 * (1 - p.2 2) / denom p.1 p.2) domain
    apply contDiffOn_const.sub
    apply ContDiffOn.div _ hd hn
    fun_prop

@[continuity, fun_prop] theorem continuous_translate :
    Continuous (fun p : ℂ × StandardSphere2 => translate p.1 p.2) := by
  apply Continuous.subtype_mk
  rw [continuous_iff_continuousAt]
  intro p
  have hp : (p.1, p.2.1) ∈ domain := ne_of_gt (denom_pos p.1 p.2)
  have hc := ((contDiffOn_ambient 0).contDiffAt (isOpen_domain.mem_nhds hp)).continuousAt
  change ContinuousAt
    ((fun q : ℂ × SphereAmbient => ambient q.1 q.2) ∘
      (fun q : ℂ × StandardSphere2 => (q.1, q.2.1))) p
  exact hc.comp (f := fun q : ℂ × StandardSphere2 => (q.1, q.2.1)) (continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)).continuousAt

lemma contDiffAt_ambient (n : WithTop ℕ∞) (c : ℂ) (x : StandardSphere2) :
    ContDiffAt ℝ n (fun p : ℂ × SphereAmbient => ambient p.1 p.2) (c, x.1) :=
  (contDiffOn_ambient n).contDiffAt
    (isOpen_domain.mem_nhds (ne_of_gt (denom_pos c x)))

@[simp] lemma ambient_north (c : ℂ) :
    ambient c (WithLp.toLp 2 ![0, 0, 1]) = WithLp.toLp 2 ![0, 0, 1] := by
  ext i
  fin_cases i <;> simp [ambient, denom]

def continuousMap {X : Type*} [TopologicalSpace X]
    (C : ContinuousMap X ℂ) (g : ContinuousMap X StandardSphere2) :
    ContinuousMap X StandardSphere2 :=
  ⟨fun x => translate (C x) (g x),
    continuous_translate.comp (C.continuous.prodMk g.continuous)⟩

def homotopy {X : Type*} [TopologicalSpace X]
    (C : ContinuousMap X ℂ) (g : ContinuousMap X StandardSphere2) :
    ContinuousMap.Homotopy g (continuousMap C g) where
  toFun p := translate ((p.1 : ℝ) • C p.2) (g p.2)
  continuous_toFun := continuous_translate.comp
    (((continuous_subtype_val.comp continuous_fst).smul
      (C.continuous.comp continuous_snd)).prodMk (g.continuous.comp continuous_snd))
  map_zero_left x := by simp
  map_one_left x := by simp [continuousMap]

def chart (x : SphereAmbient) : ℂ :=
  ⟨x 0 / (1 - x 2), x 1 / (1 - x 2)⟩

lemma ambient_not_north (c : ℂ) (x : StandardSphere2) (hx : x.1 2 ≠ 1) :
    ambient c x.1 2 ≠ 1 := by
  have hd : denom c x.1 ≠ 0 := ne_of_gt (denom_pos c x)
  have ht : 1 - x.1 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  change 1 - 2 * (1 - x.1 2) / denom c x.1 ≠ 1
  intro h
  have hz : 2 * (1 - x.1 2) / denom c x.1 = 0 := by linarith
  exact (div_ne_zero (mul_ne_zero (by norm_num) ht) hd) hz

lemma chart_ambient (c : ℂ) (x : StandardSphere2) (hx : x.1 2 ≠ 1) :
    chart (ambient c x.1) = chart x.1 + c := by
  have hd : denom c x.1 ≠ 0 := ne_of_gt (denom_pos c x)
  have ht : 1 - x.1 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  apply Complex.ext
  · change (2 * (x.1 0 + c.re * (1 - x.1 2)) / denom c x.1) /
      (1 - (1 - 2 * (1 - x.1 2) / denom c x.1)) = x.1 0 / (1 - x.1 2) + c.re
    rw [sub_sub_cancel]
    field_simp [hd, ht]
  · change (2 * (x.1 1 + c.im * (1 - x.1 2)) / denom c x.1) /
      (1 - (1 - 2 * (1 - x.1 2) / denom c x.1)) = x.1 1 / (1 - x.1 2) + c.im
    rw [sub_sub_cancel]
    field_simp [hd, ht]

end SphereTranslation
end Problem340

end

end OAI
