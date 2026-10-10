import OAI.Analysis.PeriodicLattice.Compiler

namespace OAI

/-! Periodic fluid lift of the planar dynamics. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingFluidLift {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace TorusCalculus

open scoped ContDiff

theorem mk_surjective : Function.Surjective torusMk := by
  intro q
  choose x hx using (fun i : Fin 3 =>
    (QuotientAddGroup.mk_surjective : Function.Surjective ((↑) : ℝ → UnitAddCircle)) (q i))
  exact ⟨WithLp.toLp 2 x, funext hx⟩

@[simp] theorem mk_add (x y : Space) : torusMk (x + y) = torusMk x + torusMk y := by
  ext i
  exact AddCircle.coe_add 1 (x i) (y i)

theorem spaceD_cover {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (i : Fin 3) (F : Field A) (t : ℝ) (x : Space) :
    spaceD i F t (torusMk x) =
      deriv (fun s : ℝ => spaceLift F t (x + EuclideanSpace.single i s)) 0 := by
  simp only [spaceD, spaceLift, mk_add]

theorem periodic_deriv {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {f : ℝ → A} {c : ℝ} (hf : Function.Periodic f c) :
    Function.Periodic (deriv f) c := by
  intro x
  rw [← deriv_comp_add_const]
  congr 1
  exact funext hf

theorem contDiff_partial {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {v : ℝ → ℝ → A} (hv : ContDiff ℝ ∞ (Function.uncurry v)) :
    ContDiff ℝ ∞ (fun ty : ℝ × ℝ => deriv (v ty.1) ty.2) := by
  let f : (ℝ × ℝ) → ℝ → A := fun ty y => v ty.1 y
  have hf : ContDiff ℝ ∞ (Function.uncurry f) :=
    hv.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact hf.fderiv_apply contDiff_snd contDiff_const (by simp)

end TorusCalculus

namespace FluidLift

open scoped ContDiff
open TorusCalculus

def eta (z : ℝ) : ℝ :=
  letI := twoAtLeastTwo
  Real.sin (2 * Real.pi * (z - 1 / 2)) / (2 * Real.pi)
def slope (z : ℝ) : ℝ :=
  letI := twoAtLeastTwo
  Real.cos (2 * Real.pi * (z - 1 / 2))

theorem eta_contDiff : ContDiff ℝ ∞ eta :=
  (Real.contDiff_sin.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))).div_const _

theorem slope_contDiff : ContDiff ℝ ∞ slope :=
  Real.contDiff_cos.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))

theorem eta_periodic : Function.Periodic eta 1 := by
  intro z
  dsimp [eta]
  rw [show 2 * Real.pi * (z + 1 - 1 / 2) = 2 * Real.pi * (z - 1 / 2) + 2 * Real.pi by ring,
    Real.sin_add_two_pi]

theorem slope_periodic : Function.Periodic slope 1 := by
  intro z
  dsimp [slope]
  rw [show 2 * Real.pi * (z + 1 - 1 / 2) = 2 * Real.pi * (z - 1 / 2) + 2 * Real.pi by ring,
    Real.cos_add_two_pi]

theorem eta_hasDerivAt (z : ℝ) : HasDerivAt eta (slope z) z := by
  have h := (((hasDerivAt_id z).sub_const (1 / 2)).const_mul (2 * Real.pi)).sin.div_const
    (2 * Real.pi)
  change HasDerivAt (fun z => Real.sin (2 * Real.pi * (z - 1 / 2)) / (2 * Real.pi)) _ z
  simpa [slope, Real.pi_ne_zero] using h

@[simp] theorem eta_center : eta (1 / 2) = 0 := by simp [eta]
@[simp] theorem slope_center : slope (1 / 2) = 1 := by simp [slope]

def v (d : Input) (t y : ℝ) : Planar.Point := CompilerPlanar.velocity d t (0, y)
def a (d : Input) (t y : ℝ) : ℝ := (v d t y).1
def b (d : Input) (t y : ℝ) : ℝ := (v d t y).2
def bdy (d : Input) (t y : ℝ) : ℝ := deriv (b d t) y

theorem velocity_eq (d : Input) (t : ℝ) (p : Planar.Point) :
    CompilerPlanar.velocity d t p = v d t p.2 := rfl

theorem v_contDiff (d : Input) : ContDiff ℝ ∞ (Function.uncurry (v d)) :=
  (CompilerPlanar.velocity_contDiff d).comp
    (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd))

theorem a_contDiff (d : Input) : ContDiff ℝ ∞ (Function.uncurry (a d)) := (v_contDiff d).fst

theorem b_contDiff (d : Input) : ContDiff ℝ ∞ (Function.uncurry (b d)) := (v_contDiff d).snd

theorem bdy_contDiff (d : Input) : ContDiff ℝ ∞ (Function.uncurry (bdy d)) :=
  contDiff_partial (b_contDiff d)

theorem a_periodic (d : Input) (t : ℝ) : Function.Periodic (a d t) 1 :=
  fun y => congrArg Prod.fst (CompilerPlanar.velocity_periodic d t 0 y)

theorem b_periodic (d : Input) (t : ℝ) : Function.Periodic (b d t) 1 :=
  fun y => congrArg Prod.snd (CompilerPlanar.velocity_periodic d t 0 y)

theorem bdy_periodic (d : Input) (t : ℝ) : Function.Periodic (bdy d t) 1 :=
  periodic_deriv (b_periodic d t)

def velocity (d : Input) : VectorField :=
  letI := twoAtLeastTwo
  letI := neZeroThree
  fun t q => WithLp.toLp 2
    ![slope_periodic.lift (q 2) * (a_periodic d t).lift (q 1),
      slope_periodic.lift (q 2) * (b_periodic d t).lift (q 1),
      -eta_periodic.lift (q 2) * (bdy_periodic d t).lift (q 1)]

@[simp] theorem velocity_cover (d : Input) (t : ℝ) (x : Space) :
    velocity d t (torusMk x) = WithLp.toLp 2
      ![slope (x 2) * a d t (x 1), slope (x 2) * b d t (x 1),
        -eta (x 2) * bdy d t (x 1)] := by
  simp only [velocity, torusMk, Function.Periodic.lift_coe]

theorem velocity_contDiff (d : Input) : ContDiff ℝ ∞ (lifted (velocity d)) := by
  have hcoord (i : Fin 3) : ContDiff ℝ ∞ (fun tx : ℝ × Space => tx.2 i) := by
    have hi : ContDiff ℝ ∞ (fun x : Space => x i) := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).contDiff
    exact hi.comp contDiff_snd
  have ha := (a_contDiff d).comp (contDiff_fst.prodMk (hcoord 1))
  have hb := (b_contDiff d).comp (contDiff_fst.prodMk (hcoord 1))
  have hc := (bdy_contDiff d).comp (contDiff_fst.prodMk (hcoord 1))
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i
  · exact (slope_contDiff.comp (hcoord 2)).mul ha
  · exact (slope_contDiff.comp (hcoord 2)).mul hb
  · exact (eta_contDiff.comp (hcoord 2)).neg.mul hc

theorem velocity_smooth (d : Input) : Smooth (velocity d) := (velocity_contDiff d).contDiffOn

theorem velocity_on_plane (d : Input) (t : ℝ) (p : Planar.Point) :
    velocity d t (torusMk (Planar.embed p)) =
      WithLp.toLp 2 ![(CompilerPlanar.velocity d t p).1, (CompilerPlanar.velocity d t p).2, 0] := by
  rw [velocity_cover]
  simp [Planar.embed, eta, slope, a, b, ← velocity_eq]

theorem b_hasDerivAt (d : Input) (t y : ℝ) : HasDerivAt (b d t) (bdy d t y) y :=
  (((b_contDiff d).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) y).hasDerivAt

theorem divergence_zero (d : Input) (t : ℝ) (q : Torus) : divergence (velocity d) t q = 0 := by
  obtain ⟨x, rfl⟩ := mk_surjective q
  have h₀ : spaceD 0 (fun s q => velocity d s q 0) t (torusMk x) = 0 := by
    rw [spaceD_cover]
    change deriv (fun s : ℝ => slope (x 2 + 0) * a d t (x 1 + 0)) 0 = 0
    exact deriv_const _ _
  have h₁ : spaceD 1 (fun s q => velocity d s q 1) t (torusMk x) =
      slope (x 2) * bdy d t (x 1) := by
    rw [spaceD_cover]
    change deriv (fun s : ℝ => slope (x 2 + 0) * b d t (x 1 + s)) 0 = _
    have h := ((b_hasDerivAt d t (x 1 + 0)).comp 0
      ((hasDerivAt_id (0 : ℝ)).const_add (x 1))).const_mul (slope (x 2))
    simpa [Function.comp_def] using h.deriv
  have h₂ : spaceD 2 (fun s q => velocity d s q 2) t (torusMk x) =
      -slope (x 2) * bdy d t (x 1) := by
    rw [spaceD_cover]
    change deriv (fun s : ℝ => -eta (x 2 + s) * bdy d t (x 1 + 0)) 0 = _
    have h := ((eta_hasDerivAt (x 2 + 0)).comp 0
      ((hasDerivAt_id (0 : ℝ)).const_add (x 2))).neg.mul_const (bdy d t (x 1))
    simpa [Function.comp_def] using h.deriv
  simp only [divergence, Fin.sum_univ_three, h₀, h₁, h₂]
  ring

theorem velocity_solenoidal (d : Input) : Solenoidal (velocity d) :=
  fun t _ q => divergence_zero d t q

theorem velocity_start (d : Input) (q : Torus) : velocity d 0 q = 0 := by
  obtain ⟨x, rfl⟩ := mk_surjective q
  have ha : a d 0 = fun _ => 0 := funext (fun y =>
    congrArg Prod.fst (CompilerPlanar.velocity_start d (0, y)))
  have hb : b d 0 = fun _ => 0 := funext (fun y =>
    congrArg Prod.snd (CompilerPlanar.velocity_start d (0, y)))
  rw [velocity_cover]
  ext i
  fin_cases i <;> simp [ha, hb, bdy]

def path (d : Input) : ℝ → Space := fun t => Planar.embed (CompilerPlanar.path d t)

theorem path_contDiff (d : Input) : ContDiff ℝ ∞ (path d) := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i
  · exact (CompilerPlanar.path_contDiff d).fst
  · exact (CompilerPlanar.path_contDiff d).snd
  · exact contDiff_const

theorem path_start (d : Input) : path d 0 = initialParticle := by
  simp only [path, CompilerPlanar.path_start]
  rfl

theorem path_hasDerivAt (d : Input) (hd : d.WellFormed) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (path d) (velocity d t (torusMk (path d t))) t := by
  have h := CompilerPlanar.path_solves d hd ht
  have hx : HasDerivAt (fun s => (CompilerPlanar.path d s).1)
      (CompilerPlanar.velocity d t (CompilerPlanar.path d t)).1 t := by
    simpa using h.hasFDerivAt.fst.hasDerivAt
  have hy : HasDerivAt (fun s => (CompilerPlanar.path d s).2)
      (CompilerPlanar.velocity d t (CompilerPlanar.path d t)).2 t := by
    simpa using h.hasFDerivAt.snd.hasDerivAt
  have hp : HasDerivAt (fun s => ![(CompilerPlanar.path d s).1,
      (CompilerPlanar.path d s).2, (1 : ℝ) / 2])
      ![(CompilerPlanar.velocity d t (CompilerPlanar.path d t)).1,
        (CompilerPlanar.velocity d t (CompilerPlanar.path d t)).2, (0 : ℝ)] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hx
    · exact hy
    · exact hasDerivAt_const _ _
  rw [path, velocity_on_plane]
  exact (PiLp.hasFDerivAt_toLp 2 _).comp_hasDerivAt t hp

theorem path_isParticle (d : Input) (hd : d.WellFormed) : IsParticle (velocity d) (path d) :=
  ⟨path_start d, fun _t ht => (path_hasDerivAt d hd ht).hasDerivWithinAt⟩

theorem path_unique (d : Input) (hd : d.WellFormed) {Y : ℝ → Space}
    (hY : IsParticle (velocity d) Y) {t : ℝ} (ht : 0 ≤ t) : Y t = path d t := by
  apply Trajectories.unique (v := fun t x => velocity d t (torusMk x))
    ((velocity_contDiff d).of_le (by exact WithTop.coe_le_coe.mpr le_top)) hY.2
    (path_isParticle d hd).2 _ ht
  rw [hY.1, path_start]

theorem path_event_iff (d : Input) (hd : d.WellFormed) : MaterialEvent (path d) ↔ Halts d :=
  CompilerPlanar.path_event_iff d hd

theorem eta_half_shift (z : ℝ) : eta (z + 1 / 2) = -eta z := by
  dsimp [eta]
  rw [show 2 * Real.pi * (z + 1 / 2 - 1 / 2) =
    2 * Real.pi * (z - 1 / 2) + Real.pi by ring, Real.sin_add_pi, neg_div]

theorem slope_half_shift (z : ℝ) : slope (z + 1 / 2) = -slope z := by
  dsimp [slope]
  rw [show 2 * Real.pi * (z + 1 / 2 - 1 / 2) =
    2 * Real.pi * (z - 1 / 2) + Real.pi by ring, Real.cos_add_pi]

theorem velocity_half_shift (d : Input) (t : ℝ) (q : Torus) :
    velocity d t (q + torusMk (EuclideanSpace.single 2 (1 / 2))) = -velocity d t q := by
  obtain ⟨x, rfl⟩ := mk_surjective q
  rw [← mk_add, velocity_cover, velocity_cover]
  have he := eta_half_shift (x 2)
  have hs := slope_half_shift (x 2)
  simp only [one_div] at he hs
  ext i
  fin_cases i <;> simp [he, hs]

theorem velocity_meanZero (d : Input) : MeanZero (velocity d) := by
  intro t _ht
  have : torusVolume.IsAddRightInvariant := by
    dsimp [torusVolume]
    infer_instance
  exact MeasureTheory.integral_eq_zero_of_add_right_eq_neg (velocity_half_shift d t)

end FluidLift

end
end PeriodicLattice

end OAI
