import OAI.MathematicalPhysics.Boltzmann.Branching.DatumBounds
import OAI.MathematicalPhysics.Boltzmann.Collision.AxialSecondMismatch
import OAI.MathematicalPhysics.Boltzmann.Jets.JetCoreConvergence
import OAI.MathematicalPhysics.Boltzmann.Jets.JetProfiles
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Topology.Algebra.Order.Floor

namespace OAI

section

/-! # A compact logarithmic phase for the dilated geometric mesh -/

noncomputable section

open Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.GeometricMesh

def phase (a η : ℝ) : ℝ := Real.exp (η*Int.fract (Real.log a/η))

def index (a η : ℝ) : ℤ := ⌊Real.log a/η⌋

theorem phase_bounds {η : ℝ} (hη : 0 < η) (a : ℝ) :
    phase a η ∈ Icc 1 (Real.exp η) := by
  constructor
  · exact Real.one_le_exp_iff.mpr (mul_nonneg hη.le (Int.fract_nonneg _))
  · apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_left (Int.fract_lt_one (Real.log a/η)).le hη.le).trans_eq (mul_one η)

theorem normalization {a η : ℝ} (ha : 0 < a) (hη : η ≠ 0) :
    a = phase a η*Real.exp (η*(index a η:ℝ)) := by
  unfold phase index
  rw [← Real.exp_add]
  have he : η*Int.fract (Real.log a/η)+η*(⌊Real.log a/η⌋:ℝ) = Real.log a := by
    unfold Int.fract
    field_simp
    ring
  rw [he,Real.exp_log ha]

theorem scale_ratio {s₀ r η : ℝ} (hs₀ : 0 < s₀) (hr : 0 < r) (hη : η ≠ 0) (j : ℕ) :
    DatumBounds.scale s₀ η j/r = phase (s₀/r) η*
      Real.exp (η*((index (s₀/r) η:ℝ)-(j:ℝ))) := by
  calc
    _ = (s₀/r)*Real.exp (-(j:ℝ)*η) := by unfold DatumBounds.scale; ring
    _ = (phase (s₀/r) η*Real.exp (η*(index (s₀/r) η:ℝ)))*Real.exp (-(j:ℝ)*η) := by
      exact congrArg (fun a : ℝ => a*Real.exp (-(j:ℝ)*η)) (normalization (div_pos hs₀ hr) hη)
    _ = _ := by
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring

theorem phase_subsequence {η : ℝ} (hη : 0 < η) (s₀ : ℝ) (r : ℕ → ℝ) :
    ∃ θ ∈ Icc 1 (Real.exp η), ∃ κ : ℕ → ℕ, StrictMono κ ∧
      Tendsto (fun n => phase (s₀/r (κ n)) η) atTop (𝓝 θ) :=
  isCompact_Icc.tendsto_subseq (fun n => phase_bounds hη (s₀/r n))

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # Fixed limiting mesh points arise from actual annular indices -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness.GeometricMesh

theorem index_tendsto_atTop {s₀ η : ℝ} {r : ℕ → ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : ∀ n, 0 < r n)
    (hrlim : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => index (s₀/r n) η) atTop atTop := by
  have hr' : Tendsto r atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hrlim,Eventually.of_forall hr⟩
  have hinv := tendsto_inv_nhdsGT_zero.comp hr'
  have hratio : Tendsto (fun n => s₀/r n) atTop atTop := by
    simpa only [div_eq_mul_inv,Function.comp_def] using hinv.const_mul_atTop hs₀
  exact tendsto_floor_atTop.comp ((Real.tendsto_log_atTop.comp hratio).atTop_div_const hη)

def annularIndex (s₀ η : ℝ) (r : ℕ → ℝ) (k : ℤ) (n : ℕ) : ℕ :=
  (index (s₀/r n) η-k).toNat

theorem annularIndex_eventually {s₀ η : ℝ} {r : ℕ → ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : ∀ n, 0 < r n)
    (hrlim : Tendsto r atTop (𝓝 0)) (k : ℤ) :
    ∀ᶠ n in atTop, (index (s₀/r n) η:ℝ)-(annularIndex s₀ η r k n:ℝ) = (k:ℝ) := by
  filter_upwards [(index_tendsto_atTop hs₀ hη hr hrlim).eventually_ge_atTop k] with n hn
  have he : (annularIndex s₀ η r k n:ℤ) = index (s₀/r n) η-k :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hn)
  have he' : (annularIndex s₀ η r k n:ℝ) = (index (s₀/r n) η:ℝ)-(k:ℝ) := by
    exact_mod_cast he
  rw [he']
  ring

theorem mesh_point_approximation {s₀ η θ : ℝ} {r : ℕ → ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : ∀ n, 0 < r n)
    (hrlim : Tendsto r atTop (𝓝 0))
    (hphase : Tendsto (fun n => phase (s₀/r n) η) atTop (𝓝 θ)) (k : ℤ) :
    Tendsto (fun n => DatumBounds.scale s₀ η (annularIndex s₀ η r k n)/r n)
      atTop (𝓝 (θ*Real.exp (η*(k:ℝ)))) := by
  apply (hphase.mul_const (Real.exp (η*(k:ℝ)))).congr'
  filter_upwards [annularIndex_eventually hs₀ hη hr hrlim k] with n hn
  rw [scale_ratio hs₀ (hr n) hη.ne',hn]

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # Disjoint annuli in the limiting geometric mesh -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.GeometricMesh

def point (θ η : ℝ) (k : ℤ) : ℝ := θ*Real.exp (η*(k:ℝ))

theorem point_pos {θ : ℝ} (hθ : 0 < θ) (η : ℝ) (k : ℤ) : 0 < point θ η k :=
  mul_pos hθ (Real.exp_pos _)

theorem point_mono {θ η : ℝ} (hθ : 0 ≤ θ) (hη : 0 ≤ η) : Monotone (point θ η) := by
  intro i j hij
  unfold point
  apply mul_le_mul_of_nonneg_left _ hθ
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hij) hη

theorem point_succ (θ η : ℝ) (k : ℤ) : point θ η (k+1) = Real.exp η*point θ η k := by
  unfold point
  rw [Int.cast_add,Int.cast_one,mul_add,mul_one,Real.exp_add]
  ring

theorem point_gap {θ η : ℝ} (hθ : 0 ≤ θ) (hη : 0 ≤ η) {i j : ℤ} (hij : i < j) :
    Real.exp η*point θ η i ≤ point θ η j := by
  rw [← point_succ]
  exact point_mono hθ hη (by omega)

theorem shells_disjoint {θ η : ℝ} (hθ : 0 ≤ θ) (hη : 0 ≤ η) {i j : ℤ} (hij : i ≠ j) :
    Disjoint (JetGeometry.scaleShell η (point θ η i))
      (JetGeometry.scaleShell η (point θ η j)) := by
  apply Set.disjoint_left.mpr
  intro y hi hj
  obtain hij | hji := lt_or_gt_of_ne hij
  · exact (hi.2.trans_le (point_gap hθ hη hij)).not_ge hj.1.le
  · exact (hj.2.trans_le (point_gap hθ hη hji)).not_ge hi.1.le

theorem phase_lt_exp {η : ℝ} (hη : 0 < η) (a : ℝ) : phase a η < Real.exp η := by
  apply Real.exp_lt_exp.mpr
  exact (mul_lt_mul_of_pos_left (Int.fract_lt_one _) hη).trans_eq (mul_one η)

theorem cell_bounds {θ η ρ : ℝ} (hθ : 0 < θ) (hη : 0 < η) (hρ : 0 < ρ) :
    point θ η (index (ρ/θ) η) ≤ ρ ∧
      ρ < Real.exp η*point θ η (index (ρ/θ) η) := by
  have hp := point_pos hθ η (index (ρ/θ) η)
  have he : ρ = phase (ρ/θ) η*point θ η (index (ρ/θ) η) := by
    have h := normalization (div_pos hρ hθ) hη.ne'
    calc
      ρ = θ*(ρ/θ) := by field_simp
      _ = θ*(phase (ρ/θ) η*Real.exp (η*(index (ρ/θ) η:ℝ))) := congrArg (θ*·) h
      _ = _ := by unfold point; ring
  constructor
  · calc
      _ ≤ phase (ρ/θ) η*point θ η (index (ρ/θ) η) :=
        le_mul_of_one_le_left hp.le (phase_bounds hη _).1
      _ = ρ := he.symm
  · calc
      ρ = phase (ρ/θ) η*point θ η (index (ρ/θ) η) := he
      _ < _ := mul_lt_mul_of_pos_right (phase_lt_exp hη _) hp

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # Retention of limiting mesh points above the terminal scale -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness.GeometricMesh

theorem eventually_retained {s₀ η θ l : ℝ} {r : ℕ → ℝ} {N : ℕ → ℕ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : ∀ n, 0 < r n)
    (hrlim : Tendsto r atTop (𝓝 0))
    (hphase : Tendsto (fun n => phase (s₀/r n) η) atTop (𝓝 θ))
    (hbottom : Tendsto (fun n => DatumBounds.scale s₀ η (N n)/r n) atTop (𝓝 l))
    (k : ℤ) (hk : l < θ*Real.exp (η*(k:ℝ))) :
    ∀ᶠ n in atTop, annularIndex s₀ η r k n < N n := by
  have he := hbottom.eventually_lt (mesh_point_approximation hs₀ hη hr hrlim hphase k) hk
  filter_upwards [he] with n hn
  by_contra h
  have hle := JetGeometry.scale_antitone hs₀.le hη.le (le_of_not_gt h)
  exact (not_lt_of_ge hle) ((div_lt_div_iff_of_pos_right (hr n)).mp hn)

theorem eventually_below_terminal {s₀ η θ l : ℝ} {r : ℕ → ℝ} {N : ℕ → ℕ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : ∀ n, 0 < r n)
    (hrlim : Tendsto r atTop (𝓝 0))
    (hphase : Tendsto (fun n => phase (s₀/r n) η) atTop (𝓝 θ))
    (hbottom : Tendsto (fun n => DatumBounds.scale s₀ η (N n)/r n) atTop (𝓝 l))
    (k : ℤ) (hk : θ*Real.exp (η*(k:ℝ)) < l) :
    ∀ᶠ n in atTop, N n < annularIndex s₀ η r k n := by
  have he := (mesh_point_approximation hs₀ hη hr hrlim hphase k).eventually_lt hbottom hk
  filter_upwards [he] with n hn
  by_contra h
  have hle := JetGeometry.scale_antitone hs₀.le hη.le (le_of_not_gt h)
  exact (not_lt_of_ge hle) ((div_lt_div_iff_of_pos_right (hr n)).mp hn)

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # The atomic background on the limiting geometric mesh -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

def scale (θ η : ℝ) (y : Transverse) : ℝ :=
  GeometricMesh.point θ η (GeometricMesh.index (‖y‖/θ) η)

/-- Here `l` is the limit of the first excluded scale `scale (N+1) / r`.
The retained colors have strictly larger scales. -/
def active (θ η l : ℝ) (y : Transverse) : Prop :=
  l < scale θ η y ∧ y ∈ JetGeometry.scaleShell η (scale θ η y)

def background (θ η l K α γ t : ℝ) (x : JetPrototype.Space) : Measure Velocity := by
  classical
  exact if active θ η l x.1 then AxialBackground.cell K α γ (scale θ η x.1) t x.2 else 0

theorem scale_pos {θ : ℝ} (hθ : 0 < θ) (η : ℝ) (y : Transverse) : 0 < scale θ η y :=
  GeometricMesh.point_pos hθ η _

theorem scale_measurable (θ η : ℝ) : Measurable (scale θ η) := by
  unfold scale GeometricMesh.point GeometricMesh.index
  fun_prop

theorem active_measurableSet (θ η l : ℝ) : MeasurableSet {y | active θ η l y} :=
  (measurableSet_lt measurable_const (scale_measurable θ η)).inter
    ((measurableSet_lt (scale_measurable θ η) measurable_norm).inter
      (measurableSet_lt measurable_norm ((scale_measurable θ η).const_mul _)))

theorem scale_eq_of_shell {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η)
    {k : ℤ} {y : Transverse} (hy : y ∈ JetGeometry.scaleShell η (GeometricMesh.point θ η k)) :
    scale θ η y = GeometricMesh.point θ η k := by
  have hρ : 0 < ‖y‖ := (GeometricMesh.point_pos hθ η k).trans hy.1
  have hb := GeometricMesh.cell_bounds hθ hη hρ
  have hi : GeometricMesh.index (‖y‖/θ) η = k := by
    rcases lt_trichotomy (GeometricMesh.index (‖y‖/θ) η) k with h | h | h
    · exact False.elim ((hb.2.trans_le (GeometricMesh.point_gap hθ.le hη.le h)).not_ge hy.1.le)
    · exact h
    · exact False.elim ((hy.2.trans_le (GeometricMesh.point_gap hθ.le hη.le h)).not_ge hb.1)
  exact congrArg (GeometricMesh.point θ η) hi

theorem background_on_shell {θ η l K α γ t : ℝ} (hθ : 0 < θ) (hη : 0 < η)
    {k : ℤ} {x : JetPrototype.Space}
    (hx : x.1 ∈ JetGeometry.scaleShell η (GeometricMesh.point θ η k))
    (hl : l < GeometricMesh.point θ η k) :
    background θ η l K α γ t x = AxialBackground.cell K α γ (GeometricMesh.point θ η k) t x.2 := by
  have hs := scale_eq_of_shell hθ hη hx
  have ha : active θ η l x.1 := by rw [active,hs]; exact ⟨hl,hx⟩
  rw [background,ite_eq_left ha,hs]

theorem background_gain_bound {θ η l K α γ t q : ℝ}
    (hθ : 0 < θ) (hl : 0 ≤ l) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (ht : 0 < t) (hq₁ : 1 < q) (hq₂ : q < 2)
    (x : JetPrototype.Space) {v : Velocity} (hv : transverse v ≠ 0) :
    normalizedChartGain (background θ η l K α γ t x) q v ≤
      2*(ENNReal.ofReal ((1/4)*((K*max 1 (α*γ)⁻¹)/(l+t)))*
        SheetTotal.bound q (Real.exp (8*(1+α)^2))) := by
  classical
  by_cases ha : active θ η l x.1
  · rw [background,ite_eq_left ha]
    apply (AxialBackground.cell_gain_bound hK hα hγ (scale_pos hθ η x.1) ht.le hq₁ hq₂ hv).trans
    apply mul_le_mul' le_rfl
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact div_le_div_of_nonneg_left (mul_nonneg hK (le_max_of_le_left zero_le_one))
      (add_pos_of_nonneg_of_pos hl ht) (by linarith [ha.1])
  · rw [background,ite_eq_right ha]
    simp only [normalizedChartGain,chartGain,MeasureTheory.lintegral_zero_measure,mul_zero]
    exact zero_le

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The annular label uses the geometric scale with index shifted by one -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness.GeometricMesh

def jetIndex (s₀ η : ℝ) (r : ℕ → ℝ) (k : ℤ) (n : ℕ) : ℕ :=
  annularIndex s₀ η r k n-1

theorem annularIndex_eventually_pos {s₀ η : ℝ} {r : ℕ → ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : ∀ n, 0 < r n)
    (hrlim : Tendsto r atTop (𝓝 0)) (k : ℤ) :
    ∀ᶠ n in atTop, 0 < annularIndex s₀ η r k n := by
  filter_upwards [(index_tendsto_atTop hs₀ hη hr hrlim).eventually_ge_atTop (k+1)] with n hn
  unfold annularIndex
  omega

theorem jetIndex_succ_eventually {s₀ η : ℝ} {r : ℕ → ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : ∀ n, 0 < r n)
    (hrlim : Tendsto r atTop (𝓝 0)) (k : ℤ) :
    ∀ᶠ n in atTop, jetIndex s₀ η r k n+1 = annularIndex s₀ η r k n := by
  filter_upwards [annularIndex_eventually_pos hs₀ hη hr hrlim k] with n hn
  exact Nat.sub_add_cancel hn

theorem jet_scale_approximation {s₀ η θ : ℝ} {r : ℕ → ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : ∀ n, 0 < r n)
    (hrlim : Tendsto r atTop (𝓝 0))
    (hphase : Tendsto (fun n => phase (s₀/r n) η) atTop (𝓝 θ)) (k : ℤ) :
    Tendsto (fun n => JetGeometry.jetScale s₀ η (jetIndex s₀ η r k n)/r n)
      atTop (𝓝 (θ*Real.exp (η*(k:ℝ)))) := by
  apply (mesh_point_approximation hs₀ hη hr hrlim hphase k).congr'
  filter_upwards [jetIndex_succ_eventually hs₀ hη hr hrlim k] with n hn
  exact congrArg (fun j => DatumBounds.scale s₀ η j/r n) hn.symm

theorem jetIndex_eventually_retained {s₀ η θ l : ℝ} {r : ℕ → ℝ} {N : ℕ → ℕ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : ∀ n, 0 < r n)
    (hrlim : Tendsto r atTop (𝓝 0))
    (hphase : Tendsto (fun n => phase (s₀/r n) η) atTop (𝓝 θ))
    (hbottom : Tendsto (fun n => DatumBounds.scale s₀ η (N n+1)/r n) atTop (𝓝 l))
    (k : ℤ) (hk : l < θ*Real.exp (η*(k:ℝ))) :
    ∀ᶠ n in atTop, jetIndex s₀ η r k n < N n := by
  filter_upwards [eventually_retained hs₀ hη hr hrlim hphase hbottom k hk,
    jetIndex_succ_eventually hs₀ hη hr hrlim k] with n hn he
  omega

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # Only finitely many geometric shells meet a fixed radial window -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.GeometricMesh

theorem point_strictMono {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) :
    StrictMono (point θ η) := by
  intro i j hij
  apply mul_lt_mul_of_pos_left _ hθ
  apply Real.exp_lt_exp.mpr
  exact mul_lt_mul_of_pos_left (by exact_mod_cast hij) hη

theorem shell_index {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η)
    {k : ℤ} {y : VelocityWeight.Transverse}
    (hy : y ∈ JetGeometry.scaleShell η (point θ η k)) :
    index (‖y‖/θ) η = k :=
  (point_strictMono hθ hη).injective (GeometricBackground.scale_eq_of_shell hθ hη hy)

theorem index_mono {a b η : ℝ} (ha : 0 < a) (hab : a ≤ b) (hη : 0 < η) :
    index a η ≤ index b η :=
  Int.floor_mono (div_le_div_of_nonneg_right (Real.log_le_log ha hab) hη.le)

theorem shell_index_window {θ η δ R : ℝ} (hθ₁ : 1 ≤ θ) (hθ₂ : θ ≤ Real.exp η)
    (hη : 0 < η) (hδ : 0 < δ) {k : ℤ} {y : VelocityWeight.Transverse}
    (hy : y ∈ JetGeometry.scaleShell η (point θ η k)) (hlo : δ ≤ ‖y‖) (hhi : ‖y‖ ≤ R) :
    index (δ/Real.exp η) η ≤ k ∧ k ≤ index R η := by
  have hθ : 0 < θ := zero_lt_one.trans_le hθ₁
  have hl : δ/Real.exp η ≤ ‖y‖/θ := by
    apply (div_le_div_iff₀ (Real.exp_pos η) hθ).mpr
    exact (mul_le_mul_of_nonneg_left hθ₂ hδ.le).trans
      (mul_le_mul_of_nonneg_right hlo (Real.exp_pos η).le)
  have hu : ‖y‖/θ ≤ R := by
    apply (div_le_iff₀ hθ).mpr
    exact hhi.trans (le_mul_of_one_le_right ((norm_nonneg y).trans hhi) hθ₁)
  have hidx := shell_index hθ hη hy
  exact ⟨hidx ▸ index_mono (div_pos hδ (Real.exp_pos η)) hl hη,
    hidx ▸ index_mono (div_pos (hδ.trans_le hlo) hθ) hu hη⟩

/-- The integer mesh coordinate of an actual jet label. -/
def jetMeshIndex (s₀ η r : ℝ) (j : ℕ) : ℤ := index (s₀/r) η-(j+1:ℕ)

theorem jetScale_ratio_exact {s₀ η r : ℝ} (hs₀ : 0 < s₀) (hr : 0 < r) (hη : 0 < η) (j : ℕ) :
    JetGeometry.jetScale s₀ η j/r = point (phase (s₀/r) η) η (jetMeshIndex s₀ η r j) := by
  rw [JetGeometry.jetScale,scale_ratio hs₀ hr hη.ne']
  unfold point jetMeshIndex
  push_cast
  rfl

theorem jetIndex_at_meshIndex (s₀ η : ℝ) (r : ℕ → ℝ) (n j : ℕ) :
    jetIndex s₀ η r (jetMeshIndex s₀ η (r n) j) n = j := by
  simp [jetIndex,annularIndex,jetMeshIndex]

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # Reindexing a finite cold sum on a fixed geometric mesh window -/

noncomputable section

namespace BoltzmannNonuniqueness.GeometricMesh

theorem meshIndex_at_jetIndex (s₀ η : ℝ) (r : ℕ → ℝ) (n : ℕ) {k : ℤ}
    (hk : k < index (s₀/r n) η) :
    jetMeshIndex s₀ η (r n) (jetIndex s₀ η r k n) = k := by
  unfold jetMeshIndex jetIndex annularIndex
  have he := Int.toNat_of_nonneg (by omega : 0 ≤ index (s₀/r n) η-k)
  omega

theorem finite_sum_on_window (s₀ η : ℝ) (r : ℕ → ℝ) (n N : ℕ) (L U : ℤ)
    (hU : U < index (s₀/r n) η) (f : ℕ → ℝ)
    (hsupp : ∀ j < N, f j ≠ 0 → jetMeshIndex s₀ η (r n) j ∈ Finset.Icc L U) :
    (∑ j ∈ Finset.range N, f j) = ∑ k ∈ Finset.Icc L U,
      if jetIndex s₀ η r k n < N then f (jetIndex s₀ η r k n) else 0 := by
  classical
  apply Finset.sum_bij_ne_zero (fun j _ _ => jetMeshIndex s₀ η (r n) j)
  · intro j hj hfj
    exact hsupp j (Finset.mem_range.mp hj) hfj
  · intro j₁ _ _ j₂ _ _ he
    unfold jetMeshIndex at he
    omega
  · intro k hk hfk
    have hj : jetIndex s₀ η r k n < N := by
      by_contra h
      simp only [h,ite_false,ne_eq,not_true_eq_false] at hfk
    have he := meshIndex_at_jetIndex s₀ η r n ((Finset.mem_Icc.mp hk).2.trans_lt hU)
    exact ⟨jetIndex s₀ η r k n,Finset.mem_range.mpr hj,by simpa only [hj,ite_true] using hfk,he⟩
  · intro j hj _
    rw [jetIndex_at_meshIndex]
    exact (ite_eq_left (Finset.mem_range.mp hj)).symm

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # A uniform finite list of non-small scales in a geometric mesh -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.GeometricMesh

theorem index_point_div_phase {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) (k : ℤ) :
    index (point θ η k/θ) η = k := by
  unfold point index
  rw [mul_div_cancel_left₀ _ hθ.ne',Real.log_exp,mul_div_cancel_left₀ _ hη.ne']
  exact Int.floor_intCast k

theorem point_window {θ η δ R : ℝ} (hθ₁ : 1 ≤ θ) (hθ₂ : θ ≤ Real.exp η)
    (hη : 0 < η) (hδ : 0 < δ) {k : ℤ}
    (hlo : δ ≤ point θ η k) (hhi : point θ η k ≤ R) :
    k ∈ Icc (index (δ/Real.exp η) η) (index R η) := by
  have hθ : 0 < θ := zero_lt_one.trans_le hθ₁
  have hp : 0 < point θ η k := mul_pos hθ (Real.exp_pos _)
  have hl : δ/Real.exp η ≤ point θ η k/θ := by
    apply (div_le_div_iff₀ (Real.exp_pos η) hθ).mpr
    exact (mul_le_mul_of_nonneg_left hθ₂ hδ.le).trans
      (mul_le_mul_of_nonneg_right hlo (Real.exp_pos η).le)
  have hh : point θ η k/θ ≤ R := by
    apply (div_le_iff₀ hθ).mpr
    exact hhi.trans (le_mul_of_one_le_right (hp.le.trans hhi) hθ₁)
  have he := index_point_div_phase hθ hη k
  exact ⟨he ▸ index_mono (div_pos hδ (Real.exp_pos η)) hl hη,
    he ▸ index_mono (div_pos hp hθ) hh hη⟩

theorem jetMeshIndex_injective (s₀ η r : ℝ) : Function.Injective (jetMeshIndex s₀ η r) := by
  intro j k h
  unfold jetMeshIndex at h
  omega

/-- The bound is independent of the dilation and of the retained top index. -/
theorem retained_scale_card_le {s₀ η r δ R : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (hr : 0 < r) (hδ : 0 < δ) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, δ ≤ JetGeometry.jetScale s₀ η j/r ∧
      JetGeometry.jetScale s₀ η j/r ≤ R) :
    J.card ≤ (Finset.Icc (index (δ/Real.exp η) η) (index R η)).card := by
  classical
  apply Finset.card_le_card_of_injOn (jetMeshIndex s₀ η r)
  · intro j hj
    change jetMeshIndex s₀ η r j ∈ Finset.Icc (index (δ/Real.exp η) η) (index R η)
    rw [Finset.mem_Icc]
    have h := hJ j hj
    rw [jetScale_ratio_exact hs₀ hr hη] at h
    exact point_window (phase_bounds hη (s₀/r)).1 (phase_bounds hη (s₀/r)).2 hη hδ h.1 h.2
  · exact (jetMeshIndex_injective s₀ η r).injOn

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # Discreteness of the normalized geometric scales at a positive limit -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness.GeometricMesh

theorem scale_succ (s₀ η : ℝ) (m : ℕ) :
    Real.exp η*DatumBounds.scale s₀ η (m+1) = DatumBounds.scale s₀ η m := by
  unfold DatumBounds.scale
  rw [mul_left_comm,← Real.exp_add]
  congr 2
  push_cast
  ring

theorem scale_gap {s₀ η : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η) {m n : ℕ} (hmn : m < n) :
    Real.exp η*DatumBounds.scale s₀ η n ≤ DatumBounds.scale s₀ η m := by
  calc
    _ ≤ Real.exp η*DatumBounds.scale s₀ η (m+1) :=
      mul_le_mul_of_nonneg_left (JetGeometry.scale_antitone hs₀ hη hmn) (Real.exp_pos η).le
    _ = _ := scale_succ s₀ η m

theorem indices_eventually_eq_of_same_positive_limit {s₀ η μ : ℝ}
    (hs₀ : 0 ≤ s₀) (hη : 0 < η) (hμ : 0 < μ)
    {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) {m n : ℕ → ℕ}
    (hm : Tendsto (fun j => DatumBounds.scale s₀ η (m j)/r j) atTop (𝓝 μ))
    (hn : Tendsto (fun j => DatumBounds.scale s₀ η (n j)/r j) atTop (𝓝 μ)) :
    ∀ᶠ j in atTop, m j = n j := by
  have hgap : μ < Real.exp η*μ := by
    have he : 1 < Real.exp η := Real.one_lt_exp_iff.mpr hη
    nlinarith
  have hmn := hm.eventually_lt (hn.const_mul (Real.exp η)) hgap
  have hnm := hn.eventually_lt (hm.const_mul (Real.exp η)) hgap
  filter_upwards [hmn,hnm] with j hj₁ hj₂
  rcases lt_trichotomy (m j) (n j) with h | h | h
  · have hb := div_le_div_of_nonneg_right (scale_gap hs₀ hη.le h) (hr j).le
    rw [mul_div_assoc] at hb
    exact False.elim ((not_lt_of_ge hb) hj₁)
  · exact h
  · have hb := div_le_div_of_nonneg_right (scale_gap hs₀ hη.le h) (hr j).le
    rw [mul_div_assoc] at hb
    exact False.elim ((not_lt_of_ge hb) hj₂)

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # Actual retained mesh scales have positive limits and vanishing thermal widths -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness.GeometricMesh

theorem mesh_scale_tendsto_zero {s₀ η θ : ℝ} {r : ℕ → ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : ∀ n, 0 < r n)
    (hrlim : Tendsto r atTop (𝓝 0))
    (hphase : Tendsto (fun n => phase (s₀/r n) η) atTop (𝓝 θ)) (k : ℤ) :
    Tendsto (fun n => JetGeometry.jetScale s₀ η (jetIndex s₀ η r k n)) atTop (𝓝 0) := by
  have hm := hrlim.mul (jet_scale_approximation hs₀ hη hr hrlim hphase k)
  have he (n : ℕ) : r n*(JetGeometry.jetScale s₀ η (jetIndex s₀ η r k n)/r n) =
      JetGeometry.jetScale s₀ η (jetIndex s₀ η r k n) := by
    field_simp [(hr n).ne']
  simpa only [he,zero_mul] using hm

theorem mesh_width_tendsto_zero {s₀ η θ : ℝ} {r : ℕ → ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : ∀ n, 0 < r n)
    (hrlim : Tendsto r atTop (𝓝 0))
    (hphase : Tendsto (fun n => phase (s₀/r n) η) atTop (𝓝 θ)) (d₀ : ℝ) (k : ℤ) :
    Tendsto (fun n => d₀*JetGeometry.jetScale s₀ η (jetIndex s₀ η r k n)^10)
      atTop (𝓝 0) := by
  simpa using (mesh_scale_tendsto_zero hs₀ hη hr hrlim hphase k).pow 10 |>.const_mul d₀

end BoltzmannNonuniqueness.GeometricMesh

end

end

end OAI
