import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Loading
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Material

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology NNReal
open Filter Set

def TimeCollars {F : Type*} [Zero F] (v : Field F) : Prop :=
  ∀ t, t < 1 / 4 ∨ 3 / 4 < t → v t = 0

def repeatTemplate (v : Velocity) : Velocity :=
  fun t x => ∑' n : ℤ, v (t - n) x

lemma repeatTemplate_eq {v : Velocity} (hc : TimeCollars v) {t : ℝ} {n : ℤ}
    (ht : t - n ∈ Ioo (-1 / 4 : ℝ) (5 / 4)) (x : Space) :
    repeatTemplate v t x = v (t - n) x := by
  apply tsum_eq_single n
  intro m hmn
  have hzero : v (t - m) = 0 := by
    apply hc
    rcases lt_or_gt_of_ne hmn with hm | hm
    · right
      have hh : (m : ℝ) + 1 ≤ n := by exact_mod_cast Int.add_one_le_iff.mpr hm
      linarith [ht.1]
    · left
      have hh : (n : ℝ) + 1 ≤ m := by exact_mod_cast Int.add_one_le_iff.mpr hm
      linarith [ht.2]
  rw [hzero]
  rfl

lemma repeatTemplate_zero_period (v : Velocity) : Function.Periodic (repeatTemplate v) 1 := by
  intro t
  funext x
  change (∑' n : ℤ, v (t + 1 - n) x) = ∑' n : ℤ, v (t - n) x
  have hh := (Equiv.addRight (1 : ℤ)).tsum_eq (fun n : ℤ => v (t + 1 - n) x)
  simpa only [Equiv.coe_addRight, Int.cast_add, Int.cast_one, add_sub_add_right_eq_sub] using hh.symm

lemma repeatTemplate_on_unit {v : Velocity} (hc : TimeCollars v) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : repeatTemplate v t = v t := by
  funext x
  simpa using repeatTemplate_eq hc (n := 0) (by norm_num; constructor <;> linarith [ht.1, ht.2]) x

lemma repeatTemplate_jointSmooth {v : Velocity} (hv : JointSmooth v) (hc : TimeCollars v) :
    JointSmooth (repeatTemplate v) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  let n : ℤ := ⌊z.1⌋
  have ht : z.1 - n ∈ Ioo (-1 / 4 : ℝ) (5 / 4) := by
    have h₁ := Int.floor_le z.1
    have h₂ := Int.lt_floor_add_one z.1
    change -1 / 4 < z.1 - (⌊z.1⌋ : ℤ) ∧ z.1 - (⌊z.1⌋ : ℤ) < 5 / 4
    constructor <;> linarith
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ × Space => v (y.1 - n) y.2) :=
    hv.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)
  apply hg.contDiffAt.congr_of_eventuallyEq
  have hnn : ∀ᶠ y : ℝ × Space in 𝓝 z, y.1 - n ∈ Ioo (-1 / 4 : ℝ) (5 / 4) :=
    ((continuous_fst.sub continuous_const).continuousAt).eventually (isOpen_Ioo.mem_nhds ht)
  exact hnn.mono (fun y hy => repeatTemplate_eq hc hy y.2)

lemma repeatTemplate_supported {K : Set Space} {v : Velocity} (hs : SpatiallySupported K v) :
    SpatiallySupported K (repeatTemplate v) := by
  intro t x hx
  simp only [repeatTemplate, hs _ x hx, tsum_zero]

lemma repeatTemplate_divergence {v : Velocity} (hc : TimeCollars v)
    (hd : ∀ t x, div v t x = 0) (t : ℝ) (x : Space) :
    div (repeatTemplate v) t x = 0 := by
  have he : repeatTemplate v t = v (t - (⌊t⌋ : ℤ)) := by
    funext y
    apply repeatTemplate_eq hc
    have h₁ := Int.floor_le t
    have h₂ := Int.lt_floor_add_one t
    constructor <;> linarith
  simpa only [div, spaceD, he] using hd (t - (⌊t⌋ : ℤ)) x

def afterLoadingGate (t : ℝ) : ℝ := Real.smoothTransition (4 * t - 3)

def loadedRepeat (load template : Velocity) : Velocity :=
  fun t x => load t x + afterLoadingGate t • repeatTemplate template t x

lemma loadedRepeat_jointSmooth {load v : Velocity} (hl : JointSmooth load)
    (hv : JointSmooth v) (hc : TimeCollars v) : JointSmooth (loadedRepeat load v) := by
  have hg : JointSmooth (fun t (_ : Space) => afterLoadingGate t) := by
    dsimp [JointSmooth, afterLoadingGate]
    fun_prop
  exact hl.add (hg.smul (repeatTemplate_jointSmooth hv hc))

lemma loadedRepeat_before {load v : Velocity} (hc : TimeCollars v)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) : loadedRepeat load v t = load t := by
  have hs : afterLoadingGate t • repeatTemplate v t = (0 : Space → Space) := by
    by_cases ht : t ≤ 3 / 4
    · have he : afterLoadingGate t = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
      rw [he, zero_smul]
    · rw [repeatTemplate_on_unit hc ⟨ht₀, ht₁⟩, hc t (Or.inr (lt_of_not_ge ht)), smul_zero]
  ext x i
  change (load t x + (afterLoadingGate t • repeatTemplate v t) x) i = load t x i
  rw [hs]
  simp

lemma loadedRepeat_after {load v : Velocity} (hl : TimeCollars load)
    {t : ℝ} (ht : 1 ≤ t) : loadedRepeat load v t = repeatTemplate v t := by
  have he : afterLoadingGate t = 1 := Real.smoothTransition.one_of_one_le (by linarith)
  ext x i
  simp [loadedRepeat, he, hl t (Or.inr (by linarith))]

lemma loadedRepeat_support {K L : Set Space} {load v : Velocity}
    (hl : SpatiallySupported L load) (hv : SpatiallySupported K v) :
    SpatiallySupported (L ∪ K) (loadedRepeat load v) := by
  intro t x hx
  have hn := not_or.mp hx
  dsimp [loadedRepeat]
  rw [hl t x hn.1, repeatTemplate_supported hv t x hn.2, smul_zero, add_zero]

lemma loadedRepeat_repeats {load v : Velocity} (hl : TimeCollars load) :
    RepeatsAfter 1 (loadedRepeat load v) := by
  intro t ht
  rw [loadedRepeat_after hl (by linarith), loadedRepeat_after hl ht]
  exact repeatTemplate_zero_period v t

lemma div_add {u v : Velocity} (hu : JointSmooth u) (hv : JointSmooth v) (t : ℝ) (x : Space) :
    div (fun t x => u t x + v t x) t x = div u t x + div v t x := by
  simp only [div, spaceD,
    fderiv_fun_add ((hu.slice t).differentiable (by simp) x)
      ((hv.slice t).differentiable (by simp) x), add_apply, Pi.add_apply, Finset.sum_add_distrib]

lemma div_time_smul {u : Velocity} (hu : JointSmooth u) (a : ℝ → ℝ) (t : ℝ) (x : Space) :
    div (fun t x => a t • u t x) t x = a t * div u t x := by
  simp only [div, spaceD, fderiv_fun_const_smul ((hu.slice t).differentiable (by simp) x),
    smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

lemma loadedRepeat_divergence {load v : Velocity} (hl : JointSmooth load)
    (hv : JointSmooth v) (hc : TimeCollars v)
    (hld : ∀ t x, div load t x = 0) (hvd : ∀ t x, div v t x = 0) (t : ℝ) (x : Space) :
    div (loadedRepeat load v) t x = 0 := by
  have hr := repeatTemplate_jointSmooth hv hc
  have hg : JointSmooth (fun t (_ : Space) => afterLoadingGate t) := by
    dsimp [JointSmooth, afterLoadingGate]
    fun_prop
  change div (fun t x => load t x + afterLoadingGate t • repeatTemplate v t x) t x = 0
  have hgr : JointSmooth (fun t x => afterLoadingGate t • repeatTemplate v t x) := hg.smul hr
  rw [div_add hl hgr, div_time_smul hr, hld t x, repeatTemplate_divergence hc hvd]
  ring

theorem loaded_template_realization (z : Space) {η : ℝ} (hη : 0 < η)
    {K : Set Space} (hK : IsCompact K) {v : Velocity}
    (hv : JointSmooth v) (hc : TimeCollars v) (hs : SpatiallySupported K v)
    (hd : ∀ t x, div v t x = 0) :
    let U := loadedRepeat (loadingVelocity z η) v
    JointSmooth U ∧ SpatiallySupported (loadingSupport z η ∪ K) U ∧
    BoundedMixed U ∧ (∀ x, U 0 x = 0) ∧
    Function.Periodic (repeatTemplate v) 1 ∧
    (∀ t, 1 ≤ t → U t = repeatTemplate v t) ∧
    (∃ X, IsMaterialFlow U X) ∧
    ∀ ν : ℝ, ZeroDataSolution ν
      (affineForce (inertialCoefficient U) (viscousCoefficient U) ν) U (fun _ _ => 0) := by
  let load := loadingVelocity z η
  have hl : JointSmooth load := loadingVelocity_jointSmooth z η
  have hlc : TimeCollars load := fun _ ht => loadingVelocity_zero ht
  have hU := loadedRepeat_jointSmooth hl hv hc
  have hUs := loadedRepeat_support (loadingVelocity_supported z hη) hs
  have hUp := loadedRepeat_repeats (v := v) hlc
  have hUc := (loadingSupport_compact z η).union hK
  have hzero : ∀ x, loadedRepeat load v 0 x = 0 := by
    intro x
    rw [loadedRepeat_before hc le_rfl (by norm_num), hlc 0 (Or.inl (by norm_num))]
    rfl
  exact ⟨hU, hUs, boundedMixed_of_compact_repeating hUc hU hUs hUp, hzero,
    repeatTemplate_zero_period v, fun _ ht => loadedRepeat_after hlc ht,
    exists_materialFlow_of_compact_repeating hUc hU hUs hUp,
    fun ν => residual_zero_pressure_solution ν _ hU.smooth hzero
      (fun t _ x => loadedRepeat_divergence hl hv hc (loadingVelocity_divergence z η) hd t x)⟩

end BalancedTransport.Geometry
end

end OAI
