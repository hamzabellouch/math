import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Model
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.UniformDerivatives

namespace OAI

noncomputable section
namespace VelocityDetection.PeriodicSpace
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction

abbrev Torus (n : ℕ) := Fin n → AddCircle (1 : ℝ)

abbrev compatible (n : ℕ) := C(Torus n, ℝ)

def cover {n : ℕ} (X : Coord n) : Torus n := fun i => (X i : AddCircle (1 : ℝ))

theorem continuous_cover (n : ℕ) : Continuous (@cover n) := by
  apply continuous_pi
  intro i
  exact QuotientAddGroup.continuous_mk.comp (continuous_apply i)

theorem cover_surjective (n : ℕ) : Surjective (@cover n) := by
  intro Z
  choose X hX using fun i => QuotientAddGroup.mk_surjective (Z i)
  exact ⟨X, funext hX⟩

@[simp] theorem cover_add {n : ℕ} (X Y : Coord n) : cover (X + Y) = cover X + cover Y := rfl

@[simp] theorem cover_zero {n : ℕ} : cover (0 : Coord n) = 0 := rfl

def realLift {n : ℕ} (f : compatible n) : Coord n →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun X => f (cover X))
    (f.continuous.comp (continuous_cover n)) ‖f‖
    (fun X => ContinuousMap.norm_coe_le_norm f (cover X))

@[simp] theorem realLift_apply {n : ℕ} (f : compatible n) (X : Coord n) :
    realLift f X = f (cover X) := rfl

@[simp] theorem realLift_zero {n : ℕ} : realLift (0 : compatible n) = 0 := by ext; rfl

@[simp] theorem realLift_add {n : ℕ} (f g : compatible n) :
    realLift (f + g) = realLift f + realLift g := by ext; rfl

@[simp] theorem realLift_neg {n : ℕ} (f : compatible n) : realLift (-f) = -realLift f := by ext; rfl

@[simp] theorem realLift_sub {n : ℕ} (f g : compatible n) :
    realLift (f - g) = realLift f - realLift g := by ext; rfl

@[simp] theorem realLift_smul {n : ℕ} (c : ℝ) (f : compatible n) :
    realLift (c • f) = c • realLift f := by ext; rfl

theorem ext_fun {n : ℕ} {f g : compatible n}
    (h : ∀ X, realLift f X = realLift g X) : f = g := by
  ext Z
  obtain ⟨X, rfl⟩ := cover_surjective n Z
  exact h X

@[simp] theorem norm_realLift {n : ℕ} (f : compatible n) : ‖realLift f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
    intro X
    exact ContinuousMap.norm_coe_le_norm f (cover X)
  · apply (ContinuousMap.norm_le _ (norm_nonneg (realLift f))).mpr
    intro Z
    obtain ⟨X, rfl⟩ := cover_surjective n Z
    exact BoundedContinuousFunction.norm_coe_le_norm (realLift f) X

def realLiftLI {n : ℕ} : compatible n →ₗᵢ[ℝ] (Coord n →ᵇ ℝ) where
  toFun := realLift
  map_add' := realLift_add
  map_smul' := realLift_smul
  norm_map' := norm_realLift

def translate {n : ℕ} (Y : Coord n) (v : compatible n) : compatible n :=
  v.comp ⟨fun Z => Z + cover Y, continuous_id.add_const _⟩

@[simp] theorem translate_apply {n : ℕ} (Y : Coord n) (v : compatible n) (X : Coord n) :
    realLift (translate Y v) X = realLift v (X + Y) := rfl

@[simp] theorem translate_zero {n : ℕ} (v : compatible n) : translate 0 v = v := by
  apply ext_fun
  intro X
  simp only [translate_apply, add_zero]

@[simp] theorem translate_add {n : ℕ} (Y Z : Coord n) (v : compatible n) :
    translate (Y + Z) v = translate Y (translate Z v) := by
  apply ext_fun
  intro X
  simp only [translate_apply, add_assoc]

theorem norm_translate_le {n : ℕ} (Y : Coord n) (v : compatible n) :
    ‖translate Y v‖ ≤ ‖v‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg v)).mpr
  intro Z
  exact ContinuousMap.norm_coe_le_norm v (Z + cover Y)

@[simp] theorem norm_translate {n : ℕ} (Y : Coord n) (v : compatible n) :
    ‖translate Y v‖ = ‖v‖ := by
  apply le_antisymm (norm_translate_le _ _)
  have he : translate (-Y) (translate Y v) = v := by
    rw [← translate_add, neg_add_cancel, translate_zero]
  simpa only [he] using norm_translate_le (-Y) (translate Y v)

def translateLI {n : ℕ} (Y : Coord n) : compatible n →ₗᵢ[ℝ] compatible n where
  toFun := translate Y
  map_add' := by intro v w; apply ext_fun; intro X; rfl
  map_smul' := by intro c v; apply ext_fun; intro X; rfl
  norm_map' := norm_translate Y

theorem continuous_translate {n : ℕ} (v : compatible n) :
    Continuous (fun Y : Coord n => translate Y v) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact v.continuous.comp (continuous_snd.add ((continuous_cover n).comp continuous_fst))

end VelocityDetection.PeriodicSpace
end

end OAI
