import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Transferring translations across a coarse inverse pair

For maps `f : H → X` and `r : X → H`, the maps `x ↦ f (h * r x)` form the
uniform quasi-action used in Proposition `recognition-from-height` of the
manuscript. These estimates retain the errors of the coarse inverse pair and
require only the stated metric inequalities.
-/

namespace PolycyclicRecognition

universe u v

variable {H : Type u} [Group H]
variable {X : Type v}

/-- The left translation by `h`, transferred using `f` and `r`. -/
def transferredMap (f : H → X) (r : X → H) (h : H) (x : X) : X :=
  f (h * r x)

@[simp]
theorem transferredMap_apply (f : H → X) (r : X → H) (h : H) (x : X) :
    transferredMap f r h x = f (h * r x) := rfl

/-- A normalized inverse sends the distinguished point to the original orbit. -/
theorem transferredMap_normalized (f : H → X) (r : X → H) (x₀ : X)
    (hr₀ : r x₀ = 1) (h : H) : transferredMap f r h x₀ = f h := by
  simp only [transferredMap, hr₀, mul_one]

variable [PseudoMetricSpace X]

/-- The transferred identity has the same error as `f ∘ r`. -/
theorem transferredMap_one_close (f : H → X) (r : X → H) (E' : ℝ)
    (hfr : ∀ x, dist (f (r x)) x ≤ E') (x : X) :
    dist (transferredMap f r 1 x) x ≤ E' := by
  simpa only [transferredMap, one_mul] using hfr x

variable [PseudoMetricSpace H]

/-- The error in the transferred action law is uniform in both group elements. -/
theorem transferredMap_mul_close (f : H → X) (r : X → H)
    (hleft : ∀ h a b : H, dist (h * a) (h * b) = dist a b)
    (K C E : ℝ) (hK : 0 ≤ K)
    (hf : ∀ a b, dist (f a) (f b) ≤ K * dist a b + C)
    (hrf : ∀ a, dist (r (f a)) a ≤ E) (h k : H) (x : X) :
    dist (transferredMap f r h (transferredMap f r k x))
      (transferredMap f r (h * k) x) ≤ K * E + C := by
  change dist (f (h * r (f (k * r x)))) (f ((h * k) * r x)) ≤ _
  rw [mul_assoc]
  calc
    dist (f (h * r (f (k * r x)))) (f (h * (k * r x))) ≤
        K * dist (h * r (f (k * r x))) (h * (k * r x)) + C := hf _ _
    _ = K * dist (r (f (k * r x))) (k * r x) + C := by rw [hleft]
    _ ≤ K * E + C :=
      add_le_add (mul_le_mul_of_nonneg_left (hrf (k * r x)) hK) le_rfl

/-- The transferred action agrees coarsely with left translation on orbit points. -/
theorem transferredMap_orbit_close (f : H → X) (r : X → H)
    (hleft : ∀ h a b : H, dist (h * a) (h * b) = dist a b)
    (K C E : ℝ) (hK : 0 ≤ K)
    (hf : ∀ a b, dist (f a) (f b) ≤ K * dist a b + C)
    (hrf : ∀ a, dist (r (f a)) a ≤ E) (h k : H) :
    dist (transferredMap f r h (f k)) (f (h * k)) ≤ K * E + C := by
  calc
    dist (transferredMap f r h (f k)) (f (h * k)) ≤
        K * dist (h * r (f k)) (h * k) + C := hf _ _
    _ = K * dist (r (f k)) k + C := by rw [hleft]
    _ ≤ K * E + C :=
      add_le_add (mul_le_mul_of_nonneg_left (hrf k) hK) le_rfl

/-- Both coarse upper inequalities give one upper inequality for every
transferred translation. The constants do not depend on the translating element. -/
theorem transferredMap_coarse_upper (f : H → X) (r : X → H)
    (hleft : ∀ h a b : H, dist (h * a) (h * b) = dist a b)
    (Kf Cf Kr Cr : ℝ) (hKf : 0 ≤ Kf)
    (hf : ∀ a b, dist (f a) (f b) ≤ Kf * dist a b + Cf)
    (hr : ∀ x y, dist (r x) (r y) ≤ Kr * dist x y + Cr)
    (h : H) (x y : X) :
    dist (transferredMap f r h x) (transferredMap f r h y) ≤
      (Kf * Kr) * dist x y + (Kf * Cr + Cf) := by
  calc
    dist (transferredMap f r h x) (transferredMap f r h y) ≤
        Kf * dist (h * r x) (h * r y) + Cf := hf _ _
    _ = Kf * dist (r x) (r y) + Cf := by rw [hleft]
    _ ≤ Kf * (Kr * dist x y + Cr) + Cf :=
      add_le_add (mul_le_mul_of_nonneg_left (hr x y) hKf) le_rfl
    _ = (Kf * Kr) * dist x y + (Kf * Cr + Cf) := by ring

/-- A generator step has a uniform image length even when the word is in a
subgroup equipped with its own generating set. -/
theorem orbit_right_increment_bound (f : H → X)
    (hleft : ∀ h a b : H, dist (h * a) (h * b) = dist a b)
    (K C : ℝ) (hf : ∀ a b, dist (f a) (f b) ≤ K * dist a b + C)
    (h t : H) :
    dist (f h) (f (h * t)) ≤ K * dist 1 t + C := by
  calc
    dist (f h) (f (h * t)) ≤ K * dist h (h * t) + C := hf _ _
    _ = K * dist 1 t + C := by
      have heq := hleft h 1 t
      simpa only [mul_one] using congrArg (fun d : ℝ => K * d + C) heq

end PolycyclicRecognition

end OAI
