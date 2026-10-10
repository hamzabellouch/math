import Mathlib
import OAI.Geometry.RecorderBoxes.Encoding
import OAI.Geometry.RecorderBoxes.InitialCode
import OAI.Analysis.RecorderRadix.Scales

namespace OAI

/-! Rational endpoints and the initial physical coordinate. -/

namespace Solenoidal
namespace Bridge
variable {M : Machine}
def castPoint (p : ℚ × ℚ) : ℝ × ℝ := ((p.1 : ℝ), (p.2 : ℝ))

 
def Rectangle.RationalEndpoints (P : Rectangle) : Prop :=
  ∃ l u : ℚ × ℚ, P = ⟨castPoint l, castPoint u⟩

theorem source_rational {m : ℕ} (a l : Fin (m + 1)) :
    (sourceBox a l).RationalEndpoints := by
  refine ⟨(Radix.rationalPrefix l 0, Radix.rationalPrefix a 0),
    (Radix.rationalPrefix l 1, Radix.rationalPrefix a 1), ?_⟩
  simp [sourceBox, castPoint]

theorem target_rational {m : ℕ} (b l : Fin (m + 1)) (d : Move) :
    (targetBox b l d).RationalEndpoints := by
  cases d with
  | stay => exact source_rational b l
  | right =>
    refine ⟨(Radix.rationalPrefix b (Radix.rationalPrefix l 0), 0),
      (Radix.rationalPrefix b (Radix.rationalPrefix l 1), 1), ?_⟩
    simp [targetBox, castPoint]
  | left =>
    refine ⟨(0, Radix.rationalPrefix l (Radix.rationalPrefix b 0)),
      (1, Radix.rationalPrefix l (Radix.rationalPrefix b 1)), ?_⟩
    simp [targetBox, castPoint]

def rationalKappa (M : Machine) : ℚ := 1 / (32 * (controlCount M : ℚ))

noncomputable def rationalOrigin (s : Recorder.Control M) : ℚ :=
  (if terminalControl s then 3 / 4 else 1 / 8) +
    2 * ((controlIndex M s).val : ℚ) * rationalKappa M

noncomputable def rationalPlace (s : Recorder.Control M) (p : ℚ × ℚ) : ℚ × ℚ :=
  (rationalOrigin s + rationalKappa M * p.1, 3 / 8 + rationalKappa M * p.2)

@[simp] theorem rationalKappa_coe (M : Machine) : (rationalKappa M : ℝ) = kappa M := by
  simp [rationalKappa, kappa]

@[simp] theorem rationalOrigin_coe (s : Recorder.Control M) :
    (rationalOrigin s : ℝ) = origin s := by
  cases h : terminalControl s <;> simp [rationalOrigin, origin, h]

@[simp] theorem rationalPlace_cast (s : Recorder.Control M) (p : ℚ × ℚ) :
    castPoint (rationalPlace s p) = place s (castPoint p) := by
  apply Prod.ext <;> simp [castPoint, rationalPlace, place]

theorem physical_rational (s : Recorder.Control M) {P : Rectangle}
    (hp : P.RationalEndpoints) : (physicalBox s P).RationalEndpoints := by
  obtain ⟨l, u, rfl⟩ := hp
  exact ⟨rationalPlace s l, rationalPlace s u, by simp [physicalBox]⟩

 
theorem rectangle_rational {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1)) (i : Branch M) :
    (sourceRectangle e i).RationalEndpoints ∧ (targetRectangle e i).RationalEndpoints :=
  ⟨physical_rational i.src (source_rational _ _),
    physical_rational i.dst (target_rational _ _ _)⟩

 

noncomputable def initialPhysicalRational {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1))
    (w : List M.Symbol) : ℚ × ℚ :=
  rationalPlace (.S M.initial) (initialRadixRational e w)

theorem initial_physical_is_rational {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1))
    (w : List M.Symbol) :
    configCode e (Recorder.initial w 2) = castPoint (initialPhysicalRational e w) := by
  change place (.S M.initial) (Radix.tapeCode (fun k => e ((Recorder.initial w 2).tape k)) 0) = _
  rw [initial_radix_is_rational]
  exact (rationalPlace_cast (.S M.initial) (initialRadixRational e w)).symm
end Bridge
end Solenoidal

end OAI
