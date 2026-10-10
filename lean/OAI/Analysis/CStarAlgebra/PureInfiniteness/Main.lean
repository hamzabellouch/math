import OAI.Analysis.CStarAlgebra.PureInfiniteness.Diagonalization
import OAI.Analysis.CStarAlgebra.PureInfiniteness.MatrixEntries

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap.Manuscript
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance positivityOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance positivityStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

def CuntzLE (d v : Stable.Stabilization A) : Prop :=
  ∃ r : ℕ → Stable.Stabilization A,
    Tendsto (fun j => star (r j) * v * r j) atTop (𝓝 d)

def ProperlyInfinite (h : A) : Prop :=
  CuntzLE ((⟦⟨2, MainGap.doubleCorner h⟩⟧ : Stable.Algebraic A) : Stable.Stabilization A)
    ((⟦⟨1, MainGap.scalarCorner h⟩⟧ : Stable.Algebraic A) : Stable.Stabilization A)

def PropertyP (A : Type*) [NonUnitalCStarAlgebra A] : Prop :=
  ∀ h : A, 0 ≤ h → ProperlyInfinite h

lemma finiteCuntzLE_of_stable {m n : ℕ} (d : Stable.Mat A n) (v : Stable.Mat A m)
    (h : CuntzLE (Stable.corner n d) (Stable.corner m v)) : MainGap.FiniteCuntzLE d v := by
  obtain ⟨r,hr⟩ := h
  refine ⟨fun j => Stable.block m n (r j), ?_⟩
  have ht := (Stable.continuous_block (A := A) n n).continuousAt.tendsto.comp hr
  simpa only [Function.comp_def, Stable.block_conjugate, Stable.block_corner_self] using ht

lemma PropertyP.finite (hP : PropertyP A) : MainGap.PropertyP A := by
  intro h hh
  exact finiteCuntzLE_of_stable _ _ (hP h hh)

theorem individual_to_strong (hP : PropertyP A) : MainGap.UnrestrictedDiagonalization A :=
  MainGap.individual_to_strong hP.finite

theorem individual_to_strong_spi (hP : PropertyP A) : MainGap.StronglyPurelyInfinite A :=
  MainGap.individual_to_strong_spi hP.finite

theorem individual_to_strong_main (hP : PropertyP A) :
    (∀ a b : A, 0 ≤ a → 0 ≤ b → ∀ c : A, ∀ ε : ℝ, 0 < ε →
      ∃ s t : A,
        ‖star s * a * s - a‖ < ε ∧
        ‖star t * b * t - b‖ < ε ∧
        ‖star s * c * t‖ < ε) ∧
    MainGap.StronglyPurelyInfinite A := by
  exact ⟨individual_to_strong hP, individual_to_strong_spi hP⟩

end MainGap.Manuscript

end

end OAI
