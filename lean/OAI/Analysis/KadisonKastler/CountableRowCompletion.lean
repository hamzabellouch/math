import OAI.Analysis.KadisonKastler.CompletedRows

namespace OAI

/-! Finite normalization preserves weak limits of countable row averages. -/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance countableRowAlgebraOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance countableRowAlgebraPreorder (M : VonNeumannAlgebra H) : Preorder (Algebra M) :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance countableRowAlgebraLE (M : VonNeumannAlgebra H) : LE (Algebra M) :=
  (CStarAlgebra.spectralOrder _).toLE
local instance countableRowAlgebraStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

def initialRow {M : VonNeumannAlgebra H} (r : ℕ → Algebra M) (n : ℕ) :
    Fin n → Algebra M := fun i => r i

/-- Weak convergence of the row mass to the identity makes the missing
square root converge strongly to zero. -/
theorem rowRemainder_tendsto_zero {M : VonNeumannAlgebra H}
    (r : ℕ → Algebra M) (hr : ∀ n, rowSquare (initialRow r n) ≤ 1)
    (ht : ∀ ξ η, Tendsto
      (fun n => inner ℂ η (((rowSquare (initialRow r n) : Algebra M) : H →L[ℂ] H) ξ))
      atTop (𝓝 (inner ℂ η ξ))) (ξ : H) :
    Tendsto (fun n => ((rowRemainder (initialRow r n) : Algebra M) : H →L[ℂ] H) ξ) atTop (𝓝 0) := by
  have he (n : ℕ) : ‖((rowRemainder (initialRow r n) : Algebra M) : H →L[ℂ] H) ξ‖ ^ 2 =
      (inner ℂ ξ ξ).re - (inner ℂ ξ (((rowSquare (initialRow r n) : Algebra M) : H →L[ℂ] H) ξ)).re := by
    rw [rowRemainder_apply_norm_sq _ (hr n)]
    simp
  have hi := Complex.continuous_re.continuousAt.tendsto.comp (ht ξ ξ)
  have hc : Tendsto (fun _ : ℕ => (inner ℂ ξ ξ).re) atTop (𝓝 (inner ℂ ξ ξ).re) :=
    tendsto_const_nhds
  have hs : Tendsto (fun n => ‖((rowRemainder (initialRow r n) : Algebra M) : H →L[ℂ] H) ξ‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, he, sub_self] using hc.sub hi
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hn

theorem completedRow_average_tendsto_sub_zero {M : VonNeumannAlgebra H}
    (r : ℕ → Algebra M) (hr : ∀ n, rowSquare (initialRow r n) ≤ 1)
    (ht : ∀ ξ η, Tendsto
      (fun n => inner ℂ η (((rowSquare (initialRow r n) : Algebra M) : H →L[ℂ] H) ξ))
      atTop (𝓝 (inner ℂ η ξ)))
    {F : Algebra M →ₗ[ℂ] Algebra M} {c : ℝ} (hF : CompletelyBoundedBy F c) (hc : 0 ≤ c)
    (x : Algebra M) (ξ : H) :
    Tendsto (fun n => ((finiteRightAverage (completedRow (initialRow r n)) F x -
      finiteRightAverage (initialRow r n) F x : Algebra M) : H →L[ℂ] H) ξ)
      atTop (𝓝 0) := by
  have hn := (rowRemainder_tendsto_zero r hr ht ξ).norm
  apply squeeze_zero_norm (fun n => completedRow_average_error _ (hr n) hF hc x ξ)
  simpa only [norm_zero, mul_zero] using hn.const_mul (c * ‖x‖)

/-- The normalized finite rows have every weak limit of the original partial
rows. The map being averaged is allowed to be nonnormal. -/
theorem completedRow_average_weak_limit {M : VonNeumannAlgebra H}
    (r : ℕ → Algebra M) (hr : ∀ n, rowSquare (initialRow r n) ≤ 1)
    (ht : ∀ ξ η, Tendsto
      (fun n => inner ℂ η (((rowSquare (initialRow r n) : Algebra M) : H →L[ℂ] H) ξ))
      atTop (𝓝 (inner ℂ η ξ)))
    {F : Algebra M →ₗ[ℂ] Algebra M} {c : ℝ} (hF : CompletelyBoundedBy F c) (hc : 0 ≤ c)
    (x y : Algebra M)
    (hy : ∀ ξ η, Tendsto
      (fun n => inner ℂ η ((finiteRightAverage (initialRow r n) F x : H →L[ℂ] H) ξ))
      atTop (𝓝 (inner ℂ η ((y : H →L[ℂ] H) ξ)))) :
    ∀ ξ η, Tendsto
      (fun n => inner ℂ η ((finiteRightAverage (completedRow (initialRow r n)) F x :
        H →L[ℂ] H) ξ)) atTop (𝓝 (inner ℂ η ((y : H →L[ℂ] H) ξ))) := by
  intro ξ η
  have hd := completedRow_average_tendsto_sub_zero r hr ht hF hc x ξ
  have hcont : Continuous (fun z : H => inner ℂ η z) := by fun_prop
  have hi := (hcont.tendsto (0 : H)).comp hd
  have h := hi.add (hy ξ η)
  simpa [inner_sub_right] using h

end

end KadisonKastler

end OAI
