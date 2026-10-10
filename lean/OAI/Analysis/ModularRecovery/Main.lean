import OAI.Analysis.ModularRecovery.Centralizer

namespace OAI

/-! Bounded recovery from a cyclic separating unit vector with scalar state centralizer. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace CyclicSeparatingData

def StateScalarCentralizer (S : CyclicSeparatingData H) : Prop :=
  ∀ a : H →L[ℂ] H, a ∈ S.M →
    (∀ b : H →L[ℂ] H, b ∈ S.M →
      inner ℂ S.xi ((a*b) S.xi)=inner ℂ S.xi ((b*a) S.xi)) →
    ∃ c : ℂ, a=c • (1:H →L[ℂ] H)

theorem bounded_recovery (S : CyclicSeparatingData H) (hscalar : S.StateScalarCentralizer)
    (omega : Ultrafilter ℕ) (hfree : (omega : Filter ℕ) ≤ Filter.atTop)
    (T : H →L[ℂ] H) (s : ℝ) (delta : ℕ → ℝ) (hdelta : ∀ n, 0 < delta n)
    (hdelta0 : Tendsto delta atTop (𝓝 0)) (h : ℕ → H) (hunit : ∀ n, ‖h n‖=1)
    (hband : ∀ n, S.D.HasSpectralSupport (Icc (s-delta n) (s+delta n)) (h n))
    (hpositive : 0 < Filter.limsup
      (fun n => fixedMean omega (fun t => ‖T (S.D.unitary t (h n))‖ ^ 2)) atTop) :
    ∃ (nj : ℕ → ℕ) (_ : StrictMono nj) (v : ℕ → (H →L[ℂ] H)) (C eta : ℝ),
      0 < eta ∧ ∀ j : ℕ, v j ∈ S.M ∧ ‖v j‖ ≤ C ∧ eta ≤ ‖T (v j S.xi)‖ ∧
        S.D.HasSpectralSupport (Icc (s-4*delta (nj j)) (s+4*delta (nj j)))
          (v j S.xi) := by
  have hs : S.toStandardModularData.StateScalarCentralizer := by
    intro a ha
    exact hscalar a ha.1 ha.2
  exact BoundedRecovery.bounded_recovery S.toStandardModularData
    (S.toStandardModularData.scalarCentralizer_of_state hs) omega hfree T s delta
    hdelta hdelta0 h hunit hband hpositive

end CyclicSeparatingData
end BoundedRecovery

end

end OAI
