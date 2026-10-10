import OAI.Analysis.Pureness.Quasitrace.QuasitraceExtremalReduction
import OAI.Analysis.Pureness.Quasitrace.AdditiveQuasitraceTrace

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def normalizedBaseQuasitraceCarrier : Set (A → ℂ) :=
  Prod.fst '' (normalizedQuasitraceCarrier (A := A))

theorem mem_normalizedBaseQuasitraceCarrier (g : A → ℂ) :
    g ∈ normalizedBaseQuasitraceCarrier ↔
      ∃ T : TwoQuasitrace A, T.base 1 = 1 ∧ T.base.toFun = g := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨twoQuasitraceFromCoordinates p hp, hp.2.2.1, rfl⟩
  · rintro ⟨T, hT, rfl⟩
    exact ⟨T.coordinates, T.coordinates_mem hT, rfl⟩

theorem isCompact_normalizedBaseQuasitraceCarrier :
    IsCompact (normalizedBaseQuasitraceCarrier (A := A)) :=
  isCompact_normalizedQuasitraceCarrier.image continuous_fst

theorem isClosed_normalizedBaseQuasitraceCarrier :
    IsClosed (normalizedBaseQuasitraceCarrier (A := A)) :=
  isCompact_normalizedBaseQuasitraceCarrier.isClosed

theorem convex_normalizedBaseQuasitraceCarrier :
    Convex ℝ (normalizedBaseQuasitraceCarrier (A := A)) :=
  convex_normalizedQuasitraceCarrier.linear_image (LinearMap.fst ℝ (A → ℂ) (FinMatrix A 2 → ℂ))

def additiveQuasitraceFunctions : Set (A → ℂ) := {g | ∀ a b, g (a+b) = g a+g b}

omit [PartialOrder A] [StarOrderedRing A] in
lemma isClosed_additiveQuasitraceFunctions : IsClosed (additiveQuasitraceFunctions (A := A)) :=
  isClosed_forall_pointwise _ fun a => isClosed_forall_pointwise _ fun b =>
    isClosed_eq (continuous_apply (a+b)) ((continuous_apply a).add (continuous_apply b))

omit [PartialOrder A] [StarOrderedRing A] in
lemma convex_additiveQuasitraceFunctions : Convex ℝ (additiveQuasitraceFunctions (A := A)) := by
  intro g hg k hk r s hr hs hrs a b
  change (r : ℂ)*g (a+b)+(s : ℂ)*k (a+b) =
    ((r : ℂ)*g a+(s : ℂ)*k a)+((r : ℂ)*g b+(s : ℂ)*k b)
  rw [hg a b, hk a b]
  ring

theorem normalizedBaseQuasitraceCarrier_eq_closure_extremePoints :
    normalizedBaseQuasitraceCarrier (A := A) =
      closure (convexHull ℝ ((normalizedBaseQuasitraceCarrier (A := A)).extremePoints ℝ)) :=
  (closure_convexHull_extremePoints isCompact_normalizedBaseQuasitraceCarrier
    convex_normalizedBaseQuasitraceCarrier).symm

theorem normalizedQuasitrace_additive_of_base_extremePoints
    (hext : (normalizedBaseQuasitraceCarrier (A := A)).extremePoints ℝ ⊆ additiveQuasitraceFunctions)
    (T : TwoQuasitrace A) (hT : T.base 1 = 1) : ∀ a b, T.base (a+b) = T.base a+T.base b := by
  have hsub : normalizedBaseQuasitraceCarrier (A := A) ⊆ additiveQuasitraceFunctions := by
    rw [normalizedBaseQuasitraceCarrier_eq_closure_extremePoints]
    exact closure_minimal (convexHull_min hext convex_additiveQuasitraceFunctions)
      isClosed_additiveQuasitraceFunctions
  exact hsub ((mem_normalizedBaseQuasitraceCarrier T.base.toFun).mpr ⟨T, hT, rfl⟩)

theorem normalizedQuasitrace_trace_of_base_extremePoints
    (hext : (normalizedBaseQuasitraceCarrier (A := A)).extremePoints ℝ ⊆ additiveQuasitraceFunctions)
    (T : TwoQuasitrace A) (hT : T.base 1 = 1) :
    ∃ τ : TracialState A, ∀ x, τ.functional x = T.base x :=
  (T.base.exists_tracialState_agreeing_iff hT).mpr
    (normalizedQuasitrace_additive_of_base_extremePoints hext T hT)
end CuntzPureness

end

end OAI
