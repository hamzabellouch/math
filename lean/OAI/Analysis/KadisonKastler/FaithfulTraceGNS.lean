import OAI.Analysis.KadisonKastler.TracialCauchySchwarz
import OAI.Analysis.TracialSplitting.GNSRepresentations

namespace OAI

/-! # The concrete GNS representation of a faithful tracial state -/

namespace KadisonKastler

open scoped ComplexOrder InnerProductSpace

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def FaithfulTracialState.toPositiveLinearMap (τ : FaithfulTracialState A) : A →ₚ[ℂ] ℂ where
  toLinearMap := τ.toLinearMap
  monotone' := by
    intro a b hab
    change τ.toLinearMap a ≤ τ.toLinearMap b
    obtain ⟨z, hz⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr hab)
    have hp : 0 ≤ τ.toLinearMap (b - a) := by
      rw [hz]
      exact Complex.nonneg_iff.mpr ⟨τ.positive z, (τ.positive_im z).symm⟩
    rw [map_sub] at hp
    exact sub_nonneg.mp hp

abbrev TraceStateHilbert (τ : FaithfulTracialState A) := τ.toPositiveLinearMap.GNS

def traceStateVector (τ : FaithfulTracialState A) (a : A) : TraceStateHilbert τ :=
  τ.toPositiveLinearMap.toPreGNS a

def traceStateRepresentation (τ : FaithfulTracialState A) :
    A →⋆ₐ[ℂ] (TraceStateHilbert τ →L[ℂ] TraceStateHilbert τ) :=
  τ.toPositiveLinearMap.gnsStarAlgHom

theorem norm_traceStateVector (τ : FaithfulTracialState A) (a : A) :
    ‖traceStateVector τ a‖ = traceTwoNorm τ a := by
  rw [traceStateVector, UniformSpace.Completion.norm_coe, PositiveLinearMap.preGNS_norm_def]
  rfl

@[simp] theorem traceStateVector_sub (τ : FaithfulTracialState A) (a b : A) :
    traceStateVector τ (a - b) = traceStateVector τ a - traceStateVector τ b := by
  simp only [traceStateVector, map_sub, UniformSpace.Completion.coe_sub]

@[simp] theorem traceStateRepresentation_vector (τ : FaithfulTracialState A) (a b : A) :
    traceStateRepresentation τ a (traceStateVector τ b) = traceStateVector τ (a * b) := by
  change τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom a
    (τ.toPositiveLinearMap.toPreGNS b) = _
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe]
  rfl

theorem traceStateVector_dense (τ : FaithfulTracialState A) : DenseRange (traceStateVector τ) := by
  apply UniformSpace.Completion.denseRange_coe.mono
  rintro _ ⟨a, rfl⟩
  exact ⟨τ.toPositiveLinearMap.ofPreGNS a, rfl⟩

theorem traceStateRepresentation_injective (τ : FaithfulTracialState A) :
    Function.Injective (traceStateRepresentation τ) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  have hz : traceStateVector τ a = 0 := by
    have h := congrArg (fun T => T (traceStateVector τ 1)) ha
    simpa only [traceStateRepresentation_vector, mul_one,
      zero_apply] using h
  apply τ.faithful
  have hn : traceTwoNorm τ a = 0 := by rw [← norm_traceStateVector, hz, norm_zero]
  apply Complex.ext
  · have hs := traceTwoNorm_sq τ a
    rw [hn, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hs
    exact hs.symm
  · exact τ.positive_im a

theorem norm_traceStateRepresentation (τ : FaithfulTracialState A) (a : A) :
    ‖traceStateRepresentation τ a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (traceStateRepresentation τ).toNonUnitalStarAlgHom
    (traceStateRepresentation_injective τ) a

/-- Right multiplication, supplied by the same tracial GNS construction. -/
def traceStateRight (τ : FaithfulTracialState A) (a : A) :
    TraceStateHilbert τ →L[ℂ] TraceStateHilbert τ :=
  NuclearTrace.rightGNS τ.toPositiveLinearMap τ.tracial (MulOpposite.op a)

@[simp] theorem traceStateRight_vector (τ : FaithfulTracialState A) (a b : A) :
    traceStateRight τ a (traceStateVector τ b) = traceStateVector τ (b * a) := by
  exact NuclearTrace.rightGNS_coe τ.toPositiveLinearMap τ.tracial (MulOpposite.op a)
    (τ.toPositiveLinearMap.toPreGNS b)

theorem traceState_left_right_commute (τ : FaithfulTracialState A) (a b : A) :
    Commute (traceStateRepresentation τ a) (traceStateRight τ b) :=
  NuclearTrace.left_right_commute τ.toPositiveLinearMap τ.tracial a (MulOpposite.op b)

end

end KadisonKastler

end OAI
