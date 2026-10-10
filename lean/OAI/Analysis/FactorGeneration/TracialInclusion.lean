import OAI.Analysis.FactorGeneration.OperatorLimits
import OAI.Analysis.FactorGeneration.Ultrapower

namespace OAI

namespace Generator.Tracial

/-! The restricted faithful trace and the actual P^omega -> M^omega
inclusion. All constructions are on the bounded-sequence quotient. -/
noncomputable section
open Filter
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M P : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hPM : P ≤ M)

def coordinateInclusion : P.toStarSubalgebra →⋆ₐ[ℂ] M.toStarSubalgebra :=
  StarSubalgebra.inclusion hPM

def restrictedTrace : TracialRepresentation P where
  vector := τ.vector
  norm_vector := τ.norm_vector
  cyclic a b := τ.cyclic (coordinateInclusion hPM a) (coordinateInclusion hPM b)
  separating a ha := by
    have h := τ.separating (coordinateInclusion hPM a) ha
    apply Subtype.ext
    exact congrArg (fun x : M.toStarSubalgebra => x.val) h

@[simp] theorem restrictedTrace_trace (a : P.toStarSubalgebra) :
    (restrictedTrace τ hPM).trace a = τ.trace (coordinateInclusion hPM a) := rfl

@[simp] theorem restrictedTrace_norm₂ (a : P.toStarSubalgebra) :
    (restrictedTrace τ hPM).norm₂ a = τ.norm₂ (coordinateInclusion hPM a) := rfl

def boundedInclusion : Bounded P →⋆ₐ[ℂ] Bounded M where
  toFun a := ⟨fun n => coordinateInclusion hPM (a.val n), a.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

theorem inclusion_traceRel_iff (l : Filter ℕ) (a b : Bounded P) :
    TraceRel τ l (boundedInclusion hPM a) (boundedInclusion hPM b) ↔
      TraceRel (restrictedTrace τ hPM) l a b := Iff.rfl

def quotientInclusion (l : Filter ℕ) :
    TracialQuotient (restrictedTrace τ hPM) l →⋆ₐ[ℂ] TracialQuotient τ l where
  toFun := Quotient.map (boundedInclusion hPM) (fun _ _ h => h)
  map_one' := rfl
  map_mul' a b := by
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b => rfl
  map_zero' := rfl
  map_add' a b := by
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b => rfl
  commutes' _ := rfl
  map_star' a := by induction a using Quotient.inductionOn with | h a => rfl

@[simp] theorem quotientInclusion_mk (l : Filter ℕ) (a : Bounded P) :
    quotientInclusion τ hPM l (quotientMap (restrictedTrace τ hPM) l a) =
      quotientMap τ l (boundedInclusion hPM a) := rfl

theorem quotientInclusion_injective (l : Filter ℕ) : Function.Injective (quotientInclusion τ hPM l) := by
  intro a b
  induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
      intro h
      have hh := (quotientMap_eq_iff τ l (boundedInclusion hPM a) (boundedInclusion hPM b)).mp h
      exact (quotientMap_eq_iff (restrictedTrace τ hPM) l a b).mpr
        ((inclusion_traceRel_iff τ hPM l a b).mp hh)

@[simp] theorem quotientInclusion_trace (ω : Ultrafilter ℕ)
    (a : TracialQuotient (restrictedTrace τ hPM) (ω : Filter ℕ)) :
    quotientTrace τ ω (quotientInclusion τ hPM (ω : Filter ℕ) a) =
      quotientTrace (restrictedTrace τ hPM) ω a := by
  induction a using Quotient.inductionOn with
  | h a =>
    change traceRep τ ω (boundedInclusion hPM a) = traceRep (restrictedTrace τ hPM) ω a
    exact tendsto_nhds_unique (traceRep_tendsto τ ω (boundedInclusion hPM a))
      (traceRep_tendsto (restrictedTrace τ hPM) ω a)

/-- P, as a star subalgebra of M. Its completeness is derived, not assumed. -/
def insideAlgebra : StarSubalgebra ℂ M.toStarSubalgebra :=
  P.toStarSubalgebra.comap M.toStarSubalgebra.subtype

theorem insideAlgebra_closed : IsClosed (insideAlgebra (M := M) (P := P) : Set M.toStarSubalgebra) :=
  (base_norm_closed P).preimage continuous_subtype_val

instance insideAlgebra_complete : CompleteSpace (insideAlgebra (M := M) (P := P)) :=
  (insideAlgebra_closed (M := M) (P := P)).completeSpace_coe

end

end Generator.Tracial

end OAI
