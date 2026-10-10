import OAI.Analysis.FactorGeneration.CoordinateUnitaries
import OAI.Analysis.FactorGeneration.LaurentAlgebra

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Full freeness in the faithful bounded-operator representation. The quotient
image is not asserted to be complete or weak-operator closed. -/
section
attribute [local instance] quotientL2AddCommMonoid quotientL2AddCommGroup
  quotientOperatorSemiring quotientOperatorNonAssocSemiring quotientOperatorAlgebra
  quotientOperatorSemitopology
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

abbrev QuotientOperators := L2 τ ω →L[ℂ] L2 τ ω

def quotientVectorState : QuotientOperators τ ω →L[ℂ] ℂ :=
  (innerSL ℂ (inclusion τ ω 1)).comp
    (ContinuousLinearMap.apply ℂ (L2 τ ω) (inclusion τ ω 1))

@[simp] theorem quotientVectorState_representation (a : Q τ ω) :
    quotientVectorState τ ω (quotientRepresentation τ ω a)=quotientTrace τ ω a :=
  quotientRepresentation_trace τ ω a

@[simp] theorem quotientVectorState_one : quotientVectorState τ ω 1=1 := by
  have h := quotientVectorState_representation τ ω 1
  rw [show quotientRepresentation τ ω 1=1 from (quotientRepresentation τ ω).map_one] at h
  exact h.trans (quotientTrace_one τ ω)

def representedUnitary (v : unitary (Q τ ω)) : unitary (QuotientOperators τ ω) :=
  Unitary.map (StarMonoidHom.ofClass (quotientRepresentation τ ω)) v

@[simp] theorem representedUnitary_coe (v : unitary (Q τ ω)) :
    (representedUnitary τ ω v : QuotientOperators τ ω)=quotientRepresentation τ ω (v : Q τ ω) := rfl

theorem representedUnitary_power (v : unitary (Q τ ω)) (n : ℤ) :
    (↑((representedUnitary τ ω v)^n) : QuotientOperators τ ω)=
      quotientRepresentation τ ω (↑(v^n) : Q τ ω) := by
  exact (congrArg (fun w : unitary (QuotientOperators τ ω) => (w : QuotientOperators τ ω))
    (map_zpow (Unitary.map (StarMonoidHom.ofClass (quotientRepresentation τ ω))) v n)).symm

theorem represented_nonzero_powers (v : unitary (Q τ ω)) :
    quotientRepresentation τ ω '' nonzeroUnitaryPowers v =
      nonzeroUnitaryPowers (representedUnitary τ ω v) := by
  ext x
  constructor
  · rintro ⟨q,⟨n,hn,rfl⟩,rfl⟩
    exact ⟨n,hn,(representedUnitary_power τ ω v n).symm⟩
  · rintro ⟨n,hn,rfl⟩
    exact ⟨↑(v^n),⟨n,hn,rfl⟩,(representedUnitary_power τ ω v n).symm⟩

theorem represented_centered_subalgebra (D : Subalgebra ℂ (Q τ ω)) :
    quotientRepresentation τ ω '' {d | d ∈ D ∧ quotientTrace τ ω d=0} =
      {d | d ∈ D.map (quotientRepresentation τ ω).toAlgHom ∧ quotientVectorState τ ω d=0} := by
  ext x
  constructor
  · rintro ⟨q,⟨hq,hc⟩,rfl⟩
    exact ⟨⟨q,hq,rfl⟩,by simpa only [quotientVectorState_representation] using hc⟩
  · rintro ⟨⟨q,hq,rfl⟩,hc⟩
    change quotientVectorState τ ω (quotientRepresentation τ ω q)=0 at hc
    exact ⟨q,⟨hq,by rwa [quotientVectorState_representation] at hc⟩,rfl⟩

/-- The exact endpoint formula proves freeness for the actual represented C*(v)
and the norm closure of the represented base algebra. -/
theorem represented_haar_free (v : unitary (Q τ ω)) (D : Subalgebra ℂ (Q τ ω))
    (hhaar : ∀ n : ℤ,n ≠ 0 → quotientTrace τ ω (↑(v^n) : Q τ ω)=0)
    (hpow : alternatingMomentsZero (quotientTrace τ ω) (nonzeroUnitaryPowers v)
      {d | d ∈ D ∧ quotientTrace τ ω d=0}) :
    freeSets (A := QuotientOperators τ ω) (quotientVectorState τ ω)
      (StarAlgebra.elemental (A := QuotientOperators τ ω) ℂ (quotientRepresentation τ ω (v : Q τ ω)))
      (D.map (quotientRepresentation τ ω).toAlgHom).topologicalClosure := by
  have hmap := alternatingMomentsZero_map (quotientRepresentation τ ω).toMonoidHom
    (quotientTrace τ ω) (quotientVectorState τ ω) (quotientVectorState_representation τ ω)
    _ _ hpow
  change alternatingMomentsZero (quotientVectorState τ ω)
    (quotientRepresentation τ ω '' nonzeroUnitaryPowers v)
    (quotientRepresentation τ ω '' {d | d ∈ D ∧ quotientTrace τ ω d=0}) at hmap
  have hm := (congrArg₂ (alternatingMomentsZero (quotientVectorState τ ω))
    (represented_nonzero_powers τ ω v) (represented_centered_subalgebra τ ω D)).mp hmap
  have hh := unitary_generated_free_of_power_moments (A := QuotientOperators τ ω)
    (quotientVectorState τ ω) (quotientVectorState_one τ ω) (representedUnitary τ ω v)
    (D.map (quotientRepresentation τ ω).toAlgHom)
    (fun n hn => by rw [representedUnitary_power,quotientVectorState_representation]; exact hhaar n hn) hm
  simpa only [representedUnitary_coe] using hh

end

/-! Named interfaces keep the operator topology explicit without repeatedly
elaborating its instance data inside large existential constructions. -/
section
attribute [local instance] quotientL2AddCommMonoid quotientL2AddCommGroup
  quotientOperatorSemiring quotientOperatorNonAssocSemiring quotientOperatorAlgebra
  quotientOperatorSemitopology
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def representedFreeFrom (v : unitary (Q τ ω)) (D : Subalgebra ℂ (QuotientOperators τ ω)) : Prop :=
  freeSets (quotientVectorState τ ω)
    (StarAlgebra.elemental ℂ (quotientRepresentation τ ω (v : Q τ ω))) D

def representedClosedFree (v : unitary (Q τ ω)) (D : Subalgebra ℂ (Q τ ω)) : Prop :=
  representedFreeFrom τ ω v (D.map (quotientRepresentation τ ω).toAlgHom).topologicalClosure

theorem represented_haar_free_interface (v : unitary (Q τ ω)) (D : Subalgebra ℂ (Q τ ω))
    (hhaar : ∀ n : ℤ,n ≠ 0 → quotientTrace τ ω (↑(v^n) : Q τ ω)=0)
    (hpow : alternatingMomentsZero (quotientTrace τ ω) (nonzeroUnitaryPowers v)
      {d | d ∈ D ∧ quotientTrace τ ω d=0}) : representedClosedFree τ ω v D :=
  represented_haar_free τ ω v D hhaar hpow

end

/-! A Haar unitary free from the represented base algebra, with a bounded
sequence of actual coordinate unitaries in the included algebra. -/
attribute [local instance] quotientL2AddCommMonoid quotientL2AddCommGroup
  quotientOperatorSemiring quotientOperatorNonAssocSemiring quotientOperatorAlgebra
  quotientOperatorSemitopology
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ r : N.toStarSubalgebra,IsStarProjection r → r ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ r ∧ r*q=q ∧ q*r=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

theorem exists_coordinate_haar_free (hω : (ω : Filter ℕ) ≤ atTop)
    (D : Subalgebra ℂ (Q τ ω)) (hD : TopologicalSpace.IsSeparable (D : Set (Q τ ω))) :
    ∃ t : unitary (Q τ ω),
      (∃ b : Bounded N,(∀ j,b.val j ∈ unitary N.toStarSubalgebra) ∧
        quotientInclusion τ hNM (ω : Filter ℕ)
          (quotientMap (restrictedTrace τ hNM) (ω : Filter ℕ) b)=(t : Q τ ω)) ∧
      (∀ n : ℤ,n ≠ 0 → quotientTrace τ ω (↑(t^n) : Q τ ω)=0) ∧
      representedClosedFree τ ω t D := by
  obtain ⟨t,ht,hhaar,hep⟩ := exists_coordinate_haar_endpoints
    (H := H) (N := N) (M := M) τ ω hNM hfactor hdiff hirr hsep hω D hD
  have hpow : alternatingMomentsZero (quotientTrace τ ω) (nonzeroPowerSet τ ω t)
      {d | d ∈ D ∧ quotientTrace τ ω d=0} := by
    apply endpoint_all_alternating τ ω _ D
    intro c hc d hd q hq xs hxs
    apply endpoint_moments_laurent_closure τ ω D t hep c d q hc hd
      (Submodule.le_topologicalClosure _ (Submodule.subset_span hq)) xs
    intro z hz
    exact ⟨(hxs z hz).1,(hxs z hz).2.1,
      Submodule.le_topologicalClosure _ (Submodule.subset_span (hxs z hz).2.2)⟩
  exact ⟨t,ht,hhaar,represented_haar_free_interface τ ω t D hhaar hpow⟩

end Generator.Tracial

end

end OAI
