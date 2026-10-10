import OAI.Analysis.FactorGeneration.LaurentMoments

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Complete each supported partial unitary by the identity on its orthogonal
complement. If the quotient support is one, the quotient value is unchanged. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def PartialUnitary.completed (v : PartialUnitary M) : M.toStarSubalgebra :=
  v.val+(1-v.support.val)

theorem PartialUnitary.completed_unitary (v : PartialUnitary M) :
    v.completed ∈ _root_.unitary M.toStarSubalgebra := by
  have hp := v.support.property.isIdempotentElem.eq
  have hs := v.support.property.isSelfAdjoint.star_eq
  have hi := v.unitary.initial
  have hf := v.unitary.final
  have hleft := v.unitary.support_mul
  have hright := v.unitary.mul_support
  have hleft' := v.unitary.adjoint.support_mul
  have hright' := v.unitary.adjoint.mul_support
  dsimp only [CornerUnitary.adjoint] at hleft' hright'
  constructor <;>
    simp only [PartialUnitary.completed,star_add,star_sub,star_one,hs,add_mul,mul_add,
      sub_mul,mul_sub,one_mul,mul_one,hi,hf,hleft,hright,hleft',hright',hp] <;> abel

theorem PartialUnitary.completed_mem (v : PartialUnitary M)
    (hv : v.val.val ∈ N) : v.completed.val ∈ N := by
  have hp : v.support.val.val ∈ N := by
    rw [← v.unitary.initial]
    have hstar : star v.val.val ∈ N := star_mem hv
    exact N.mul_mem hstar hv
  exact N.add_mem hv (N.sub_mem N.one_mem hp)

def boundedCompletedUnitary (u : ℕ → PartialUnitary M) : Bounded M :=
  boundedPartialUnitary u+(1-boundedPartialSupport u)

@[simp] theorem boundedCompletedUnitary_apply (u : ℕ → PartialUnitary M) (j : ℕ) :
    (boundedCompletedUnitary u).val j=(u j).completed := rfl

theorem boundedCompletedUnitary_unitary (u : ℕ → PartialUnitary M) (j : ℕ) :
    (boundedCompletedUnitary u).val j ∈ _root_.unitary M.toStarSubalgebra :=
  (u j).completed_unitary

theorem quotient_completed_eq (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
    (u : ℕ → PartialUnitary M)
    (hi : star (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u))*
      quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u)=1) :
    quotientMap τ (ω : Filter ℕ) (boundedCompletedUnitary u)=
      quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u) := by
  have hp : quotientMap τ (ω : Filter ℕ) (boundedPartialSupport u)=1 := by
    rw [← boundedPartialUnitary_initial,map_mul,quotientMap_star]
    exact hi
  let q := quotientMap τ (ω : Filter ℕ)
  have hs : q (1-boundedPartialSupport u)=0 :=
    (map_sub q 1 (boundedPartialSupport u)).trans
      ((congrArg₂ (fun a b => a-b) (map_one q) hp).trans (sub_self _))
  exact (map_add q (boundedPartialUnitary u) (1-boundedPartialSupport u)).trans
    ((congrArg (fun b => q (boundedPartialUnitary u)+b) hs).trans (add_zero _))

theorem bounded_unitary_of_coordinates (a : Bounded M)
    (ha : ∀ j,a.val j ∈ _root_.unitary M.toStarSubalgebra) : a ∈ _root_.unitary (Bounded M) := by
  constructor
  · apply Subtype.ext; funext j; exact (ha j).1
  · apply Subtype.ext; funext j; exact (ha j).2

theorem quotient_unitary_of_coordinates (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
    (a : Bounded M) (ha : ∀ j,a.val j ∈ _root_.unitary M.toStarSubalgebra) :
    quotientMap τ (ω : Filter ℕ) a ∈ _root_.unitary (Q τ ω) := by
  have hu := bounded_unitary_of_coordinates a ha
  constructor
  · rw [← quotientMap_star,← map_mul,hu.1,map_one]
  · rw [← quotientMap_star,← map_mul,hu.2,map_one]

theorem bounded_coordinate_unitaries_inclusion (hNM : N ≤ M) (a : Bounded M)
    (ha : ∀ j,a.val j ∈ _root_.unitary M.toStarSubalgebra ∧ (a.val j).val ∈ N) :
    ∃ b : Bounded N,(∀ j,b.val j ∈ _root_.unitary N.toStarSubalgebra) ∧ boundedInclusion hNM b=a := by
  let b : Bounded N := ⟨fun j => ⟨(a.val j).val,(ha j).2⟩,a.property⟩
  refine ⟨b,?_,rfl⟩
  intro j
  constructor
  · apply Subtype.ext
    change star (a.val j).val*(a.val j).val=1
    exact congrArg (fun x : M.toStarSubalgebra => x.val) (ha j).1.1
  · apply Subtype.ext
    change (a.val j).val*star (a.val j).val=1
    exact congrArg (fun x : M.toStarSubalgebra => x.val) (ha j).1.2

end

/-! Ordered independence with actual coordinate unitaries in the included
algebra, obtained by completing the constructed partial-unitary coordinates. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

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

theorem exists_coordinate_ordered_unitary
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (x : ℕ → Q τ ω) (hx : ∀ i,quotientTrace τ ω (x i)=0) :
    ∃ b : Bounded M,
      (∀ j,b.val j ∈ unitary M.toStarSubalgebra ∧ (b.val j).val ∈ N) ∧
      ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) b) x := by
  obtain ⟨u,hu,hi,hf,hm⟩ := exists_full_support_ordered_independence τ hNM
    hfactor hdiff hirr hsep ω hω x hx
  refine ⟨boundedCompletedUnitary u,?_,?_⟩
  · intro j
    exact ⟨boundedCompletedUnitary_unitary u j,(u j).completed_mem (hu j)⟩
  · rwa [quotient_completed_eq τ ω u hi]

end

/-! Two coordinate-unitary witnesses produce the reduced-moment Haar precursor
while retaining actual unitary coordinates in the included algebra. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

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

theorem exists_coordinate_reduced_unitary
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (x : ℕ → Q τ ω) (hx : ∀ i,quotientTrace τ ω (x i)=0) :
    ∃ a : Bounded M,
      (∀ j,a.val j ∈ unitary M.toStarSubalgebra ∧ (a.val j).val ∈ N) ∧
      ReducedOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) a) x := by
  obtain ⟨a,ha,ham⟩ := exists_coordinate_ordered_unitary τ hNM hfactor hdiff hirr hsep ω hω x hx
  let u := quotientMap τ (ω : Filter ℕ) a
  have hu : u ∈ unitary (Q τ ω) := quotient_unitary_of_coordinates τ ω a (fun j => (ha j).1)
  obtain ⟨b,hb,hbm⟩ := exists_coordinate_ordered_unitary τ hNM hfactor hdiff hirr hsep ω hω
    (productCenteredFamily τ ω u x) (productCenteredFamily_centered τ ω u x hu.2 hx ham)
  refine ⟨a*b,?_,?_⟩
  · intro j
    exact ⟨(unitary M.toStarSubalgebra).mul_mem (ha j).1 (hb j).1,N.mul_mem (ha j).2 (hb j).2⟩
  · rw [map_mul]
    intro c d sign xs hxs
    exact product_reduced_moment τ ω u (quotientMap τ (ω : Filter ℕ) b) x hbm c d sign xs hxs

end

/-! Full integer endpoint moments and an actual included coordinate-unitary
Haar witness, before imposing an operator topology on generated algebras. -/
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

omit hfactor hdiff hirr hsep in
private theorem coordinate_haar_endpoints_of_coordinates
    (D : Subalgebra ℂ (Q τ ω)) (x : ℕ → Q τ ω)
    (hdense : ∀ d ∈ D,quotientTrace τ ω d=0 → d ∈ closure (Set.range x))
    (a : Bounded M)
    (ha : ∀ j,a.val j ∈ unitary M.toStarSubalgebra ∧ (a.val j).val ∈ N)
    (hm : ReducedOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) a) x) :
    ∃ t : unitary (Q τ ω),
      (∃ b : Bounded N,(∀ j,b.val j ∈ unitary N.toStarSubalgebra) ∧
        quotientInclusion τ hNM (ω : Filter ℕ)
          (quotientMap (restrictedTrace τ hNM) (ω : Filter ℕ) b)=(t : Q τ ω)) ∧
      (∀ n : ℤ,n ≠ 0 → quotientTrace τ ω (↑(t^n) : Q τ ω)=0) ∧
      ∀ c ∈ D,∀ d ∈ D,∀ n : ℤ,n ≠ 0 → ∀ xs : List (Q τ ω × ℤ),
        (∀ z ∈ xs,z.1 ∈ D ∧ quotientTrace τ ω z.1=0 ∧ z.2 ≠ 0) →
        quotientTrace τ ω (c*integerValueWord τ ω t n xs d)=0 := by
  let t : unitary (Q τ ω) := ⟨quotientMap τ (ω : Filter ℕ) a,
    quotient_unitary_of_coordinates τ ω a (fun j => (ha j).1)⟩
  obtain ⟨b,hb⟩ := bounded_coordinate_unitaries_inclusion hNM a ha
  have hhaar := reducedOrderedMoments_haar τ ω t x hm
  refine ⟨t,⟨b,hb.1,?_⟩,hhaar,?_⟩
  · change quotientMap τ (ω : Filter ℕ) (boundedInclusion hNM b)=quotientMap τ (ω : Filter ℕ) a
    exact congrArg (quotientMap τ (ω : Filter ℕ)) hb.2
  · intro c hc d hd n hn xs hxs
    apply reduced_integer_moment_closedSpan τ ω t x hm c d
      (subalgebra_mem_centered_closedSpan τ ω D x hdense c hc)
      (subalgebra_mem_centered_closedSpan τ ω D x hdense d hd) n hn xs
    intro z hz
    exact ⟨Submodule.closure_subset_topologicalClosure_span _
      (hdense z.1 (hxs z hz).1 (hxs z hz).2.1),(hxs z hz).2.2⟩

private theorem coordinate_haar_endpoints_of_dense_family (hω : (ω : Filter ℕ) ≤ atTop)
    (D : Subalgebra ℂ (Q τ ω)) (x : ℕ → Q τ ω)
    (hx : ∀ i,x i ∈ D ∧ quotientTrace τ ω (x i)=0)
    (hdense : ∀ d ∈ D,quotientTrace τ ω d=0 → d ∈ closure (Set.range x)) :
    ∃ t : unitary (Q τ ω),
      (∃ b : Bounded N,(∀ j,b.val j ∈ unitary N.toStarSubalgebra) ∧
        quotientInclusion τ hNM (ω : Filter ℕ)
          (quotientMap (restrictedTrace τ hNM) (ω : Filter ℕ) b)=(t : Q τ ω)) ∧
      (∀ n : ℤ,n ≠ 0 → quotientTrace τ ω (↑(t^n) : Q τ ω)=0) ∧
      ∀ c ∈ D,∀ d ∈ D,∀ n : ℤ,n ≠ 0 → ∀ xs : List (Q τ ω × ℤ),
        (∀ z ∈ xs,z.1 ∈ D ∧ quotientTrace τ ω z.1=0 ∧ z.2 ≠ 0) →
        quotientTrace τ ω (c*integerValueWord τ ω t n xs d)=0 := by
  obtain ⟨a,ha⟩ := exists_coordinate_reduced_unitary (H := H) (N := N) (M := M) τ hNM hfactor hdiff hirr hsep
    ω hω x (fun i => (hx i).2)
  exact coordinate_haar_endpoints_of_coordinates τ ω hNM D x hdense a ha.1 ha.2

theorem exists_coordinate_haar_endpoints (hω : (ω : Filter ℕ) ≤ atTop)
    (D : Subalgebra ℂ (Q τ ω)) (hD : TopologicalSpace.IsSeparable (D : Set (Q τ ω))) :
    ∃ t : unitary (Q τ ω),
      (∃ b : Bounded N,(∀ j,b.val j ∈ unitary N.toStarSubalgebra) ∧
        quotientInclusion τ hNM (ω : Filter ℕ)
          (quotientMap (restrictedTrace τ hNM) (ω : Filter ℕ) b)=(t : Q τ ω)) ∧
      (∀ n : ℤ,n ≠ 0 → quotientTrace τ ω (↑(t^n) : Q τ ω)=0) ∧
      ∀ c ∈ D,∀ d ∈ D,∀ n : ℤ,n ≠ 0 → ∀ xs : List (Q τ ω × ℤ),
        (∀ z ∈ xs,z.1 ∈ D ∧ quotientTrace τ ω z.1=0 ∧ z.2 ≠ 0) →
        quotientTrace τ ω (c*integerValueWord τ ω t n xs d)=0 := by
  obtain ⟨x,hx⟩ := exists_centered_dense_quotient_family (H := H) (M := M) τ ω D hD
  exact coordinate_haar_endpoints_of_dense_family τ ω hNM hfactor hdiff hirr hsep
    hω D x hx.1 hx.2

end Generator.Tracial

end

end OAI
