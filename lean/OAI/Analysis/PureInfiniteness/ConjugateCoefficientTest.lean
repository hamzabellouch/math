import OAI.Analysis.Nuclearity.CompletedConjugation
import OAI.Analysis.Nuclearity.UnitizedConeMembership
import OAI.Analysis.PureInfiniteness.ApproximateUnitConjugation
import OAI.Analysis.Nuclearity.NuclearConeNullspace

namespace OAI

/-! The separating-functional step of KR02 7.18: nonnegativity on the
actual coefficient cone passes to every conjugate of an abelian compression
and to the closed positive cone they generate. -/

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder InnerProductSpace
open Filter Topology

namespace WeakPureInfiniteness

variable {A B C H I : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [CStarAlgebra C] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder C] [StarOrderedRing C] [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype I]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ Filter.atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local instance coefficientTestOrder : PartialOrder (MinimalTensor B C) := CStarAlgebra.spectralOrder _
local instance coefficientTestOrdered : StarOrderedRing (MinimalTensor B C) := CStarAlgebra.spectralOrderedRing _

omit [TopologicalSpace.SeparableSpace B] [Fact ((U : Filter ℕ) ≤ Filter.atTop)] in
theorem polynomial_conjugate_nonneg_of_coefficient_test
    (hB : Nuclear B) (β : B →⋆ₙₐ[ℂ] N)
    (π : Unitization ℂ N →⋆ₐ[ℂ] (H →L[ℂ] H))
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ d c, Commute (π d) (η c))
    (ξ : H) (hcyc : DenseRange (fun a => π a ξ)) (v : N)
    (hv : ∀ b c, Commute (innerHomCompression β v b) (innerHomCompression β v c))
    (x : I → B) (y : I → C) (z : MinimalTensor B C)
    (htest : ∀ w : N,
      (innerHomCompression β w : B → N) ∈ finiteUnitizedAbelianCoefficientCone U β →
      0 ≤ (compressedTensorFunctional hB β
        (π.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ N)) η
        (fun d c => hc (d : Unitization ℂ N) c) ξ w z).re) :
    0 ≤ (compressedTensorFunctional hB β
      (π.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ N)) η
      (fun d c => hc (d : Unitization ℂ N) c) ξ v
        (star (∑ i, minimalElementary (x i) (y i)) * z *
          (∑ i, minimalElementary (x i) (y i)))).re := by
  classical
  let ρ := π.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ N)
  let hρ : ∀ d c, Commute (ρ d) (η c) := fun d c => hc (d : Unitization ℂ N) c
  let Φ := compressedTensorFunctional hB β ρ η hρ ξ
  let d := ∑ i, minimalElementary (x i) (y i)
  change 0 ≤ (Φ v (star d * z * d)).re
  by_contra hn
  have hneg : (Φ v (star d * z * d)).re < 0 := lt_of_not_ge hn
  obtain ⟨a, ha⟩ := completed_conjugation_inner_approximation hB β π η hc ξ hcyc v x y
    (fun _ : Unit => z) (-(Φ v (star d * z * d)).re / 2) (by linarith)
  let w := ∑ i, unitizedRightMul (β (x i) * v) (a i)
  change ‖(fun _ : Unit => Φ v (star d * z * d) - Φ w z)‖ <
    -(Φ v (star d * z * d)).re / 2 at ha
  have hw := htest w (coefficient_inner_mem_cone U β v hv a x)
  have he : ‖Φ v (star d * z * d) - Φ w z‖ < -(Φ v (star d * z * d)).re / 2 := by
    exact (norm_le_pi_norm (fun _ : Unit => Φ v (star d * z * d) - Φ w z) ()).trans_lt ha
  have hr := (Complex.abs_re_le_norm (Φ v (star d * z * d) - Φ w z)).trans_lt he
  rw [Complex.sub_re] at hr
  have hb := (abs_lt.mp hr).1
  change 0 ≤ (Φ w z).re at hw
  linarith

omit [Fintype I] [TopologicalSpace.SeparableSpace B] [Fact ((U : Filter ℕ) ≤ Filter.atTop)] in
theorem conjugate_nonneg_of_coefficient_test
    (hB : Nuclear B) (β : B →⋆ₙₐ[ℂ] N)
    (π : Unitization ℂ N →⋆ₐ[ℂ] (H →L[ℂ] H))
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ d c, Commute (π d) (η c))
    (ξ : H) (hcyc : DenseRange (fun a => π a ξ)) (v : N)
    (hv : ∀ b c, Commute (innerHomCompression β v b) (innerHomCompression β v c))
    (z : MinimalTensor B C)
    (htest : ∀ w : N,
      (innerHomCompression β w : B → N) ∈ finiteUnitizedAbelianCoefficientCone U β →
      0 ≤ (compressedTensorFunctional hB β
        (π.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ N)) η
        (fun d c => hc (d : Unitization ℂ N) c) ξ w z).re)
    (d : MinimalTensor B C) :
    0 ≤ (compressedTensorFunctional hB β
      (π.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ N)) η
      (fun d c => hc (d : Unitization ℂ N) c) ξ v (star d * z * d)).re := by
  classical
  let ρ := π.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ N)
  let hρ : ∀ d c, Commute (ρ d) (η c) := fun d c => hc (d : Unitization ℂ N) c
  let Φ := compressedTensorFunctional hB β ρ η hρ ξ v
  let S : Set (MinimalTensor B C) := {d | 0 ≤ (Φ (star d * z * d)).re}
  have hS : IsClosed S := isClosed_functional_conjugate_nonneg
    (⟨Φ.toLinearMap, map_continuous Φ⟩ : MinimalTensor B C →L[ℂ] ℂ) z
  have hpoly : Set.range (tensorPolynomial (A := B) (C := C)) ⊆ S := by
    rintro _ ⟨p, rfl⟩
    let x (i : p.support) := p i.val • i.val.1
    let y (i : p.support) := i.val.2
    have hp : tensorPolynomial p = ∑ i : p.support, minimalElementary (x i) (y i) := by
      rw [tensorPolynomial_eq_sum]
      exact (Finset.sum_coe_sort p.support (fun i => minimalElementary (p i • i.1) i.2)).symm
    change 0 ≤ (Φ (star (tensorPolynomial p) * z * tensorPolynomial p)).re
    rw [hp]
    exact polynomial_conjugate_nonneg_of_coefficient_test U hB β π η hc ξ hcyc v hv x y z htest
  exact (closure_minimal hpoly hS) (tensorPolynomial_dense d)

omit [Fintype I] [TopologicalSpace.SeparableSpace B] [Fact ((U : Filter ℕ) ≤ Filter.atTop)] in
theorem base_nonneg_of_coefficient_test
    (hB : Nuclear B) (β : B →⋆ₙₐ[ℂ] N)
    (π : Unitization ℂ N →⋆ₐ[ℂ] (H →L[ℂ] H))
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ d c, Commute (π d) (η c))
    (ξ : H) (hcyc : DenseRange (fun a => π a ξ)) (v : N)
    (hv : ∀ b c, Commute (innerHomCompression β v b) (innerHomCompression β v c))
    (z : MinimalTensor B C)
    (htest : ∀ w : N,
      (innerHomCompression β w : B → N) ∈ finiteUnitizedAbelianCoefficientCone U β →
      0 ≤ (compressedTensorFunctional hB β
        (π.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ N)) η
        (fun d c => hc (d : Unitization ℂ N) c) ξ w z).re) :
    0 ≤ (compressedTensorFunctional hB β
      (π.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ N)) η
      (fun d c => hc (d : Unitization ℂ N) c) ξ v z).re := by
  let Φ := compressedTensorFunctional hB β
    (π.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ N)) η
    (fun d c => hc (d : Unitization ℂ N) c) ξ v
  exact continuous_functional_nonneg_of_conjugates
    (⟨Φ.toLinearMap, map_continuous Φ⟩ : MinimalTensor B C →L[ℂ] ℂ) z
    (conjugate_nonneg_of_coefficient_test U hB β π η hc ξ hcyc v hv z htest)

omit [Fintype I] [TopologicalSpace.SeparableSpace B]
  [Fact ((U : Filter ℕ) ≤ Filter.atTop)] in
theorem abelianTensorCone_nonneg_of_coefficient_test
    (hB : Nuclear B) (β : B →⋆ₙₐ[ℂ] N)
    (π : Unitization ℂ N →⋆ₐ[ℂ] (H →L[ℂ] H))
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ d c, Commute (π d) (η c))
    (ξ : H) (hcyc : DenseRange (fun a => π a ξ)) (z : selfAdjoint (MinimalTensor B C))
    (htest : ∀ w : N,
      (innerHomCompression β w : B → N) ∈ finiteUnitizedAbelianCoefficientCone U β →
      0 ≤ (compressedTensorFunctional hB β
        (π.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ N)) η
        (fun d c => hc (d : Unitization ℂ N) c) ξ w z).re) :
    ∀ ψ ∈ abelianTensorCone U hB β
      (π.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ N)) η
      (fun d c => hc (d : Unitization ℂ N) c) ξ, 0 ≤ ψ z := by
  let ρ := π.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ N)
  let hρ : ∀ d c, Commute (ρ d) (η c) := fun d c => hc (d : Unitization ℂ N) c
  let K : ConvexCone ℝ (WeakDual ℝ (selfAdjoint (MinimalTensor B C))) :=
    { carrier := {ψ | 0 ≤ ψ z}
      smul_mem' := by
        intro t ht ψ hψ
        change 0 ≤ t * ψ z
        exact mul_nonneg ht.le hψ
      add_mem' := by
        intro ψ hψ θ hθ
        change 0 ≤ ψ z + θ z
        exact add_nonneg hψ hθ }
  have hclosed : IsClosed (K : Set (WeakDual ℝ (selfAdjoint (MinimalTensor B C)))) :=
    isClosed_le continuous_const (WeakDual.eval_continuous z)
  have hgen : conjugateGenerators (fun v : abelianCompressionIndex U β =>
      compressedTensorFunctional hB β ρ η hρ ξ v.val) ⊆ (K : Set _) := by
    rintro ψ (rfl | ⟨v, rfl | ⟨d, rfl⟩⟩)
    · change (0 : ℝ) ≤ 0
      exact le_refl 0
    · exact base_nonneg_of_coefficient_test U hB β π η hc ξ hcyc v.val v.property z htest
    · exact conjugate_nonneg_of_coefficient_test U hB β π η hc ξ hcyc v.val v.property z htest d
  exact closure_minimal (ConvexCone.hull_min hgen) hclosed

end WeakPureInfiniteness

end

end OAI
