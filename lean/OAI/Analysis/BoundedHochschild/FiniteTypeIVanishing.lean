import OAI.Analysis.BoundedHochschild.FiniteTypeIPieces

namespace OAI

/-! Unconditional bounded Hochschild vanishing on finite type I algebras. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open FinitePathMain HochschildCorners

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem finite_typeI_central_partition (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (hI : TypeICentralSummand (1 : M)) :
    ∃ D : MaximalCentralPartition M HomogeneousTypeICorner, D.complement = 0 := by
  obtain ⟨D⟩ := exists_maximal_central_partition e HomogeneousTypeICorner
  refine ⟨D, ?_⟩
  by_contra h0
  obtain ⟨q, hq, hqle, hq0, hhom⟩ := finite_typeI_homogeneous_subprojection e hfinite hI
    D.complement_isProjection D.complement_central h0
  exact hq0 (D.maximal q hq.1 (fun a => (hq.2 a).eq) hqle hhom)

/-- Finite type I algebras have bounded primitives in every positive degree.
The bound is independent of the ranks of their homogeneous central pieces. -/
theorem finite_typeI_primitive (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (hI : TypeICentralSummand (1 : M))
    {n : ℕ} (f : Cochain M (n + 1)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ + n * ‖f‖ ∧ ∀ x, differentialValue g x = f x := by
  classical
  obtain ⟨D, hD⟩ := finite_typeI_central_partition e hfinite hI
  have htotal (a : M) (ha : ∀ i, D.projection i * a = 0) : a = 0 :=
    D.total a (by rw [hD, zero_mul]) ha
  have hpieces (i : D.Index) :
      ∃ b : Cochain (Corner (D.projection i) (D.isProjection i)) n,
        ‖b‖ ≤ ‖f‖ ∧ ∀ x, differentialValue b x =
          CentralCorner.restrict (D.projection i) (D.isProjection i) (D.central i) f x := by
    obtain ⟨hp, d, E, j, hab⟩ := D.property i
    obtain ⟨b, hbn, hb⟩ := finite_homogeneous_typeI_primitive_of_abelian_diagonal
      (cornerPredualEquiv (D.projection i) (D.isProjection i) e) E j hab
      (CentralCorner.restrict (D.projection i) (D.isProjection i) (D.central i) f)
      (CentralCorner.restrict_cocycle _ _ _ f hf)
    exact ⟨b, hbn.trans (CentralCorner.restrict_norm _ _ _ f), hb⟩
  choose b hbn hb using hpieces
  exact primitive_of_central_cut_primitives e (HochschildSakai.mul_hasPreadjoint e)
    D.projection D.isProjection D.central D.orthogonal htotal f hf
    (fun i => CentralCorner.extend (D.projection i) (D.isProjection i) (D.central i) (b i))
    (fun i => CentralCorner.extend_supported _ _ _ _)
    (fun i => CentralCorner.extend_primitive _ _ _ f (b i) (hb i))
    ‖f‖ (norm_nonneg f) (fun i => (CentralCorner.extend_norm _ _ _ _).trans (hbn i))

/-- In a finite algebra the absence of a type II₁ central summand forces type I. -/
theorem finite_typeI_of_noTypeII1 (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (hno : NoTypeII1Summand M) :
    TypeICentralSummand (1 : M) := by
  obtain ⟨p, hp, hc, hI, _, hII⟩ := exists_typeI_central_cut e
  have hcc (a : M) : (1 - p) * a = a * (1 - p) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hc]
  have hfinC : FiniteAlgebra (Corner (1 - p) hp.one_sub) :=
    (finiteCorner_iff (1 - p) hp.one_sub).mp
      (finiteCorner_of_finiteAlgebra hfinite (1 - p) hp.one_sub)
  have hcomp := hno (1 - p) hp.one_sub hcc hfinC hII
  have hp1 : p = 1 := (sub_eq_zero.mp hcomp).symm
  simpa only [hp1] using hI

/-- The entire finite case of the classical non-II₁ vanishing input. -/
theorem finite_noTypeII1_primitive (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (hno : NoTypeII1Summand M)
    {n : ℕ} (f : Cochain M (n + 2)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M (n + 1), ‖g‖ ≤ ‖f‖ + (n + 1) * ‖f‖ ∧
      ∀ x, differentialValue g x = f x := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    finite_typeI_primitive e hfinite (finite_typeI_of_noTypeII1 e hfinite hno) f hf

end BoundedHochschild.KadisonRingrose

end

end OAI
