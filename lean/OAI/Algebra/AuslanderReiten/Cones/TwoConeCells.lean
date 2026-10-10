import OAI.Algebra.AuslanderReiten.Cones.TwoCone

namespace OAI

namespace ArExplicit.TwoCone

universe u
variable {R : Type u} [Ring R] (D : Data R)

abbrev firstInclusion (n : ℕ) : D.term n →ₗ[R] firstTerm D n :=
  LinearMap.inl R (D.term n) (D.term (n+2))

abbrev firstProjection (n : ℕ) : firstTerm D n →ₗ[R] D.term (n+2) :=
  LinearMap.snd R (D.term n) (D.term (n+2))

abbrev inclusion (n : ℕ) : firstTerm D n →ₗ[R] term D n :=
  LinearMap.inl R (firstTerm D n) (firstTerm D (n+2))

abbrev projection (n : ℕ) : term D n →ₗ[R] firstTerm D (n+2) :=
  LinearMap.snd R (firstTerm D n) (firstTerm D (n+2))

theorem firstInclusion_comm (n : ℕ) :
    (firstD D n).comp (firstInclusion D (n+1)) = (firstInclusion D n).comp (D.d n) := by
  ext x <;> simp [firstD, coneBlock_apply]

theorem firstProjection_comm (n : ℕ) :
    (firstProjection D n).comp (firstD D n) = -(D.d (n+2)).comp (firstProjection D (n+1)) := by
  apply LinearMap.ext
  intro x
  rfl

theorem inclusion_comm (n : ℕ) :
    (d D n).comp (inclusion D (n+1)) = (inclusion D n).comp (firstD D n) := by
  ext x <;> simp [d, coneBlock_apply]

theorem projection_comm (n : ℕ) :
    (projection D n).comp (d D n) = -(firstD D (n+2)).comp (projection D (n+1)) := by
  apply LinearMap.ext
  intro x
  rfl

theorem firstInclusion_injective (n : ℕ) : Function.Injective (firstInclusion D n) := by
  intro x y h
  exact congrArg Prod.fst h

theorem firstProjection_surjective (n : ℕ) : Function.Surjective (firstProjection D n) :=
  fun x => ⟨(0,x), rfl⟩

theorem first_exact (n : ℕ) :
    Function.Exact (firstInclusion D n) (firstProjection D n) := by
  rintro ⟨x,y⟩
  constructor
  · intro h
    exact ⟨x, Prod.ext rfl h.symm⟩
  · rintro ⟨z,hz⟩
    exact (congrArg Prod.snd hz).symm

theorem inclusion_injective (n : ℕ) : Function.Injective (inclusion D n) := by
  intro x y h
  exact congrArg Prod.fst h

theorem projection_surjective (n : ℕ) : Function.Surjective (projection D n) :=
  fun x => ⟨(0,x), rfl⟩

theorem exact (n : ℕ) : Function.Exact (inclusion D n) (projection D n) := by
  rintro ⟨x,y⟩
  constructor
  · intro h
    exact ⟨x, Prod.ext rfl h.symm⟩
  · rintro ⟨z,hz⟩
    exact (congrArg Prod.snd hz).symm

abbrev topProjection (n : ℕ) : term D n →ₗ[R] D.term (n+4) :=
  (firstProjection D (n+2)).comp (projection D n)

theorem topProjection_comm (n : ℕ) :
    (topProjection D n).comp (d D n) =
      (D.d (n+4)).comp (topProjection D (n+1)) := by
  apply LinearMap.ext
  rintro ⟨⟨a,b⟩,⟨c,e⟩⟩
  change -(-D.d (n+4) e) = D.d (n+4) e
  exact neg_neg _

end ArExplicit.TwoCone

end OAI
