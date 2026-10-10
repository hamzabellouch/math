import OAI.Analysis.KadisonKastler.CommonRightProjection

namespace OAI

/-! # Cyclicity from the common left and right vector actions

The projection onto the closed commutant orbit belongs to the original
von Neumann algebra. Common vector actions make it commute with the
irreducible common subalgebra, so its scalar value is one. Applying the
same argument to the commutant proves both cyclicity and separation.
No cyclicity or standard-form conclusion is assumed.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A common right vector value makes the left action preserve the closed
commutant orbit. -/
theorem commutant_orbit_invariant_of_common_vector
    (N : VonNeumannAlgebra H) (Ω : H)
    (r : H →L[ℂ] H) (hr : r ∈ N)
    (s : H →L[ℂ] H) (hs : s ∈ N.commutant)
    (hvector : r Ω = s Ω)
    {ξ : H} (hξ : ξ ∈ Generator.vectorOrbitClosure N.commutant.toStarSubalgebra Ω) :
    r ξ ∈ Generator.vectorOrbitClosure N.commutant.toStarSubalgebra Ω := by
  apply vectorOrbitClosure_invariant_of_orbit N.commutant.toStarSubalgebra Ω r ?_ hξ
  intro x
  refine ⟨x * (⟨s, hs⟩ : Algebra N.commutant), ?_⟩
  have hc : r * x.val = x.val * r :=
    VonNeumannAlgebra.mem_commutant_iff.mp x.property r hr
  calc
    r (x.val Ω) = x.val (r Ω) :=
      congrArg (fun T : H →L[ℂ] H => T Ω) hc
    _ = x.val (s Ω) := by rw [hvector]
    _ = (x * (⟨s, hs⟩ : Algebra N.commutant)).val Ω := rfl

/-- Irreducibility and common vector actions force the commutant orbit to
be all of the actual Hilbert space. -/
theorem commutant_orbitClosure_eq_top_of_relative_scalar
    (N : VonNeumannAlgebra H) (R : StarSubalgebra ℂ (H →L[ℂ] H))
    (hRN : R ≤ N.toStarSubalgebra) (Ω : H) (hΩ : Ω ≠ 0)
    (hirr : ∀ T ∈ N, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hvector : ∀ r ∈ R, ∃ s ∈ N.commutant, r Ω = s Ω) :
    Generator.vectorOrbitClosure N.commutant.toStarSubalgebra Ω = ⊤ := by
  let K := Generator.vectorOrbitClosure N.commutant.toStarSubalgebra Ω
  have hpN : K.starProjection ∈ N := by
    have hp : K.starProjection ∈ N.commutant.commutant := by
      apply VonNeumannAlgebra.mem_commutant_iff.mpr
      intro x hx
      exact (Generator.vectorOrbitProjection_commutes N.commutant.toStarSubalgebra
        Ω ⟨x, hx⟩).symm
    simpa only [VonNeumannAlgebra.commutant_commutant] using hp
  have hpR (r : H →L[ℂ] H) (hr : r ∈ R) : r * K.starProjection = K.starProjection * r := by
    symm
    apply Generator.starProjection_commutes_of_invariant
    · obtain ⟨s, hs, hvec⟩ := hvector r hr
      exact fun ξ hξ => commutant_orbit_invariant_of_common_vector N Ω r
        (hRN hr) s hs hvec hξ
    · obtain ⟨s, hs, hvec⟩ := hvector (star r) (R.star_mem' hr)
      exact fun ξ hξ => commutant_orbit_invariant_of_common_vector N Ω (star r)
        (hRN (R.star_mem' hr)) s hs hvec hξ
  obtain ⟨z, hz⟩ := hirr K.starProjection hpN hpR
  have hpΩ : K.starProjection Ω = Ω :=
    Submodule.starProjection_eq_self_iff.mpr (Generator.mem_vectorOrbitClosure _ _)
  have hz1 : z = 1 := by
    apply smul_left_injective ℂ hΩ
    have he := hpΩ
    rw [hz] at he
    simpa only [smul_apply, one_apply_eq_self, one_smul] using he
  have hp1 : K.starProjection = 1 := by simpa only [hz1, one_smul] using hz
  apply top_unique
  intro ξ _
  apply Submodule.starProjection_eq_self_iff.mp
  rw [show (Generator.vectorOrbitClosure N.commutant.toStarSubalgebra Ω).starProjection = 1
    from hp1]
  rfl

/-- The corresponding dense-range formulation is suitable for uniqueness
of operators on the commutant orbit. -/
theorem commutant_orbit_dense_of_relative_scalar
    (N : VonNeumannAlgebra H) (R : StarSubalgebra ℂ (H →L[ℂ] H))
    (hRN : R ≤ N.toStarSubalgebra) (Ω : H) (hΩ : Ω ≠ 0)
    (hirr : ∀ T ∈ N, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hvector : ∀ r ∈ R, ∃ s ∈ N.commutant, r Ω = s Ω) :
    DenseRange (fun x : Algebra N.commutant => x.val Ω) := by
  intro ξ
  have hξ : ξ ∈ Generator.vectorOrbitClosure N.commutant.toStarSubalgebra Ω := by
    rw [commutant_orbitClosure_eq_top_of_relative_scalar N R hRN Ω hΩ hirr hvector]
    trivial
  exact hξ

/-- The common left/right vector correspondence gives both dense orbits.
Only the two relative scalar-commutant statements are used. -/
theorem preparedPair_dense_orbits
    (N : VonNeumannAlgebra H)
    (R S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hRN : R ≤ N.toStarSubalgebra) (hSN : S ≤ N.commutant.toStarSubalgebra)
    (Ω : H) (hΩ : Ω ≠ 0)
    (hirrR : ∀ T ∈ N, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hirrS : ∀ T ∈ N.commutant, (∀ s ∈ S, s * T = T * s) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hRS : ∀ r ∈ R, ∃ s ∈ S, r Ω = s Ω)
    (hSR : ∀ s ∈ S, ∃ r ∈ R, s Ω = r Ω) :
    DenseRange (fun x : Algebra N => x.val Ω) ∧
      DenseRange (fun x : Algebra N.commutant => x.val Ω) := by
  have hright : DenseRange (fun x : Algebra N.commutant => x.val Ω) :=
    commutant_orbit_dense_of_relative_scalar N R hRN Ω hΩ hirrR (by
      intro r hr
      obtain ⟨s, hs, hv⟩ := hRS r hr
      exact ⟨s, hSN hs, hv⟩)
  have hleft := commutant_orbit_dense_of_relative_scalar N.commutant S hSN Ω hΩ hirrS (by
    intro s hs
    obtain ⟨r, hr, hv⟩ := hSR s hs
    refine ⟨r, ?_, hv⟩
    rw [VonNeumannAlgebra.commutant_commutant]
    exact hRN hr)
  change DenseRange (fun x : N.commutant.commutant.toStarSubalgebra => x.val Ω) at hleft
  rw [VonNeumannAlgebra.commutant_commutant] at hleft
  exact ⟨hleft, hright⟩

/-- A vector cyclic for the commutant separates the original algebra. -/
theorem separating_of_dense_commutant_orbit
    (N : VonNeumannAlgebra H) (Ω : H)
    (hcyclic : DenseRange (fun x : Algebra N.commutant => x.val Ω))
    (a : Algebra N) (ha : a.val Ω = 0) : a = 0 := by
  apply Subtype.ext
  apply operator_eq_of_mem_commutant_of_eq_on_cyclicVector N.commutant Ω hcyclic
    a.val 0
  · rw [VonNeumannAlgebra.commutant_commutant]
    exact a.property
  · exact N.commutant.commutant.zero_mem
  · simpa only [zero_apply] using ha

/-- In the prepared-pair argument, the actual common vector is cyclic and
separating for both sides; no separate standard-position premise remains. -/
theorem preparedPair_cyclic_separating
    (N : VonNeumannAlgebra H)
    (R S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hRN : R ≤ N.toStarSubalgebra) (hSN : S ≤ N.commutant.toStarSubalgebra)
    (Ω : H) (hΩ : Ω ≠ 0)
    (hirrR : ∀ T ∈ N, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hirrS : ∀ T ∈ N.commutant, (∀ s ∈ S, s * T = T * s) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hRS : ∀ r ∈ R, ∃ s ∈ S, r Ω = s Ω)
    (hSR : ∀ s ∈ S, ∃ r ∈ R, s Ω = r Ω) :
    DenseRange (fun x : Algebra N => x.val Ω) ∧
      DenseRange (fun x : Algebra N.commutant => x.val Ω) ∧
      (∀ a : Algebra N, a.val Ω = 0 → a = 0) ∧
      (∀ a : Algebra N.commutant, a.val Ω = 0 → a = 0) := by
  obtain ⟨hleft, hright⟩ := preparedPair_dense_orbits N R S hRN hSN Ω hΩ
    hirrR hirrS hRS hSR
  refine ⟨hleft, hright, separating_of_dense_commutant_orbit N Ω hright, ?_⟩
  apply separating_of_dense_commutant_orbit N.commutant Ω
  change DenseRange (fun x : N.commutant.commutant.toStarSubalgebra => x.val Ω)
  rw [VonNeumannAlgebra.commutant_commutant]
  exact hleft

/-- The source's central-vector identity supplies both vector
correspondences when the right algebra is the conjugate of the left one. -/
theorem preparedPair_cyclic_separating_of_conjugate_algebra
    (N : VonNeumannAlgebra H)
    (R S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hRN : R ≤ N.toStarSubalgebra) (hSN : S ≤ N.commutant.toStarSubalgebra)
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hS : (S : Set (H →L[ℂ] H)) = conjugationOperator J '' (R : Set (H →L[ℂ] H)))
    (Ω : H) (hΩ : Ω ≠ 0)
    (hirrR : ∀ T ∈ N, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hirrS : ∀ T ∈ N.commutant, (∀ s ∈ S, s * T = T * s) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hcentral : ∀ r ∈ R, r Ω = conjugationOperator J (star r) Ω) :
    DenseRange (fun x : Algebra N => x.val Ω) ∧
      DenseRange (fun x : Algebra N.commutant => x.val Ω) ∧
      (∀ a : Algebra N, a.val Ω = 0 → a = 0) ∧
      (∀ a : Algebra N.commutant, a.val Ω = 0 → a = 0) := by
  apply preparedPair_cyclic_separating N R S hRN hSN Ω hΩ hirrR hirrS
  · intro r hr
    refine ⟨conjugationOperator J (star r), ?_, hcentral r hr⟩
    change conjugationOperator J (star r) ∈ (S : Set (H →L[ℂ] H))
    rw [hS]
    exact ⟨star r, R.star_mem' hr, rfl⟩
  · intro s hs
    change s ∈ (S : Set (H →L[ℂ] H)) at hs
    rw [hS] at hs
    obtain ⟨r, hr, rfl⟩ := hs
    refine ⟨star r, R.star_mem' hr, ?_⟩
    simpa only [star_star] using (hcentral (star r) (R.star_mem' hr)).symm

end

end KadisonKastler

end OAI
