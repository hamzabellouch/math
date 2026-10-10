import OAI.NumberTheory.SiegelZeros.Estimates.KoszulBounded

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.W30
universe u
variable {R : Type u} [CommRing R]

theorem scalarCone_positive_exact (C : ChainComplex (ModuleCat.{u} R) ℕ)
    {Q : Type u} [AddCommGroup Q] [Module R Q] (π : C.X 0 →ₗ[R] Q) (r : R)
    (hzero : LinearMap.range (C.d 1 0).hom = LinearMap.ker π)
    (hexact : ∀ n, LinearMap.range (C.d (n + 2) (n + 1)).hom =
      LinearMap.ker (C.d (n + 1) n).hom)
    (hr : IsSMulRegular Q r) (n : ℕ) :
    LinearMap.range ((scalarConeComplex C r).d (n + 2) (n + 1)).hom =
      LinearMap.ker ((scalarConeComplex C r).d (n + 1) n).hom := by
  cases n with
  | zero =>
    change LinearMap.range
        (ChainComplex.of.d (scalarConeObject C) (scalarConeMap C r) 2 1).hom =
      LinearMap.ker
        (ChainComplex.of.d (scalarConeObject C) (scalarConeMap C r) 1 0).hom
    erw [ChainComplex.of_d (scalarConeObject C) (scalarConeMap C r) 1,
      ChainComplex.of_d (scalarConeObject C) (scalarConeMap C r) 0]
    exact coneBottom_exact (C.d 2 1).hom (C.d 1 0).hom π r (hexact 0) hzero hr
  | succ n =>
    have hd₁ : (scalarConeComplex C r).d (n + 1 + 2) (n + 1 + 1) =
        scalarConeMap C r (n + 1 + 1) := ChainComplex.of_d _ _ (n + 1 + 1)
    have hd₀ : (scalarConeComplex C r).d (n + 1 + 1) (n + 1) =
        scalarConeMap C r (n + 1) := ChainComplex.of_d _ _ (n + 1)
    rw [hd₁, hd₀]
    exact scalarCone_interior_exact C r n (hexact (n + 1)) (hexact n)

theorem iterateScalarCones_exact (rs : List R) {Q : Type u}
    [AddCommGroup Q] [Module R Q] (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (π : C.X 0 →ₗ[R] Q) (hπ : Function.Surjective π)
    (hzero : LinearMap.range (C.d 1 0).hom = LinearMap.ker π)
    (hexact : ∀ n, LinearMap.range (C.d (n + 2) (n + 1)).hom =
      LinearMap.ker (C.d (n + 1) n).hom)
    (hreg : RingTheory.Sequence.IsRegular Q rs) :
    ∃ ε : (iterateScalarCones C rs).X 0 →ₗ[R]
        (Q ⧸ (Ideal.ofList rs • ⊤ : Submodule R Q)),
      Function.Surjective ε ∧
      LinearMap.range ((iterateScalarCones C rs).d 1 0).hom = LinearMap.ker ε ∧
      ∀ n, LinearMap.range ((iterateScalarCones C rs).d (n + 2) (n + 1)).hom =
        LinearMap.ker ((iterateScalarCones C rs).d (n + 1) n).hom := by
  induction rs generalizing Q C with
  | nil =>
    let e := (Ideal.ofList ([] : List R) • (⊤ : Submodule R Q)).quotEquivOfEqBot
      (by simp)
    refine ⟨e.symm.toLinearMap.comp π, e.symm.surjective.comp hπ, ?_, hexact⟩
    calc
      _ = LinearMap.ker π := hzero
      _ = _ := by
        ext x
        change π x = 0 ↔ e.symm (π x) = 0
        exact ⟨fun h => by rw [h, map_zero], fun h => e.symm.injective (by simpa using h)⟩
  | cons r rs ih =>
    obtain ⟨hr, htail⟩ := (RingTheory.Sequence.isRegular_cons_iff Q r rs).mp hreg
    let C' := scalarConeComplex C r
    let π' : C'.X 0 →ₗ[R] QuotSMulTop r Q := coneQuotientAugmentation π r
    have hπ' : Function.Surjective π' := coneQuotientAugmentation_surjective π r hπ
    have hz' : LinearMap.range (C'.d 1 0).hom = LinearMap.ker π' := by
      change LinearMap.range
          (ChainComplex.of.d (scalarConeObject C) (scalarConeMap C r) 1 0).hom =
        LinearMap.ker (coneQuotientAugmentation π r)
      erw [ChainComplex.of_d (scalarConeObject C) (scalarConeMap C r) 0]
      exact coneQuotientAugmentation_exact (C.d 1 0).hom π r hπ hzero
    have he' : ∀ n, LinearMap.range (C'.d (n + 2) (n + 1)).hom =
        LinearMap.ker (C'.d (n + 1) n).hom :=
      scalarCone_positive_exact C π r hzero hexact hr
    obtain ⟨ε, hε, hzε, heε⟩ := ih C' π' hπ' hz' he' htail
    let e := Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner Q r rs
    refine ⟨e.symm.toLinearMap.comp ε, e.symm.surjective.comp hε, ?_, heε⟩
    calc
      _ = LinearMap.ker ε := hzε
      _ = _ := by
        ext x
        change ε x = 0 ↔ e.symm (ε x) = 0
        exact ⟨fun h => by rw [h, map_zero], fun h => e.symm.injective (by simpa using h)⟩

theorem regularSequenceComplex_exact (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) :
    ∃ ε : (regularSequenceComplex rs).X 0 →ₗ[R] (R ⧸ Ideal.ofList rs),
      Function.Surjective ε ∧
      LinearMap.range ((regularSequenceComplex rs).d 1 0).hom = LinearMap.ker ε ∧
      ∀ n, LinearMap.range ((regularSequenceComplex rs).d (n + 2) (n + 1)).hom =
        LinearMap.ker ((regularSequenceComplex rs).d (n + 1) n).hom := by
  have hzero : LinearMap.range (emptyKoszulComplex.d 1 0).hom =
      LinearMap.ker (LinearMap.id : R →ₗ[R] R) := by
    have hd : (emptyKoszulComplex (R := R)).d 1 0 = 0 :=
      ChainComplex.of_d emptyKoszulObject (fun _ => 0) 0
    rw [hd]
    change LinearMap.range (0 : (Fin 0 → R) →ₗ[R] R) =
      LinearMap.ker (LinearMap.id : R →ₗ[R] R)
    exact LinearMap.range_zero.trans LinearMap.ker_id.symm
  have hexact : ∀ n : ℕ,
      LinearMap.range ((emptyKoszulComplex (R := R)).d (n + 2) (n + 1)).hom =
      LinearMap.ker ((emptyKoszulComplex (R := R)).d (n + 1) n).hom := by
    intro n
    let : Subsingleton ((emptyKoszulComplex (R := R)).X (n + 1)) := by
      change Subsingleton (Fin 0 → R)
      infer_instance
    exact Subsingleton.elim _ _
  have h := iterateScalarCones_exact rs emptyKoszulComplex
    (LinearMap.id : R →ₗ[R] R) Function.surjective_id hzero hexact hreg
  have hI : (Ideal.ofList rs • (⊤ : Submodule R R)) = Ideal.ofList rs := by
    change Ideal.ofList rs * ⊤ = Ideal.ofList rs
    exact Ideal.mul_top _
  rw [hI] at h
  exact h

end SiegelZerosAwei.W30

end

end SiegelZeros

end OAI
