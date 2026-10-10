import OAI.RepresentationTheory.RestrictedTilting.Basic

namespace OAI

namespace FiberFunctorProof
section Numerator
variable {R K ι : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]
  [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] [GCDMonoid R] in
lemma coordinateMap_injective : Function.Injective (coordinateMap (R := R) (K := K) (ι := ι)) := by
  intro v w h
  funext i
  exact (FaithfulSMul.algebraMap_injective R K) (congrFun h i)

noncomputable def coordinateEquiv : (ι → R) ≃ₗ[R] coordinateLattice (R := R) (K := K) (ι := ι) :=
  LinearEquiv.ofInjective (coordinateMap (R := R) (K := K) (ι := ι)) coordinateMap_injective

omit [IsDomain R] [GCDMonoid R] in
lemma coordinateEquiv_apply (v : ι → R) :
    (coordinateEquiv (K := K) v).val = coordinateMap v := rfl

variable (x y : R) (hx : x ≠ 0) (hxy : IsRelPrime x y)
  (P : (ι → K) ≃ₗ[K] (ι → K)) (d e : ℕ)
  (hP : ∀ v ∈ coordinateLattice (R := R), (x*y)^d • P v ∈ coordinateLattice (R := R))
  (hQ : ∀ v ∈ coordinateLattice (R := R), (x*y)^e • P.symm v ∈ coordinateLattice (R := R))

 

noncomputable def latticeNumerator : gluedLattice x y P →ₗ[R] (ι → R) :=
  (coordinateEquiv (K := K)).symm.toLinearMap ∘ₗ
    (((x^d) • (gluedLattice x y P).subtype).codRestrict _
      (fun z => gluedLattice_bound x y hx hxy P d hP z.property))

lemma latticeNumerator_coordinates (z : gluedLattice x y P) :
    coordinateMap (latticeNumerator x y hx hxy P d hP z) = x^d • z.val := by
  change (coordinateEquiv (K := K)
    ((coordinateEquiv (K := K)).symm _)).val = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

include hQ in
omit [IsDomain R] [GCDMonoid R] [IsFractionRing R K] in
lemma latticeDenominator_mem (v : ι → R) :
    x^e • coordinateMap (K := K) v ∈ gluedLattice x y P := by
  have hv : coordinateMap (K := K) v ∈ coordinateLattice (R := R) := ⟨v,rfl⟩
  constructor
  · exact ⟨0, by simpa using (coordinateLattice (R := R)).smul_mem (x^e) hv⟩
  · refine ⟨x^e • P.symm (coordinateMap v), ⟨e, ?_⟩, ?_⟩
    · simpa only [mul_pow, mul_smul, smul_comm (y^e)] using hQ _ hv
    · change P (x^e • P.symm (coordinateMap v)) = _
      rw [linearEquiv_map_base_smul, LinearEquiv.apply_symm_apply]

noncomputable def latticeDenominator : (ι → R) →ₗ[R] gluedLattice x y P :=
  ((x^e) • coordinateMap (R := R) (K := K)).codRestrict _
    (latticeDenominator_mem x y P e hQ)

lemma latticeNumerator_denominator (v : ι → R) :
    latticeNumerator x y hx hxy P d hP (latticeDenominator x y P e hQ v) =
      x^(d+e) • v := by
  apply coordinateMap_injective (K := K)
  rw [latticeNumerator_coordinates, map_smul]
  change x^d • (x^e • coordinateMap v) = _
  rw [← mul_smul, ← pow_add]

lemma latticeDenominator_numerator (z : gluedLattice x y P) :
    latticeDenominator x y P e hQ (latticeNumerator x y hx hxy P d hP z) =
      x^(d+e) • z := by
  apply Subtype.ext
  change x^e • coordinateMap (latticeNumerator x y hx hxy P d hP z) = x^(d+e) • z.val
  rw [latticeNumerator_coordinates, ← mul_smul, ← pow_add, Nat.add_comm]

end Numerator
end FiberFunctorProof

end OAI
