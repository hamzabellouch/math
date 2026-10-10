import Mathlib
import OAI.NumberTheory.PrimePackets.ArtinEuler
import OAI.NumberTheory.PrimePackets.FrobeniusCoset

namespace OAI

noncomputable section
open Module
open scoped NumberField Classical BigOperators
namespace PrimeDegreePackets.GaloisIdealCharacter

section FiniteCharacters
variable (H : Type*) [CommGroup H] [Finite H]

def additiveCharEquiv : AddChar (Additive H) ℂ ≃ (H →* ℂˣ) :=
  AddChar.toMonoidHomEquiv.trans <|
    ((MulEquiv.monoidHomCongrLeft (MulEquiv.multiplicativeAdditive (H := H))).toEquiv).trans
      MonoidHom.toHomUnitsMulEquiv.toEquiv

def complexMulBasis : Basis (H →* ℂˣ) ℂ (H → ℂ) :=
  ((AddChar.complexBasis (Additive H)).map
    (LinearEquiv.funCongrLeft ℂ ℂ Additive.ofMul)).reindex (additiveCharEquiv H)

@[simp] lemma complexMulBasis_apply (χ : H →* ℂˣ) (h : H) :
    complexMulBasis H χ h = (χ h : ℂ) := by
  simp [complexMulBasis, additiveCharEquiv]

end FiniteCharacters

lemma det_eq_prod_of_eigenbasis {ι M : Type*} [Fintype ι] [AddCommGroup M]
    [Module ℂ M] (b : Basis ι ℂ M) (T : Module.End ℂ M) (a : ι → ℂ)
    (h : ∀ i, T (b i) = a i • b i) : T.det = ∏ i, a i := by
  rw [← LinearMap.det_toMatrix b]
  have he : LinearMap.toMatrix b b T = Matrix.diagonal a := by
    ext i j
    rw [LinearMap.toMatrix_apply', h j, map_smul]
    by_cases hij : i = j
    · subst j; simp
    · simp [hij]
  rw [he, Matrix.det_diagonal]

section OrbitFunctions
variable (C X : Type*) [CommGroup C] [Finite C] [MulAction C X] [Finite X]
local notation "Ω" => MulAction.orbitRel.Quotient C X
abbrev orbitQuotient (o : Ω) := C ⧸ MulAction.stabilizer C o.out
local notation "H" => orbitQuotient C X
local instance permutationArtinOrbitFintype : Fintype Ω := Fintype.ofFinite _
local instance permutationArtinCharacterFintype (o : Ω) : Fintype (H o →* ℂˣ) :=
  Fintype.ofFinite _

def orbitFunctionEquiv : (X → ℂ) ≃ₗ[ℂ] ((o : Ω) → H o → ℂ) :=
  (LinearEquiv.funCongrLeft ℂ ℂ
    (MulAction.selfEquivSigmaOrbitsQuotientStabilizer C X).symm).trans
    (LinearEquiv.piCurry ℂ (fun (o : Ω) (_ : H o) => ℂ))

omit [Finite C] [Finite X] in
@[simp] lemma orbitFunctionEquiv_apply (f : X → ℂ) (o : Ω) (h : H o) :
    orbitFunctionEquiv C X f o h = f (MulAction.ofQuotientStabilizer C o.out h) := by
  rfl

omit [Finite C] [Finite X] in
lemma orbitFunctionEquiv_translate (g : C) (f : X → ℂ) (o : Ω) (h : H o) :
    orbitFunctionEquiv C X (LinearEquiv.funCongrLeft ℂ ℂ (MulAction.toPerm g) f) o h =
      orbitFunctionEquiv C X f o ((g : H o) * h) := by
  simp only [orbitFunctionEquiv_apply]
  change f (g • MulAction.ofQuotientStabilizer C o.out h) =
    f (MulAction.ofQuotientStabilizer C o.out (g • h))
  rw [MulAction.ofQuotientStabilizer_smul]

def orbitCharacterBasis : Basis ((o : Ω) × (H o →* ℂˣ)) ℂ ((o : Ω) → H o → ℂ) :=
  Pi.basis (fun o => complexMulBasis (H o))

lemma orbitCharacterBasis_eigen (g : C) (j : (o : Ω) × (H o →* ℂˣ)) :
    let e := orbitFunctionEquiv C X
    (e.toLinearMap ∘ₗ (LinearEquiv.funCongrLeft ℂ ℂ (MulAction.toPerm g)).toLinearMap ∘ₗ
      e.symm.toLinearMap) (orbitCharacterBasis C X j) =
        (j.2 (g : H j.1) : ℂ) • orbitCharacterBasis C X j := by
  dsimp only
  ext o h
  change orbitFunctionEquiv C X
      (LinearEquiv.funCongrLeft ℂ ℂ (MulAction.toPerm g)
        ((orbitFunctionEquiv C X).symm (orbitCharacterBasis C X j))) o h = _
  rw [orbitFunctionEquiv_translate, LinearEquiv.apply_symm_apply]
  obtain ⟨a, χ⟩ := j
  by_cases hao : a = o
  · subst o
    simp [orbitCharacterBasis, Pi.basis_apply, map_mul]
  · simp [orbitCharacterBasis, Pi.basis_apply, hao]

omit [Finite C] [Finite X] in
lemma generator_quotient (g : C) (hg : ∀ c : C, c ∈ Subgroup.zpowers g)
    (o : Ω) : ∀ h : H o, h ∈ Subgroup.zpowers (g : H o) := by
  intro h
  induction h using Quotient.inductionOn
  rename_i c
  obtain ⟨m, hm⟩ := hg c
  exact ⟨m, by simpa using congrArg (QuotientGroup.mk' (MulAction.stabilizer C o.out)) hm⟩

lemma det_translate (g : C) (hg : ∀ c : C, c ∈ Subgroup.zpowers g) (z : ℂ) :
    (LinearMap.id - z • (LinearEquiv.funCongrLeft ℂ ℂ
      (MulAction.toPerm (β := X) g)).toLinearMap).det =
      ∏ o : Ω, (1 - z ^ Nat.card o.orbit) := by
  let e := orbitFunctionEquiv C X
  let T : Module.End ℂ (X → ℂ) := LinearMap.id - z •
    (LinearEquiv.funCongrLeft ℂ ℂ (MulAction.toPerm g)).toLinearMap
  rw [← LinearMap.det_conj T e]
  rw [det_eq_prod_of_eigenbasis (orbitCharacterBasis C X) _
    (fun j => 1 - (j.2 (g : H j.1) : ℂ) * z)]
  · rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro o _
    rw [prod_characters_at_generator _ (generator_quotient C X g hg o)]
    congr 2
    exact (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer C o.out)).symm.trans
      (Nat.card_congr (Set.equivOfEq (MulAction.orbitRel.Quotient.orbit_eq_orbit_out
        o Quotient.out_eq')).symm)
  · intro j
    have h := orbitCharacterBasis_eigen C X g j
    change (e.toLinearMap ∘ₗ _ ∘ₗ e.symm.toLinearMap) _ = _ at h
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.smul_apply, map_sub, map_smul, LinearEquiv.apply_symm_apply, T, LinearEquiv.coe_coe]
    rw [show e ((LinearEquiv.funCongrLeft ℂ ℂ (MulAction.toPerm g))
        (e.symm (orbitCharacterBasis C X j))) = _ from h]
    simp only [smul_smul, sub_smul, one_smul, mul_comm]

end OrbitFunctions

 

theorem actual_nonnormal_artin_localEuler
    (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (L : IntermediateField F E) (P : Ideal (𝓞 F)) (hP : P ≠ ⊥)
    (Q : Ideal (𝓞 E)) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
    [Algebra.IsUnramifiedAt (𝓞 F) Q]
    (g : E ≃ₐ[F] E) (hg : IsArithFrobAt (𝓞 F) g Q) (s : ℂ) :
    letI : Fintype (Ideal.primesOver P (𝓞 L)) := Fintype.ofFinite _
    (LinearMap.det (LinearMap.id - (Ideal.absNorm P : ℂ)^(-s) •
      (LinearEquiv.funCongrLeft ℂ ℂ
        (MulAction.toPerm (β := (E ≃ₐ[F] E) ⧸ L.fixingSubgroup) g⁻¹)).toLinearMap))⁻¹ =
      ∏ R : Ideal.primesOver P (𝓞 L), (1 - (Ideal.absNorm R.val : ℂ)^(-s))⁻¹ := by
  let : Fintype (Ideal.primesOver P (𝓞 L)) := Fintype.ofFinite _
  let C := Subgroup.zpowers g
  let X := (E ≃ₐ[F] E) ⧸ L.fixingSubgroup
  let c : C := ⟨g, Subgroup.mem_zpowers g⟩
  let : CommGroup C := IsCyclic.commGroup
  let : Fintype (MulAction.orbitRel.Quotient C X) := Fintype.ofFinite _
  have hgen : ∀ x : C, x ∈ Subgroup.zpowers c⁻¹ := by
    simpa only [Subgroup.zpowers_inv] using (zpowers_subtype_generator g)
  have hdet := det_translate C X c⁻¹ hgen ((Ideal.absNorm P : ℂ)^(-s))
  change (LinearMap.det (LinearMap.id - (Ideal.absNorm P : ℂ)^(-s) •
    (LinearEquiv.funCongrLeft ℂ ℂ (MulAction.toPerm (β := X) c⁻¹)).toLinearMap))⁻¹ = _
  rw [hdet, ← Finset.prod_inv_distrib]
  obtain ⟨e, he⟩ := actual_frobenius_coset_cycle_lengths F E L P hP Q g hg
  apply Fintype.prod_equiv e
  intro o
  rw [he o]
  have hnorm : Ideal.absNorm (e o).val =
      Ideal.absNorm P ^ (e o).val.inertiaDeg (𝓞 F) := by
    let R := e o
    let : R.val.IsPrime := R.property.1
    let : R.val.LiesOver P := R.property.2
    let : R.val.IsMaximal := R.property.1.isMaximal
      (Ideal.ne_bot_of_mem_primesOver hP R.property)
    exact (Ideal.absNorm_pow_inertiaDeg P R.val).symm
  rw [hnorm, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI
