import Mathlib
import OAI.NumberTheory.PrimePackets.FrobeniusOrder
import OAI.NumberTheory.PrimePackets.RayFrobenius

namespace OAI

noncomputable section
open Module
open scoped NumberField Classical BigOperators
namespace PrimeDegreePackets.GaloisIdealCharacter

lemma prod_one_sub_rootsOfUnity (n : ℕ) (hn : 0 < n) (z : ℂ) :
    letI : NeZero n := ⟨hn.ne'⟩
    letI : Fintype (rootsOfUnity n ℂ) := Fintype.ofFinite _
    (∏ ζ : rootsOfUnity n ℂ, (1 - (ζ.val : ℂ) * z)) = 1 - z ^ n := by
  let : NeZero n := ⟨hn.ne'⟩
  let : Fintype (rootsOfUnity n ℂ) := Fintype.ofFinite _
  obtain ⟨a, ha⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ n
  let ζ : rootsOfUnity n ℂ := ha.toRootsOfUnity
  have hcoe : (ζ.val : ℂ) = a := rfl
  let e : Fin n ≃ rootsOfUnity n ℂ := Equiv.ofBijective (fun i => ζ ^ i.val) (by
    constructor
    · intro i j hij
      apply Fin.ext
      apply ha.pow_inj i.isLt j.isLt
      have := congrArg (fun x : rootsOfUnity n ℂ => (x.val : ℂ)) hij
      simpa only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hcoe] using this
    · intro b
      have hb : (b.val : ℂ)^n = 1 := by
        simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
          congrArg Units.val ((mem_rootsOfUnity n b.val).mp b.property)
      obtain ⟨i, hi, hbi⟩ := ha.eq_pow_of_pow_eq_one hb
      refine ⟨⟨i, hi⟩, ?_⟩
      apply Subtype.ext
      apply Units.ext
      simpa only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hcoe] using hbi)
  have hp := congrArg (Polynomial.eval (1 : ℂ))
    (X_pow_sub_C_eq_prod ha hn (rfl : z ^ n = z ^ n))
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, one_pow, Polynomial.eval_prod] at hp
  rw [hp, Finset.prod_range]
  exact (Fintype.prod_equiv e (fun i => 1 - a^i.val * z)
    (fun b => 1 - (b.val : ℂ) * z) (fun i => by
      change 1 - a^i.val * z = 1 - (ζ.val : ℂ)^i.val * z
      rw [hcoe])).symm

lemma prod_comp_surjective_hom {A B : Type*} [CommGroup A] [CommGroup B]
    [Fintype A] [Fintype B] (f : A →* B) (hf : Function.Surjective f) (v : B → ℂ) :
    (∏ a, v (f a)) = (∏ b, v b) ^ Nat.card f.ker := by
  rw [← Fintype.prod_fiberwise' f v, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro b _
  rw [Finset.prod_const, Finset.card_univ]
  congr 1
  exact (Fintype.card_eq_nat_card).trans
    (Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective hf b))

lemma zpowers_subtype_generator {G : Type*} [Group G] (g : G) :
    ∀ x : Subgroup.zpowers g,
      x ∈ Subgroup.zpowers (⟨g, Subgroup.mem_zpowers g⟩ : Subgroup.zpowers g) := by
  intro x
  obtain ⟨m, hm⟩ := x.property
  exact ⟨m, Subtype.ext hm⟩

lemma prod_characters_at_generator {H : Type*} [CommGroup H] [Finite H]
    (g : H) (hg : ∀ x : H, x ∈ Subgroup.zpowers g) (z : ℂ) :
    letI : Fintype (H →* ℂˣ) := Fintype.ofFinite _
    (∏ χ : H →* ℂˣ, (1 - (χ g : ℂ) * z)) = 1 - z ^ Nat.card H := by
  let : Fintype (H →* ℂˣ) := Fintype.ofFinite _
  let : Fintype (rootsOfUnity (Nat.card H) ℂ) := Fintype.ofFinite _
  let e := (IsCyclic.monoidHomMulEquivRootsOfUnityOfGenerator hg ℂˣ).trans
    (rootsOfUnityUnitsMulEquiv ℂ (Nat.card H))
  rw [← prod_one_sub_rootsOfUnity (Nat.card H) Nat.card_pos z]
  apply Fintype.prod_equiv e.toEquiv
  intro χ
  rfl

lemma prod_characters_at_element {G : Type*} [CommGroup G] [Finite G]
    (g : G) (z : ℂ) :
    letI : Fintype (G →* ℂˣ) := Fintype.ofFinite _
    (∏ χ : G →* ℂˣ, (1 - (χ g : ℂ) * z)) =
      (1 - z ^ orderOf g) ^ Nat.card (G ⧸ Subgroup.zpowers g) := by
  let : Fintype (G →* ℂˣ) := Fintype.ofFinite _
  let H := Subgroup.zpowers g
  let : Fintype (H →* ℂˣ) := Fintype.ofFinite _
  let gH : H := ⟨g, Subgroup.mem_zpowers g⟩
  let r := MonoidHom.domRestrictHom H ℂˣ
  change (∏ χ : G →* ℂˣ, (1 - (r χ gH : ℂ) * z)) = _
  rw [prod_comp_surjective_hom r (MonoidHom.domRestrict_surjective (M := ℂ) H)
    (fun χ : H →* ℂˣ => 1 - (χ gH : ℂ) * z)]
  rw [prod_characters_at_generator gH (zpowers_subtype_generator g),
    CommGroup.card_domRestrictHom_ker (M := ℂ), Nat.card_zpowers]

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [IsCyclic (E ≃ₐ[F] E)]
attribute [local instance] IsCyclic.commGroup
local instance artinCharacterFintype : Fintype ((E ≃ₐ[F] E) →* ℂˣ) := Fintype.ofFinite _
local instance artinPrimesOverFintype (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    Fintype (Ideal.primesOver P.asIdeal (𝓞 E)) := Fintype.ofFinite _

 

theorem actual_cyclic_artin_localEuler
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    [Algebra.IsUnramifiedAt (𝓞 F) (primeAbove F E P).val] (s : ℂ) :
    (∏ χ : (E ≃ₐ[F] E) →* ℂˣ,
      (1 - (χ (primeFrobenius F E P) : ℂ) * (Ideal.absNorm P.asIdeal : ℂ)^(-s))⁻¹) =
      ∏ Q : Ideal.primesOver P.asIdeal (𝓞 E),
        (1 - (Ideal.absNorm Q.val : ℂ)^(-s))⁻¹ := by
  let Q₀ := primeAbove F E P
  let : Q₀.val.IsPrime := Q₀.property.1
  let : Q₀.val.IsMaximal := Q₀.property.1.isMaximal (primeAbove_ne_bot F E P)
  let : Q₀.val.LiesOver P.asIdeal := Q₀.property.2
  let g := primeFrobenius F E P
  have ho : orderOf g = Q₀.val.inertiaDeg (𝓞 F) :=
    orderOf_eq_inertiaDeg_of_isArithFrobAt F E P.asIdeal Q₀.val g
      (primeFrobenius_spec F E P)
  have hcp : Nat.card (Ideal.primesOver P.asIdeal (𝓞 E)) * orderOf g = finrank F E := by
    have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      P.asIdeal (𝓞 E) (E ≃ₐ[F] E)
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx P.asIdeal Q₀.val (E ≃ₐ[F] E),
      Ideal.inertiaDegIn_eq_inertiaDeg P.asIdeal Q₀.val (E ≃ₐ[F] E),
      Ideal.ramificationIdx_eq_one_of_isUnramifiedAt, one_mul,
      IsGalois.card_aut_eq_finrank, ← ho] at h
    exact h
  have hcg : Nat.card ((E ≃ₐ[F] E) ⧸ Subgroup.zpowers g) * orderOf g = finrank F E := by
    rw [← Nat.card_zpowers g, ← Subgroup.card_eq_card_quotient_mul_card_subgroup,
      IsGalois.card_aut_eq_finrank]
  have hc : Nat.card ((E ≃ₐ[F] E) ⧸ Subgroup.zpowers g) =
      Nat.card (Ideal.primesOver P.asIdeal (𝓞 E)) := by
    exact Nat.eq_of_mul_eq_mul_right (orderOf_pos g) (hcg.trans hcp.symm)
  have hnorm (Q : Ideal.primesOver P.asIdeal (𝓞 E)) :
      Ideal.absNorm Q.val = Ideal.absNorm P.asIdeal ^ orderOf g := by
    let : Q.val.IsPrime := Q.property.1
    let : Q.val.LiesOver P.asIdeal := Q.property.2
    let : Q.val.IsMaximal := Q.property.1.isMaximal
      (Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.property)
    rw [← Ideal.absNorm_pow_inertiaDeg P.asIdeal Q.val,
      ← Ideal.inertiaDeg_eq_of_isGaloisGroup P.asIdeal Q₀.val Q.val (E ≃ₐ[F] E), ho]
  have hfactor (Q : Ideal.primesOver P.asIdeal (𝓞 E)) :
      (Ideal.absNorm Q.val : ℂ)^(-s) = ((Ideal.absNorm P.asIdeal : ℂ)^(-s))^orderOf g := by
    rw [hnorm Q, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
  rw [Finset.prod_inv_distrib, prod_characters_at_element]
  simp_rw [hfactor]
  rw [Finset.prod_const, Finset.card_univ, inv_pow, hc, Nat.card_eq_fintype_card]

end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI
