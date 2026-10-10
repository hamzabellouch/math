import Mathlib
import OAI.NumberTheory.PrimePackets.FrobeniusTower
import OAI.NumberTheory.PrimePackets.PermutationArtin

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Module
namespace PrimeDegreePackets.ArtinInduction

def unitCharacterRep {H : Type*} [Monoid H] (χ : H →* ℂˣ) : Representation ℂ H ℂ where
  toFun h := (χ h : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' h k := by ext; simp [mul_comm]

section Cosets
variable {G : Type*} [Group G] (H : Subgroup G) (χ : H →* ℂˣ)

def cosetRemainder (a : G) : H := ⟨a * (QuotientGroup.mk (a⁻¹) : G ⧸ H).out, by
  have he := (Quotient.out_eq' (QuotientGroup.mk (a⁻¹) : G ⧸ H))
  have hm := QuotientGroup.eq.mp he.symm
  simpa using hm⟩

lemma cosetRemainder_mul (h : H) (a : G) :
    cosetRemainder H (h * a) = h * cosetRemainder H a := by
  have hq : (QuotientGroup.mk ((h * a)⁻¹) : G ⧸ H) = QuotientGroup.mk a⁻¹ := by
    apply QuotientGroup.eq.mpr
    simp
  apply Subtype.ext
  simp only [cosetRemainder, hq, Subgroup.coe_mul, mul_assoc]

def coindCosetEquiv :
    Representation.coindV H.subtype (unitCharacterRep χ) ≃ₗ[ℂ] (G ⧸ H → ℂ) where
  toFun f q := f.val q.out⁻¹
  invFun f := ⟨(fun a => (χ (cosetRemainder H a) : ℂ) * f (QuotientGroup.mk a⁻¹)), by
    intro h a
    change (χ (cosetRemainder H (h * a)) : ℂ) * f (QuotientGroup.mk ((h * a)⁻¹)) =
      (χ h : ℂ) * ((χ (cosetRemainder H a) : ℂ) * f (QuotientGroup.mk a⁻¹))
    have hq : (QuotientGroup.mk ((h * a)⁻¹) : G ⧸ H) = QuotientGroup.mk a⁻¹ := by
      apply QuotientGroup.eq.mpr
      simp
    simp only [cosetRemainder_mul, map_mul, Units.val_mul, hq, mul_assoc]⟩
  left_inv f := by
    apply Subtype.ext
    funext a
    have he := f.property (cosetRemainder H a)
      ((QuotientGroup.mk a⁻¹ : G ⧸ H).out⁻¹)
    change f.val ((a * _) * _) = (χ (cosetRemainder H a) : ℂ) * _ at he
    simpa only [mul_inv_cancel_right, LinearMap.id_apply] using he.symm
  right_inv f := by
    funext q
    have hq : (QuotientGroup.mk (q.out⁻¹)⁻¹ : G ⧸ H) = q := by
      simp
    simp only [hq]
    have hr : cosetRemainder H q.out⁻¹ = 1 := by
      apply Subtype.ext
      simp only [cosetRemainder, inv_inv, Quotient.out_eq', inv_mul_cancel, Subgroup.coe_one]
    simp only [hr, map_one, Units.val_one, one_mul]
  map_add' f g := by rfl
  map_smul' r f := by rfl

lemma coindCosetEquiv_apply (f : Representation.coindV H.subtype (unitCharacterRep χ))
    (q : G ⧸ H) : coindCosetEquiv H χ f q = f.val q.out⁻¹ := rfl

lemma coindCosetEquiv_symm_apply (f : G ⧸ H → ℂ) (a : G) :
    ((coindCosetEquiv H χ).symm f).val a =
      (χ (cosetRemainder H a) : ℂ) * f (QuotientGroup.mk a⁻¹) := rfl

def cosetMonomialRep : Representation ℂ G (G ⧸ H → ℂ) :=
  (coindCosetEquiv H χ).conjRingEquiv.toMonoidHom.comp
    (Representation.coind H.subtype (unitCharacterRep χ))

def cosetWeight (g : G) (q : G ⧸ H) : ℂˣ :=
  χ (cosetRemainder H (q.out⁻¹ * g))

lemma cosetMonomialRep_apply (g : G) (f : G ⧸ H → ℂ) (q : G ⧸ H) :
    cosetMonomialRep H χ g f q = (cosetWeight H χ g q : ℂ) * f (g⁻¹ • q) := by
  change (χ (cosetRemainder H (q.out⁻¹ * g)) : ℂ) *
    f (QuotientGroup.mk ((q.out⁻¹ * g)⁻¹)) = _
  congr 2
  rw [mul_inv_rev, inv_inv]
  change g⁻¹ • (QuotientGroup.mk q.out : G ⧸ H) = g⁻¹ • q
  exact congrArg (fun a => g⁻¹ • a) (Quotient.out_eq' q)

end Cosets
end PrimeDegreePackets.ArtinInduction
end

noncomputable section
open scoped Classical BigOperators
open Module
namespace PrimeDegreePackets.ArtinInduction
namespace Spectral
variable {C X : Type*} [CommGroup C] [Fintype C] [Fintype X] [MulAction C X]
variable (ρ : Representation ℂ C (X → ℂ)) (w : C → X → ℂˣ)
variable (hw : ∀ c f x, ρ c f x = (w c x : ℂ) * f (c⁻¹ • x))

def stabilizerWeight (x : X) : MulAction.stabilizer C x →* ℂˣ where
  toFun d := w d.val x
  map_one' := by
    apply Units.ext
    have he := congrArg (fun (T : Module.End ℂ (X → ℂ)) => T (fun _ => 1) x) ρ.map_one
    simpa only [hw, mul_one, Module.End.one_apply, Subgroup.coe_one, Units.val_one] using he
  map_mul' a b := by
    apply Units.ext
    have he := congrArg (fun (T : Module.End ℂ (X → ℂ)) => T (fun _ => 1) x)
      (ρ.map_mul a.val b.val)
    simp only [hw, mul_one, Module.End.mul_apply] at he
    have ha : a.val⁻¹ • x = x := a⁻¹ |>.property
    simpa only [hw, ha, mul_one, Subgroup.coe_mul, Units.val_mul] using he

def project (ψ : C →* ℂˣ) (v : X → ℂ) : X → ℂ :=
  ∑ c : C, (ψ c : ℂ)⁻¹ • ρ c v

omit [Fintype X] [MulAction C X] in
lemma project_eigen (ψ : C →* ℂˣ) (v : X → ℂ) (g : C) :
    ρ g (project ρ ψ v) = (ψ g : ℂ) • project ρ ψ v := by
  simp only [project, map_sum, map_smul, Finset.smul_sum, smul_smul]
  simp only [← Module.End.mul_apply, ← map_mul]
  apply Fintype.sum_equiv (Equiv.mulLeft g)
  intro c
  change (ψ c : ℂ)⁻¹ • ρ (g * c) v =
    ((ψ g : ℂ) * (ψ (g * c) : ℂ)⁻¹) • ρ (g * c) v
  simp only [map_mul, Units.val_mul, mul_inv_rev]
  congr 1
  field_simp

omit [Fintype X] in
lemma project_single_at (x : X) (ψ : C →* ℂˣ)
    (hψ : ψ.comp (MulAction.stabilizer C x).subtype = stabilizerWeight ρ w hw x) :
    project ρ ψ ((Pi.single x (1 : ℂ) : X → ℂ)) x = (Nat.card (MulAction.stabilizer C x) : ℂ) := by
  simp only [project, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hw]
  have he (c : C) : (ψ c : ℂ)⁻¹ * ((w c x : ℂ) * (Pi.single x (1 : ℂ) : X → ℂ) (c⁻¹ • x)) =
      if c ∈ MulAction.stabilizer C x then 1 else 0 := by
    by_cases hc : c ∈ MulAction.stabilizer C x
    · have hi : c⁻¹ • x = x := (MulAction.stabilizer C x).inv_mem hc
      have hv : ψ c = w c x := congrArg (fun f : MulAction.stabilizer C x →* ℂˣ => f ⟨c,hc⟩) hψ
      simp only [hc, ite_true, hi, Pi.single_eq_same, mul_one, hv]
      exact inv_mul_cancel₀ (Units.ne_zero _)
    · have hi : c⁻¹ • x ≠ x := by
        intro hi
        apply hc
        simpa only [inv_inv] using (MulAction.stabilizer C x).inv_mem hi
      simp only [hc, ite_false, Pi.single_eq_of_ne hi, mul_zero]
  simp_rw [he]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

omit [Fintype X] in
lemma project_single_ne_zero (x : X) (ψ : C →* ℂˣ)
    (hψ : ψ.comp (MulAction.stabilizer C x).subtype = stabilizerWeight ρ w hw x) :
    project ρ ψ ((Pi.single x (1 : ℂ) : X → ℂ)) ≠ 0 := by
  intro he
  have hz := congrFun he x
  rw [project_single_at ρ w hw x ψ hψ] at hz
  exact (Nat.cast_ne_zero.mpr (Nat.card_pos.ne') : (Nat.card (MulAction.stabilizer C x) : ℂ) ≠ 0) hz

lemma character_eval_generator_injective {A : Type*} [Group A]
    (a : A) (ha : ∀ b : A, b ∈ Subgroup.zpowers a) :
    Function.Injective (fun ψ : A →* ℂˣ => (ψ a : ℂ)) := by
  intro ψ φ he
  have he' : ψ a = φ a := Units.ext he
  apply MonoidHom.ext
  intro b
  obtain ⟨m, rfl⟩ := ha b
  simp only [map_zpow, he']

omit [Fintype C] in
lemma quotient_generator (D : Subgroup C) (g : C)
    (hg : ∀ c : C, c ∈ Subgroup.zpowers g) :
    ∀ q : C ⧸ D, q ∈ Subgroup.zpowers (QuotientGroup.mk g) := by
  intro q
  induction q using Quotient.inductionOn
  rename_i c
  obtain ⟨m, rfl⟩ := hg c
  exact ⟨m, by simp only [QuotientGroup.mk_zpow]⟩

include hw in
lemma exists_transitive_eigenbasis [MulAction.IsPretransitive C X]
    (x : X) (g : C) (hg : ∀ c : C, c ∈ Subgroup.zpowers g) :
    ∃ ψ : C →* ℂˣ,
      ψ.comp (MulAction.stabilizer C x).subtype = stabilizerWeight ρ w hw x ∧
      ∃ b : Basis (C ⧸ MulAction.stabilizer C x →* ℂˣ) ℂ (X → ℂ),
        ∀ η, ρ g (b η) =
          ((ψ g : ℂ) * (η (QuotientGroup.mk g) : ℂ)) • b η := by
  let D := MulAction.stabilizer C x
  let : Fintype (C ⧸ D →* ℂˣ) := Fintype.ofFinite _
  obtain ⟨ψ, hψ⟩ := MonoidHom.domRestrict_surjective (M := ℂ) D
    (stabilizerWeight ρ w hw x)
  let ψ' (η : C ⧸ D →* ℂˣ) : C →* ℂˣ := ψ * η.comp (QuotientGroup.mk' D)
  have hψ' (η : C ⧸ D →* ℂˣ) :
      (ψ' η).comp D.subtype = stabilizerWeight ρ w hw x := by
    apply MonoidHom.ext
    intro d
    have hd : ψ d.val = w d.val x := congrArg
      (fun f : D →* ℂˣ => f d) hψ
    simp only [ψ', MonoidHom.comp_apply, MonoidHom.mul_apply]
    change ψ d.val * η (QuotientGroup.mk d.val) = w d.val x
    rw [(QuotientGroup.eq_one_iff d.val).mpr d.property, map_one, mul_one]
    exact hd
  let μ (η : C ⧸ D →* ℂˣ) : ℂ := (ψ' η g : ℂ)
  have hμ : Function.Injective μ := by
    intro η ζ he
    apply character_eval_generator_injective (QuotientGroup.mk g)
      (quotient_generator D g hg)
    change (ψ g : ℂ) * (η (QuotientGroup.mk g) : ℂ) =
      (ψ g : ℂ) * (ζ (QuotientGroup.mk g) : ℂ) at he
    exact mul_left_cancel₀ (Units.ne_zero _) he
  let v (η : C ⧸ D →* ℂˣ) := project ρ (ψ' η) ((Pi.single x (1 : ℂ) : X → ℂ))
  have hv (η : C ⧸ D →* ℂˣ) : Module.End.HasEigenvector (ρ g) (μ η) (v η) := by
    refine ⟨?_, project_single_ne_zero ρ w hw x (ψ' η) (hψ' η)⟩
    exact (Module.End.mem_eigenspace_iff.mpr (project_eigen ρ (ψ' η) ((Pi.single x (1 : ℂ) : X → ℂ)) g))
  have hli : LinearIndependent ℂ v := Module.End.eigenvectors_linearIndependent' (ρ g) μ hμ v hv
  have hDX : Nat.card (C ⧸ D) = Nat.card X := by
    rw [← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer C x)]
    rw [MulAction.orbit_eq_univ C x]
    exact Nat.card_congr (Equiv.Set.univ X)
  have hcard : Fintype.card (C ⧸ D →* ℂˣ) = finrank ℂ (X → ℂ) := by
    rw [← Module.finrank_eq_card_basis (GaloisIdealCharacter.complexMulBasis (C ⧸ D)),
      Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hDX
  let b := basisOfLinearIndependentOfCardEqFinrank' v hli hcard
  refine ⟨ψ, hψ, b, ?_⟩
  intro η
  simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank']
  exact Module.End.mem_eigenspace_iff.mp (hv η).1

include hw in
lemma transitive_det [MulAction.IsPretransitive C X]
    (x : X) (g : C) (hg : ∀ c : C, c ∈ Subgroup.zpowers g) (z : ℂ) :
    (LinearMap.id - z • ρ g).det =
      1 - (w (g ^ Nat.card X) x : ℂ) * z ^ Nat.card X := by
  let D := MulAction.stabilizer C x
  let : Fintype (C ⧸ D →* ℂˣ) := Fintype.ofFinite _
  obtain ⟨ψ, hψ⟩ := MonoidHom.domRestrict_surjective (M := ℂ) D
    (stabilizerWeight ρ w hw x)
  let ψ' (η : C ⧸ D →* ℂˣ) : C →* ℂˣ := ψ * η.comp (QuotientGroup.mk' D)
  have hψ' (η : C ⧸ D →* ℂˣ) :
      (ψ' η).comp D.subtype = stabilizerWeight ρ w hw x := by
    apply MonoidHom.ext
    intro d
    have hd : ψ d.val = w d.val x := congrArg
      (fun f : D →* ℂˣ => f d) hψ
    simp only [ψ', MonoidHom.comp_apply, MonoidHom.mul_apply]
    change ψ d.val * η (QuotientGroup.mk d.val) = w d.val x
    rw [(QuotientGroup.eq_one_iff d.val).mpr d.property, map_one, mul_one]
    exact hd
  let μ (η : C ⧸ D →* ℂˣ) : ℂ := (ψ' η g : ℂ)
  have hμ : Function.Injective μ := by
    intro η ζ he
    apply character_eval_generator_injective (QuotientGroup.mk g)
      (quotient_generator D g hg)
    change (ψ g : ℂ) * (η (QuotientGroup.mk g) : ℂ) =
      (ψ g : ℂ) * (ζ (QuotientGroup.mk g) : ℂ) at he
    exact mul_left_cancel₀ (Units.ne_zero _) he
  let v (η : C ⧸ D →* ℂˣ) := project ρ (ψ' η) ((Pi.single x (1 : ℂ) : X → ℂ))
  have hv (η : C ⧸ D →* ℂˣ) : Module.End.HasEigenvector (ρ g) (μ η) (v η) := by
    refine ⟨?_, project_single_ne_zero ρ w hw x (ψ' η) (hψ' η)⟩
    exact (Module.End.mem_eigenspace_iff.mpr (project_eigen ρ (ψ' η) ((Pi.single x (1 : ℂ) : X → ℂ)) g))
  have hli : LinearIndependent ℂ v := Module.End.eigenvectors_linearIndependent' (ρ g) μ hμ v hv
  have hDX : Nat.card (C ⧸ D) = Nat.card X := by
    rw [← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer C x)]
    rw [MulAction.orbit_eq_univ C x]
    exact Nat.card_congr (Equiv.Set.univ X)
  have hcard : Fintype.card (C ⧸ D →* ℂˣ) = finrank ℂ (X → ℂ) := by
    rw [← Module.finrank_eq_card_basis (GaloisIdealCharacter.complexMulBasis (C ⧸ D)),
      Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hDX
  let b := basisOfLinearIndependentOfCardEqFinrank' v hli hcard
  rw [GaloisIdealCharacter.det_eq_prod_of_eigenbasis b _ (fun η => 1 - μ η * z)]
  · have he : (∏ η : C ⧸ D →* ℂˣ, (1 - μ η * z)) =
        1 - ((ψ g : ℂ) * z) ^ Nat.card (C ⧸ D) := by
      have ht := GaloisIdealCharacter.prod_characters_at_generator
        (QuotientGroup.mk g : C ⧸ D) (quotient_generator D g hg) ((ψ g : ℂ) * z)
      convert ht using 1
      apply Finset.prod_congr rfl
      intro η _
      change 1 - (ψ g : ℂ) * (η (QuotientGroup.mk g) : ℂ) * z = _
      ring
    rw [he, hDX, mul_pow]
    congr 2
    have hm : g ^ Nat.card X ∈ D := by
      rw [← hDX]
      exact D.pow_index_mem g
    have hh := congrArg (fun f : D →* ℂˣ => f ⟨g ^ Nat.card X, hm⟩) hψ
    change ψ (g ^ Nat.card X) = w (g ^ Nat.card X) x at hh
    simpa only [map_pow, Units.val_pow_eq_pow_val] using congrArg Units.val hh
  · intro η
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank']
    change ((LinearMap.id - z • ρ g) : Module.End ℂ (X → ℂ)) (v η) = _
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      Module.End.mem_eigenspace_iff.mp (hv η).1, smul_smul, sub_smul, one_smul, mul_comm]

include hw in
omit [Fintype C] [Fintype X] in
lemma weight_one (x : X) : w 1 x = 1 := by
  apply Units.ext
  have he := congrArg (fun (T : Module.End ℂ (X → ℂ)) => T (fun _ => 1) x) ρ.map_one
  simpa only [hw, mul_one, Module.End.one_apply, Units.val_one] using he

include hw in
omit [Fintype C] [Fintype X] in
lemma weight_mul (a b : C) (x : X) : w (a*b) x = w a x * w b (a⁻¹ • x) := by
  apply Units.ext
  have he := congrArg (fun (T : Module.End ℂ (X → ℂ)) => T (fun _ => 1) x) (ρ.map_mul a b)
  simpa only [Module.End.mul_apply, hw, mul_one, Units.val_mul] using he

local notation "Ω" => MulAction.orbitRel.Quotient C X
local instance : Fintype Ω := Fintype.ofFinite _
local instance (o : Ω) : Fintype o.orbit := Fintype.ofFinite _

def orbitRep (o : Ω) : Representation ℂ C (o.orbit → ℂ) where
  toFun c :=
    { toFun := fun f x => (w c x.val : ℂ) * f (c⁻¹ • x)
      map_add' := by intro f g; ext x; simp [mul_add]
      map_smul' := by intro a f; ext x; simp [mul_left_comm] }
  map_one' := by
    apply LinearMap.ext
    intro f
    funext x
    change (w 1 x.val : ℂ) * f (1⁻¹ • x) = f x
    simp [weight_one ρ w hw]
  map_mul' a b := by
    apply LinearMap.ext
    intro f
    funext x
    change (w (a*b) x.val : ℂ) * f ((a*b)⁻¹ • x) =
      (w a x.val : ℂ) * ((w b (a⁻¹ • x).val : ℂ) * f (b⁻¹ • (a⁻¹ • x)))
    simp only [weight_mul ρ w hw, Units.val_mul, mul_inv_rev,
      mul_smul, MulAction.orbitRel.Quotient.orbit.coe_smul]
    simp only [mul_assoc]

omit [Fintype C] [Fintype X] in
lemma orbitRep_apply (o : Ω) (c : C) (f : o.orbit → ℂ) (x : o.orbit) :
    orbitRep ρ w hw o c f x = (w c x.val : ℂ) * f (c⁻¹ • x) := rfl

def orbitFunctionEquiv : (X → ℂ) ≃ₗ[ℂ] ((o : Ω) → o.orbit → ℂ) :=
  (LinearEquiv.funCongrLeft ℂ ℂ (MulAction.selfEquivSigmaOrbits' C X).symm).trans
    (LinearEquiv.piCurry ℂ (fun (o : Ω) (_ : o.orbit) => ℂ))

omit [Fintype C] [Fintype X] in
lemma orbitFunctionEquiv_apply (f : X → ℂ) (o : Ω) (x : o.orbit) :
    orbitFunctionEquiv (C := C) (X := X) f o x = f x.val := rfl

include hw in
omit [Fintype C] [Fintype X] in
lemma orbitFunctionEquiv_intertwine (c : C) (f : X → ℂ) (o : Ω) :
    orbitFunctionEquiv (C := C) (X := X) (ρ c f) o =
      orbitRep ρ w hw o c (orbitFunctionEquiv (C := C) (X := X) f o) := by
  ext x
  simp only [orbitFunctionEquiv_apply, orbitRep_apply, hw,
    MulAction.orbitRel.Quotient.orbit.coe_smul]

def orbitAnchor (o : Ω) : o.orbit :=
  ⟨o.out, (MulAction.orbitRel.Quotient.mem_orbit).mpr (Quotient.out_eq' o)⟩

include hw in
lemma det_monomial (g : C) (hg : ∀ c : C, c ∈ Subgroup.zpowers g) (z : ℂ) :
    (LinearMap.id - z • ρ g).det =
      ∏ o : Ω, (1 - (w (g ^ Nat.card o.orbit) o.out : ℂ) * z ^ Nat.card o.orbit) := by
  let D (o : Ω) := MulAction.stabilizer C (orbitAnchor (C := C) o)
  let (o : Ω) : Fintype (C ⧸ D o →* ℂˣ) := Fintype.ofFinite _
  have h (o : Ω) := exists_transitive_eigenbasis
    (orbitRep ρ w hw o) (fun c x => w c x.val) (orbitRep_apply ρ w hw o)
    (orbitAnchor (C := C) o) g hg
  choose Ψ hΨ b hb using h
  let e := orbitFunctionEquiv (C := C) (X := X)
  let B := Pi.basis b
  let μ (j : (o : Ω) × (C ⧸ D o →* ℂˣ)) : ℂ :=
    (Ψ j.1 g : ℂ) * (j.2 (QuotientGroup.mk g) : ℂ)
  have heig (j : (o : Ω) × (C ⧸ D o →* ℂˣ)) :
      e (ρ g (e.symm (B j))) = μ j • B j := by
    ext o x
    change orbitFunctionEquiv (C := C) (X := X) (ρ g (e.symm (B j))) o x = _
    rw [orbitFunctionEquiv_intertwine ρ w hw]
    change orbitRep ρ w hw o g (e (e.symm (B j)) o) x = _
    rw [LinearEquiv.apply_symm_apply]
    obtain ⟨a, η⟩ := j
    by_cases hao : a = o
    · subst o
      simp only [B, Pi.basis_apply, Pi.single_eq_same]
      simpa only [μ, Pi.smul_apply, Pi.single_eq_same] using congrFun (hb a η) x
    · simp [B, Pi.basis_apply, hao]
  rw [← LinearMap.det_conj _ e]
  rw [GaloisIdealCharacter.det_eq_prod_of_eigenbasis B _ (fun j => 1 - μ j * z)]
  · rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro o _
    have ht := GaloisIdealCharacter.prod_characters_at_generator
      (QuotientGroup.mk g : C ⧸ D o) (quotient_generator (D o) g hg) ((Ψ o g : ℂ) * z)
    have hprod : (∏ η : C ⧸ D o →* ℂˣ, (1 - μ ⟨o,η⟩ * z)) =
        1 - ((Ψ o g : ℂ) * z) ^ Nat.card (C ⧸ D o) := by
      convert ht using 1
      apply Finset.prod_congr rfl
      intro η _
      change 1 - (Ψ o g : ℂ) * (η (QuotientGroup.mk g) : ℂ) * z = _
      ring
    rw [hprod]
    have hDX : Nat.card (C ⧸ D o) = Nat.card o.orbit := by
      rw [← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer C (orbitAnchor (C := C) o))]
      rw [MulAction.orbit_eq_univ C (orbitAnchor (C := C) o)]
      exact Nat.card_congr (Equiv.Set.univ _)
    rw [hDX, mul_pow]
    congr 2
    have hm : g ^ Nat.card o.orbit ∈ D o := by
      rw [← hDX]
      exact (D o).pow_index_mem g
    have hh := congrArg (fun f : D o →* ℂˣ => f ⟨g ^ Nat.card o.orbit, hm⟩) (hΨ o)
    change Ψ o (g ^ Nat.card o.orbit) = w (g ^ Nat.card o.orbit) o.out at hh
    simpa only [map_pow, Units.val_pow_eq_pow_val] using congrArg Units.val hh
  · intro j
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.smul_apply, map_sub, map_smul, LinearEquiv.apply_symm_apply,
      LinearEquiv.coe_coe]
    rw [heig]
    simp only [smul_smul, sub_smul, one_smul, mul_comm]

end Spectral
end PrimeDegreePackets.ArtinInduction
end

noncomputable section
open Module
open scoped Classical NumberField Pointwise
namespace PrimeDegreePackets.ArtinInduction
open GaloisIdealCharacter
variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

lemma actual_frobenius_coset_primes
    (L : IntermediateField F E) (P : Ideal (𝓞 F)) (hP : P ≠ ⊥)
    (Q : Ideal (𝓞 E)) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
    [Algebra.IsUnramifiedAt (𝓞 F) Q]
    (g : E ≃ₐ[F] E) (hg : IsArithFrobAt (𝓞 F) g Q) :
    ∃ e : MulAction.orbitRel.Quotient (Subgroup.zpowers g)
        ((E ≃ₐ[F] E) ⧸ L.fixingSubgroup) ≃ Ideal.primesOver P (𝓞 L),
      ∀ o, Nat.card o.orbit = (e o).val.inertiaDeg (𝓞 F) ∧
        (e o).val = cosetPrime F E L Q o.out := by
  rw [zpowers_frobenius_eq_stabilizer F E P Q g hg]
  refine ⟨Equiv.ofBijective (primeOfCosetOrbit F E L P Q)
    (primeOfCosetOrbit_bijective F E L P Q), ?_⟩
  intro o
  constructor
  · induction o using Quotient.inductionOn
    rename_i a
    induction a using Quotient.inductionOn
    rename_i a
    exact cosetOrbit_card_eq_inertiaDeg F E L P hP Q a
  · have h := congrArg (fun x => (primeOfCosetOrbit F E L P Q x).val)
      (Quotient.out_eq' o)
    exact h.symm

lemma actual_coset_weight
    (L : IntermediateField F E) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (Q : Ideal (𝓞 E)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    [Algebra.IsUnramifiedAt (𝓞 F) Q]
    (g : E ≃ₐ[F] E) (hg : IsArithFrobAt (𝓞 F) g Q)
    (χ : (E ≃ₐ[L] E) →* ℂˣ)
    (R : Ideal.primesOver P.asIdeal (𝓞 L))
    (q : (E ≃ₐ[F] E) ⧸ L.fixingSubgroup)
    (hR : R.val = cosetPrime F E L Q q) :
    cosetWeight L.fixingSubgroup
      (χ.comp (IntermediateField.fixingSubgroupEquiv L).toMonoidHom)
      (g ^ R.val.inertiaDeg (𝓞 F)) q =
      χ (primeFrobenius L E
        ⟨R.val, R.property.1, Ideal.ne_bot_of_mem_primesOver P.ne_bot R.property⟩) := by
  let a := q.out
  let Q' : Ideal (𝓞 E) := a⁻¹ • Q
  let : Q'.IsPrime := Ideal.IsPrime.smul _
  let : Q'.LiesOver P.asIdeal := Ideal.LiesOver.smul _
  let : Q'.IsMaximal := Ideal.IsPrime.isMaximal inferInstance
    (Ideal.ne_bot_of_liesOver_of_ne_bot P.ne_bot Q')
  let : (Q'.under (𝓞 F)).IsMaximal := by
    rw [← Q'.over_def P.asIdeal]
    infer_instance
  let : Algebra.IsUnramifiedAt (𝓞 F) Q' := by
    apply Ideal.ramificationIdx_eq_one_iff.mp
    change (a⁻¹ • Q).ramificationIdx (𝓞 F) = 1
    rw [Ideal.ramificationIdx_smul, Ideal.ramificationIdx_eq_one_of_isUnramifiedAt]
  let : Algebra.IsUnramifiedAt (𝓞 L) Q' :=
    Algebra.IsUnramifiedAt.of_restrictScalars (𝓞 F) Q'
  have hR' : R.val = Q'.under (𝓞 L) := by
    rw [hR]
    have hq : (QuotientGroup.mk a : (E ≃ₐ[F] E) ⧸ L.fixingSubgroup) = q :=
      Quotient.out_eq' q
    rw [← hq]
    rfl
  have hg' : IsArithFrobAt (𝓞 F) (a⁻¹ * g * a) Q' := by
    simpa only [inv_inv] using hg.conj a⁻¹
  obtain ⟨τ, hτ, hτF⟩ := actual_frobenius_tower F E L P.asIdeal P.ne_bot Q'
    (a⁻¹ * g * a) hg'
  rw [← hR'] at hτ
  have hτ' : τ.restrictScalars F = a⁻¹ * g ^ R.val.inertiaDeg (𝓞 F) * a := by
    rw [hτ]
    simpa only [inv_inv] using (conj_pow (a := a⁻¹) (b := g))
  let τH := (IntermediateField.fixingSubgroupEquiv L).symm τ
  have hv : τH.val = a⁻¹ * g ^ R.val.inertiaDeg (𝓞 F) * a := hτ'
  have hm : a⁻¹ * g ^ R.val.inertiaDeg (𝓞 F) * a ∈ L.fixingSubgroup :=
    hv ▸ τH.property
  have hq : (QuotientGroup.mk ((a⁻¹ * g ^ R.val.inertiaDeg (𝓞 F))⁻¹) :
      (E ≃ₐ[F] E) ⧸ L.fixingSubgroup) = q := by
    calc
      _ = QuotientGroup.mk a := by
        apply QuotientGroup.eq.mpr
        simpa only [inv_inv, mul_assoc] using hm
      _ = q := Quotient.out_eq' q
  have hrem : cosetRemainder L.fixingSubgroup (a⁻¹ * g ^ R.val.inertiaDeg (𝓞 F)) = τH := by
    apply Subtype.ext
    change (a⁻¹ * g ^ R.val.inertiaDeg (𝓞 F)) *
      (QuotientGroup.mk ((a⁻¹ * g ^ R.val.inertiaDeg (𝓞 F))⁻¹) :
        (E ≃ₐ[F] E) ⧸ L.fixingSubgroup).out = τH.val
    rw [hq, hv]
  change χ ((IntermediateField.fixingSubgroupEquiv L)
    (cosetRemainder L.fixingSubgroup (a⁻¹ * g ^ R.val.inertiaDeg (𝓞 F)))) = _
  rw [hrem, (IntermediateField.fixingSubgroupEquiv L).apply_symm_apply]
  symm
  rw [← idealHom_prime L E χ]
  exact idealHom_prime_frobenius L E χ _ Q' hR'.symm τ hτF

end PrimeDegreePackets.ArtinInduction

end

noncomputable section
open Module
open scoped Classical NumberField Pointwise BigOperators
namespace PrimeDegreePackets.ArtinInduction
open GaloisIdealCharacter

theorem actual_monomial_artin_localEuler
    (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (L : IntermediateField F E) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (Q : Ideal (𝓞 E)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    [Algebra.IsUnramifiedAt (𝓞 F) Q]
    (g : E ≃ₐ[F] E) (hg : IsArithFrobAt (𝓞 F) g Q)
    (χ : (E ≃ₐ[L] E) →* ℂˣ) (s : ℂ) :
    letI : Fintype (Ideal.primesOver P.asIdeal (𝓞 L)) := Fintype.ofFinite _
    let ρ := Representation.coind L.fixingSubgroup.subtype
      (unitCharacterRep (χ.comp (IntermediateField.fixingSubgroupEquiv L).toMonoidHom))
    (LinearMap.det (LinearMap.id - (Ideal.absNorm P.asIdeal : ℂ)^(-s) • ρ g))⁻¹ =
      ∏ R : Ideal.primesOver P.asIdeal (𝓞 L),
        (1 - (χ (GaloisIdealCharacter.primeFrobenius L E
          ⟨R.val, R.property.1, Ideal.ne_bot_of_mem_primesOver P.ne_bot R.property⟩) : ℂ) *
          (Ideal.absNorm R.val : ℂ)^(-s))⁻¹ := by
  let : Fintype (Ideal.primesOver P.asIdeal (𝓞 L)) := Fintype.ofFinite _
  let X := (E ≃ₐ[F] E) ⧸ L.fixingSubgroup
  let C := Subgroup.zpowers g
  let c : C := ⟨g, Subgroup.mem_zpowers g⟩
  let : CommGroup C := IsCyclic.commGroup
  let : Fintype C := Fintype.ofFinite _
  let : Fintype X := Fintype.ofFinite _
  let : Fintype (MulAction.orbitRel.Quotient C X) := Fintype.ofFinite _
  let Ψ := χ.comp (IntermediateField.fixingSubgroupEquiv L).toMonoidHom
  let ρ := Representation.coind L.fixingSubgroup.subtype (unitCharacterRep Ψ)
  let r := cosetMonomialRep L.fixingSubgroup Ψ
  let rC := r.comp C.subtype
  let z := (Ideal.absNorm P.asIdeal : ℂ)^(-s)
  have hdet := Spectral.det_monomial rC
    (fun c q => cosetWeight L.fixingSubgroup Ψ c.val q)
    (fun c f q => cosetMonomialRep_apply L.fixingSubgroup Ψ c.val f q)
    c (zpowers_subtype_generator g) z
  have hconj : (LinearMap.id - z • ρ g).det = (LinearMap.id - z • r g).det := by
    let e := coindCosetEquiv L.fixingSubgroup Ψ
    rw [← LinearMap.det_conj _ e]
    congr 1
    apply LinearMap.ext
    intro f
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.smul_apply, map_sub, map_smul, LinearEquiv.apply_symm_apply,
      LinearEquiv.coe_coe]
    rfl
  change (LinearMap.det (LinearMap.id - z • ρ g))⁻¹ = _
  rw [hconj]
  change (LinearMap.det (LinearMap.id - z • rC c))⁻¹ = _
  rw [hdet, ← Finset.prod_inv_distrib]
  obtain ⟨e, he⟩ := actual_frobenius_coset_primes F E L P.asIdeal P.ne_bot Q g hg
  apply Fintype.prod_equiv e
  intro o
  simp only [Subgroup.coe_pow]
  rw [(he o).1]
  rw [actual_coset_weight F E L P Q g hg χ (e o) o.out (he o).2]
  have hnorm : Ideal.absNorm (e o).val =
      Ideal.absNorm P.asIdeal ^ (e o).val.inertiaDeg (𝓞 F) := by
    let R := e o
    let : R.val.IsPrime := R.property.1
    let : R.val.LiesOver P.asIdeal := R.property.2
    let : R.val.IsMaximal := R.property.1.isMaximal
      (Ideal.ne_bot_of_mem_primesOver P.ne_bot R.property)
    exact (Ideal.absNorm_pow_inertiaDeg P.asIdeal R.val).symm
  rw [hnorm, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

end PrimeDegreePackets.ArtinInduction

end

end OAI
