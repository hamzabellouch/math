import OAI.Algebra.Determinantal.FiberDimension

namespace OAI

namespace PermanentBorder.NormalizationMonogenic
open Polynomial

section Nilpotent
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

lemma adjoin_eq_top_of_nilpotent_reduction (u : A) (p : R[X])
    (hp : IsNilpotent (aeval u p))
    (h : ∀ z : A, ∃ q : R[X], ∃ w : A, z = aeval u q + aeval u p * w) :
    Algebra.adjoin R {u} = ⊤ := by
  have hd (n : ℕ) (z : A) :
      ∃ q : R[X], ∃ w : A, z = aeval u q + (aeval u p)^n*w := by
    induction n with
    | zero => exact ⟨0,z,by simp⟩
    | succ n ih =>
      obtain ⟨q,w,hw⟩ := ih
      obtain ⟨r,v,hv⟩ := h w
      refine ⟨q+p^n*r,v,?_⟩
      rw [hw,hv]
      simp only [map_add,map_mul,map_pow,pow_succ]
      ring
  rcases hp with ⟨n,hn⟩
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top]
  intro z
  obtain ⟨q,w,hw⟩ := hd n z
  exact ⟨q,by simpa [hn] using hw.symm⟩

end Nilpotent

section Local
variable {K A : Type*} [Field K] [IsAlgClosed K] [CommRing A]
  [Algebra K A] [Module.Finite K A] [IsLocalRing A]

lemma adjoin_uniformizer_eq_top (u : A)
    (hu : IsLocalRing.maximalIdeal A = Ideal.span {u}) :
    Algebra.adjoin K {u} = ⊤ := by
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  have hj : IsNilpotent (IsLocalRing.maximalIdeal A) := by
    rw [← IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) bot_ne_top]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  have hnil : IsNilpotent u := by
    obtain ⟨n,hn⟩ := hj
    refine ⟨n,?_⟩
    have hh : u^n ∈ (IsLocalRing.maximalIdeal A)^n :=
      Ideal.pow_mem_pow (by rw [hu]; exact Ideal.subset_span (by simp)) n
    simpa [hn] using hh
  apply adjoin_eq_top_of_nilpotent_reduction u X (by simpa using hnil)
  intro z
  have : Module.Finite K (IsLocalRing.ResidueField A) := inferInstance
  obtain ⟨c,hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := K) (K := IsLocalRing.ResidueField A)).2 (IsLocalRing.residue A z)
  have hm : z - algebraMap K A c ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    rw [map_sub, sub_eq_zero]
    rw [IsScalarTower.algebraMap_apply K A (IsLocalRing.ResidueField A)] at hc
    exact hc.symm
  rw [hu,Ideal.mem_span_singleton] at hm
  obtain ⟨w,hw⟩ := hm
  refine ⟨C c,w,?_⟩
  simpa only [aeval_C,aeval_X] using (sub_eq_iff_eq_add.mp hw).trans (add_comm _ _)

end Local

section Nakayama
variable {A : Type*} [CommRing A] [IsNoetherianRing A]

lemma nilradical_eq_span_of_mod_square
    (ρ v a : A) (hρ : Ideal.span {ρ} = nilradical A)
    (ha : a ∈ nilradical A) (hr : ρ - v*a ∈ (nilradical A)^2) :
    nilradical A = Ideal.span {a} := by
  apply le_antisymm
  · apply Submodule.le_of_le_smul_of_le_jacobson_bot
      (IsNoetherian.noetherian (nilradical A)) Ideal.radical_le_jacobson
    nth_rw 1 [← hρ]
    rw [Ideal.span_le]
    intro z hz
    have heq : z = ρ := Set.mem_singleton_iff.mp hz
    subst z
    change ρ ∈ Ideal.span {a} ⊔ nilradical A • nilradical A
    have hr' : ρ - v*a ∈ Ideal.span {a} ⊔ nilradical A • nilradical A := by
      apply Submodule.mem_sup_right
      simpa only [Ideal.smul_eq_mul, pow_two] using hr
    have hvp : v*a ∈ Ideal.span {a} ⊔ nilradical A • nilradical A :=
      Submodule.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    simpa using (Ideal.span {a} ⊔ nilradical A • nilradical A).add_mem hr' hvp
  · exact Ideal.span_le.mpr (by simpa using ha)

end Nakayama

section Global
variable {K A : Type*} [Field K] [IsAlgClosed K] [CommRing A]
  [Algebra K A] [Module.Finite K A] [IsPrincipalIdealRing A]

lemma exists_adjoin_eq_top : ∃ u : A, Algebra.adjoin K {u} = ⊤ := by
  classical
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  have : IsNoetherianRing A := IsNoetherianRing.of_finite K A
  let J := nilradical A
  let ρ := Submodule.IsPrincipal.generator J
  have hJρ : Ideal.span {ρ} = J := Submodule.IsPrincipal.span_singleton_generator J
  have hρ : ρ ∈ J := by rw [← hJρ]; exact Ideal.subset_span (by simp)
  let ι := MaximalSpectrum A
  let : Fintype ι := Fintype.ofFinite _
  let θ : ι → K := fun i => Infinite.natEmbedding K ((Fintype.equivFin ι) i).val
  have hθ : Function.Injective θ := (Infinite.natEmbedding K).injective.comp
    (Fin.val_injective.comp (Fintype.equivFin ι).injective)
  have hcop : Pairwise (fun i j : ι => IsCoprime (i.asIdeal ^ 2) (j.asIdeal ^ 2)) :=
    fun i j hij => (i.isCoprime_of_ne hij).pow
  obtain ⟨u,hu⟩ := Ideal.pi_quotient_surjective hcop
    (fun i => Ideal.Quotient.mk (i.asIdeal ^ 2) (algebraMap K A (θ i) + ρ))
  let p : K[X] := ∏ i : ι, (X - C (θ i))
  have hp0 (i : ι) : p.eval (θ i) = 0 := by
    simp only [p, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  have hp' (i : ι) : p.derivative.eval (θ i) ≠ 0 := by
    simpa only [eval₂_id] using
      (separable_prod_X_sub_C_iff.mpr hθ).eval₂_derivative_ne_zero
        (RingHom.id K) (by simpa only [eval₂_id] using hp0 i)
  have hρi (i : ι) : ρ ∈ i.asIdeal := by
    exact nilradical_le_prime i.asIdeal hρ
  have hut (i : ι) : Ideal.Quotient.mk i.asIdeal u =
      algebraMap K (A ⧸ i.asIdeal) (θ i) := by
    have h := congrArg (Ideal.Quotient.factor (Ideal.pow_le_self (by decide : 2 ≠ 0))) (hu i)
    change Ideal.Quotient.mk i.asIdeal u = Ideal.Quotient.mk i.asIdeal
      (algebraMap K A (θ i) + ρ) at h
    simpa [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (hρi i)] using h
  have hpu (i : ι) : Ideal.Quotient.mk (i.asIdeal ^ 2) (aeval u p) =
      algebraMap K (A ⧸ i.asIdeal ^ 2) (p.derivative.eval (θ i)) *
        Ideal.Quotient.mk (i.asIdeal ^ 2) ρ := by
    have hn : (Ideal.Quotient.mk (i.asIdeal ^ 2) ρ)^2 = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow (hρi i) 2
    change (Ideal.Quotient.mkₐ K (i.asIdeal ^ 2)) (aeval u p) = _
    rw [← aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, hu i, map_add]
    change aeval (algebraMap K _ (θ i) + Ideal.Quotient.mk (i.asIdeal^2) ρ) p = _
    rw [aeval_add_of_sq_eq_zero _ _ _ hn]
    simp only [aeval_algebraMap_apply_eq_algebraMap_eval, hp0, map_zero, zero_add]
  obtain ⟨v,hv⟩ := Ideal.pi_quotient_surjective hcop
    (fun i => algebraMap K (A ⧸ i.asIdeal^2) ((p.derivative.eval (θ i))⁻¹))
  have hr : ρ - v * aeval u p ∈ J^2 := by
    rw [show J^2 = ⨅ i : ι, i.asIdeal^2 from IsArtinianRing.nilradical_pow_eq_iInf A 2]
    simp only [Ideal.mem_iInf]
    intro i
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hv i, hpu,
      ← mul_assoc, ← map_mul, inv_mul_cancel₀ (hp' i), map_one, one_mul, sub_self]
  have hpJ : aeval u p ∈ J := by
    rw [show J = ⨅ i : ι, i.asIdeal from IsArtinianRing.nilradical_eq_iInf A]
    simp only [Ideal.mem_iInf]
    intro i
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change (Ideal.Quotient.mkₐ K i.asIdeal) (aeval u p) = 0
    rw [← aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, hut,
      aeval_algebraMap_apply_eq_algebraMap_eval, hp0, map_zero]
  have hJp : J = Ideal.span {aeval u p} :=
    nilradical_eq_span_of_mod_square ρ v (aeval u p) hJρ hpJ hr
  refine ⟨u, adjoin_eq_top_of_nilpotent_reduction u p ?_ ?_⟩
  · exact mem_nilradical.mp hpJ
  · intro z
    let (i : ι) : Field (A ⧸ i.asIdeal) := Ideal.Quotient.field _
    choose c hc using fun i : ι =>
      (IsAlgClosed.algebraMap_bijective_of_isIntegral
        (k := K) (K := A ⧸ i.asIdeal)).2 (Ideal.Quotient.mk i.asIdeal z)
    let q := Lagrange.interpolate Finset.univ θ c
    have hq (i : ι) : q.eval (θ i) = c i :=
      Lagrange.eval_interpolate_at_node _ hθ.injOn (Finset.mem_univ i)
    have hz : z - aeval u q ∈ J := by
      rw [show J = ⨅ i : ι, i.asIdeal from IsArtinianRing.nilradical_eq_iInf A]
      simp only [Ideal.mem_iInf]
      intro i
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
      change _ = (Ideal.Quotient.mkₐ K i.asIdeal) (aeval u q)
      rw [← aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, hut,
        aeval_algebraMap_apply_eq_algebraMap_eval, hq, hc]
    rw [hJp,Ideal.mem_span_singleton] at hz
    obtain ⟨w,hw⟩ := hz
    exact ⟨q,w,by linear_combination hw⟩

end Global
end PermanentBorder.NormalizationMonogenic

namespace PermanentBorder.NormalizationMonogenic
open Polynomial
section LocalLift
variable {S B : Type*} [CommRing S] [IsLocalRing S] [CommRing B]
  [Algebra S B] [Module.Finite S B]

lemma adjoin_eq_top_of_residue_surjective (u : B)
    (hu : Function.Surjective fun p : S[X] =>
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal S).map (algebraMap S B)) (aeval u p)) :
    Algebra.adjoin S {u} = ⊤ := by
  let A := Algebra.adjoin S {u}
  have him : (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal S).map (algebraMap S B))) ''
      (A : Set B) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨p,hp⟩ := hu z
    refine ⟨aeval u p, ?_, hp⟩
    change aeval u p ∈ Algebra.adjoin S {u}
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨p,rfl⟩
  have hspan := (IsLocalRing.quotient_span_eq_top_iff_span_eq_top (S := B) (A : Set B)).mp
    (by rw [him]; exact Submodule.span_univ)
  apply Subalgebra.toSubmodule_injective
  change A.toSubmodule = ⊤
  change Submodule.span S (A.toSubmodule : Set B) = ⊤ at hspan
  simpa only [Submodule.span_eq] using hspan

lemma exists_adjoin_eq_top_of_residue_principal
    [IsAlgClosed (IsLocalRing.ResidueField S)]
    [IsPrincipalIdealRing (B ⧸ (IsLocalRing.maximalIdeal S).map (algebraMap S B))] :
    ∃ u : B, Algebra.adjoin S {u} = ⊤ := by
  let J := (IsLocalRing.maximalIdeal S).map (algebraMap S B)
  let Q := B ⧸ J
  let K := IsLocalRing.ResidueField S
  let : Algebra K Q := Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map)
  have : IsScalarTower S K Q := IsScalarTower.of_algebraMap_eq fun x => rfl
  have : Module.Finite K Q := Module.Finite.of_restrictScalars_finite S K Q
  obtain ⟨v,hv⟩ := exists_adjoin_eq_top (K := K) (A := Q)
  obtain ⟨u,hu⟩ := Ideal.Quotient.mk_surjective v
  refine ⟨u, adjoin_eq_top_of_residue_surjective u ?_⟩
  intro z
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at hv
  obtain ⟨p,hp⟩ := hv z
  obtain ⟨p',hp'⟩ := Polynomial.map_surjective (IsLocalRing.residue S)
    Ideal.Quotient.mk_surjective p
  refine ⟨p', ?_⟩
  change (Ideal.Quotient.mkₐ S J) (aeval u p') = z
  rw [← aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, hu]
  rw [← hp, ← hp']
  exact (aeval_map_algebraMap K v p').symm

lemma exists_adjoin_eq_top_of_principal [IsPrincipalIdealRing B]
    [IsAlgClosed (IsLocalRing.ResidueField S)] :
    ∃ u : B, Algebra.adjoin S {u} = ⊤ := by
  have : IsPrincipalIdealRing (B ⧸ (IsLocalRing.maximalIdeal S).map (algebraMap S B)) :=
    IsPrincipalIdealRing.of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  exact exists_adjoin_eq_top_of_residue_principal
end LocalLift
end PermanentBorder.NormalizationMonogenic

namespace PermanentBorder.NormalizationDerivation
open Polynomial TensorProduct

section Localization
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [Algebra.FormallyEtale S T]

noncomputable def extendEtale (d : Derivation R S S) : Derivation R T T :=
  ((TensorProduct.AlgebraTensorModule.rid S T T).toLinearMap.comp
    ((d.liftKaehlerDifferential.baseChange T).comp
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap)).compDer
        (KaehlerDifferential.D R T)

@[simp] lemma extendEtale_algebraMap (d : Derivation R S S) (s : S) :
    extendEtale (T := T) d (algebraMap S T s) = algebraMap S T (d s) := by
  simp only [extendEtale, Derivation.coe_comp, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, Derivation.coeFn_coe,
    LinearEquiv.coe_coe, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.baseChange_tmul, Derivation.liftKaehlerDifferential_comp_D,
    TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one]

end Localization

section Polynomial
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

noncomputable def coeffDeriv (d : Derivation R S S) : Derivation R S[X] S[X] :=
  PolynomialModule.equivPolynomialSelf.compDer d.mapCoeffs

@[simp] lemma coeffDeriv_coeff (d : Derivation R S S) (p : S[X]) (i : ℕ) :
    (coeffDeriv d p).coeff i = d (p.coeff i) := rfl

@[simp] lemma coeffDeriv_C (d : Derivation R S S) (s : S) :
    coeffDeriv d (C s) = C (d s) := by
  ext i
  simp only [coeffDeriv_coeff, coeff_C]
  split_ifs <;> simp

@[simp] lemma coeffDeriv_X (d : Derivation R S S) :
    coeffDeriv d (X : S[X]) = 0 := by
  ext i
  simp only [coeffDeriv_coeff, coeff_X, coeff_zero]
  split_ifs <;> simp

noncomputable def hamiltonian (d : Derivation R S S) (p : S[X]) :
    Derivation R S[X] S[X] :=
  p.derivative • coeffDeriv d - (coeffDeriv d p) • (derivative'.restrictScalars R)

lemma hamiltonian_self (d : Derivation R S S) (p : S[X]) : hamiltonian d p p = 0 := by
  simp only [hamiltonian, Derivation.sub_apply, Derivation.smul_apply,
    Derivation.restrictScalars_apply, derivative'_apply, smul_eq_mul]
  ring

@[simp] lemma hamiltonian_C (d : Derivation R S S) (p : S[X]) (s : S) :
    hamiltonian d p (C s) = p.derivative * C (d s) := by
  simp [hamiltonian]

@[simp] lemma hamiltonian_X (d : Derivation R S S) (p : S[X]) :
    hamiltonian d p X = -(coeffDeriv d p) := by
  simp [hamiltonian]

lemma hamiltonian_preserves_equation (d : Derivation R S S) (p q : S[X])
    (hq : p ∣ q) : p ∣ hamiltonian d p q := by
  obtain ⟨q,rfl⟩ := hq
  rw [Derivation.leibniz, hamiltonian_self]
  simp only [smul_eq_mul, mul_zero, add_zero]
  exact dvd_mul_right _ _

end Polynomial

section Monogenic
variable {R S B : Type*} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]

noncomputable def scaledExtension (d : Derivation R S S) (u : B) (p : S[X])
    (hu : Algebra.adjoin S {u} = ⊤)
    (hp : ∀ q : S[X], aeval u q = 0 ↔ p ∣ q) : Derivation R B B :=
  Derivation.liftOfSurjective
    (f := (aeval u).restrictScalars R)
    (by change Function.Surjective (aeval u : S[X] →ₐ[S] B)
        rwa [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval])
    (d := hamiltonian d p)
    (fun q hq => (hp _).mpr (hamiltonian_preserves_equation d p q ((hp q).mp hq)))

lemma scaledExtension_aeval (d : Derivation R S S) (u : B) (p q : S[X])
    (hu : Algebra.adjoin S {u} = ⊤)
    (hp : ∀ q : S[X], aeval u q = 0 ↔ p ∣ q) :
    scaledExtension d u p hu hp (aeval u q) = aeval u (hamiltonian d p q) :=
  by
    unfold scaledExtension
    apply Derivation.liftOfSurjective_apply

@[simp] lemma scaledExtension_algebraMap (d : Derivation R S S) (u : B) (p : S[X])
    (hu : Algebra.adjoin S {u} = ⊤)
    (hp : ∀ q : S[X], aeval u q = 0 ↔ p ∣ q) (s : S) :
    scaledExtension d u p hu hp (algebraMap S B s) =
      aeval u p.derivative * algebraMap S B (d s) := by
  rw [← aeval_C u s, scaledExtension_aeval, hamiltonian_C, map_mul, aeval_C]

@[simp] lemma scaledExtension_generator (d : Derivation R S S) (u : B) (p : S[X])
    (hu : Algebra.adjoin S {u} = ⊤)
    (hp : ∀ q : S[X], aeval u q = 0 ↔ p ∣ q) :
    scaledExtension d u p hu hp u = -aeval u (coeffDeriv d p) := by
  simpa only [aeval_X, hamiltonian_X, map_neg] using
    scaledExtension_aeval d u p X hu hp

end Monogenic
end PermanentBorder.NormalizationDerivation

namespace PermanentBorder.NormalizationDerivation
open Polynomial
section FractionGenerator
variable {S Q L B : Type*} [CommRing S] [IsDomain S] [Field Q] [Field L] [CommRing B]
  [Algebra S Q] [IsFractionRing S Q] [Algebra Q L] [Algebra S L] [IsScalarTower S Q L]
  [Algebra S B] [Algebra B L] [IsScalarTower S B L] [IsIntegralClosure B S L]
  [Algebra.IsAlgebraic Q L]

lemma adjoin_fraction_generator {u : B} (hu : Algebra.adjoin S {u} = ⊤) :
    Algebra.adjoin Q {algebraMap B L u} = ⊤ := by
  have := IsIntegralClosure.isLocalization S Q L B
  let A := Algebra.adjoin Q {algebraMap B L u}
  have hb (b : B) : algebraMap B L b ∈ A := by
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at hu
    obtain ⟨p,rfl⟩ := hu b
    change (IsScalarTower.toAlgHom S B L) (aeval u p) ∈ A
    rw [← aeval_algHom_apply]
    rw [← aeval_map_algebraMap Q]
    change aeval (algebraMap B L u) _ ∈ Algebra.adjoin Q {algebraMap B L u}
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨_,rfl⟩
  apply eq_top_iff.mpr
  intro z _
  obtain ⟨⟨b,a⟩,he⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B (nonZeroDivisors S)) z
  obtain ⟨s,hs,ha⟩ := a.property
  have hs0 : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
  have he' : z * algebraMap S L s = algebraMap B L b := by
    rw [IsScalarTower.algebraMap_apply S B L, ha]
    exact he
  have hq0 : algebraMap S Q s ≠ 0 := by simpa only [map_zero] using (IsFractionRing.injective S Q).ne hs0
  have hz : z = algebraMap Q L ((algebraMap S Q s)⁻¹) * algebraMap B L b := by
    rw [← he', IsScalarTower.algebraMap_apply S Q L]
    rw [mul_comm z, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hq0, map_one, one_mul]
  rw [hz]
  exact A.mul_mem (A.algebraMap_mem _) (hb b)
end FractionGenerator

section Normalization
variable {R S Q L B : Type*} [CommRing R] [CommRing S] [IsDomain S]
  [IsIntegrallyClosed S] [IsLocalRing S] [IsAlgClosed (IsLocalRing.ResidueField S)]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]
  [Field L] [Algebra Q L] [Algebra S L] [IsScalarTower S Q L]
  [FiniteDimensional Q L] [Algebra.IsSeparable Q L]
  [CommRing B] [IsDedekindDomain B] [IsPrincipalIdealRing B]
  [Algebra S B] [Module.Finite S B] [Algebra B L] [IsScalarTower S B L]
  [IsIntegralClosure B S L] [Module.IsTorsionFree S B]
  [Algebra R S] [Algebra R B] [IsScalarTower R S B]

include Q L in

lemma exists_scaled_normalization_derivation (d : Derivation R S S) :
    ∃ (g : B) (D : Derivation R B B),
      differentIdeal S B = Ideal.span {g} ∧
      ∀ s : S, D (algebraMap S B s) = g * algebraMap S B (d s) := by
  obtain ⟨u,hu⟩ := NormalizationMonogenic.exists_adjoin_eq_top_of_principal (S := S) (B := B)
  have hi : IsIntegral S u := IsIntegralClosure.isIntegral S L u
  let p := minpoly S u
  have hp (q : S[X]) : aeval u q = 0 ↔ p ∣ q := minpoly.isIntegrallyClosed_dvd_iff hi q
  refine ⟨aeval u p.derivative, scaledExtension d u p hu hp, ?_, ?_⟩
  · have h := conductor_mul_differentIdeal S Q L u (adjoin_fraction_generator (Q := Q) hu)
    rw [conductor_eq_top_of_adjoin_eq_top hu, Ideal.top_mul] at h
    exact h
  · exact scaledExtension_algebraMap d u p hu hp
end Normalization
end PermanentBorder.NormalizationDerivation

end OAI
