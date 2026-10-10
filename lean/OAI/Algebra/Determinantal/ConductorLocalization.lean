import OAI.Algebra.Determinantal.ConductorBounds

namespace OAI

namespace PermanentBorder.Conductor
open Polynomial Matrix Module
section LocalComparison
variable {K S Q ι : Type*} [Field K] [Infinite K]
  [CommRing S] [IsDomain S] [IsPrincipalIdealRing S] [IsLocalRing S] [Algebra K S]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]
  [Fintype ι] [DecidableEq ι]

include K in

theorem normalization_conductor_le_adjugate (T : Matrix ι ι S)
    (hsep : (T.charpoly.map (algebraMap S Q)).Separable) :
    letI := (normalizationInclusion (Q := Q) T.charpoly T.charpoly_monic).toRingHom.toAlgebra
    algebraConductor (AdjoinRoot T.charpoly)
      (integralClosure S (AdjoinRoot (T.charpoly.map (algebraMap S Q)))) ≤
      matrixEntryIdeal (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly)) := by
  let := (normalizationInclusion (Q := Q) T.charpoly T.charpoly_monic).toRingHom.toAlgebra
  obtain ⟨l, u, hl, hu, hnorm⟩ := exists_normalizing_matrix_generators (K := K) T hsep
  intro a ha
  apply conductor_mem_adjugate_of_lattice T (genericBaseChange (Q := Q) T.charpoly)
    (genericBaseChange_injective (Q := Q) T.charpoly T.charpoly_monic) l hl u hu hnorm a
  intro x hx
  obtain ⟨b, hb⟩ := ha (⟨x, hx⟩ : integralClosure S
    (AdjoinRoot (T.charpoly.map (algebraMap S Q))))
  exact ⟨b, congrArg Subtype.val hb⟩

include K in

theorem normalization_adjugate_length (T : Matrix ι ι S)
    (hsep : (T.charpoly.map (algebraMap S Q)).Separable) :
    let R := integralClosure S (AdjoinRoot (T.charpoly.map (algebraMap S Q)))
    letI := (normalizationInclusion (Q := Q) T.charpoly T.charpoly_monic).toRingHom.toAlgebra
    Module.length S (AdjoinRoot T.charpoly ⧸
      (matrixEntryIdeal (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly))).restrictScalars S) ≤
    Module.length S (AdjoinRoot T.charpoly ⧸
      (algebraConductor (AdjoinRoot T.charpoly) R).restrictScalars S) ∧
    Module.length S (AdjoinRoot T.charpoly ⧸
      (algebraConductor (AdjoinRoot T.charpoly) R).restrictScalars S) =
    Module.length S (R ⧸ LinearMap.range
      (normalizationInclusion (Q := Q) T.charpoly T.charpoly_monic).toLinearMap) := by
  let R := integralClosure S (AdjoinRoot (T.charpoly.map (algebraMap S Q)))
  let := (normalizationInclusion (Q := Q) T.charpoly T.charpoly_monic).toRingHom.toAlgebra
  refine ⟨?_, normalization_conductor_colength T.charpoly_monic hsep⟩
  let c := (algebraConductor (AdjoinRoot T.charpoly) R).restrictScalars S
  let J := (matrixEntryIdeal
    (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly))).restrictScalars S
  have h : c ≤ J := normalization_conductor_le_adjugate (K := K) T hsep
  exact Module.length_le_of_surjective (Submodule.factor h)
    (Submodule.factor_surjective h)
end LocalComparison
end PermanentBorder.Conductor

namespace PermanentBorder.RootLocalization
open Polynomial

section BaseChange
variable {S U : Type*} [CommRing S] [CommRing U] [Algebra S U]
variable (f : S[X]) (g : U[X]) (hfg : f.map (algebraMap S U) = g)

noncomputable def changeRoot : AdjoinRoot f →ₐ[S] AdjoinRoot g :=
  AdjoinRoot.mapAlgHom (Algebra.ofId S U) f g hfg.symm.dvd

@[simp] theorem changeRoot_mk (p : S[X]) :
    changeRoot f g hfg (AdjoinRoot.mk f p) =
      AdjoinRoot.mk g (p.map (algebraMap S U)) := by
  change aeval (AdjoinRoot.root g) p = _
  exact AdjoinRoot.aeval_eq_of_algebra (R := S) (S := U) _ p

@[simp] theorem changeRoot_root :
    changeRoot f g hfg (AdjoinRoot.root f) = AdjoinRoot.root g := by
  simpa only [AdjoinRoot.root, Polynomial.map_X] using changeRoot_mk f g hfg X

theorem changeRoot_injective (hf : f.Monic)
    (hSU : Function.Injective (algebraMap S U)) :
    Function.Injective (changeRoot f g hfg) := by
  subst g
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  rw [changeRoot_mk, AdjoinRoot.mk_eq_zero] at hz
  rw [AdjoinRoot.mk_eq_zero, ← modByMonic_eq_zero_iff_dvd hf]
  apply Polynomial.map_injective (algebraMap S U) hSU
  rw [Polynomial.map_zero, map_modByMonic _ hf,
    (modByMonic_eq_zero_iff_dvd (hf.map _)).mpr hz]

variable (M : Submonoid S) [IsLocalization M U]

theorem changeRoot_denominators (x : AdjoinRoot g) :
    ∃ s : M, ∃ b : AdjoinRoot f, s • x = changeRoot f g hfg b := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨s, hs, hp⟩ := IsLocalization.integerNormalization_spec M p
  refine ⟨⟨s, hs⟩, AdjoinRoot.mk f (IsLocalization.integerNormalization M p), ?_⟩
  rw [changeRoot_mk, hp]
  exact (map_smul (((AdjoinRoot.mkₐ g).restrictScalars S).toLinearMap) s p).symm

theorem changeRoot_isLocalizedModule (hf : f.Monic) (hM : M ≤ nonZeroDivisors S) :
    IsLocalizedModule M (changeRoot f g hfg).toLinearMap where
  map_units s := by
    have h := (IsLocalization.map_units U s).map (Algebra.lsmul S S (AdjoinRoot g)).toRingHom
    convert h using 1
    ext z
    change (s : S) • z = (algebraMap S U (s : S)) • z
    exact (algebraMap_smul U (s : S) z).symm
  surj x := by
    obtain ⟨s, b, hb⟩ := changeRoot_denominators f g hfg M x
    exact ⟨⟨b,s⟩, hb⟩
  exists_of_eq h := by
    refine ⟨1, ?_⟩
    simpa only [one_smul] using
      changeRoot_injective f g hfg hf (IsLocalization.injective U hM) h

end BaseChange
end PermanentBorder.RootLocalization

namespace PermanentBorder.ConductorLocalization
section
variable {S U B C E : Type*} [CommRing S] [CommRing U] [CommRing B]
  [CommRing C] [CommRing E] [Algebra S U] [Algebra S B] [Algebra S C]
  [Algebra U C] [IsScalarTower S U C] [Algebra S E] [Algebra U E]
  [IsScalarTower S U E]
variable (M : Submonoid S) [IsLocalization M U]

include M in

theorem integral_conductor_localizes (j : B →ₐ[S] C) (g : B →ₐ[S] E)
    (q : C →ₐ[U] E) (hcomp : (q.restrictScalars S).comp j = g)
    (b : B) (hb : ∀ x : E, IsIntegral S x → ∃ a : B, g a = g b * x) :
    ∀ x : E, IsIntegral U x → ∃ a : C, q a = q (j b) * x := by
  intro x hx
  obtain ⟨s, hs⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (M := M) x hx
  obtain ⟨a, ha⟩ := hb ((s : S) • x) hs
  obtain ⟨u, hu⟩ := IsLocalization.map_units U s
  have hu' : (u : U) = algebraMap S U (s : S) := hu
  refine ⟨(↑u⁻¹ : U) • j a, ?_⟩
  have hj (a : B) : q (j a) = g a := AlgHom.congr_fun hcomp a
  rw [map_smul, hj, ha, mul_smul_comm, ← hj b]
  rw [← algebraMap_smul U (s : S), ← hu', smul_smul]
  simp
end
end PermanentBorder.ConductorLocalization

namespace PermanentBorder.IdealLocalization
section
variable {S B C : Type*} [CommRing S] [CommRing B] [CommRing C]
  [Algebra S B] [Algebra S C]
variable (M : Submonoid S) (j : B →ₐ[S] C) [IsLocalizedModule M j.toLinearMap]

noncomputable def localizedIdeal (I : Ideal B) : Ideal C where
  __ := (I.restrictScalars S).localized₀ M j.toLinearMap
  smul_mem' c _ hx := by
    obtain ⟨x,hx,s,rfl⟩ := hx
    obtain ⟨⟨y,t⟩,hy⟩ := IsLocalizedModule.surj M j.toLinearMap c
    have hy' : IsLocalizedModule.mk' j.toLinearMap y t = c :=
      IsLocalizedModule.mk'_eq_iff.mpr hy.symm
    rw [← hy', smul_eq_mul, IsLocalizedModule.mk'_mul_mk']
    exact ⟨y*x,I.mul_mem_left y hx,t*s,rfl⟩

theorem map_le_localizedIdeal (I : Ideal B) :
    I.map j.toRingHom ≤ localizedIdeal M j I := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  exact ⟨x,hx,1, by simp⟩

theorem map_mem_localized (I : Ideal B) (x : C)
    (hx : x ∈ I.map j.toRingHom) :
    x ∈ (I.restrictScalars S).localized₀ M j.toLinearMap :=
  map_le_localizedIdeal M j I hx
end
end PermanentBorder.IdealLocalization

namespace PermanentBorder.Conductor
open Polynomial Matrix RootLocalization
section
variable {S U ι : Type*} [CommRing S] [CommRing U] [Algebra S U]
  [Fintype ι] [DecidableEq ι]

noncomputable def matrixRootChange (T : Matrix ι ι S) :
    AdjoinRoot T.charpoly →ₐ[S] AdjoinRoot (T.map (algebraMap S U)).charpoly :=
  changeRoot T.charpoly (T.map (algebraMap S U)).charpoly (T.charpoly_map _).symm

@[simp] theorem matrixRootChange_root (T : Matrix ι ι S) :
    matrixRootChange (U := U) T (AdjoinRoot.root T.charpoly) =
      AdjoinRoot.root (T.map (algebraMap S U)).charpoly := changeRoot_root ..

theorem matrixRootChange_adjugate (T : Matrix ι ι S) :
    (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly)).map
      (matrixRootChange (U := U) T) =
    (T.map (algebraMap S U)).charmatrix.adjugate.map
      (AdjoinRoot.mk (T.map (algebraMap S U)).charpoly) := by
  have h1 : T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly) =
      (T.charmatrix.map (AdjoinRoot.mk T.charpoly)).adjugate :=
    (AdjoinRoot.mk T.charpoly).map_adjugate T.charmatrix
  have h2 : (T.charmatrix.map (AdjoinRoot.mk T.charpoly)).adjugate.map
      (matrixRootChange (U := U) T) =
      ((T.charmatrix.map (AdjoinRoot.mk T.charpoly)).map
        (matrixRootChange (U := U) T)).adjugate :=
    (matrixRootChange (U := U) T).map_adjugate _
  have h3 : (T.map (algebraMap S U)).charmatrix.adjugate.map
      (AdjoinRoot.mk (T.map (algebraMap S U)).charpoly) =
      ((T.map (algebraMap S U)).charmatrix.map
        (AdjoinRoot.mk (T.map (algebraMap S U)).charpoly)).adjugate :=
    (AdjoinRoot.mk (T.map (algebraMap S U)).charpoly).map_adjugate _
  rw [h1,h2,h3]
  congr 1
  have hc (x : S) : matrixRootChange (U := U) T (AdjoinRoot.of T.charpoly x) =
      AdjoinRoot.of (T.map (algebraMap S U)).charpoly (algebraMap S U x) :=
    (matrixRootChange (U := U) T).commutes x
  ext i j
  simp only [Matrix.map_apply,charmatrix,Matrix.sub_apply,map_sub,
    Matrix.scalar_apply,Matrix.diagonal_apply]
  split_ifs <;> simp only [RingHom.mapMatrix_apply, Matrix.map_apply, map_zero, AdjoinRoot.mk_X, matrixRootChange_root,
    AdjoinRoot.mk_C, hc]

omit [Fintype ι] [DecidableEq ι] in
theorem matrixEntryIdeal_map {B C : Type*} [CommRing B] [CommRing C]
    (f : B →+* C) (N : Matrix ι ι B) :
    (matrixEntryIdeal N).map f = matrixEntryIdeal (N.map f) := by
  rw [matrixEntryIdeal,Ideal.map_span,matrixEntryIdeal]
  congr 1
  ext x
  simp only [Set.mem_image,Set.mem_range,exists_exists_eq_and,Matrix.map_apply]

theorem adjugateIdeal_baseChange (T : Matrix ι ι S) :
    (matrixEntryIdeal (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly))).map
      (matrixRootChange (U := U) T).toRingHom =
    matrixEntryIdeal ((T.map (algebraMap S U)).charmatrix.adjugate.map
      (AdjoinRoot.mk (T.map (algebraMap S U)).charpoly)) := by
  rw [matrixEntryIdeal_map]
  congr 1
  exact matrixRootChange_adjugate T
end
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Polynomial Matrix Module RootLocalization

@[simp] theorem genericBaseChange_root {V Q : Type*} [CommRing V] [Field Q]
    [Algebra V Q] (f : V[X]) :
    genericBaseChange (Q := Q) f (AdjoinRoot.root f) =
      AdjoinRoot.root (f.map (algebraMap V Q)) := by
  simpa only [AdjoinRoot.root, Polynomial.map_X] using genericBaseChange_mk (Q := Q) f X

section GenericTransport
variable {S U Q ι : Type*} [CommRing S] [CommRing U] [Field Q]
  [Algebra S U] [Algebra S Q] [Algebra U Q] [IsScalarTower S U Q]
  [Fintype ι] [DecidableEq ι]

theorem charpoly_map_tower (T : Matrix ι ι S) :
    T.charpoly.map (algebraMap S Q) =
      (T.map (algebraMap S U)).charpoly.map (algebraMap U Q) := by
  rw [charpoly_map, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]

noncomputable def genericMatrixChange (T : Matrix ι ι S) :
    AdjoinRoot (T.charpoly.map (algebraMap S Q)) ≃ₐ[Q]
      AdjoinRoot ((T.map (algebraMap S U)).charpoly.map (algebraMap U Q)) :=
  AdjoinRoot.algEquivOfEq Q _ _ (charpoly_map_tower T)

theorem genericMatrixChange_comp (T : Matrix ι ι S) :
    ((genericBaseChange (Q := Q) (T.map (algebraMap S U)).charpoly).restrictScalars S).comp
      (matrixRootChange (U := U) T) =
    ((genericMatrixChange (U := U) (Q := Q) T).restrictScalars S).toAlgHom.comp
      (genericBaseChange (Q := Q) T.charpoly) := by
  apply AdjoinRoot.algHom_ext
  change genericBaseChange (Q := Q) (T.map (algebraMap S U)).charpoly
      (matrixRootChange (U := U) T (AdjoinRoot.root T.charpoly)) =
    genericMatrixChange (U := U) (Q := Q) T
      (genericBaseChange (Q := Q) T.charpoly (AdjoinRoot.root T.charpoly))
  rw [matrixRootChange_root,genericBaseChange_root,genericBaseChange_root]
  exact (AdjoinRoot.algEquivOfEq_root _ _ _).symm
end GenericTransport

section LocalCondition
variable {K S Q ι : Type*} [Field K] [Infinite K]
  [CommRing S] [IsDomain S] [IsPrincipalIdealRing S] [IsLocalRing S] [Algebra K S]
  [Field Q] [Algebra S Q] [IsFractionRing S Q] [Fintype ι] [DecidableEq ι]

include K in
theorem integral_conductor_le_adjugate_local (T : Matrix ι ι S)
    (hsep : (T.charpoly.map (algebraMap S Q)).Separable)
    (b : AdjoinRoot T.charpoly)
    (hb : ∀ x : AdjoinRoot (T.charpoly.map (algebraMap S Q)), IsIntegral S x →
      ∃ a : AdjoinRoot T.charpoly,
        genericBaseChange (Q := Q) T.charpoly a =
          genericBaseChange (Q := Q) T.charpoly b * x) :
    b ∈ matrixEntryIdeal (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly)) := by
  let := (normalizationInclusion (Q := Q) T.charpoly T.charpoly_monic).toRingHom.toAlgebra
  apply normalization_conductor_le_adjugate (K := K) T hsep
  intro x
  obtain ⟨a,ha⟩ := hb x.val x.property
  exact ⟨a,Subtype.ext ha⟩
end LocalCondition

section GlobalComparison
variable {K S ι : Type*} [Field K] [Infinite K]
  [CommRing S] [IsDomain S] [IsPrincipalIdealRing S] [Algebra K S]
  [Fintype ι] [DecidableEq ι]

include K in

theorem normalization_conductor_le_adjugate_global (T : Matrix ι ι S)
    (hsep : (T.charpoly.map (algebraMap S (FractionRing S))).Separable) :
    letI := (normalizationInclusion (Q := FractionRing S) T.charpoly T.charpoly_monic).toRingHom.toAlgebra
    algebraConductor (AdjoinRoot T.charpoly)
      (integralClosure S (AdjoinRoot (T.charpoly.map (algebraMap S (FractionRing S))))) ≤
      matrixEntryIdeal (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly)) := by
  let Q := FractionRing S
  let := (normalizationInclusion (Q := Q) T.charpoly T.charpoly_monic).toRingHom.toAlgebra
  let J := matrixEntryIdeal (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly))
  intro b hb
  let U (P : Ideal S) [P.IsMaximal] := Localization.AtPrime P
  let C (P : Ideal S) [P.IsMaximal] := AdjoinRoot (T.map (algebraMap S (U P))).charpoly
  let j (P : Ideal S) [P.IsMaximal] : AdjoinRoot T.charpoly →ₐ[S] C P :=
    matrixRootChange (U := U P) T
  have hj (P : Ideal S) [P.IsMaximal] : IsLocalizedModule P.primeCompl (j P).toLinearMap :=
    changeRoot_isLocalizedModule _ _ _ _ T.charpoly_monic P.primeCompl_le_nonZeroDivisors
  apply @Submodule.mem_of_localization_maximal S (AdjoinRoot T.charpoly) _ _ _
    C _ _ (fun P _ => (j P).toLinearMap) hj b (J.restrictScalars S)
  intro P hP
  let := hj P
  let T' := T.map (algebraMap S (U P))
  let e := (genericMatrixChange (U := U P) (Q := Q) T).restrictScalars S
  let g := e.toAlgHom.comp (genericBaseChange (Q := Q) T.charpoly)
  have hbg : ∀ x : AdjoinRoot (T'.charpoly.map (algebraMap (U P) Q)),
      IsIntegral S x → ∃ a : AdjoinRoot T.charpoly, g a = g b * x := by
    intro x hx
    obtain ⟨a,ha⟩ := hb (⟨e.symm x, IsIntegral.map e.symm.toAlgHom hx⟩ :
      integralClosure S (AdjoinRoot (T.charpoly.map (algebraMap S Q))))
    have ha0 : genericBaseChange (Q := Q) T.charpoly a =
        genericBaseChange (Q := Q) T.charpoly b * e.symm x := congrArg Subtype.val ha
    have ha' := congrArg e ha0
    refine ⟨a, ?_⟩
    simpa only [g,AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,map_mul,AlgEquiv.apply_symm_apply] using ha'
  have hbP := ConductorLocalization.integral_conductor_localizes P.primeCompl (j P) g
    (genericBaseChange (Q := Q) T'.charpoly) (genericMatrixChange_comp T) b hbg
  have hsep' : (T'.charpoly.map (algebraMap (U P) Q)).Separable := by
    rw [← charpoly_map_tower T]
    exact hsep
  have hbJ := integral_conductor_le_adjugate_local (K := K) T' hsep' (j P b) hbP
  apply IdealLocalization.map_mem_localized P.primeCompl (j P) J
  rw [show j P = matrixRootChange (U := U P) T from rfl,adjugateIdeal_baseChange]
  exact hbJ
end GlobalComparison
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Module Polynomial
section CokernelEquiv
variable {S B A : Type*} [CommRing S] [IsDomain S] [IsPrincipalIdealRing S]
  [CommRing B] [CommRing A] [Algebra S B] [Algebra S A] [Algebra B A]
  [IsScalarTower S B A] [NoZeroSMulDivisors S A] [Module.Finite S A]

theorem exists_conductor_cokernel_equiv
    (hi : Function.Injective (algebraMap B A))
    (hden : ∀ x : A, ∃ s : S, s ≠ 0 ∧ ∃ b : B, s • x = algebraMap B A b)
    (lam : B →ₗ[S] S) (e : B ≃ₗ[S] Module.Dual S B)
    (he : ∀ a b : B, e a b = lam (a*b)) :
    Nonempty ((B ⧸ (algebraConductor B A).restrictScalars S) ≃ₗ[S]
      (A ⧸ LinearMap.range (IsScalarTower.toAlgHom S B A).toLinearMap)) := by
  classical
  let i : B →ₗ[S] A := (IsScalarTower.toAlgHom S B A).toLinearMap
  have hr : Submodule.map e.toLinearMap ((algebraConductor B A).restrictScalars S) =
      LinearMap.range i.dualMap := by
    ext ℓ
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨L, hL⟩ := (in_dual_restriction_image_iff hi hden lam e he a).mpr ha
      refine ⟨L, ?_⟩
      ext b
      exact (hL b).trans (he a b).symm
    · rintro ⟨L, rfl⟩
      refine ⟨e.symm (i.dualMap L), ?_, by simp⟩
      apply (in_dual_restriction_image_iff hi hden lam e he _).mp
      refine ⟨L, ?_⟩
      intro b
      rw [← he, e.apply_symm_apply]
      rfl
  let eqv := Submodule.Quotient.equiv _ _ e hr
  obtain ⟨d⟩ := exists_dual_cokernel_equiv (Module.Free.chooseBasis S A) i hi
    (finrank_eq_of_denominators hi hden)
  exact ⟨eqv.trans d.symm⟩
end CokernelEquiv

section NormalizationCokernel
variable {S Q : Type*} [CommRing S] [IsDomain S] [IsPrincipalIdealRing S]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]
variable {f : S[X]} (hf : f.Monic)
local notation "R" => integralClosure S (AdjoinRoot (f.map (algebraMap S Q)))

theorem exists_normalization_conductor_cokernel_equiv
    (hsep : (f.map (algebraMap S Q)).Separable) :
    letI := (normalizationInclusion (Q := Q) f hf).toRingHom.toAlgebra
    Nonempty ((AdjoinRoot f ⧸ (algebraConductor (AdjoinRoot f) R).restrictScalars S) ≃ₗ[S]
      (R ⧸ LinearMap.range (normalizationInclusion (Q := Q) f hf).toLinearMap)) := by
  let := (normalizationInclusion (Q := Q) f hf).toRingHom.toAlgebra
  have : Module.Finite S R := finite_integralClosure_adjoinRoot (hf.map _) hsep
  have : NoZeroSMulDivisors S R := normalization_torsionFree (f := f)
  exact exists_conductor_cokernel_equiv
    (normalizationInclusion_injective (Q := Q) f hf)
    (normalizationInclusion_denominators (Q := Q) f hf)
    (topRemainderCoefficient hf) (coefficientPairingEquiv hf) (coefficientPairingEquiv_apply hf)
end NormalizationCokernel
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Polynomial Module Matrix
section ScalarLength
variable {K S ι : Type*} [Field K] [Infinite K]
  [CommRing S] [IsDomain S] [IsPrincipalIdealRing S] [Algebra K S]
  [Fintype ι] [DecidableEq ι]

theorem normalization_adjugate_length_global (T : Matrix ι ι S)
    (hsep : (T.charpoly.map (algebraMap S (FractionRing S))).Separable) :
    let R := integralClosure S (AdjoinRoot (T.charpoly.map (algebraMap S (FractionRing S))))
    Module.length K (AdjoinRoot T.charpoly ⧸
      (matrixEntryIdeal (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly))).restrictScalars S) ≤
    Module.length K (R ⧸ LinearMap.range
      (normalizationInclusion (Q := FractionRing S) T.charpoly T.charpoly_monic).toLinearMap) := by
  let Q := FractionRing S
  let R := integralClosure S (AdjoinRoot (T.charpoly.map (algebraMap S Q)))
  let := (normalizationInclusion (Q := Q) T.charpoly T.charpoly_monic).toRingHom.toAlgebra
  let c := (algebraConductor (AdjoinRoot T.charpoly) R).restrictScalars S
  let J := (matrixEntryIdeal
    (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly))).restrictScalars S
  have h : c ≤ J := normalization_conductor_le_adjugate_global (K := K) T hsep
  obtain ⟨e⟩ := exists_normalization_conductor_cokernel_equiv T.charpoly_monic hsep
  calc
    _ ≤ Module.length K (AdjoinRoot T.charpoly ⧸ c) :=
      Module.length_le_of_surjective ((Submodule.factor h).restrictScalars K)
        (Submodule.factor_surjective h)
    _ = _ := (e.restrictScalars K).length_eq
end ScalarLength
end PermanentBorder.Conductor

end OAI
