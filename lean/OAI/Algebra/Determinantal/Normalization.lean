import OAI.Algebra.Determinantal.ConductorDuality

namespace OAI

namespace PermanentBorder.Conductor
open Polynomial Module
section GenericLattice
variable {S Q : Type*} [CommRing S] [IsDomain S]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]
variable (f : S[X])

noncomputable def genericBaseChange :
    AdjoinRoot f →ₐ[S] AdjoinRoot (f.map (algebraMap S Q)) :=
  AdjoinRoot.mapAlgHom (Algebra.ofId S Q) f (f.map (algebraMap S Q)) (dvd_refl _)

omit [IsDomain S] [IsFractionRing S Q] in
@[simp] theorem genericBaseChange_mk (g : S[X]) :
    genericBaseChange (Q := Q) f (AdjoinRoot.mk f g) =
      AdjoinRoot.mk (f.map (algebraMap S Q)) (g.map (algebraMap S Q)) := by
  change aeval (AdjoinRoot.root (f.map (algebraMap S Q))) g = _
  exact AdjoinRoot.aeval_eq_of_algebra (R := S) (S := Q) _ g

omit [IsDomain S] in

theorem genericBaseChange_injective (hf : f.Monic) :
    Function.Injective (genericBaseChange (Q := Q) f) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective z
  rw [genericBaseChange_mk, AdjoinRoot.mk_eq_zero] at hz
  rw [AdjoinRoot.mk_eq_zero, ← modByMonic_eq_zero_iff_dvd hf]
  apply Polynomial.map_injective (algebraMap S Q) (IsFractionRing.injective S Q)
  rw [Polynomial.map_zero, map_modByMonic _ hf,
    (modByMonic_eq_zero_iff_dvd (hf.map _)).mpr hz]

theorem genericBaseChange_denominators
    (x : AdjoinRoot (f.map (algebraMap S Q))) :
    ∃ s : S, s ≠ 0 ∧ ∃ b : AdjoinRoot f,
      s • x = genericBaseChange (Q := Q) f b := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨s, hs, hp⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors S) p
  refine ⟨s, mem_nonZeroDivisors_iff_ne_zero.mp hs,
    AdjoinRoot.mk f (IsLocalization.integerNormalization (nonZeroDivisors S) p), ?_⟩
  rw [genericBaseChange_mk, hp]
  exact (map_smul (((AdjoinRoot.mkₐ (f.map (algebraMap S Q))).restrictScalars S).toLinearMap) s p).symm

variable (hf : f.Monic)

noncomputable def normalizationInclusion :
    AdjoinRoot f →ₐ[S] integralClosure S (AdjoinRoot (f.map (algebraMap S Q))) := by
  haveI : Module.Finite S (AdjoinRoot f) := hf.finite_adjoinRoot
  exact (genericBaseChange (Q := Q) f).codRestrict _
    (fun z => IsIntegral.map (genericBaseChange (Q := Q) f) (Algebra.IsIntegral.isIntegral z))

omit [IsDomain S] [IsFractionRing S Q] in
@[simp] theorem normalizationInclusion_val (z : AdjoinRoot f) :
    (normalizationInclusion (Q := Q) f hf z).val = genericBaseChange (Q := Q) f z := rfl

omit [IsDomain S] in
theorem normalizationInclusion_injective :
    Function.Injective (normalizationInclusion (Q := Q) f hf) := by
  intro z w h
  apply genericBaseChange_injective (Q := Q) f hf
  exact congrArg Subtype.val h

theorem normalizationInclusion_denominators
    (x : integralClosure S (AdjoinRoot (f.map (algebraMap S Q)))) :
    ∃ s : S, s ≠ 0 ∧ ∃ b : AdjoinRoot f,
      s • x = normalizationInclusion (Q := Q) f hf b := by
  obtain ⟨s, hs, b, hb⟩ := genericBaseChange_denominators f x.val
  exact ⟨s, hs, b, Subtype.ext hb⟩
end GenericLattice
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Polynomial Module
section ActualNormalization
variable {S Q : Type*} [CommRing S] [IsDomain S] [IsPrincipalIdealRing S]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]
variable {f : S[X]} (hf : f.Monic)
local notation "R" => integralClosure S (AdjoinRoot (f.map (algebraMap S Q)))

omit [IsDomain S] [IsPrincipalIdealRing S] in

theorem normalization_torsionFree : NoZeroSMulDivisors S R := by
  let ι : R →ₗ[S] AdjoinRoot (f.map (algebraMap S Q)) :=
    (integralClosure S (AdjoinRoot (f.map (algebraMap S Q)))).val.toLinearMap
  have : NoZeroSMulDivisors S (AdjoinRoot (f.map (algebraMap S Q))) := by
    constructor
    intro s x h
    rw [← IsScalarTower.algebraMap_smul Q s x] at h
    rcases eq_zero_or_eq_zero_of_smul_eq_zero h with hs | hx
    · exact Or.inl ((IsFractionRing.injective S Q) (hs.trans (map_zero _).symm))
    · exact Or.inr hx
  exact Function.Injective.noZeroSMulDivisors ι Subtype.val_injective
    (map_zero ι) (map_smul ι)

theorem normalization_conductor_colength
    (hsep : (f.map (algebraMap S Q)).Separable) :
    letI := (normalizationInclusion (Q := Q) f hf).toRingHom.toAlgebra
    Module.length S (AdjoinRoot f ⧸
      (algebraConductor (AdjoinRoot f) R).restrictScalars S) =
    Module.length S (R ⧸ LinearMap.range
      (normalizationInclusion (Q := Q) f hf).toLinearMap) := by
  let := (normalizationInclusion (Q := Q) f hf).toRingHom.toAlgebra
  have : Module.Finite S R :=
    finite_integralClosure_adjoinRoot (hf.map _) hsep
  have : NoZeroSMulDivisors S R := normalization_torsionFree (f := f)
  exact monic_conductor_colength hf
    (normalizationInclusion_injective (Q := Q) f hf)
    (normalizationInclusion_denominators (Q := Q) f hf)
end ActualNormalization
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Polynomial Matrix Module
section Eigenbasis
variable {Q L ι : Type*} [Field Q] [Field L] [Algebra Q L]
  [Fintype ι] [DecidableEq ι]

theorem exists_splitting_eigenbasis (T : Matrix ι ι Q)
    (hsep : T.charpoly.Separable)
    (hsplit : (T.charpoly.map (algebraMap Q L)).Splits) :
    ∃ b : Basis (T.charpoly.rootSet L) L (ι → L),
      ∀ μ, (T.map (algebraMap Q L)) *ᵥ b μ = μ.val • b μ := by
  classical
  let U := T.map (algebraMap Q L)
  have he (μ : T.charpoly.rootSet L) : Module.End.HasEigenvalue U.mulVecLin μ.val := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_mulVecLin]
    change (T.map (algebraMap Q L)).charpoly.IsRoot _
    rw [charpoly_map]
    simpa only [IsRoot, eval_map, aeval_def] using (mem_rootSet.mp μ.property).2
  choose v hv using fun μ => (he μ).exists_hasEigenvector
  have hvi : LinearIndependent L v :=
    Module.End.eigenvectors_linearIndependent' U.mulVecLin _ Subtype.val_injective v hv
  have hc : Fintype.card (T.charpoly.rootSet L) = Module.finrank L (ι → L) := by
    rw [card_rootSet_eq_natDegree hsep hsplit, T.charpoly_natDegree_eq_dim,
      Module.finrank_fintype_fun_eq_card]
  let b := basisOfLinearIndependentOfCardEqFinrank' v hvi hc
  refine ⟨b, fun μ => ?_⟩
  simpa only [b, coe_basisOfLinearIndependentOfCardEqFinrank', U, Matrix.mulVecLin_apply] using (hv μ).apply_eq_smul
end Eigenbasis

section NonzeroCoordinates
variable {Q L ι γ : Type*} [Field Q] [Infinite Q] [Field L] [Algebra Q L]
  [Fintype ι] [DecidableEq ι] [Finite γ]

theorem exists_ground_vector_all_coords_ne_zero (b : Basis γ L (ι → L)) :
    ∃ v : ι → Q, ∀ j, b.repr (algebraMap Q L ∘ v) j ≠ 0 := by
  classical
  let c : (ι → Q) →ₗ[Q] (ι → L) :=
    { toFun := fun v => (algebraMap Q L) ∘ v
      map_add' := by intro x y; ext; simp
      map_smul' := by intro a x; ext; simp [Algebra.smul_def] }
  let p (j : γ) := LinearMap.ker ((b.coord j).restrictScalars Q |>.comp c)
  have hp (j : γ) : p j ≠ ⊤ := by
    intro h
    have hz (i : ι) : b.repr (Pi.single i 1) j = 0 := by
      have he : Pi.single i 1 ∈ p j := h ▸ Submodule.mem_top
      change b.repr (algebraMap Q L ∘ Pi.single i 1) j = 0 at he
      have hc : algebraMap Q L ∘ Pi.single i (1 : Q) = Pi.single i (1 : L) := by
        ext x; simp [Pi.single_apply, apply_ite]
      simpa only [hc] using he
    have hh : b.repr (b j) j = 0 := by
      have hb : b j = ∑ i, (b j i) • Pi.single i (1 : L) := by
        ext i; simp [Pi.single_apply]
      rw [hb, map_sum, Finsupp.finsetSum_apply]
      simp [hz]
    simp at hh
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  exact ⟨v, hv⟩
end NonzeroCoordinates
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Polynomial Matrix Module
section Coordinates
variable {L V γ : Type*} [Field L] [AddCommGroup V] [Module L V]
variable (b : Basis γ L V) (φ : V →ₗ[L] V) (μ : γ → L)
variable (hφ : ∀ i, φ (b i) = μ i • b i)

include hφ in
theorem eigenbasis_coord_apply (j : γ) (x : V) :
    b.coord j (φ x) = μ j * b.coord j x := by
  classical
  have he : (b.coord j).comp φ = μ j • b.coord j := by
    apply b.ext
    intro i
    simp only [LinearMap.comp_apply, hφ, map_smul, LinearMap.smul_apply,
      Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
    split_ifs with h
    · subst i; rfl
    · simp
  exact congrArg (fun f : V →ₗ[L] L => f x) he

include hφ in
theorem eigenbasis_coord_pow (j : γ) (x : V) (n : ℕ) :
    b.coord j ((φ ^ n) x) = μ j ^ n * b.coord j x := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ', Module.End.mul_apply, eigenbasis_coord_apply b φ μ hφ,
      hn, pow_succ', mul_assoc]

include hφ in
theorem eigenbasis_coord_aeval (j : γ) (x : V) (p : L[X]) :
    b.coord j ((aeval φ p) x) = p.eval (μ j) * b.coord j x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq, add_mul]
  | monomial n c =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, eigenbasis_coord_pow b φ μ hφ, eval_monomial, smul_eq_mul,
      mul_assoc]
end Coordinates
section Extension
variable {Q L ι : Type*} [Field Q] [Field L] [Algebra Q L]
  [Fintype ι] [DecidableEq ι]

theorem matrix_aeval_mulVec (T : Matrix ι ι Q) (p : Q[X]) (v : ι → Q) :
    (aeval T.mulVecLin p) v = (aeval T p) *ᵥ v := by
  have h := Polynomial.aeval_algHom_apply
    (Matrix.toLinAlgEquiv' (R := Q) (n := ι)) T p
  exact congrArg (fun f : (ι → Q) →ₗ[Q] (ι → Q) => f v) h

theorem matrix_aeval_map_mulVec (T : Matrix ι ι Q) (p : Q[X]) (v : ι → Q) :
    algebraMap Q L ∘ ((aeval T.mulVecLin p) v) =
      (aeval (T.map (algebraMap Q L)).mulVecLin (p.map (algebraMap Q L)))
        (algebraMap Q L ∘ v) := by
  rw [matrix_aeval_mulVec, matrix_aeval_mulVec]
  have hm : (aeval T p).map (algebraMap Q L) =
      aeval (T.map (algebraMap Q L)) (p.map (algebraMap Q L)) := by
    apply Polynomial.map_aeval_eq_aeval_map (R := Q) (S := Matrix ι ι Q)
      (T := L) (U := Matrix ι ι L) (φ := algebraMap Q L)
      (ψ := (algebraMap Q L).mapMatrix)
    ext c i j
    simp only [RingHom.comp_apply, Matrix.algebraMap_matrix_apply,
      Algebra.algebraMap_self, Matrix.map_apply, RingHom.mapMatrix_apply]
    split_ifs <;> simp_all
  rw [← hm]
  funext i
  exact (algebraMap Q L).map_mulVec (aeval T p) v i
end Extension
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Polynomial Matrix Module
section
variable {Q ι : Type*} [Field Q] [Fintype ι] [DecidableEq ι]

noncomputable def cyclicMap (T : Matrix ι ι Q) (v : ι → Q) :
    AdjoinRoot T.charpoly →ₗ[Q] (ι → Q) := by
  let ev : Q[X] →ₗ[Q] (ι → Q) :=
    (LinearMap.applyₗ v).comp (aeval T.mulVecLin).toLinearMap
  let I := (Ideal.span ({T.charpoly} : Set Q[X])).restrictScalars Q
  exact I.liftQ ev (by
    intro p hp
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hp
    change (aeval T.mulVecLin (T.charpoly * g)) v = 0
    rw [map_mul]
    have hc : aeval T.mulVecLin T.charpoly = 0 := by
      simpa only [Matrix.charpoly_mulVecLin] using T.mulVecLin.aeval_self_charpoly
    rw [hc, zero_mul, LinearMap.zero_apply])

@[simp] theorem cyclicMap_mk (T : Matrix ι ι Q) (v : ι → Q) (p : Q[X]) :
    cyclicMap T v (AdjoinRoot.mk T.charpoly p) = (aeval T.mulVecLin p) v := rfl

theorem cyclicMap_root_mul (T : Matrix ι ι Q) (v : ι → Q)
    (x : AdjoinRoot T.charpoly) :
    cyclicMap T v (AdjoinRoot.root T.charpoly * x) = T *ᵥ cyclicMap T v x := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  change cyclicMap T v (AdjoinRoot.mk T.charpoly X * AdjoinRoot.mk T.charpoly p) = _
  rw [← map_mul, cyclicMap_mk, map_mul, aeval_X, Module.End.mul_apply, cyclicMap_mk]
  rfl
end
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Polynomial Matrix Module
section
variable {Q ι : Type*} [Field Q] [Infinite Q] [Fintype ι] [DecidableEq ι]

theorem exists_cyclicMap_bijective (T : Matrix ι ι Q)
    (hsep : T.charpoly.Separable) :
    ∃ v : ι → Q, Function.Bijective (cyclicMap T v) := by
  let L := T.charpoly.SplittingField
  obtain ⟨b, hb⟩ := exists_splitting_eigenbasis (L := L) T hsep
    (SplittingField.splits T.charpoly)
  obtain ⟨v, hv⟩ := exists_ground_vector_all_coords_ne_zero (Q := Q) b
  have hi : Function.Injective (cyclicMap T v) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    apply rootEvaluation_injective T.charpoly_monic hsep (SplittingField.splits T.charpoly)
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    rw [cyclicMap_mk] at hz
    funext μ
    rw [rootEvaluation_mk, map_zero, Pi.zero_apply]
    have hve : (aeval (T.map (algebraMap Q L)).mulVecLin (p.map (algebraMap Q L)))
        (algebraMap Q L ∘ v) = 0 := by
      rw [← matrix_aeval_map_mulVec, hz]
      ext i; simp
    have he := eigenbasis_coord_aeval b (T.map (algebraMap Q L)).mulVecLin
      (fun μ => μ.val) (fun μ => by simpa using hb μ) μ
      (algebraMap Q L ∘ v) (p.map (algebraMap Q L))
    rw [hve, map_zero] at he
    have hp : aeval μ.val p * (b.repr (algebraMap Q L ∘ v)) μ = 0 := by
      simpa only [eval_map, aeval_def, Basis.coord_apply] using he.symm
    exact (mul_eq_zero.mp hp).resolve_right (hv μ)
  let : Module.Finite Q (AdjoinRoot T.charpoly) := T.charpoly_monic.finite_adjoinRoot
  have hd : Module.finrank Q (AdjoinRoot T.charpoly) = Module.finrank Q (ι → Q) := by
    rw [show Module.finrank Q (AdjoinRoot T.charpoly) = T.charpoly.natDegree from
      finrank_quotient_span_eq_natDegree, T.charpoly_natDegree_eq_dim,
      Module.finrank_fintype_fun_eq_card]
  exact ⟨v, hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hi⟩

theorem exists_generic_matrix_equiv (T : Matrix ι ι Q)
    (hsep : T.charpoly.Separable) :
    ∃ e : (ι → Q) ≃ₗ[Q] AdjoinRoot T.charpoly,
      ∀ x, e (T *ᵥ x) = AdjoinRoot.root T.charpoly * e x := by
  obtain ⟨v, hv⟩ := exists_cyclicMap_bijective T hsep
  let e := LinearEquiv.ofBijective (cyclicMap T v) hv
  refine ⟨e.symm, fun x => ?_⟩
  apply e.injective
  rw [e.apply_symm_apply]
  change T *ᵥ x = cyclicMap T v (AdjoinRoot.root T.charpoly * e.symm x)
  rw [cyclicMap_root_mul]
  exact congrArg T.mulVec (e.apply_symm_apply x).symm
end
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
section Semilocal
variable {S A : Type*} [CommRing S] [IsLocalRing S]
  [CommRing A] [Algebra S A] [Module.Finite S A]

include S in

theorem finite_maximalSpectrum_of_finite_local : Finite (MaximalSpectrum A) := by
  classical
  let m := IsLocalRing.maximalIdeal S
  let J := m.map (algebraMap S A)
  have hle (M : MaximalSpectrum A) : J ≤ M.asIdeal := by
    change m.map (algebraMap S A) ≤ M.asIdeal
    rw [Ideal.map_le_iff_le_comap]
    have hm : (M.asIdeal.comap (algebraMap S A)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal M.asIdeal
    exact (IsLocalRing.eq_maximalIdeal hm).symm.le
  let : Algebra (S ⧸ m) (A ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map)
  have : IsScalarTower S (S ⧸ m) (A ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  have : Module.Finite (S ⧸ m) (A ⧸ J) :=
    Module.Finite.of_restrictScalars_finite S _ _
  let : Field (S ⧸ m) := Ideal.Quotient.field m
  have : IsArtinianRing (A ⧸ J) := IsArtinianRing.of_finite (S ⧸ m) _
  have hker : RingHom.ker (Ideal.Quotient.mk J) = J := by
    ext x
    exact Ideal.Quotient.eq_zero_iff_mem
  let ι : MaximalSpectrum A → MaximalSpectrum (A ⧸ J) := fun M =>
    ⟨M.asIdeal.map (Ideal.Quotient.mk J),
      Ideal.IsMaximal.map_of_surjective_of_ker_le (Ideal.Quotient.mk_surjective)
        (by rw [hker]; exact hle M)⟩
  apply Finite.of_injective ι
  intro M N h
  apply MaximalSpectrum.ext
  have he := congrArg MaximalSpectrum.asIdeal h
  have hi (P : MaximalSpectrum A) :
      (P.asIdeal.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = P.asIdeal := by
    rw [Ideal.comap_map_of_surjective _ (Ideal.Quotient.mk_surjective)]
    rw [← RingHom.ker_eq_comap_bot, hker, sup_of_le_left (hle P)]
  exact (hi M).symm.trans ((congrArg (Ideal.comap (Ideal.Quotient.mk J)) he).trans (hi N))
end Semilocal

section FieldNormalization
variable {S Q L : Type*} [CommRing S] [IsDomain S] [IsPrincipalIdealRing S] [IsLocalRing S]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]
  [Field L] [Algebra Q L] [Algebra S L] [IsScalarTower S Q L]
  [FiniteDimensional Q L] [Algebra.IsSeparable Q L]

include Q in

theorem integralClosure_isPrincipalIdealRing :
    IsPrincipalIdealRing (integralClosure S L) := by
  have : Module.Finite S (integralClosure S L) :=
    IsIntegralClosure.finite S Q L (integralClosure S L)
  have : Finite (MaximalSpectrum (integralClosure S L)) :=
    finite_maximalSpectrum_of_finite_local (S := S)
  have : IsDedekindDomain (integralClosure S L) :=
    integralClosure.isDedekindDomain S Q L
  apply IsPrincipalIdealRing.of_finite_maximals
  rw [← MaximalSpectrum.range_asIdeal]
  exact Set.finite_range _
end FieldNormalization
end PermanentBorder.Conductor

end OAI
