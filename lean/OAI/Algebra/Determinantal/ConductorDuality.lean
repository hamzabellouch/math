import OAI.Algebra.Determinantal.ConditionalBound

namespace OAI

namespace PermanentBorder.Conductor
open Module

section Conductor
variable (B A : Type*) [CommRing B] [CommRing A] [Algebra B A]

def algebraConductor : Ideal B where
  carrier := {a | ∀ x : A, ∃ b : B, algebraMap B A b = algebraMap B A a * x}
  zero_mem' := by intro x; exact ⟨0, by simp⟩
  add_mem' := by
    intro a b ha hb x
    obtain ⟨c, hc⟩ := ha x
    obtain ⟨d, hd⟩ := hb x
    exact ⟨c+d, by simp only [map_add, hc, hd, add_mul]⟩
  smul_mem' := by
    intro a b hb x
    obtain ⟨c, hc⟩ := hb x
    exact ⟨a*c, by simp only [smul_eq_mul, map_mul, hc, mul_assoc]⟩

@[simp] theorem mem_algebraConductor (a : B) :
    a ∈ algebraConductor B A ↔
      ∀ x : A, ∃ b : B, algebraMap B A b = algebraMap B A a * x := Iff.rfl
end Conductor

section Multiplication
variable {S B A : Type*} [CommRing S] [CommRing B] [CommRing A]
  [Algebra S B] [Algebra S A] [Algebra B A] [IsScalarTower S B A]
variable (hi : Function.Injective (algebraMap B A))

noncomputable def conductorMultiplication (a : B) (ha : a ∈ algebraConductor B A) :
    A →ₗ[S] B where
  toFun x := Classical.choose (ha x)
  map_add' x y := by
    apply hi
    rw [Classical.choose_spec (ha (x+y)), map_add,
      Classical.choose_spec (ha x), Classical.choose_spec (ha y), mul_add]
  map_smul' s x := by
    apply hi
    rw [Classical.choose_spec (ha (s • x))]
    change algebraMap B A a * (s • x) =
      (IsScalarTower.toAlgHom S B A) (s • Classical.choose (ha x))
    rw [map_smul]
    change algebraMap B A a * (s • x) = s • algebraMap B A (Classical.choose (ha x))
    rw [Classical.choose_spec (ha x), mul_smul_comm]

@[simp] theorem conductorMultiplication_spec (a : B) (ha : a ∈ algebraConductor B A) (x : A) :
    algebraMap B A (conductorMultiplication (S := S) hi a ha x) = algebraMap B A a * x :=
  Classical.choose_spec (ha x)

@[simp] theorem conductorMultiplication_algebraMap (a : B)
    (ha : a ∈ algebraConductor B A) (b : B) :
    conductorMultiplication (S := S) hi a ha (algebraMap B A b) = a*b := by
  apply hi
  simp
end Multiplication

section DualImage
variable {S B A : Type*} [CommRing S] [IsDomain S] [CommRing B] [CommRing A]
  [Algebra S B] [Algebra S A] [Algebra B A] [IsScalarTower S B A]
  [NoZeroSMulDivisors S A]
variable (hi : Function.Injective (algebraMap B A))
  (hden : ∀ x : A, ∃ s : S, s ≠ 0 ∧ ∃ b : B, s • x = algebraMap B A b)
  (lam : B →ₗ[S] S) (e : B ≃ₗ[S] Module.Dual S B)
  (he : ∀ a b : B, e a b = lam (a*b))

include hi hden e he

theorem in_dual_restriction_image_iff (a : B) :
    (∃ ℓ : A →ₗ[S] S, ∀ b : B, ℓ (algebraMap B A b) = lam (a*b)) ↔
      a ∈ algebraConductor B A := by
  constructor
  · rintro ⟨ℓ, hℓ⟩ x
    let ψ : B →ₗ[S] S :=
      { toFun := fun b => ℓ (algebraMap B A b * x)
        map_add' := by intro b c; simp [add_mul]
        map_smul' := by
          intro s b
          change ℓ ((IsScalarTower.toAlgHom S B A) (s • b) * x) = _
          rw [map_smul, smul_mul_assoc, map_smul]
          rfl }
    let c : B := e.symm ψ
    have hc (b : B) : e c b = ℓ (algebraMap B A b*x) := by
      change e (e.symm ψ) b = ψ b
      rw [e.apply_symm_apply]
    obtain ⟨s, hs, z, hz⟩ := hden x
    have hsc : s • c = a*z := by
      apply e.injective
      ext b
      calc
        e (s • c) b = s • (e c b) := by simp
        _ = s • ℓ (algebraMap B A b*x) := by rw [hc]
        _ = ℓ (algebraMap B A b * (s • x)) := by
          rw [mul_smul_comm, map_smul]
        _ = lam (a*(b*z)) := by rw [hz, ← map_mul, hℓ]
        _ = e (a*z) b := by rw [he]; congr 1; ring
    refine ⟨c, ?_⟩
    apply smul_right_injective A hs
    calc
      s • algebraMap B A c = (IsScalarTower.toAlgHom S B A) (s • c) := by rw [map_smul]; rfl
      _ = algebraMap B A (a*z) := by rw [hsc]; rfl
      _ = algebraMap B A a * (s • x) := by rw [map_mul, hz]
      _ = s • (algebraMap B A a * x) := mul_smul_comm _ _ _
  · intro ha
    refine ⟨lam.comp (conductorMultiplication hi a ha), ?_⟩
    intro b
    simp
end DualImage
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Module

section SmithDual
variable {S V W ι : Type*} [CommRing S] [IsDomain S] [IsPrincipalIdealRing S]
  [AddCommGroup V] [Module S V] [AddCommGroup W] [Module S W]
  [Fintype ι]

theorem exists_dual_cokernel_equiv (b : Basis ι S W) (i : V →ₗ[S] W)
    (hi : Function.Injective i) (hrank : Module.finrank S V = Module.finrank S W) :
    Nonempty ((W ⧸ LinearMap.range i) ≃ₗ[S]
      ((Module.Dual S V) ⧸ LinearMap.range i.dualMap)) := by
  classical
  let j := LinearEquiv.ofInjective i hi
  have hrank' : Module.finrank S (LinearMap.range i) = Module.finrank S W := by
    rw [← j.finrank_eq, hrank]
  obtain ⟨bw, a, bn, hh⟩ := (LinearMap.range i).exists_smith_normal_form_of_rank_eq b hrank'
  let bv : Basis ι S V := bn.map j.symm
  have hib (k : ι) : i (bv k) = a k • bw k := by
    change i (j.symm (bn k)) = a k • bw k
    rw [← hh]
    exact congrArg Subtype.val (j.apply_symm_apply (bn k))
  let α : W ≃ₗ[S] Module.Dual S V := bw.equiv bv.dualBasis (Equiv.refl ι)
  let β : V ≃ₗ[S] Module.Dual S W := bv.equiv bw.dualBasis (Equiv.refl ι)
  have hid : α.toLinearMap.comp i = i.dualMap.comp β.toLinearMap := by
    apply bv.ext
    intro k
    apply bv.ext
    intro l
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.dualMap_apply]
    rw [hib, map_smul, show α (bw k) = bv.dualBasis k by simp [α],
      show β (bv k) = bw.dualBasis k by simp [β], hib]
    simp only [LinearMap.smul_apply, LinearMap.map_smul, Basis.dualBasis_apply]
    by_cases h : k = l
    · simp [h]
    · simp [h]
  have hr : Submodule.map α.toLinearMap (LinearMap.range i) = LinearMap.range i.dualMap := by
    rw [← LinearMap.range_comp, hid, LinearMap.range_comp]
    rw [β.range, Submodule.map_top]
  exact ⟨Submodule.Quotient.equiv _ _ α hr⟩

theorem dual_restriction_colength (b : Basis ι S W) (i : V →ₗ[S] W)
    (hi : Function.Injective i) (hrank : Module.finrank S V = Module.finrank S W) :
    Module.length S (W ⧸ LinearMap.range i) =
      Module.length S ((Module.Dual S V) ⧸ LinearMap.range i.dualMap) := by
  obtain ⟨e⟩ := exists_dual_cokernel_equiv b i hi hrank
  exact e.length_eq
end SmithDual
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Polynomial Module Matrix

section MonicPairing
variable {R : Type*} [CommRing R] [Nontrivial R]
variable {f : R[X]} (hf : f.Monic)

noncomputable def topRemainderCoefficient : AdjoinRoot f →ₗ[R] R :=
  (Polynomial.lcoeff R (f.natDegree-1)).comp (AdjoinRoot.modByMonicHom hf)

noncomputable def coefficientPairing : AdjoinRoot f →ₗ[R] Module.Dual R (AdjoinRoot f) :=
  (Algebra.lmul R (AdjoinRoot f)).toLinearMap.compr₂ (topRemainderCoefficient hf)

omit [Nontrivial R] in
@[simp] theorem coefficientPairing_apply (a b : AdjoinRoot f) :
    coefficientPairing hf a b = topRemainderCoefficient hf (a*b) := rfl

theorem topRemainderCoefficient_pow {l : ℕ} (hl : l < f.natDegree) :
    topRemainderCoefficient hf (AdjoinRoot.root f ^ l) =
      if f.natDegree-1 = l then 1 else 0 := by
  change (AdjoinRoot.modByMonicHom hf (AdjoinRoot.root f ^ l)).coeff _ = _
  rw [show AdjoinRoot.root f ^ l = AdjoinRoot.mk f (X ^ l) by simp]
  rw [AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff hf).mpr]
  · simp [coeff_X_pow]
  · simpa only [degree_X_pow, degree_eq_natDegree hf.ne_zero, Nat.cast_lt] using hl

noncomputable def pairingMatrix : Matrix (Fin f.natDegree) (Fin f.natDegree) R :=
  LinearMap.toMatrix (AdjoinRoot.powerBasisAux' hf)
    (AdjoinRoot.powerBasisAux' hf).dualBasis (coefficientPairing hf)

omit [Nontrivial R] in
theorem pairingMatrix_apply (i j : Fin f.natDegree) :
    pairingMatrix hf i j =
      topRemainderCoefficient hf (AdjoinRoot.root f ^ ((i : ℕ) + j)) := by
  rw [pairingMatrix, LinearMap.toMatrix_apply, Basis.dualBasis_repr,
    coefficientPairing_apply]
  have hb (l : Fin f.natDegree) :
      AdjoinRoot.powerBasisAux' hf l = AdjoinRoot.root f ^ (l : ℕ) :=
    (AdjoinRoot.powerBasis' hf).basis_eq_pow l
  rw [hb, hb, ← pow_add, add_comm]

theorem pairingMatrix_reverse_det :
    ((pairingMatrix hf).submatrix id Fin.revPerm).det = 1 := by
  let A := (pairingMatrix hf).submatrix id Fin.revPerm
  have ha (i j : Fin f.natDegree) :
      A i j = topRemainderCoefficient hf
        (AdjoinRoot.root f ^ ((i : ℕ) + (f.natDegree-1-j))) := by
    simp only [A, submatrix_apply, id_eq, pairingMatrix_apply, Fin.revPerm_apply, Fin.val_rev]
    congr 2; omega
  have htri : A.IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    rw [ha, topRemainderCoefficient_pow hf (by omega)]
    rw [ite_eq_right (by omega)]
  rw [Matrix.det_of_isLowerTriangular A htri]
  have hdiag (i : Fin f.natDegree) : A i i = 1 := by
    rw [ha, topRemainderCoefficient_pow hf (by omega)]
    rw [ite_eq_left (by omega)]
  simp only [hdiag, Finset.prod_const_one]

theorem pairingMatrix_det_isUnit : IsUnit (pairingMatrix hf).det := by
  have h : IsUnit (((pairingMatrix hf).submatrix id Fin.revPerm).det) := by
    rw [pairingMatrix_reverse_det hf]
    exact isUnit_one
  rw [Matrix.det_permute'] at h
  exact isUnit_of_mul_isUnit_right h

noncomputable def coefficientPairingEquiv :
    AdjoinRoot f ≃ₗ[R] Module.Dual R (AdjoinRoot f) :=
  Matrix.toLinOfInv (AdjoinRoot.powerBasisAux' hf)
    (AdjoinRoot.powerBasisAux' hf).dualBasis
    (Matrix.mul_nonsing_inv _ (pairingMatrix_det_isUnit hf))
    (Matrix.nonsing_inv_mul _ (pairingMatrix_det_isUnit hf))

@[simp] theorem coefficientPairingEquiv_apply (a b : AdjoinRoot f) :
    coefficientPairingEquiv hf a b = topRemainderCoefficient hf (a*b) := by
  change (Matrix.toLin (AdjoinRoot.powerBasisAux' hf)
    (AdjoinRoot.powerBasisAux' hf).dualBasis (pairingMatrix hf)) a b = _
  rw [pairingMatrix, Matrix.toLin_toMatrix]
  rfl
end MonicPairing
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Module
section Colength
variable {S B A : Type*} [CommRing S] [IsDomain S] [IsPrincipalIdealRing S]
  [CommRing B] [CommRing A] [Algebra S B] [Algebra S A] [Algebra B A]
  [IsScalarTower S B A] [NoZeroSMulDivisors S A] [Module.Finite S A]

omit [IsPrincipalIdealRing S] [NoZeroSMulDivisors S A] in

theorem finrank_eq_of_denominators
    (hi : Function.Injective (algebraMap B A))
    (hden : ∀ x : A, ∃ s : S, s ≠ 0 ∧ ∃ b : B, s • x = algebraMap B A b) :
    Module.finrank S B = Module.finrank S A := by
  let i : B →ₗ[S] A := (IsScalarTower.toAlgHom S B A).toLinearMap
  have ht : Module.IsTorsion S (A ⧸ LinearMap.range i) := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨s, hs, b, hb⟩ := hden x
      refine ⟨⟨s, mem_nonZeroDivisors_iff_ne_zero.mpr hs⟩, ?_⟩
      change s • (Submodule.Quotient.mk x : A ⧸ LinearMap.range i) = 0
      rw [← Submodule.Quotient.mk_smul]
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨b, hb.symm⟩
  have hr := (LinearMap.range i).finrank_quotient_add_finrank
  rw [ht.finrank_eq_zero, zero_add] at hr
  exact (LinearEquiv.ofInjective i hi).finrank_eq.trans hr

theorem conductor_colength
    (hi : Function.Injective (algebraMap B A))
    (hden : ∀ x : A, ∃ s : S, s ≠ 0 ∧ ∃ b : B, s • x = algebraMap B A b)
    (lam : B →ₗ[S] S) (e : B ≃ₗ[S] Module.Dual S B)
    (he : ∀ a b : B, e a b = lam (a*b)) :
    Module.length S (B ⧸ (algebraConductor B A).restrictScalars S) =
      Module.length S (A ⧸ LinearMap.range
        (IsScalarTower.toAlgHom S B A).toLinearMap) := by
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
  exact eqv.length_eq.trans
    (dual_restriction_colength (Module.Free.chooseBasis S A) i hi
      (finrank_eq_of_denominators hi hden)).symm
end Colength
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Module Polynomial

theorem monic_conductor_colength
    {S : Type*} [CommRing S] [IsDomain S] [IsPrincipalIdealRing S]
    {f : S[X]} (hf : f.Monic)
    {A : Type*} [CommRing A] [Algebra S A] [Algebra (AdjoinRoot f) A]
    [IsScalarTower S (AdjoinRoot f) A] [NoZeroSMulDivisors S A] [Module.Finite S A]
    (hi : Function.Injective (algebraMap (AdjoinRoot f) A))
    (hden : ∀ x : A, ∃ s : S, s ≠ 0 ∧ ∃ b : AdjoinRoot f,
      s • x = algebraMap (AdjoinRoot f) A b) :
    Module.length S (AdjoinRoot f ⧸
        (algebraConductor (AdjoinRoot f) A).restrictScalars S) =
      Module.length S (A ⧸ LinearMap.range
        (IsScalarTower.toAlgHom S (AdjoinRoot f) A).toLinearMap) :=
  conductor_colength hi hden (topRemainderCoefficient hf) (coefficientPairingEquiv hf)
    (coefficientPairingEquiv_apply hf)
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Polynomial Module

section RootEmbedding
variable {Q L : Type*} [Field Q] [Field L] [Algebra Q L]
variable {f : Q[X]} (hf : f.Monic)

noncomputable def rootEvaluation : AdjoinRoot f →ₐ[Q] ((f.rootSet L) → L) :=
  AlgHom.pi fun x => AdjoinRoot.liftAlgHom f (Algebra.ofId Q L) x.val (aeval_eq_zero_of_mem_rootSet x.property)

@[simp] theorem rootEvaluation_mk (p : Q[X]) (x : f.rootSet L) :
    rootEvaluation (f := f) (AdjoinRoot.mk f p) x = aeval x.val p := by
  rfl

include hf in

theorem rootEvaluation_injective (hsep : f.Separable)
    (hsplit : (f.map (algebraMap Q L)).Splits) :
    Function.Injective (rootEvaluation (f := f) (L := L)) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro z hz
  let p := AdjoinRoot.modByMonicHom hf z
  have hpz : AdjoinRoot.mk f p = z := AdjoinRoot.mk_leftInverse hf z
  have hpd : p.degree < f.degree := by
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective z
    exact degree_modByMonic_lt g hf
  have hp : p = 0 := by
    by_contra hp
    have hpmap : p.map (algebraMap Q L) ≠ 0 := mt
      (fun h => Polynomial.map_injective _ (algebraMap Q L).injective (h.trans (Polynomial.map_zero _).symm)) hp
    have hc : Fintype.card (f.rootSet L) = f.natDegree := by
      exact card_rootSet_eq_natDegree hsep hsplit
    have hd : (p.map (algebraMap Q L)).natDegree < Fintype.card (f.rootSet L) := by
      rw [natDegree_map, hc]
      exact natDegree_lt_natDegree hp hpd
    apply hpmap
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (p.map (algebraMap Q L)) (f := fun x : f.rootSet L => x.val) Subtype.val_injective ?_ hd
    intro x
    have := congrFun hz x
    rw [← hpz, rootEvaluation_mk] at this
    simpa only [eval_map, aeval_def, Pi.zero_apply] using this
  rw [← hpz, hp, map_zero]
end RootEmbedding

section Normalization
variable {S Q : Type*} [CommRing S] [IsDomain S] [IsPrincipalIdealRing S]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]
variable {f : Q[X]} (hf : f.Monic) (hsep : f.Separable)

include hf hsep in

theorem finite_integralClosure_adjoinRoot :
    Module.Finite S (integralClosure S (AdjoinRoot f)) := by
  let L := f.SplittingField
  let : Algebra.IsSeparable Q L :=
    Algebra.isSeparable_of_separable_splitting_field Q L hsep
  let : Module.Finite S (integralClosure S L) :=
    IsIntegralClosure.finite S Q L (integralClosure S L)
  let ev (x : f.rootSet L) : AdjoinRoot f →ₐ[S] L :=
    (AdjoinRoot.liftAlgHom f (Algebra.ofId Q L) x.val
      (aeval_eq_zero_of_mem_rootSet x.property)).restrictScalars S
  let ι : integralClosure S (AdjoinRoot f) →ₗ[S] (f.rootSet L → integralClosure S L) :=
    { toFun := fun z x => ⟨ev x z.val, IsIntegral.map (ev x) z.property⟩
      map_add' := by intro z w; ext x; simp
      map_smul' := by intro s z; ext x; simp }
  apply Module.Finite.of_injective ι
  intro z w h
  apply Subtype.ext
  apply rootEvaluation_injective hf hsep (SplittingField.splits f)
  funext x
  exact congrArg Subtype.val (congrFun h x)
end Normalization
end PermanentBorder.Conductor

end OAI
