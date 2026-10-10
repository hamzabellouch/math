import OAI.Algebra.Determinantal.WildParameters

namespace OAI
namespace PermanentBorder.CurveFamily
open MvPolynomial Module FrobeniusPlane
open scoped Classical
variable {K : Type*} [Field K] [CharP K 2]

noncomputable def singularIdeal (f : Plane K) : Ideal (Plane K) :=
  Ideal.span {f,pderiv 0 f,pderiv 1 f}

omit [CharP K 2] in
lemma singular_zero_iff (f : Plane K) (x : Fin 2 → K) :
    x ∈ zeroLocus K (singularIdeal f) ↔
      eval x f=0 ∧ eval x (pderiv 0 f)=0 ∧ eval x (pderiv 1 f)=0 := by
  change singularIdeal f ≤ RingHom.ker (aeval x) ↔ _
  rw [singularIdeal,Ideal.span_le]
  simp only [Set.insert_subset_iff,Set.singleton_subset_iff]
  rfl

lemma singular_add_square_eq (a b c d : Plane K) :
    singularIdeal (squareForm a b c d) ⊔ Ideal.span {d^2} = Ideal.span {a^2,b^2,c^2,d^2} := by
  rw [← wild_ideal_eq, squareForm_mixed,singularIdeal,← Ideal.span_union]
  congr 1
  ext p
  simp only [Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff]
  tauto

lemma singular_wild_card_le (a b c d : Plane K)
    [Fintype (zeroLocus K (singularIdeal (squareForm a b c d)))]
    [Module.Finite K (Plane K ⧸ halfIdeal a b c d)] :
    Fintype.card {x : zeroLocus K (singularIdeal (squareForm a b c d)) // eval x.val d=0} ≤
      finrank K (Plane K ⧸ halfIdeal a b c d) := by
  classical
  let := finite_zeroLocus (halfIdeal a b c d)
  let := Fintype.ofFinite (zeroLocus K (halfIdeal a b c d))
  let v : {x : zeroLocus K (singularIdeal (squareForm a b c d)) // eval x.val d=0} →
      zeroLocus K (halfIdeal a b c d) := fun x => ⟨x.val.val,by
    have h := (singular_zero_iff _ _).mp x.val.property
    have h' := (wild_zero_iff a b c d x.val.val).mp
      ⟨h.1,h.2.1,h.2.2,by rw [squareForm_mixed,map_pow,x.property]; simp⟩
    change halfIdeal a b c d ≤ RingHom.ker (aeval x.val.val)
    rw [halfIdeal,Ideal.span_le]
    simp only [Set.insert_subset_iff,Set.singleton_subset_iff]
    exact h'⟩
  have hv : Function.Injective v := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : zeroLocus K (halfIdeal a b c d) => z.val) hxy
  exact (Fintype.card_le_of_injective v hv).trans (zero_card_le_finrank _)

lemma singular_point_card_le (a b c d : Plane K)
    [Fintype (zeroLocus K (singularIdeal (squareForm a b c d)))]
    [Module.Finite K (Plane K ⧸ halfIdeal a b c d)] :
    Fintype.card (zeroLocus K (singularIdeal (squareForm a b c d))) ≤
      finrank K (Plane K ⧸ halfIdeal a b c d) +
        Fintype.card {x : zeroLocus K (singularIdeal (squareForm a b c d)) // eval x.val d≠0} := by
  classical
  have h := singular_wild_card_le a b c d
  have he := Fintype.card_congr (Equiv.sumCompl
    (fun x : zeroLocus K (singularIdeal (squareForm a b c d)) => eval x.val d=0))
  rw [Fintype.card_sum] at he
  simp only [ne_eq] at *
  omega

theorem singular_enlarged_length [IsAlgClosed K] [PerfectRing K 2]
    (a b c d : Plane K)
    [Fintype (zeroLocus K (singularIdeal (squareForm a b c d)))]
    [Module.Finite K (Plane K ⧸ halfIdeal a b c d)] :
    let I := singularIdeal (squareForm a b c d)
    Module.length K (Plane K ⧸ (I ⊔ Ideal.span {d^2}*I.radical)) ≤
      (5*finrank K (Plane K ⧸ halfIdeal a b c d) +
        Fintype.card {x : zeroLocus K I // eval x.val d≠0} : ℕ) := by
  intro I
  have hF := frobenius_quotient_bound (halfIdeal a b c d) (I ⊔ Ideal.span {d^2}) (by
    intro p hp
    rw [singular_add_square_eq]
    simpa only [Set.image_insert_eq,Set.image_singleton] using
      square_mem_of_mem_span {a,b,c,d} hp)
  obtain ⟨hfinite,hbound⟩ := hF
  let := hfinite
  have hrad := radical_length_eq_zero_card I
  have hpoint := singular_point_card_le a b c d
  calc
    _ ≤ Module.length K (Plane K ⧸ (I ⊔ Ideal.span {d^2})) +
        Module.length K (Plane K ⧸ I.radical) :=
      IdealColength.quotient_product_length I I.radical (d^2)
    _ = (finrank K (Plane K ⧸ (I ⊔ Ideal.span {d^2})) +
        Fintype.card (zeroLocus K I) : ℕ) := by rw [Module.length_eq_finrank,hrad]; simp
    _ ≤ _ := by exact_mod_cast (show finrank K (Plane K ⧸ (I ⊔ Ideal.span {d^2})) +
        Fintype.card (zeroLocus K I) ≤ _ by
          dsimp [I] at *
          omega)

end PermanentBorder.CurveFamily

namespace PermanentBorder.PlaneBivariate
open Polynomial MvPolynomial
variable (K : Type*) [Field K]

noncomputable def toBivariate : MvPolynomial (Fin 2) K →ₐ[K] K[X][X] :=
  aeval ![Polynomial.C Polynomial.X,Polynomial.X]

noncomputable def fromBivariate : K[X][X] →ₐ[K] MvPolynomial (Fin 2) K :=
  Polynomial.eval₂AlgHom (Polynomial.aeval (X 0)) (X 1) (fun _ => Commute.all _ _)

@[simp] lemma to_zero : toBivariate K (X 0)=Polynomial.C Polynomial.X := by simp [toBivariate]
@[simp] lemma to_one : toBivariate K (X 1)=Polynomial.X := by simp [toBivariate]
@[simp] lemma to_C (c : K) : toBivariate K (C c)=Polynomial.C (Polynomial.C c) := by
  simp [toBivariate]
@[simp] lemma from_X : fromBivariate K Polynomial.X=X 1 := by simp [fromBivariate]
@[simp] lemma from_C_X : fromBivariate K (Polynomial.C Polynomial.X)=X 0 := by simp [fromBivariate]
@[simp] lemma from_C_C (c : K) : fromBivariate K (Polynomial.C (Polynomial.C c))=MvPolynomial.C c := by
  simp [fromBivariate]

lemma from_to : (fromBivariate K).comp (toBivariate K) = AlgHom.id K _ := by
  ext i
  fin_cases i <;> simp

lemma to_from : (toBivariate K).comp (fromBivariate K) = AlgHom.id K _ := by
  apply Polynomial.algHom_ext'
  · apply Polynomial.algHom_ext
    simp
  · simp

noncomputable def equiv : MvPolynomial (Fin 2) K ≃ₐ[K] K[X][X] :=
  AlgEquiv.ofAlgHom (toBivariate K) (fromBivariate K) (to_from K) (from_to K)

@[simp] lemma equiv_apply (p : MvPolynomial (Fin 2) K) : equiv K p=toBivariate K p := rfl
@[simp] lemma equiv_symm_apply (p : K[X][X]) : (equiv K).symm p=fromBivariate K p := rfl

lemma derivative_to (p : MvPolynomial (Fin 2) K) :
    Polynomial.derivative (toBivariate K p) = toBivariate K (pderiv 1 p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp =>
    rw [map_mul,Polynomial.derivative_mul,pderiv_mul,map_add,map_mul]
    fin_cases i <;> simp [hp]

lemma map_to {L : Type*} [Field L] [Algebra K L] (p : MvPolynomial (Fin 2) K) :
    toBivariate L (p.map (algebraMap K L)) =
      (toBivariate K p).map (Polynomial.mapRingHom (algebraMap K L)) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add,Polynomial.map_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,Polynomial.map_mul,MvPolynomial.map_X,hp]
    fin_cases i <;> simp

end PermanentBorder.PlaneBivariate

namespace PermanentBorder.PlaneScaling
open Polynomial MvPolynomial
variable {K σ : Type*} [Field K]

noncomputable def scale : MvPolynomial σ K →ₐ[K] (MvPolynomial σ K)[X] :=
  MvPolynomial.aeval (fun i => Polynomial.C (MvPolynomial.X i)*Polynomial.X)

lemma scale_monomial (s : σ →₀ ℕ) (c : K) :
    scale (MvPolynomial.monomial s c) =
      Polynomial.monomial s.degree (MvPolynomial.monomial s c) := by
  classical
  simp only [scale,MvPolynomial.aeval_def,MvPolynomial.eval₂_monomial,
    mul_pow,Finsupp.prod,Finset.prod_mul_distrib,← map_pow,← map_prod,
    Finset.prod_pow_eq_pow_sum,← Polynomial.C_mul_X_pow_eq_monomial]
  change Polynomial.C (MvPolynomial.C c) * (Polynomial.C _ * Polynomial.X ^ s.degree) = _
  rw [← mul_assoc,← map_mul]
  simp only [MvPolynomial.monomial_eq,Finsupp.prod]

lemma coeff_scale (p : MvPolynomial σ K) (n : ℕ) :
    (scale p).coeff n = homogeneousComponent n p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [scale_monomial,Polynomial.coeff_monomial]
    ext t
    simp only [coeff_homogeneousComponent,apply_ite,MvPolynomial.coeff_monomial,
      AddMonoidAlgebra.coeff_zero]
    split_ifs <;> simp_all
    rintro rfl
    contradiction
  | add p q hp hq => simp only [map_add,Polynomial.coeff_add,hp,hq]

lemma degree_le_of_scale (p : MvPolynomial σ K) (n : ℕ)
    (h : (scale p).natDegree ≤ n) : p.totalDegree ≤ n := by
  classical
  apply Finset.sup_le
  intro s hs
  change s.degree ≤ n
  by_contra hn
  have hz : homogeneousComponent s.degree p=0 := by
    rw [← coeff_scale]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have he := congrArg (fun polynomial : MvPolynomial σ K => polynomial.coeff s) hz
  simp only [coeff_homogeneousComponent,ite_true,AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply] at he
  exact (MvPolynomial.mem_support_iff.mp hs) he

end PermanentBorder.PlaneScaling

namespace PermanentBorder.Conductor
open Polynomial Module
variable {K S : Type*} [Field K] [CommRing S] [IsDomain S]
  [IsPrincipalIdealRing S] [Algebra K S]

theorem normalization_length_le_ideal (f : S[X]) (hf : f.Monic)
    (hsep : (f.map (algebraMap S (FractionRing S))).Separable) (J : Ideal S[X])
    (hJ : ∀ z ∈ J, ∀ t : AdjoinRoot (f.map (algebraMap S (FractionRing S))), IsIntegral S t →
      ∃ q : S[X], AdjoinRoot.mk _ (q.map (algebraMap S (FractionRing S))) =
        AdjoinRoot.mk _ (z.map (algebraMap S (FractionRing S)))*t) :
    let R := integralClosure S (AdjoinRoot (f.map (algebraMap S (FractionRing S))))
    Module.length K (R ⧸ LinearMap.range
      (normalizationInclusion (Q := FractionRing S) f hf).toLinearMap) ≤ Module.length K (S[X] ⧸ J) := by
  let R := integralClosure S (AdjoinRoot (f.map (algebraMap S (FractionRing S))))
  let := (normalizationInclusion (Q := FractionRing S) f hf).toRingHom.toAlgebra
  let c := (algebraConductor (AdjoinRoot f) R).restrictScalars S
  let g : S[X] →ₗ[K] (AdjoinRoot f ⧸ c) :=
    (c.mkQ.restrictScalars K).comp ((AdjoinRoot.mkₐ f).toLinearMap.restrictScalars K)
  have hg : Function.Surjective g := c.mkQ_surjective.comp AdjoinRoot.mk_surjective
  have hker : J.restrictScalars K ≤ g.ker := by
    intro z hz
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change AdjoinRoot.mk f z ∈ algebraConductor (AdjoinRoot f) R
    intro t
    obtain ⟨q,hq⟩ := hJ z hz t.val t.property
    refine ⟨AdjoinRoot.mk f q,?_⟩
    apply Subtype.ext
    change genericBaseChange (Q := FractionRing S) f (AdjoinRoot.mk f q) =
      genericBaseChange (Q := FractionRing S) f (AdjoinRoot.mk f z)*t.val
    simpa only [genericBaseChange_mk] using hq
  let v := (J.restrictScalars K).liftQ g hker
  have hv : Function.Surjective v := by
    intro y
    obtain ⟨z,hz⟩ := hg y
    exact ⟨Ideal.Quotient.mk J z,hz⟩
  obtain ⟨e⟩ := exists_normalization_conductor_cokernel_equiv hf hsep
  calc
    _ = Module.length K (AdjoinRoot f ⧸ c) := (e.restrictScalars K).length_eq.symm
    _ ≤ Module.length K (S[X] ⧸ J) := Module.length_le_of_surjective v hv

theorem normalization_length_le_enlarged [CharP S 2]
    (δ : Derivation K S S) (x : S) (hx : δ x = 1)
    (hres : ∀ (P : Ideal S) [P.IsMaximal], IsAlgClosed P.ResidueField)
    (f a b c d : S[X]) (hf : f.Monic)
    (hsep : (f.map (algebraMap S (FractionRing S))).Separable)
    (hsq : f=a^2+C x*b^2+X*c^2+C x*X*d^2)
    (hder : f.derivative=c^2+C x*d^2) :
    let R := integralClosure S (AdjoinRoot (f.map (algebraMap S (FractionRing S))))
    Module.length K (R ⧸ LinearMap.range
      (normalizationInclusion (Q := FractionRing S) f hf).toLinearMap) ≤
      Module.length K (S[X] ⧸ ReducedBranchConductor.enlargedGradientIdeal f b c d x) := by
  apply normalization_length_le_ideal f hf hsep
  intro z hz t ht
  exact ReducedBranchConductor.reduced_global_realization δ x hx hres f a b c d hf hsep
    hsq hder z hz t ht

end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Polynomial MvPolynomial Module
open FrobeniusPlane CurveFamily PlaneBivariate
open scoped Classical
variable {K : Type*} [Field K] [CharP K 2]

omit [CharP K 2] in
lemma equiv_ring_apply (p : Plane K) : (equiv K).toRingHom p = toBivariate K p := rfl

lemma map_singularIdeal (a b c d : Plane K) :
    (singularIdeal (squareForm a b c d)).map (equiv K).toRingHom =
      ReducedBranchConductor.gradientIdeal (toBivariate K (squareForm a b c d))
        (toBivariate K b) (toBivariate K c) (toBivariate K d) Polynomial.X := by
  rw [singularIdeal,Ideal.map_span]
  simp only [squareForm_partial_zero,squareForm_partial_one,
    Set.image_insert_eq,Set.image_singleton,equiv_ring_apply,map_add,map_mul,map_pow,to_zero,to_one,
    ReducedBranchConductor.gradientIdeal]

lemma map_enlargedIdeal (a b c d : Plane K) :
    (singularIdeal (squareForm a b c d) ⊔ Ideal.span {d^2}*
      (singularIdeal (squareForm a b c d)).radical).map (equiv K).toRingHom =
      ReducedBranchConductor.enlargedGradientIdeal (toBivariate K (squareForm a b c d))
        (toBivariate K b) (toBivariate K c) (toBivariate K d) Polynomial.X := by
  rw [Ideal.map_sup,Ideal.map_mul,Ideal.map_radical_of_surjective
      (show Function.Surjective (equiv K).toRingHom from (equiv K).surjective)
      (by rw [(RingHom.injective_iff_ker_eq_bot (equiv K).toRingHom).mp (equiv K).injective]; exact bot_le),
    map_singularIdeal,ReducedBranchConductor.enlargedGradientIdeal,Ideal.map_span]
  simp only [Set.image_singleton,map_pow,equiv_ring_apply]

theorem normalization_length_le_half [IsAlgClosed K] [PerfectRing K 2]
    (a b c d : Plane K)
    (hf : (toBivariate K (squareForm a b c d)).Monic)
    (hsep : ((toBivariate K (squareForm a b c d)).map
      (algebraMap K[X] (FractionRing K[X]))).Separable)
    [Fintype (zeroLocus K (singularIdeal (squareForm a b c d)))]
    [Module.Finite K (Plane K ⧸ halfIdeal a b c d)] :
    let f := toBivariate K (squareForm a b c d)
    let R := integralClosure K[X] (AdjoinRoot (f.map (algebraMap K[X] (FractionRing K[X]))))
    Module.length K (R ⧸ LinearMap.range
      (normalizationInclusion (Q := FractionRing K[X]) f hf).toLinearMap) ≤
      (5*finrank K (Plane K ⧸ halfIdeal a b c d) +
        Fintype.card {x : zeroLocus K (singularIdeal (squareForm a b c d)) // eval x.val d≠0} : ℕ) := by
  let f := toBivariate K (squareForm a b c d)
  let I := singularIdeal (squareForm a b c d)
  let J := I ⊔ Ideal.span {d^2}*I.radical
  let e := Ideal.quotientEquivAlg (R₁ := K) J
    (ReducedBranchConductor.enlargedGradientIdeal f (toBivariate K b) (toBivariate K c)
      (toBivariate K d) Polynomial.X) (equiv K) (map_enlargedIdeal a b c d).symm
  have hu := normalization_length_le_enlarged (Polynomial.derivative' : Derivation K K[X] K[X]) Polynomial.X
    (by simp) (ReducedBranchConductor.polynomial_residue_algClosed (K := K))
    f (toBivariate K a) (toBivariate K b) (toBivariate K c) (toBivariate K d) hf hsep
    (by simp [f,squareForm]) (by
      rw [derivative_to,squareForm_partial_one]
      simp)
  exact hu.trans (e.toLinearEquiv.length_eq.symm.le.trans (singular_enlarged_length a b c d))

end PermanentBorder.Conductor

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert FrobeniusPlane
open scoped Classical
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

lemma inField_squareForm (E : IntermediateField K L) {a b c d : Plane L}
    (ha : InField E a) (hb : InField E b) (hc : InField E c) (hd : InField E d) :
    InField E (squareForm a b c d) := by
  obtain ⟨a₀,rfl⟩ := inField_lift E ha
  obtain ⟨b₀,rfl⟩ := inField_lift E hb
  obtain ⟨c₀,rfl⟩ := inField_lift E hc
  obtain ⟨d₀,rfl⟩ := inField_lift E hd
  intro s
  have he : squareForm (MvPolynomial.map E.val.toRingHom a₀) (MvPolynomial.map E.val.toRingHom b₀)
      (MvPolynomial.map E.val.toRingHom c₀) (MvPolynomial.map E.val.toRingHom d₀) =
      (squareForm a₀ b₀ c₀ d₀).map E.val.toRingHom := by simp [squareForm]
  rw [he,coeff_map]
  exact ((squareForm a₀ b₀ c₀ d₀).coeff s).property

lemma singular_finite (f : Plane L) {k : ℕ} (hk : 1 ≤ k)
    (hf : f.totalDegree ≤ k) (hlead : homogeneousComponent k f ≠ 0)
    (hpartial : pderiv 1 (homogeneousComponent k f) ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent k f) (pderiv 1 (homogeneousComponent k f))) :
    Module.Finite L (Plane L ⧸ singularIdeal f) := by
  let q := Ideal.Quotient.mkₐ L (singularIdeal f)
  have he : homogeneousComponent (k-1) (pderiv 1 f)=pderiv 1 (homogeneousComponent k f) := by
    simpa only [Nat.sub_add_cancel hk] using partial_leading f (k-1) 1
  have hfq : q f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hdq : q (pderiv 1 f) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hdeg : (pderiv 1 f).totalDegree ≤ k-1 :=
    partial_degree (by rwa [Nat.sub_add_cancel hk]) 1
  exact (finite_of_leading_pair q Ideal.Quotient.mk_surjective hf hdeg hfq hdq hlead
    (by rwa [he]) (by rwa [he]) (B := k-1) (by omega) (by omega) (by omega)).1

variable [CharP L 2]

theorem ordinary_parameter_bound {a b c d : Plane L} {k R : ℕ}
    (hk : 1 ≤ k) (hR : k-1 ≤ 2*R)
    (hf : (squareForm a b c d).totalDegree ≤ k)
    (hlead : homogeneousComponent k (squareForm a b c d) ≠ 0)
    (hpartial : pderiv 1 (homogeneousComponent k (squareForm a b c d)) ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent k (squareForm a b c d))
      (pderiv 1 (homogeneousComponent k (squareForm a b c d))))
    (B : Fin 3 → ℕ) (t : Fin 4 → Plane K)
    (h₀ : ∀ s, R ≤ s.degree → a.coeff s=algebraMap K L ((t 0).coeff s))
    (h : ∀ i s, B i ≤ s.degree → (![b,c,d] i).coeff s=algebraMap K L ((t i.succ).coeff s))
    [Fintype (zeroLocus L (singularIdeal (squareForm a b c d)))] :
    ∃ (E : IntermediateField K L) (n : ℕ), InField E (squareForm a b c d) ∧
      Algebra.trdeg K E ≤ (n : Cardinal) ∧
      8*n+Fintype.card {x : zeroLocus L (singularIdeal (squareForm a b c d)) // eval x.val d≠0} ≤
        8*(Fintype.card (Index R)+∑ i, Fintype.card (Index (B i))) := by
  let ι := {x : zeroLocus L (singularIdeal (squareForm a b c d)) // eval x.val d≠0}
  let x : ι → Fin 2 → L := fun z => z.val.val
  have hx : Function.Injective x := by
    intro z w hzw
    exact Subtype.ext (Subtype.ext hzw)
  have hsing (i : ι) := (singular_zero_iff _ _).mp i.val.property
  obtain ⟨E,n,ha,hb,hc,hd,hE,hn⟩ := node_parameter_bound x a b c d R B (t 0)
    (fun i => t i.succ) h₀ h (fun i => i.property)
    (fun i => by simpa only [squareForm_partial_zero,map_add,map_mul,map_pow,eval_X] using (hsing i).2.1)
    (fun i => by simpa only [squareForm_partial_one,map_add,map_mul,map_pow,eval_X] using (hsing i).2.2)
    (fun i => by simpa only [squareForm,map_add,map_mul,map_pow,eval_X] using (hsing i).1)
  have hcount := distinct_critical_point_count x hx (squareForm a b c d) k R hk hR hf hlead
    hpartial hcop (fun i => (hsing i).1) (fun i => (hsing i).2.2)
  refine ⟨E,n,inField_squareForm E ha hb hc hd,hE,?_⟩
  have hecard : Fintype.card {z : zeroLocus L (singularIdeal (squareForm a b c d)) // eval z.val d≠0} =
      Fintype.card ι := Fintype.card_congr (Equiv.refl _)
  rw [hecard]
  calc
    _ ≤ 8*n+8*finrank L (filtered (pointEvaluation x) R) := Nat.add_le_add_left hcount _
    _ = 8*(n+finrank L (filtered (pointEvaluation x) R)) := by omega
    _ ≤ _ := Nat.mul_le_mul_left 8 hn

end PermanentBorder.CurveFamily

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert FrobeniusPlane
open scoped Classical
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [CharP L 2]

lemma halfIdeal_finite {a b c d : Plane L} {k : ℕ} (hk : 4 ≤ k)
    (hf : (squareForm a b c d).totalDegree ≤ k)
    (hs : Squarefree (homogeneousComponent k (squareForm a b c d))) :
    Module.Finite L (Plane L ⧸ halfIdeal a b c d) := by
  have hrep : ∃ r, k=2*r ∨ k=2*r+1 := ⟨k/2,by omega⟩
  obtain ⟨r,h|h⟩ := hrep
  · subst k
    exact (halfIdeal_even_finite (by omega) hf hs).1
  · subst k
    exact (halfIdeal_odd_finite (by omega) hf hs).1

lemma ordinary_even_count (r : ℕ) :
    2*(Fintype.card (Index r)+∑ i : Fin 3, Fintype.card (Index (![r,r,r-1] i))) =
      (2*r)*(2*r+1) := by
  have h := even_count r
  simp only [LowPlane.card_index,Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.isValue,
    Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero] at h ⊢
  omega

lemma ordinary_odd_count (r : ℕ) :
    2*(Fintype.card (Index (r+1))+∑ _i : Fin 3, Fintype.card (Index (r))) =
      (2*r+1)*(2*r+2) := by
  have h := odd_count r
  simp only [LowPlane.card_index,Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.isValue,
    Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero] at h ⊢
  omega

variable [CharP K 2] [PerfectRing K 2] [Infinite K] [IsAlgClosed L]

theorem half_curve_parameter_bound {a b c d : Plane L} {k : ℕ}
    (hk : 4 ≤ k) (hf : (squareForm a b c d).totalDegree ≤ k)
    (hs : Squarefree (homogeneousComponent k (squareForm a b c d)))
    (hlead : homogeneousComponent k (squareForm a b c d) ≠ 0)
    (hpartial : pderiv 1 (homogeneousComponent k (squareForm a b c d)) ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent k (squareForm a b c d))
      (pderiv 1 (homogeneousComponent k (squareForm a b c d))))
    (H : Plane K) (hH : H.IsHomogeneous k)
    (he : homogeneousComponent k (squareForm a b c d)=H.map (algebraMap K L))
    [Fintype (zeroLocus L (singularIdeal (squareForm a b c d)))] :
    ∃ (E : IntermediateField K L) (n : ℕ), InField E (squareForm a b c d) ∧
      Algebra.trdeg K E ≤ (n : Cardinal) ∧
      18*n+5*finrank L (Plane L ⧸ halfIdeal a b c d) +
        Fintype.card {x : zeroLocus L (singularIdeal (squareForm a b c d)) // eval x.val d≠0} ≤
          9*(k*(k+1)) := by
  have hrep : ∃ r, k=2*r ∨ k=2*r+1 := ⟨k/2,by omega⟩
  obtain ⟨r,h|h⟩ := hrep
  · subst k
    obtain ⟨t,ht⟩ := fixed_half_forms_even (by omega) hf H hH he
    obtain ⟨E,nw,ha,hb,hc,hd,hE,hw⟩ := wild_parameter_bound_even (by omega) hf hs t ht
    obtain ⟨F,nn,hfF,hF,hn⟩ := ordinary_parameter_bound (R := r) (by omega) (by omega) hf hlead hpartial hcop
      ![r,r,r-1] t (ht 0) (by intro _i; fin_cases _i; exact ht 1; exact ht 2; exact ht 3)
    have hcount := ordinary_even_count r
    by_cases hmin : nw≤nn
    · exact ⟨E,nw,inField_squareForm E ha hb hc hd,hE,by omega⟩
    · exact ⟨F,nn,hfF,hF,by omega⟩
  · subst k
    obtain ⟨t,ht⟩ := fixed_half_forms_odd (by omega) hf H hH he
    obtain ⟨E,nw,ha,hb,hc,hd,hE,hw⟩ := wild_parameter_bound_odd (by omega) hf hs t ht
    obtain ⟨F,nn,hfF,hF,hn⟩ := ordinary_parameter_bound (R := r+1) (by omega) (by omega) hf hlead hpartial hcop
      (fun _ : Fin 3 => r) t (ht 0) (by intro _i; fin_cases _i; exact ht 1; exact ht 2; exact ht 3)
    have hcount := ordinary_odd_count r
    by_cases hmin : nw≤nn
    · exact ⟨E,nw,inField_squareForm E ha hb hc hd,hE,by
        have hsimp : 2*r+1+1=2*r+2 := by omega
        rw [hsimp]
        omega⟩
    · exact ⟨F,nn,hfF,hF,by
        have hsimp : 2*r+1+1=2*r+2 := by omega
        rw [hsimp]
        omega⟩

end PermanentBorder.CurveFamily

end OAI
