import Mathlib
import OAI.Algebra.FiniteTensor.KernelRelations

namespace OAI

/-! Finite generic minor reductions and polynomial Artin approximation from minors. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading
noncomputable section
open MvPolynomial

 theorem eval_sum_parameters {R L σ ι : Type*} [CommRing R] [CommRing L]
    (c : R →+* L) (a : σ → L) (x : ι → L)
    (q : MvPolynomial (σ ⊕ ι) R) :
    eval₂ c (Sum.elim a x) q=
      eval₂ (eval₂Hom c x) a (sumAlgEquiv R σ ι q) := by
  induction q using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add,eval₂_add,hp,hq]
  | mul_X p i hp => cases i <;> simp [hp]

 theorem eval_sum_parameters_symm {R L σ ι : Type*} [CommRing R] [CommRing L]
    (c : R →+* L) (a : σ → L) (x : ι → L)
    (q : MvPolynomial σ (MvPolynomial ι R)) :
    eval₂ c (Sum.elim a x) ((sumAlgEquiv R σ ι).symm q)=eval₂ (eval₂Hom c x) a q := by
  rw [eval_sum_parameters,AlgEquiv.apply_symm_apply]

 theorem pderiv_sum_symm {R σ ι : Type*} [CommRing R]
    (q : MvPolynomial σ (MvPolynomial ι R)) (i : σ) :
    pderiv (Sum.inl i) ((sumAlgEquiv R σ ι).symm q)=
      (sumAlgEquiv R σ ι).symm (pderiv i q) := by
  apply (sumAlgEquiv R σ ι).injective
  rw [←pderiv_sumAlgEquiv,AlgEquiv.apply_symm_apply,AlgEquiv.apply_symm_apply]

 theorem sum_symm_map_C {R σ ι : Type*} [CommRing R] (g : MvPolynomial σ R) :
    (sumAlgEquiv R σ ι).symm (map MvPolynomial.C g)=rename Sum.inl g := by
  induction g using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp => simp [hp]

 

theorem finite_generic_minor_reduction {R L σ : Type*} [CommRing R] [IsDomain R]
    [CharZero R] [Field L] [Algebra R L] [FaithfulSMul R L]
    [Fintype σ] [DecidableEq σ] (a : σ → L) :
    ∃ s : Set L,s.Finite ∧ s⊆Set.range a ∧
      ∃ f : σ → MvPolynomial (σ ⊕ s) R,
        (∀ k,MvPolynomial.aeval (Sum.elim a ((↑) : s → L)) (f k)=0) ∧
        Matrix.det (fun k i=>MvPolynomial.aeval (Sum.elim a ((↑) : s → L))
          (pderiv (Sum.inl i) (f k)))≠0 ∧
        ∀ g : MvPolynomial σ R,MvPolynomial.aeval a g=0 →
          ∃ (n : ℕ) (H : MvPolynomial (σ ⊕ s) R),0<n ∧
            MvPolynomial.aeval (Sum.elim a ((↑) : s → L)) H≠0 ∧
            H*(rename Sum.inl g)^n∈Ideal.span (Set.range f) := by
  classical
  let K := FractionRing R
  let : Algebra K L := FractionRing.liftAlgebra R L
  let : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  obtain ⟨s,hs⟩ := (AlgebraicIndependent.matroid K L).exists_isBasis (Set.range a)
  obtain ⟨hind,hsub,halg⟩ := AlgebraicIndependent.matroid_isBasis_iff.mp hs
  have hfin : s.Finite := (Set.finite_range a).subset hsub
  let x : s → L := Subtype.val
  have hx : AlgebraicIndependent K x := hind
  have hxR : AlgebraicIndependent R x := hx.restrictScalars (IsFractionRing.injective R K)
  let B := MvPolynomial s R
  let : Algebra B L := (MvPolynomial.aeval (R:=R) x).toRingHom.toAlgebra
  let : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective B L).mpr hxR
  have ha (i : σ) : IsAlgebraic B (a i) := by
    have hai : IsAlgebraic (Algebra.adjoin K (Set.range x)) (a i) := by
      have hr : Set.range x=s := by
        ext y
        constructor
        · rintro ⟨z,rfl⟩
          exact z.property
        · intro hy
          exact ⟨⟨y,hy⟩,rfl⟩
      rw [hr]
      exact halg (a i) (Set.mem_range_self i)
    obtain ⟨P,hP,hPa⟩ := polynomial_parameter_algebraicity x (a i) hx hai
    exact ⟨P,hP,hPa⟩
  choose P hP hroot hder using fun i=>exists_relation_derivative_ne_zero
    (FaithfulSMul.algebraMap_injective B L) (a i) (ha i)
  let E := sumAlgEquiv R σ s
  let q := fun i=>Polynomial.aeval (MvPolynomial.X i : MvPolynomial σ B) (P i)
  let f := fun i=>E.symm (q i)
  have he (p : MvPolynomial σ B) :
      MvPolynomial.aeval (R:=R) (Sum.elim a x) (E.symm p)=MvPolynomial.aeval (R:=B) a p :=
    eval_sum_parameters_symm (algebraMap R L) a x p
  have hf (i : σ) : MvPolynomial.aeval (R:=R) (Sum.elim a x) (f i)=0 := by
    rw [he]
    change MvPolynomial.aeval (R:=B) a (Polynomial.aeval (MvPolynomial.X i) (P i))=0
    rw [←Polynomial.aeval_algHom_apply]
    simpa using hroot i
  have hd : Matrix.det (fun k i=>MvPolynomial.aeval (R:=R) (Sum.elim a x)
      (pderiv (Sum.inl i) (f k)))≠0 := by
    have hm (k i : σ) : MvPolynomial.aeval (R:=R) (Sum.elim a x)
        (pderiv (Sum.inl i) (f k))=MvPolynomial.aeval (R:=B) a (pderiv i (q k)) := by
      change MvPolynomial.aeval (R:=R) (Sum.elim a x)
        (pderiv (Sum.inl i) (E.symm (q k)))=_
      rw [pderiv_sum_symm,he]
    simp_rw [hm]
    exact diagonal_relation_det_ne_zero a P hder
  refine ⟨s,hfin,hsub,f,hf,hd,?_⟩
  intro g hg
  let g' : MvPolynomial σ B := map MvPolynomial.C g
  have hg' : MvPolynomial.aeval (R:=B) a g'=0 := by
    change eval₂ (MvPolynomial.aeval (R:=R) x).toRingHom a (map MvPolynomial.C g)=0
    rw [eval₂_map]
    have hc : (MvPolynomial.aeval (R:=R) x).toRingHom.comp MvPolynomial.C=algebraMap R L := by
      ext r
      simp
    rw [hc]
    exact hg
  obtain ⟨n,H,hn,hH,hHI⟩ := nonmonic_diagonal_kernel_power_mem a P hP hroot g' hg'
  refine ⟨n,E.symm H,hn,by rw [he]; exact hH,?_⟩
  have hi := Ideal.mem_map_of_mem E.symm.toRingHom hHI
  have hm : (Ideal.span (Set.range q)).map E.symm.toRingHom=Ideal.span (Set.range f) := by
    rw [Ideal.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨z,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨q i,⟨i,rfl⟩,rfl⟩
  change E.symm (H*g'^n)∈(Ideal.span (Set.range q)).map E.symm.toRingHom at hi
  rw [hm,map_mul,map_pow] at hi
  have hgflat : E.symm g'=rename Sum.inl g := sum_symm_map_C g
  rwa [hgflat] at hi

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPolynomial

 

theorem finite_generic_domain_reduction {R A σ : Type*} [CommRing R] [IsDomain R]
    [CharZero R] [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A]
    [Fintype σ] [DecidableEq σ] (a : σ → A) :
    ∃ (s : Set (FractionRing A)) (_ : s.Finite) (c : s → A),
      (∀ j, ∃ i,c j=a i) ∧
      ∃ f : σ → MvPolynomial (σ ⊕ s) R,
        (∀ k,MvPolynomial.aeval (Sum.elim a c) (f k)=0) ∧
        Matrix.det (fun k i=>MvPolynomial.aeval (Sum.elim a c)
          (pderiv (Sum.inl i) (f k)))≠0 ∧
        ∀ g : MvPolynomial σ R,MvPolynomial.aeval a g=0 →
          ∃ (n : ℕ) (H : MvPolynomial (σ ⊕ s) R),0<n ∧
            MvPolynomial.aeval (Sum.elim a c) H≠0 ∧
            H*(rename Sum.inl g)^n∈Ideal.span (Set.range f) := by
  classical
  let L := FractionRing A
  let j : A →+* L := algebraMap A L
  have hj : Function.Injective j := IsFractionRing.injective A L
  let : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr
    (by
      intro r t h
      apply FaithfulSMul.algebraMap_injective R A
      apply hj
      simpa only [j,←IsScalarTower.algebraMap_apply R A L] using h)
  obtain ⟨s,hs,hsub,f,hf,hd,hg⟩ := finite_generic_minor_reduction (R:=R) (fun i=>j (a i))
  have hpre (v : s) : ∃ i,j (a i)=(v : L) := hsub v.property
  choose t ht using hpre
  let c : s → A := fun v=>a (t v)
  have he (q : MvPolynomial (σ ⊕ s) R) :
      j (MvPolynomial.aeval (R:=R) (Sum.elim a c) q)=
        MvPolynomial.aeval (R:=R) (Sum.elim (fun i=>j (a i)) ((↑) : s → L)) q := by
    change j (eval₂ (algebraMap R A) (Sum.elim a c) q)=_
    rw [hom_eval₂]
    congr 1
    funext v
    cases v with
    | inl i => rfl
    | inr v => exact ht v
  refine ⟨s,hs,c,fun v=>⟨t v,rfl⟩,f,?_,?_,?_⟩
  · intro k
    apply hj
    rw [he,hf,map_zero]
  · intro hz
    apply hd
    have hmap := RingHom.map_det j (fun k i=>MvPolynomial.aeval (R:=R)
      (Sum.elim a c) (pderiv (Sum.inl i) (f k)))
    rw [hz,map_zero] at hmap
    change 0=Matrix.det (fun k i=>j (MvPolynomial.aeval (R:=R)
      (Sum.elim a c) (pderiv (Sum.inl i) (f k)))) at hmap
    simpa only [he] using hmap.symm
  · intro g hzero
    have hzeroL : MvPolynomial.aeval (R:=R) (fun i=>j (a i)) g=0 := by
      change eval₂ (algebraMap R L) (fun i=>j (a i)) g=0
      have h := congrArg j hzero
      rw [map_zero] at h
      change j (eval₂ (algebraMap R A) a g)=0 at h
      rw [hom_eval₂] at h
      simpa only [j,←IsScalarTower.algebraMap_eq R A L] using h
    obtain ⟨n,H,hn,hH,hI⟩ := hg g hzeroL
    refine ⟨n,H,hn,?_,hI⟩
    intro hz
    apply hH
    rw [←he,hz,map_zero]

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPolynomial
variable {K τ : Type*} [Field K] [CharZero K] [Finite τ]

def MinorArtinAt (K τ : Type*) [Field K] [Finite τ] : Prop :=
  ∀ (σ ρ : Type) [Fintype σ] [DecidableEq σ] [Fintype ρ] [DecidableEq ρ]
    (f : σ → MvPolynomial (σ ⊕ ρ) (MvPolynomial τ K))
    (a : (σ ⊕ ρ) → MvPowerSeries τ K),
    (∀ k,aeval a (f k)=0) →
    Matrix.det (fun k i=>aeval a (pderiv (Sum.inl i) (f k)))≠0 →
    ∀ n,∃ b : (σ ⊕ ρ) → MvPowerSeries τ K,
      (∀ k,aeval b (f k)=0) ∧
      (∀ i,IsAlgebraic (MvPolynomial τ K) (b i)) ∧
      ∀ i,b i-a i∈(jetIdeal (K:=K) (σ:=τ))^n

 

theorem polynomial_artin_of_minor (hm : MinorArtinAt K τ) : PolynomialArtinAt K τ := by
  intro m r g a ha n
  let R := MvPolynomial τ K
  let A := MvPowerSeries τ K
  let : IsDomain A := NoZeroDivisors.to_isDomain _
  let : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr (by
    intro p q h
    apply MvPolynomial.coe_injective
    change (algebraMap (MvPolynomial τ K) (MvPowerSeries τ K)) p=(algebraMap (MvPolynomial τ K) (MvPowerSeries τ K)) q at h
    simpa only [MvPowerSeries.algebraMap_apply', Algebra.algebraMap_self, MvPowerSeries.map_id, RingHom.id_apply] using h)
  obtain ⟨s,hs,c,hc,f,hf,hd,hker⟩ := finite_generic_domain_reduction (R:=R) a
  let : Finite s := hs.to_subtype
  let := Fintype.ofFinite s
  let : DecidableEq s := Classical.decEq _
  let a' := Sum.elim a c
  choose e H he hH hI using fun k=>hker (g k) (ha k)
  let N := max n (Finset.univ.sup fun k=>((aeval a' (H k) : A).order.toNat+1))
  
  
  let t := Fintype.equivFin s
  let v : Fin m ⊕ s ≃ Fin m ⊕ Fin (Fintype.card s) := Equiv.sumCongr (Equiv.refl _) t
  let f' := fun k=>rename v (f k)
  let a'' := fun i=>a' (v.symm i)
  have hev (q : MvPolynomial (Fin m ⊕ s) R) : aeval a'' (rename v q)=aeval a' q := by
    simp only [aeval_rename]
    have he : a'' ∘ v=a' := by funext i; simp [a'']
    rw [he]
  have hfd (k i : Fin m) : pderiv (Sum.inl i) (f' k)=rename v (pderiv (Sum.inl i) (f k)) := by
    change pderiv (v (Sum.inl i)) (rename v (f k))=_
    exact pderiv_rename v.injective _ _
  obtain ⟨b,hb,hbalg,hba⟩ := hm (Fin m) (Fin (Fintype.card s)) f' a''
    (fun k=>by rw [hev]; exact hf k)
    (by simp_rw [hfd,hev]; exact hd) N
  let b' := fun i=>b (v i)
  have hb' (k : Fin m) : aeval b' (f k)=0 := by
    simpa only [f',aeval_rename,b',Function.comp_def] using hb k
  have hbclose (i : Fin m ⊕ s) : b' i-a' i∈(jetIdeal (K:=K) (σ:=τ))^N := by
    simpa only [b',a'',Equiv.symm_apply_apply] using hba (v i)
  refine ⟨fun i=>b' (Sum.inl i),?_,fun i=>hbalg _,?_⟩
  · intro k
    have hHjet : aeval b' (H k)-aeval a' (H k)∈
        (jetIdeal (K:=K) (σ:=τ))^((aeval a' (H k) : A).order.toNat+1) := by
      apply Ideal.pow_le_pow_right (show (aeval a' (H k) : A).order.toNat+1≤N from
        (Finset.le_sup (f:=fun k=>((aeval a' (H k) : A).order.toNat+1)) (Finset.mem_univ k)).trans (le_max_right _ _))
      simpa only [←eval₂_eq_eval_map,aeval_def] using mv_eval_sub_mem _ (map (algebraMap R A) (H k)) b' a' hbclose
    have hHb : aeval b' (H k)≠0 := ne_zero_of_close_jet (hH k) hHjet
    have hspan : Ideal.span (Set.range f)≤RingHom.ker (aeval b').toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨j,rfl⟩
      exact hb' j
    have heq := hspan (hI k)
    change aeval b' (H k*(rename Sum.inl (g k))^e k)=0 at heq
    rw [map_mul,map_pow,aeval_rename] at heq
    exact (pow_eq_zero_iff (he k).ne').mp ((mul_eq_zero.mp heq).resolve_left hHb)
  · intro i
    exact Ideal.pow_le_pow_right (le_max_left _ _) (hbclose (Sum.inl i))

end
end PD4Tensor.Spreading
end

end OAI
