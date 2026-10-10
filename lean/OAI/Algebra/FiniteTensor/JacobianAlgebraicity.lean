import Mathlib
import OAI.Algebra.FiniteTensor.AdicSystems

namespace OAI

/-! Algebraicity from nondegenerate Jacobians and rectangular correction systems. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators
open MvPolynomial

variable {K L σ : Type*} [Field K] [Field L] [Algebra K L]
variable [Fintype σ] [DecidableEq σ]

 
theorem derivation_mv_aeval {M : Type*} [AddCommGroup M] [Module L M]
    [Module K M] [IsScalarTower K L M] (D : Derivation K L M)
    (a : σ → L) (p : MvPolynomial σ K) :
    D (aeval a p)=∑ i : σ,aeval a (pderiv i p) • D (a i) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add,hp,hq,add_smul,Finset.sum_add_distrib]
  | mul_X p k hp =>
    simp only [map_mul,aeval_X,D.leibniz,hp,pderiv_mul,map_add,add_smul,
      Finset.sum_add_distrib]
    rw [Finset.smul_sum]
    apply Eq.trans _ (add_comm _ _)
    congr 1
    · rw [Finset.sum_eq_single k]
      · simp
      · intro i hi hik
        simp [pderiv_X,Ne.symm hik]
      · simp
    · apply Finset.sum_congr rfl
      intro i hi
      rw [mul_smul,smul_comm]

private theorem matrix_module_kernel_zero {M : Type*} [AddCommGroup M] [Module L M]
    (J : Matrix σ σ L) (hJ : J.det≠0) (v : σ → M)
    (hv : ∀ k,∑ i : σ,J k i • v i=0) : ∀ i,v i=0 := by
  intro i
  have h : J.det • v i=0 := by
    calc
      J.det • v i = ∑ j : σ,(J.adjugate*J) i j • v j := by
        rw [Matrix.adjugate_mul]
        simp [Matrix.smul_apply,Matrix.one_apply]
      _ = ∑ k : σ,J.adjugate i k • (∑ j : σ,J k j • v j) := by
        simp only [Matrix.mul_apply,Finset.sum_smul,Finset.smul_sum,mul_smul]
        rw [Finset.sum_comm]
      _ = 0 := by simp only [hv,smul_zero,Finset.sum_const_zero]
  exact (smul_eq_zero.mp h).resolve_left hJ

 

theorem isAlgebraic_of_mv_jacobian (f : σ → MvPolynomial σ K) (a : σ → L)
    (hf : ∀ k,aeval a (f k)=0)
    (hJ : Matrix.det (fun k i=>aeval a (pderiv i (f k)))≠0) :
    ∀ i,IsAlgebraic K (a i) := by
  let E : IntermediateField K L := IntermediateField.adjoin K (Set.range a)
  let b : σ → E := fun i=>⟨a i,IntermediateField.subset_adjoin K _ (Set.mem_range_self i)⟩
  have hb (k : σ) : aeval b (f k)=0 := by
    apply E.val.injective
    change E.val (aeval b (f k))=E.val 0
    rw [map_zero,MvPolynomial.comp_aeval_apply]
    exact hf k
  let J : Matrix σ σ E := fun k i=>aeval b (pderiv i (f k))
  have hJE : J.det≠0 := by
    intro h
    have hh := congrArg E.val h
    rw [map_zero,E.val.map_det] at hh
    have hm : E.val.mapMatrix J=(fun k i=>aeval a (pderiv i (f k))) := by
      ext k i
      exact MvPolynomial.comp_aeval_apply b E.val (pderiv i (f k))
    rw [hm] at hh
    exact hJ hh
  let D := KaehlerDifferential.D K E
  have hDb : ∀ i,D (b i)=0 := by
    apply matrix_module_kernel_zero J hJE
    intro k
    rw [←derivation_mv_aeval D b (f k),hb k,map_zero]
  have hD : ∀ x : E,D x=0 := by
    rintro ⟨x,hx⟩
    change x∈IntermediateField.adjoin K (Set.range a) at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨i,rfl⟩ := hx
      exact hDb i
    | algebraMap r => exact D.map_algebraMap r
    | add x y hx hy ihx ihy =>
      change D ((⟨x,hx⟩ : E)+⟨y,hy⟩)=0
      rw [map_add,ihx,ihy,add_zero]
    | inv x hx ih =>
      change D ((⟨x,hx⟩ : E)⁻¹)=0
      rw [Derivation.leibniz_inv,ih,smul_zero]
    | mul x y hx hy ihx ihy =>
      change D ((⟨x,hx⟩ : E)*⟨y,hy⟩)=0
      rw [D.leibniz,ihx,ihy,smul_zero,smul_zero,add_zero]
  have hsub : (⊤ : Submodule E Ω[E⁄K])≤⊥ := by
    rw [←KaehlerDifferential.span_range_derivation,Submodule.span_le]
    rintro _ ⟨x,rfl⟩
    exact hD x
  let : Algebra.FormallyUnramified K E := ⟨
    (subsingleton_iff_forall_eq 0).mpr (fun x=>hsub trivial)⟩
  let : Algebra.EssFiniteType K E := IntermediateField.essFiniteType_iff.mpr
    (IntermediateField.fg_adjoin_of_finite (Set.finite_range a))
  let : Algebra.IsSeparable K E := Algebra.FormallyUnramified.isSeparable K E
  intro i
  exact (isAlgebraic_algHom_iff E.val E.val.injective).mpr
    (Algebra.IsAlgebraic.isAlgebraic (b i))

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators
open MvPolynomial
variable {R S L σ : Type*} [CommRing R] [IsDomain R]
variable [Fintype σ] [DecidableEq σ]

 
theorem isAlgebraic_of_mv_jacobian_domain_field [Field L] [Algebra R L] [FaithfulSMul R L]
    (f : σ → MvPolynomial σ R) (a : σ → L)
    (hf : ∀ k,aeval a (f k)=0)
    (hJ : Matrix.det (fun k i=>aeval a (pderiv i (f k)))≠0) :
    ∀ i,IsAlgebraic R (a i) := by
  let F := FractionRing R
  let : Algebra F L := FractionRing.liftAlgebra R L
  let : IsScalarTower R F L := FractionRing.isScalarTower_liftAlgebra R L
  have heval (p : MvPolynomial σ R) :
      aeval a (map (algebraMap R F) p)=aeval a p := by
    simp only [aeval_def,eval₂_map,←IsScalarTower.algebraMap_eq R F L]
  have hf' (k : σ) : aeval a (map (algebraMap R F) (f k))=0 := by
    rw [heval,hf]
  have hJ' : Matrix.det (fun k i=>aeval a
      (pderiv i (map (algebraMap R F) (f k))))≠0 := by
    simpa only [pderiv_map,heval] using hJ
  intro i
  exact (IsFractionRing.isAlgebraic_iff R F L).mpr
    (isAlgebraic_of_mv_jacobian (fun k=>map (algebraMap R F) (f k)) a hf' hJ' i)

 

theorem isAlgebraic_of_mv_jacobian_domain [CommRing S] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S]
    (f : σ → MvPolynomial σ R) (a : σ → S)
    (hf : ∀ k,aeval a (f k)=0)
    (hJ : Matrix.det (fun k i=>aeval a (pderiv i (f k)))≠0) :
    ∀ i,IsAlgebraic R (a i) := by
  let L := FractionRing S
  let b : σ → L := fun i=>algebraMap S L (a i)
  have heval (p : MvPolynomial σ R) :
      aeval b p=algebraMap S L (aeval a p) := by
    exact (MvPolynomial.comp_aeval_apply a (IsScalarTower.toAlgHom R S L) p).symm
  have hb (k : σ) : aeval b (f k)=0 := by rw [heval,hf,map_zero]
  have hJb : Matrix.det (fun k i=>aeval b (pderiv i (f k)))≠0 := by
    simp only [heval]
    have hm := (algebraMap S L).map_det
      (show Matrix σ σ S from fun k i=>aeval a (pderiv i (f k)))
    intro h
    apply hJ
    apply IsFractionRing.injective S L
    exact hm.trans (h.trans (map_zero _).symm)
  intro i
  have ha := isAlgebraic_of_mv_jacobian_domain_field f b hb hJb i
  exact (isAlgebraic_algebraMap_iff (IsFractionRing.injective S L)).mp ha

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators Matrix
open MvPolynomial
variable {K τ σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]

 

theorem algebraic_series_of_mv_jacobian
    (f : σ → MvPolynomial σ (MvPowerSeries τ K))
    (hcoeff : ∀ k d,IsAlgebraic (MvPolynomial τ K) ((f k).coeff d))
    (a : σ → MvPowerSeries τ K) (hf : ∀ k,eval a (f k)=0)
    (hJ : Matrix.det (fun k i=>eval a (pderiv i (f k)))≠0) :
    ∀ i,IsAlgebraic (MvPolynomial τ K) (a i) := by
  classical
  let : IsDomain (MvPowerSeries τ K) := NoZeroDivisors.to_isDomain _
  let A := Subalgebra.algebraicClosure (MvPolynomial τ K) (MvPowerSeries τ K)
  have hp (k : σ) : f k∈RingHom.range (map A.val.toRingHom) := by
    apply mem_range_map_iff_coeffs_subset.mpr
    intro c hc
    obtain ⟨d,hd,rfl⟩ := mem_coeffs_iff.mp hc
    exact ⟨⟨_,hcoeff k d⟩,rfl⟩
  choose p hmap using hp
  have heval (k : σ) : aeval a (p k)=eval a (f k) := by
    rw [←hmap k,eval_map]
    rfl
  have hderiv (k i : σ) : aeval a (pderiv i (p k))=eval a (pderiv i (f k)) := by
    rw [←hmap k,pderiv_map,eval_map]
    rfl
  have hroot (k : σ) : aeval a (p k)=0 := by rw [heval,hf]
  have hJ' : Matrix.det (fun k i=>aeval a (pderiv i (p k)))≠0 := by
    simpa only [hderiv] using hJ
  intro i
  exact (isAlgebraic_of_mv_jacobian_domain p a hroot hJ' i).restrictScalars
    (MvPolynomial τ K)

 

theorem algebraic_series_mv_tougeron [Finite τ]
    (I : Ideal (MvPowerSeries τ K)) [IsAdicComplete I (MvPowerSeries τ K)]
    (f : σ → MvPolynomial σ (MvPowerSeries τ K))
    (hcoeff : ∀ k d,IsAlgebraic (MvPolynomial τ K) ((f k).coeff d))
    (a e : σ → MvPowerSeries τ K) (he : ∀ k,e k∈I)
    (hJ : Matrix.det (fun k i=>eval a (pderiv i (f k)))≠0)
    (hf : ∀ k,eval a (f k)=
      (Matrix.det (fun k i=>eval a (pderiv i (f k))))^2*e k) :
    ∃ b : σ → MvPowerSeries τ K,(∀ k,eval b (f k)=0) ∧
      (∀ i,IsAlgebraic (MvPolynomial τ K) (b i)) ∧
      ∀ i,∃ v∈I,b i=a i+(Matrix.det (fun k j=>eval a (pderiv j (f k))))*v := by
  let : IsDomain (MvPowerSeries τ K) := NoZeroDivisors.to_isDomain _
  obtain ⟨b,hb,hJb,hclose⟩ := mv_tougeron_nondegenerate I f a e he hJ hf
  exact ⟨b,hb,algebraic_series_of_mv_jacobian f hcoeff b hb hJb,hclose⟩

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPolynomial
variable {R S σ ρ : Type*} [CommRing R] [CommRing S]

 
def freezeRight (a : ρ → R) : MvPolynomial (σ ⊕ ρ) R →+* MvPolynomial σ R :=
  (map (eval₂Hom (RingHom.id R) a)).comp (sumAlgEquiv R σ ρ).toRingHom

@[simp] theorem freezeRight_C (a : ρ → R) (r : R) :
    freezeRight (σ:=σ) a (C r)=C r := by simp [freezeRight]
@[simp] theorem freezeRight_X_left (a : ρ → R) (i : σ) :
    freezeRight a (X (Sum.inl i))=X i := by simp [freezeRight]
@[simp] theorem freezeRight_X_right (a : ρ → R) (i : ρ) :
    freezeRight (σ:=σ) a (X (Sum.inr i))=C (a i) := by simp [freezeRight]

theorem eval_freezeRight (a : ρ → R) (b : σ → R) (p : MvPolynomial (σ ⊕ ρ) R) :
    eval b (freezeRight a p)=eval (Sum.elim b a) p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp => cases i <;> simp only [map_mul,hp,freezeRight_X_left,
      freezeRight_X_right,eval_X,eval_C,Sum.elim_inl,Sum.elim_inr]

theorem pderiv_freezeRight (a : ρ → R) (i : σ) (p : MvPolynomial (σ ⊕ ρ) R) :
    pderiv i (freezeRight a p)=freezeRight a (pderiv (Sum.inl i) p) := by
  change pderiv i (map (eval₂Hom (RingHom.id R) a) ((sumAlgEquiv R σ ρ) p))=
    map (eval₂Hom (RingHom.id R) a) ((sumAlgEquiv R σ ρ) (pderiv (Sum.inl i) p))
  rw [pderiv_map,pderiv_sumAlgEquiv]

theorem freezeRight_map (φ : R →+* S) (a : ρ → R) (p : MvPolynomial (σ ⊕ ρ) R) :
    freezeRight (fun i=>φ (a i)) (map φ p)=map φ (freezeRight a p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp => cases i <;> simp only [map_mul,map_X,hp,freezeRight_X_left,
      freezeRight_X_right,map_C]

 

theorem freezeRight_algebraic {K τ : Type*} [Field K]
    (f : MvPolynomial (σ ⊕ ρ) (MvPowerSeries τ K))
    (hf : ∀ d,IsAlgebraic (MvPolynomial τ K) (f.coeff d))
    (a : ρ → MvPowerSeries τ K) (ha : ∀ i,IsAlgebraic (MvPolynomial τ K) (a i)) :
    ∀ d,IsAlgebraic (MvPolynomial τ K) ((freezeRight a f).coeff d) := by
  classical
  let A := Subalgebra.algebraicClosure (MvPolynomial τ K) (MvPowerSeries τ K)
  have hp : f∈Set.range (map A.val.toRingHom) := by
    apply mem_range_map_iff_coeffs_subset.mpr
    intro c hc
    obtain ⟨d,hd,rfl⟩ := mem_coeffs_iff.mp hc
    exact ⟨⟨_,hf d⟩,rfl⟩
  obtain ⟨p,hp⟩ := hp
  let b : ρ → A := fun i=>⟨a i,ha i⟩
  have heq : freezeRight a f=map A.val.toRingHom (freezeRight b p) := by
    rw [←hp]
    exact freezeRight_map A.val.toRingHom b p
  intro d
  rw [heq,coeff_map]
  exact ((freezeRight b p).coeff d).property

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators Matrix
open MvPolynomial
variable {K τ σ ρ : Type*} [Field K] [Finite τ] [Fintype σ] [DecidableEq σ]

 

theorem algebraic_rectangular_tougeron
    (I : Ideal (MvPowerSeries τ K)) [IsAdicComplete I (MvPowerSeries τ K)]
    (f : σ → MvPolynomial (σ ⊕ ρ) (MvPowerSeries τ K))
    (hcoeff : ∀ k d,IsAlgebraic (MvPolynomial τ K) ((f k).coeff d))
    (a : (σ ⊕ ρ) → MvPowerSeries τ K)
    (ha : ∀ i : ρ,IsAlgebraic (MvPolynomial τ K) (a (Sum.inr i)))
    (e : σ → MvPowerSeries τ K) (he : ∀ k,e k∈I)
    (hJ : Matrix.det (fun k i=>eval a (pderiv (Sum.inl i) (f k)))≠0)
    (hf : ∀ k,eval a (f k)=
      (Matrix.det (fun k i=>eval a (pderiv (Sum.inl i) (f k))))^2*e k) :
    ∃ b : (σ ⊕ ρ) → MvPowerSeries τ K,(∀ k,eval b (f k)=0) ∧
      (∀ i,IsAlgebraic (MvPolynomial τ K) (b i)) ∧
      (∀ i : ρ,b (Sum.inr i)=a (Sum.inr i)) ∧
      ∀ i : σ,∃ v∈I,b (Sum.inl i)=a (Sum.inl i)+
        (Matrix.det (fun k j=>eval a (pderiv (Sum.inl j) (f k))))*v := by
  let g : σ → MvPolynomial σ (MvPowerSeries τ K) :=
    fun k=>freezeRight (fun i=>a (Sum.inr i)) (f k)
  have haeq : Sum.elim (fun i=>a (Sum.inl i)) (fun i=>a (Sum.inr i))=a := by
    funext i; cases i <;> rfl
  have hg (k : σ) : eval (fun i=>a (Sum.inl i)) (g k)=eval a (f k) := by
    change eval _ (freezeRight _ (f k))=eval a (f k)
    rw [eval_freezeRight,haeq]
  have hgderiv (k i : σ) : eval (fun j=>a (Sum.inl j)) (pderiv i (g k))=
      eval a (pderiv (Sum.inl i) (f k)) := by
    change eval _ (pderiv i (freezeRight _ (f k)))=eval a _
    rw [pderiv_freezeRight,eval_freezeRight,haeq]
  have hgc (k : σ) : ∀ d,IsAlgebraic (MvPolynomial τ K) ((g k).coeff d) :=
    freezeRight_algebraic (f k) (hcoeff k) _ ha
  have hJg : Matrix.det (fun k i=>eval (fun j=>a (Sum.inl j)) (pderiv i (g k)))≠0 := by
    simpa only [hgderiv] using hJ
  have hfg (k : σ) : eval (fun j=>a (Sum.inl j)) (g k)=
      (Matrix.det (fun k i=>eval (fun j=>a (Sum.inl j)) (pderiv i (g k))))^2*e k := by
    simpa only [hg,hgderiv] using hf k
  obtain ⟨b,hb,halg,hclose⟩ := algebraic_series_mv_tougeron I g hgc _ e he hJg hfg
  refine ⟨Sum.elim b (fun i=>a (Sum.inr i)),?_,?_,fun _=>rfl,?_⟩
  · intro k
    exact (eval_freezeRight _ b (f k)).symm.trans (hb k)
  · intro i
    cases i with
    | inl i => exact halg i
    | inr i => exact ha i
  · intro i
    simpa only [hgderiv,Sum.elim_inl] using hclose i

end
end PD4Tensor.Spreading
end

end OAI
