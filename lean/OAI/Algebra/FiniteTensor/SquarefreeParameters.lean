import Mathlib

namespace OAI

/-! Squarefree parameter algebras, selectors and formal gradient base change. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor

open scoped BigOperators

variable (K : Type*) [Field K] (m : ℕ)

 
def squareIdeal : Ideal (MvPolynomial (Fin m) K) :=
  Ideal.span (Set.range (fun i : Fin m => (MvPolynomial.X i : MvPolynomial (Fin m) K) ^ 2))

abbrev T := MvPolynomial (Fin m) K ⧸ squareIdeal K m

def t (i : Fin m) : T K m := Ideal.Quotient.mk (squareIdeal K m) (MvPolynomial.X i)

def augmentation : T K m →+* K :=
  Ideal.Quotient.lift (squareIdeal K m)
    (MvPolynomial.eval₂Hom (RingHom.id K) (fun _ => 0)) (by
      have h : squareIdeal K m ≤
          RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id K) (fun _ : Fin m => 0)) := by
        apply Ideal.span_le.mpr
        rintro _ ⟨i, rfl⟩
        simp
      exact fun a ha => h ha)

def parameterIdeal : Ideal (T K m) := Ideal.span (Set.range (t K m))

end PD4Tensor

namespace PD4Tensor
noncomputable section
variable (K : Type*) [Field K] (m : ℕ)

@[simp] theorem t_sq (i : Fin m) : t K m i ^ 2 = 0 := by
  unfold t
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_range_self i)

 
theorem parameterIdeal_le_nilradical : parameterIdeal K m ≤ nilradical (T K m) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact mem_nilradical.mpr ⟨2, t_sq K m i⟩

private theorem squareIdeal_as_monomials : squareIdeal K m =
    Ideal.span ((fun a : Fin m →₀ ℕ => MvPolynomial.monomial a (1 : K)) ''
      Set.range (fun i : Fin m => Finsupp.single i 2)) := by
  unfold squareIdeal
  congr 1
  ext p
  simp only [Set.mem_range, Set.mem_image]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Finsupp.single i 2, ⟨i, rfl⟩, (MvPolynomial.X_pow_eq_monomial).symm⟩
  · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, MvPolynomial.X_pow_eq_monomial⟩

 
theorem squarefree_monomial_ne_zero (a : Fin m →₀ ℕ) (ha : ∀ i, a i ≤ 1) :
    Ideal.Quotient.mk (squareIdeal K m) (MvPolynomial.monomial a 1) ≠ 0 := by
  classical
  rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem, squareIdeal_as_monomials,
    MvPolynomial.mem_ideal_span_monomial_image]
  intro h
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := h a (by simp [MvPolynomial.support_monomial])
  have htwo : 2 ≤ a i := by simpa using hi i
  have hi1 := ha i
  omega

 
theorem triple_ne_zero (i j k : Fin m) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    t K m i * t K m j * t K m k ≠ 0 := by
  unfold t
  rw [← map_mul, ← map_mul]
  change Ideal.Quotient.mk (squareIdeal K m)
    ((MvPolynomial.monomial (Finsupp.single i 1) 1) *
      (MvPolynomial.monomial (Finsupp.single j 1) 1) *
      (MvPolynomial.monomial (Finsupp.single k 1) 1)) ≠ 0
  simp only [MvPolynomial.monomial_mul_monomial, one_mul]
  apply squarefree_monomial_ne_zero
  intro l
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> simp_all

 
theorem triple_mul_unit_ne_zero (i j k : Fin m) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {b : T K m} (hb : IsUnit b) : (t K m i * t K m j * t K m k) * b ≠ 0 := by
  intro h
  apply triple_ne_zero K m i j k hij hik hjk
  apply hb.mul_left_cancel
  simpa [mul_comm] using h

@[simp] theorem augmentation_t (i : Fin m) : augmentation K m (t K m i)=0 := by
  simp [augmentation,t,Ideal.Quotient.lift_mk]

@[simp] theorem augmentation_algebraMap (c : K) :
    augmentation K m (algebraMap K (T K m) c)=c := by
  change augmentation K m (Ideal.Quotient.mk (squareIdeal K m) (MvPolynomial.C c))=c
  simp [augmentation,Ideal.Quotient.lift_mk]

def augmentationAlg : T K m →ₐ[K] K :=
  { augmentation K m with commutes' := augmentation_algebraMap K m }

 
theorem sub_constant_mem (a : T K m) :
    a - algebraMap K (T K m) (augmentation K m a) ∈ parameterIdeal K m := by
  refine Quotient.inductionOn' a ?_
  intro p
  change Ideal.Quotient.mk (squareIdeal K m) p -
    algebraMap K (T K m) (augmentation K m (Ideal.Quotient.mk (squareIdeal K m) p)) ∈
      parameterIdeal K m
  induction p using MvPolynomial.induction_on with
  | C c =>
      change algebraMap K (T K m) c - algebraMap K (T K m)
        (augmentation K m (algebraMap K (T K m) c)) ∈ parameterIdeal K m
      simp
  | add p q hp hq =>
      simpa only [map_add,add_sub_add_comm] using (parameterIdeal K m).add_mem hp hq
  | mul_X p i _ =>
      simp only [map_mul,show Ideal.Quotient.mk (squareIdeal K m) (MvPolynomial.X i)=t K m i from rfl,
        augmentation_t,mul_zero,map_zero,sub_zero]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))

 
theorem isUnit_of_augmentation_ne_zero (a : T K m) (ha : augmentation K m a ≠ 0) : IsUnit a := by
  have hn : IsNilpotent (a-algebraMap K (T K m) (augmentation K m a)) :=
    mem_nilradical.mp (parameterIdeal_le_nilradical K m (sub_constant_mem K m a))
  have hu := (isUnit_iff_ne_zero.mpr ha).map (algebraMap K (T K m))
  have h := hn.isUnit_add_left_of_commute hu (Commute.all _ _)
  simpa only [add_sub_cancel] using h

end
end PD4Tensor

namespace PD4Tensor
noncomputable section
variable {K ι : Type*} [Field K]
 
def threeParameters (q : Fin 3 ↪ ι) : ι → T K 3 :=
  Function.extend q (t K 3) (fun _ => 0)

@[simp] theorem threeParameters_selected (q : Fin 3 ↪ ι) (j : Fin 3) :
    threeParameters (K:=K) q (q j) = t K 3 j := q.injective.extend_apply _ _ _

@[simp] theorem threeParameters_other (q : Fin 3 ↪ ι) (i : ι) (hi : i∉Set.range q) :
    threeParameters (K:=K) q i = 0 := Function.extend_apply' _ _ _ hi

theorem threeParameters_sq (q : Fin 3 ↪ ι) (i : ι) :
    threeParameters (K:=K) q i * threeParameters (K:=K) q i=0 := by
  by_cases hi : i∈Set.range q
  · obtain ⟨j,rfl⟩ := hi
    simpa only [threeParameters_selected,← pow_two] using t_sq K 3 j
  · simp [threeParameters_other q i hi]

@[simp] theorem augmentation_threeParameters (q : Fin 3 ↪ ι) (i : ι) :
    augmentation K 3 (threeParameters (K:=K) q i)=0 := by
  by_cases hi : i∈Set.range q
  · obtain ⟨j,rfl⟩ := hi; simp
  · simp [threeParameters_other q i hi]

end
end PD4Tensor

namespace PD4Tensor
noncomputable section
variable (K : Type*) [Field K] (m : ℕ) {ι : Type*}

 

def parameterSelector (active : Fin m ↪ ι) (q : Fin 3 ↪ ι) : T K m →ₐ[K] T K 3 :=
  Ideal.Quotient.liftₐ (squareIdeal K m)
    (MvPolynomial.aeval (fun i => threeParameters (K:=K) q (active i))) (by
      change squareIdeal K m ≤ RingHom.ker (MvPolynomial.aeval (fun i => threeParameters (K:=K) q (active i))).toRingHom
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change (MvPolynomial.aeval (fun i => threeParameters (K:=K) q (active i)))
        ((MvPolynomial.X i)^2)=0
      rw [map_pow,MvPolynomial.aeval_X,pow_two,threeParameters_sq])

@[simp] theorem parameterSelector_t (active : Fin m ↪ ι) (q : Fin 3 ↪ ι) (i : Fin m) :
    parameterSelector K m active q (t K m i)=threeParameters (K:=K) q (active i) := by
  change (MvPolynomial.aeval (fun i => threeParameters (K:=K) q (active i))) (MvPolynomial.X i)=_
  exact MvPolynomial.aeval_X _ _

theorem augmentation_parameterSelector (active : Fin m ↪ ι) (q : Fin 3 ↪ ι) (a : T K m) :
    augmentation K 3 (parameterSelector K m active q a)=augmentation K m a := by
  have heq : (augmentationAlg K 3).comp (parameterSelector K m active q)=augmentationAlg K m := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change augmentation K 3 (parameterSelector K m active q (t K m i))=augmentation K m (t K m i)
    simp only [parameterSelector_t,augmentation_threeParameters,augmentation_t]
  exact AlgHom.congr_fun heq a

theorem augmentation_zero_of_mem (a : T K m) (ha : a∈parameterIdeal K m) :
    augmentation K m a=0 := by
  have hle : parameterIdeal K m ≤ RingHom.ker (augmentation K m) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact augmentation_t K m i
  exact hle ha

end
end PD4Tensor

namespace PD4Tensor
noncomputable section
variable {R S σ : Type*} [CommRing R] [CommRing S]

 
theorem map_formal_pderiv (f : R →+* S) (i : σ) (F : MvPowerSeries σ R) :
    MvPowerSeries.map f (MvPowerSeries.pderiv i F)=
      MvPowerSeries.pderiv i (MvPowerSeries.map f F) := by
  ext d
  simp only [MvPowerSeries.coeff_map,MvPowerSeries.coeff_pderiv,map_mul,map_add,map_natCast,map_one]

variable {τ : Type*} [Fintype τ]

 
theorem map_formal_gradient (f : R →+* S)
    (H : τ → MvPowerSeries σ R) (hH : MvPowerSeries.HasSubst H)
    (F a : MvPowerSeries τ R)
    (ha : MvPowerSeries.subst H a∈Ideal.span
      (Set.range (fun i => MvPowerSeries.subst H (MvPowerSeries.pderiv i F)))) :
    MvPowerSeries.subst (fun i => MvPowerSeries.map f (H i)) (MvPowerSeries.map f a) ∈
      Ideal.span (Set.range (fun i =>
        MvPowerSeries.subst (fun i => MvPowerSeries.map f (H i))
          (MvPowerSeries.pderiv i (MvPowerSeries.map f F)))) := by
  obtain ⟨b,hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp ha
  refine Ideal.mem_span_range_iff_exists_fun.mpr ⟨fun i => MvPowerSeries.map f (b i),?_⟩
  have hh := congrArg (MvPowerSeries.map f) hb
  simpa only [map_sum,map_mul,MvPowerSeries.map_subst hH,map_formal_pderiv] using hh

end
end PD4Tensor

namespace PD4Tensor
noncomputable section
open scoped BigOperators
variable {ι κ : Type*} [Fintype κ] [DecidableEq ι]
  {A : ι → Type*} [∀ i,AddCommMonoid (A i)]

 

def activeExtension (active : κ ↪ ι) (b : ∀ j,A (active j)) : ∀ i,A i :=
  ∑ j,Pi.single (active j) (b j)

@[simp] theorem activeExtension_selected (active : κ ↪ ι) (b : ∀ j,A (active j)) (j : κ) :
    activeExtension active b (active j)=b j := by
  classical
  simp only [activeExtension,Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · exact Pi.single_eq_same _ _
  · intro k _ hk
    exact Pi.single_eq_of_ne (fun h => hk (active.injective h).symm) _
  · simp

theorem activeExtension_other (active : κ ↪ ι) (b : ∀ j,A (active j))
    (i : ι) (hi : i∉Set.range active) : activeExtension active b i=0 := by
  classical
  simp only [activeExtension,Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  exact Pi.single_eq_of_ne (fun h => hi ⟨j,h.symm⟩) _

 

theorem sum_activeExtension [Fintype ι] {B : Type*} [AddCommMonoid B]
    (active : κ ↪ ι) (b : ∀ j,A (active j)) (f : ∀ i,A i →+ B) :
    ∑ i,f i (activeExtension active b i)=∑ j,f (active j) (b j) := by
  classical
  simp only [activeExtension,Finset.sum_apply,map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (active j)]
  · rw [Pi.single_eq_same]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi,map_zero]
  · simp

 

omit [Fintype κ] [DecidableEq ι] in
theorem embedding_preimage (active : κ ↪ ι) (q : Fin 3 ↪ ι)
    (hq : ∀ j,q j∈Set.range active) :
    ∃ r : Fin 3 ↪ κ,∀ j,active (r j)=q j := by
  classical
  choose r hr using hq
  refine ⟨⟨r,?_⟩,hr⟩
  intro i j hij
  apply q.injective
  rw [←hr i,←hr j,hij]

end
end PD4Tensor
end

end OAI
