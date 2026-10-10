import Mathlib
import OAI.Probability.BinarySweep.FiniteLaws.IndependentOperator

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

lemma finiteLaw_complex_expectation {Ω G R : Type*} [Fintype Ω] [Fintype G]
    [AddCommMonoid R] [Module ℂ R] (f : Ω → G) (A : G → R) :
    (∑g, (finiteLaw f g:ℂ) • A g)=
      (Fintype.card Ω:ℂ)⁻¹ • ∑ω, A (f ω) := by
  simp only [finiteLaw,Complex.ofReal_sum,Complex.ofReal_inv,Complex.ofReal_natCast,
    apply_ite,Complex.ofReal_zero,Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [ite_smul,zero_smul]
  simp [Finset.smul_sum]

lemma uniform_average_product {R : Type*} [Semiring R] [Algebra ℂ R] {n : ℕ}
    {X : Fin n → Type*} [∀j, Fintype (X j)] (A : (j : Fin n) → X j → R) :
    (Fintype.card (∀j,X j):ℂ)⁻¹ •
      (∑f : ∀j,X j, (List.ofFn (fun j => A j (f j))).reverse.prod)=
    (List.ofFn (fun j => (Fintype.card (X j):ℂ)⁻¹ • ∑a, A j a)).reverse.prod := by
  have he : (Fintype.card (∀j,X j):ℂ)⁻¹=∏j,(Fintype.card (X j):ℂ)⁻¹ := by
    simp [Fintype.card_pi,Finset.prod_inv_distrib]
  rw [he,Finset.smul_sum]
  simpa only [Finset.smul_sum] using independent_average_product
    (fun j _ => (Fintype.card (X j):ℂ)⁻¹) A

lemma complexAverage_finiteLaw {G V Ω : Type*} [Group G] [Fintype G] [Fintype Ω]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (f : Ω → G) :
    complexAverage ρ (fun g => (finiteLaw f g:ℂ))=
      (Fintype.card Ω:ℂ)⁻¹ • ∑ω,continuousRep ρ (f ω) := by
  rw [complexAverage_sum,finiteLaw_complex_expectation]

lemma binary_average_product {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Slot d)) V) :
    complexAverage ρ (fun g => (binaryLaw d g:ℂ))=
      (List.ofFn (fun j => (Fintype.card (({i : Fin d // i≠j} → Bool) → Bool):ℂ)⁻¹ •
        ∑c,continuousRep ρ (coordinateLayer d j c))).reverse.prod := by
  rw [binaryLaw,complexAverage_finiteLaw]
  simp_rw [binarySweep,map_list_prod,List.map_reverse,List.map_ofFn,Function.comp_def]
  exact uniform_average_product (fun j c => continuousRep ρ (coordinateLayer d j c))

lemma finiteLaw_pi {I : Type*} [Fintype I] {Ω X : I → Type*}
    [∀i, Fintype (Ω i)] [∀i,Fintype (X i)]
    (f : ∀i, Ω i → X i) (x : ∀i, X i) :
    finiteLaw (fun (ω : ∀i, Ω i) i => f i (ω i)) x=∏i, finiteLaw (f i) (x i) := by
  classical
  unfold finiteLaw
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro ω _
  have he : (fun i => f i (ω i))=x ↔ ∀i, f i (ω i)=x i := funext_iff
  rw [he]
  by_cases h : ∀i, f i (ω i)=x i
  · simp [h,Fintype.card_pi,Finset.prod_inv_distrib]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    rw [ite_eq_right (by aesop)]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma finiteLaw_equiv {Ω Ω' X : Type*} [Fintype Ω] [Fintype Ω'] [Fintype X]
    (e : Ω ≃ Ω') (f : Ω' → X) : finiteLaw (f ∘ e)=finiteLaw f := by
  funext x
  unfold finiteLaw
  rw [Fintype.card_congr e]
  exact e.sum_comp (fun ω' => if f ω'=x then (Fintype.card Ω':ℝ)⁻¹ else 0)

lemma finiteLaw_complex_comp_expectation {Ω X R : Type*} [Fintype Ω] [Fintype X]
    [AddCommMonoid R] [Module ℂ R] (f : Ω → X) (A : X → R) :
    (Fintype.card Ω:ℂ)⁻¹ • ∑ω,A (f ω)=∑x,(finiteLaw f x:ℂ) • A x :=
  (finiteLaw_complex_expectation f A).symm

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

def pushLaw {A B : Type*} [Fintype A] (p : A → ℝ) (f : A → B) (b : B) : ℝ :=
  ∑a, if f a=b then p a else 0

lemma finiteLaw_pushLaw {A B : Type*} [Fintype A] [Fintype B] (f : A → B) :
    finiteLaw f=pushLaw (uniformLaw A) f := rfl

lemma pushLaw_expectation {A B R : Type*} [Fintype A] [Fintype B]
    [AddCommMonoid R] [Module ℝ R] (p : A → ℝ) (f : A → B) (F : B → R) :
    (∑b,pushLaw p f b • F b)=∑a,p a • F (f a) := by
  unfold pushLaw
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  simp [ite_smul]

lemma pushLaw_comp {A B C : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (f : A → B) (g : B → C) :
    pushLaw (pushLaw p f) g=pushLaw p (g ∘ f) := by
  funext c
  have he := pushLaw_expectation p f (fun b => if g b=c then (1:ℝ) else 0)
  simpa [pushLaw,smul_eq_mul,mul_ite] using he

lemma pushLaw_equiv {A B C : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : B → ℝ) (f : B → C) :
    pushLaw (p ∘ e) (f ∘ e)=pushLaw p f := by
  funext c
  exact e.sum_comp (fun b => if f b=c then p b else 0)

lemma pushLaw_equiv_apply {A B : Type*} [Fintype A]
    (e : A ≃ B) (p : A → ℝ) (b : B) : pushLaw p e b=p (e.symm b) := by
  simp only [pushLaw,←e.eq_symm_apply]
  simp

lemma pushLaw_id {A : Type*} [Fintype A] (p : A → ℝ) : pushLaw p id=p := by
  funext a; simp [pushLaw]

lemma pushLaw_prod {A B X Y : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) (f : A → X) (g : B → Y) :
    pushLaw (fun ab : A×B => p ab.1*q ab.2) (Prod.map f g)=
      fun xy => pushLaw p f xy.1 * pushLaw q g xy.2 := by
  funext xy
  simp only [pushLaw,Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm (f := fun b a => (if f a=xy.1 then p a else 0)*(if g b=xy.2 then q b else 0))]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rcases xy with ⟨x,y⟩
  simp only [Prod.map_apply,Prod.mk.injEq]
  split_ifs <;> simp_all

lemma pushLaw_pi {I : Type*} [Fintype I] [DecidableEq I] {A X : I → Type*}
    [∀i,Fintype (A i)] [∀i,Fintype (X i)]
    (p : ∀i,A i → ℝ) (f : ∀i,A i → X i) :
    pushLaw (fun a : ∀i,A i => ∏i,p i (a i)) (fun a i => f i (a i))=
      fun x => ∏i,pushLaw (p i) (f i) (x i) := by
  funext x
  unfold pushLaw
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [funext_iff]
  by_cases h : ∀i,f i (a i)=x i
  · simp [h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    rw [ite_eq_right (by aesop)]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma uniformLaw_prod {A B : Type*} [Fintype A] [Fintype B] :
    uniformLaw (A×B)=fun ab => uniformLaw A ab.1 * uniformLaw B ab.2 := by
  funext ab
  simp [uniformLaw,Fintype.card_prod,mul_comm]

lemma uniformLaw_pi {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*} [∀i,Fintype (A i)] :
    uniformLaw (∀i,A i)=fun a => ∏i,uniformLaw (A i) (a i) := by
  funext a
  simp [uniformLaw,Fintype.card_pi,Finset.prod_inv_distrib]

lemma uniformLaw_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) :
    uniformLaw B ∘ e=uniformLaw A := by
  funext a
  simp [uniformLaw,Fintype.card_congr e]

end BinaryCoordinateSweeps

end

end OAI
