import OAI.Algebra.Drinfeld.Grading

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section
namespace FiniteAlgebraNorm
open scoped Matrix.Norms.Operator
variable (A : Type*) [Ring A] [Algebra ℝ A] [FiniteDimensional ℝ A]

abbrev normedRing : NormedRing A :=
  NormedRing.induced A (Matrix (Fin (Module.finrank ℝ A)) (Fin (Module.finrank ℝ A)) ℝ)
    (Algebra.leftMulMatrix (Module.finBasis ℝ A))
    (Algebra.leftMulMatrix_injective (Module.finBasis ℝ A))

abbrev normedAlgebra : @NormedAlgebra ℝ A _ (normedRing A).toSeminormedRing :=
  NormedAlgebra.induced ℝ A (Matrix (Fin (Module.finrank ℝ A)) (Fin (Module.finrank ℝ A)) ℝ)
    (Algebra.leftMulMatrix (Module.finBasis ℝ A))

variable (K A : Type*) [RCLike K] [Ring A] [Algebra K A] [FiniteDimensional K A]

abbrev normedRingOver : NormedRing A :=
  NormedRing.induced A (Matrix (Fin (Module.finrank K A)) (Fin (Module.finrank K A)) K)
    (Algebra.leftMulMatrix (Module.finBasis K A))
    (Algebra.leftMulMatrix_injective (Module.finBasis K A))

abbrev normedAlgebraOver : @NormedAlgebra K A _ (normedRingOver K A).toSeminormedRing :=
  NormedAlgebra.induced K A (Matrix (Fin (Module.finrank K A)) (Fin (Module.finrank K A)) K)
    (Algebra.leftMulMatrix (Module.finBasis K A))

end FiniteAlgebraNorm

namespace FinitePicard

section
open MeasureTheory Set intervalIntegral
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def term (Ω : ℝ → A) (a : ℝ) : ℕ → ℝ → A
  | 0 => fun _ => 1
  | n+1 => fun t => ∫ s in a..t, Ω s * term Ω a n s

@[simp] theorem term_zero (Ω : ℝ → A) (a t : ℝ) : term Ω a 0 t=1 := rfl
@[simp] theorem term_succ (Ω : ℝ → A) (a t : ℝ) (n : ℕ) :
    term Ω a (n+1) t=∫ s in a..t, Ω s * term Ω a n s := rfl

@[simp] theorem term_base (Ω : ℝ → A) (a : ℝ) (n : ℕ) : term Ω a (n+1) a=0 := by
  simp

variable [CompleteSpace A]

theorem continuous_term {Ω : ℝ → A} (hΩ : Continuous Ω) (a : ℝ) (n : ℕ) :
    Continuous (term Ω a n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact (intervalIntegral.differentiable_integral_of_continuous (hΩ.mul ih)).continuous

theorem derivative_succ {Ω : ℝ → A} (hΩ : Continuous Ω) (a t : ℝ) (n : ℕ) :
    HasDerivAt (term Ω a (n+1)) (Ω t * term Ω a n t) t := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact (hΩ.mul (continuous_term hΩ a n)).intervalIntegrable a t
  · exact (hΩ.mul (continuous_term hΩ a n)).stronglyMeasurableAtFilter volume _
  · exact (hΩ.mul (continuous_term hΩ a n)).continuousAt

def transport (Ω : ℝ → A) (a : ℝ) (N : ℕ) (t : ℝ) : A :=
  ∑ n∈Finset.range (N+1),term Ω a n t

omit [CompleteSpace A] in
@[simp] theorem transport_base (Ω : ℝ → A) (a : ℝ) (N : ℕ) :
    transport Ω a N a=1 := by
  unfold transport
  rw [Finset.sum_range_succ']
  simp

theorem derivative_transport {Ω : ℝ → A} (hΩ : Continuous Ω) (a t : ℝ) (N : ℕ) :
    HasDerivAt (transport Ω a (N+1)) (Ω t * transport Ω a N t) t := by
  have hf : transport Ω a (N+1) = fun t => 1 + ∑ n∈Finset.range (N+1),term Ω a (n+1) t := by
    funext t
    simp only [transport,Finset.sum_range_succ',term_zero]
    exact add_comm _ _
  have hh := HasDerivAt.fun_sum (u:=Finset.range (N+1)) (fun n _ => derivative_succ hΩ a t n)
  have he := (hasDerivAt_const t (1:A)).add hh
  have hfun : ((fun _ : ℝ => (1:A)) + fun s => ∑ n∈Finset.range (N+1),term Ω a (n+1) s) = transport Ω a (N+1) := hf.symm
  rw [hfun] at he
  exact he.congr_deriv (by simp only [zero_add,transport,Finset.mul_sum])

omit [CompleteSpace A] in

theorem continuousOn_term {Ω : ℝ → A} {a b : ℝ}
    (hΩ : IntervalIntegrable Ω volume a b) (n : ℕ) :
    ContinuousOn (term Ω a n) (uIcc a b) := by
  induction n with
  | zero => exact continuousOn_const
  | succ n ih =>
    exact intervalIntegral.continuousOn_primitive_interval' (hΩ.mul_continuousOn ih) left_mem_uIcc

omit [CompleteSpace A] in
theorem continuousOn_transport {Ω : ℝ → A} {a b : ℝ}
    (hΩ : IntervalIntegrable Ω volume a b) (N : ℕ) :
    ContinuousOn (transport Ω a N) (uIcc a b) :=
  continuousOn_finsetSum _ (fun n _ => continuousOn_term hΩ n)

omit [CompleteSpace A] in
theorem collar_limit {Ω : ℝ → A} {a b : ℝ}
    (hΩ : IntervalIntegrable Ω volume a b) (N : ℕ) :
    Filter.Tendsto (transport Ω a N) (nhdsWithin a (uIcc a b)) (nhds (1:A)) := by
  have h := continuousOn_transport hΩ N a left_mem_uIcc
  change Filter.Tendsto _ _ (nhds (transport Ω a N a)) at h
  simpa only [transport_base] using h

end

open MeasureTheory Set intervalIntegral
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem integral_mem_submodule [FiniteDimensional ℝ A] (S : Submodule ℝ A)
    (f : ℝ → A) (a b : ℝ) (hf : ∀ t, f t ∈ S) :
    (∫ t in a..b, f t) ∈ S := by
  by_cases hi : IntervalIntegrable f volume a b
  · apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S _).mp
    intro l hl
    have hz : ∀ t, l (f t)=0 := fun t => (S.mem_dualAnnihilator l).mp hl _ (hf t)
    change l.toContinuousLinearMap (∫ t in a..b, f t)=0
    rw [← l.toContinuousLinearMap.intervalIntegral_comp_comm hi]
    change (∫ t in a..b, l (f t))=0
    simp only [hz, intervalIntegral.integral_zero]
  · rw [integral_undef hi]
    exact S.zero_mem

structure NilpotentFiltration (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] where
  space : ℕ → Submodule ℝ A
  antitone : Antitone space
  one_mem : (1 : A) ∈ space 0
  mul_mem : ∀ m n {x y : A}, x ∈ space m → y ∈ space n → x*y ∈ space (m+n)
  cutoff : ℕ
  terminal : space (cutoff+1)=⊥

variable [FiniteDimensional ℝ A]

omit [FiniteDimensional ℝ A] in
theorem pow_mem (F : NilpotentFiltration A) {X : A} (hX : X ∈ F.space 1) (n : ℕ) :
    X^n ∈ F.space n := by
  induction n with
  | zero => simpa using F.one_mem
  | succ n ih => simpa only [pow_succ] using F.mul_mem n 1 ih hX

omit [FiniteDimensional ℝ A] in
theorem pow_cutoff_eq_zero (F : NilpotentFiltration A) {X : A}
    (hX : X ∈ F.space 1) : X^(F.cutoff+1)=0 := by
  simpa only [F.terminal,Submodule.mem_bot] using pow_mem F hX (F.cutoff+1)

theorem term_mem (F : NilpotentFiltration A) {Ω : ℝ → A}
    (hΩ : ∀ t, Ω t ∈ F.space 1) (a : ℝ) (n : ℕ) (t : ℝ) :
    term Ω a n t ∈ F.space n := by
  induction n generalizing t with
  | zero => exact F.one_mem
  | succ n ih =>
    apply integral_mem_submodule
    intro s
    simpa only [Nat.add_comm 1 n] using F.mul_mem 1 n (hΩ s) (ih s)

theorem last_term_zero (F : NilpotentFiltration A) {Ω : ℝ → A}
    (hΩ : ∀ t, Ω t ∈ F.space 1) (a t : ℝ) :
    term Ω a (F.cutoff+1) t=0 := by
  have h := term_mem F hΩ a (F.cutoff+1) t
  simpa only [F.terminal,Submodule.mem_bot] using h

theorem last_product_zero (F : NilpotentFiltration A) {Ω : ℝ → A}
    (hΩ : ∀ t, Ω t ∈ F.space 1) (a t : ℝ) :
    Ω t * term Ω a F.cutoff t=0 := by
  have h := F.mul_mem 1 F.cutoff (hΩ t) (term_mem F hΩ a F.cutoff t)
  simpa only [Nat.add_comm 1 F.cutoff,F.terminal,Submodule.mem_bot] using h

theorem derivative_succ_of_integrable {Ω : ℝ → A} {a b t : ℝ}
    (hi : IntervalIntegrable Ω volume a b) (hc : ContinuousOn Ω (Ioo a b))
    (ht : t ∈ Ioo a b) (n : ℕ) :
    HasDerivAt (term Ω a (n+1)) (Ω t * term Ω a n t) t := by
  have hc' : ∀ x ∈ Ioo a b, ContinuousAt (fun s => Ω s * term Ω a n s) x := by
    intro x hx
    apply (hc.continuousAt (isOpen_Ioo.mem_nhds hx)).mul
    apply (continuousOn_term hi n).continuousAt
    rw [uIcc_of_le (le_trans hx.1.le hx.2.le)]
    exact Icc_mem_nhds hx.1 hx.2
  apply intervalIntegral.integral_hasDerivAt_right
  · exact (hi.mul_continuousOn (continuousOn_term hi n)).mono_set
      (uIcc_subset_uIcc_left (by rw [uIcc_of_le (le_trans ht.1.le ht.2.le)]; exact ⟨ht.1.le,ht.2.le⟩))
  · exact ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo hc' t ht
  · exact hc' t ht

theorem derivative_transport_of_integrable {Ω : ℝ → A} {a b t : ℝ}
    (hi : IntervalIntegrable Ω volume a b) (hc : ContinuousOn Ω (Ioo a b))
    (ht : t ∈ Ioo a b) (N : ℕ) :
    HasDerivAt (transport Ω a (N+1)) (Ω t * transport Ω a N t) t := by
  have hf : transport Ω a (N+1) = fun t => 1 + ∑ n∈Finset.range (N+1),term Ω a (n+1) t := by
    funext t
    simp only [transport,Finset.sum_range_succ',term_zero]
    exact add_comm _ _
  have hh := HasDerivAt.fun_sum (u:=Finset.range (N+1))
    (fun n _ => derivative_succ_of_integrable hi hc ht n)
  have he := (hasDerivAt_const t (1:A)).add hh
  have hfun : ((fun _ : ℝ => (1:A)) + fun s => ∑ n∈Finset.range (N+1),term Ω a (n+1) s) = transport Ω a (N+1) := hf.symm
  rw [hfun] at he
  exact he.congr_deriv (by simp only [zero_add,transport,Finset.mul_sum])

theorem derivative_nilpotent_transport (F : NilpotentFiltration A) {Ω : ℝ → A}
    (hΩ : ∀ s, Ω s ∈ F.space 1) {a b t : ℝ}
    (hi : IntervalIntegrable Ω volume a b) (hc : ContinuousOn Ω (Ioo a b))
    (ht : t ∈ Ioo a b) :
    HasDerivAt (transport Ω a F.cutoff) (Ω t * transport Ω a F.cutoff t) t := by
  have he : transport Ω a (F.cutoff+1)=transport Ω a F.cutoff := by
    funext s
    simp only [transport,Finset.sum_range_succ,last_term_zero F hΩ,add_zero]
  rw [← he]
  have hd := derivative_transport_of_integrable hi hc ht F.cutoff
  rw [he] at hd
  rw [he]
  exact hd

end FinitePicard

namespace TruncatedWords
open AssociativeElimination WordGrading
variable {R α : Type*} [CommRing R]

abbrev wt : α → ℕ := fun _ => 1

def relations (P : Set (A R α)) (N : ℕ) (x y : A R α) : Prop :=
  y=0 ∧ (x∈P ∨ x∈above wt (N+1))

abbrev Q (P : Set (A R α)) (N : ℕ) := RingQuot (relations P N)

def quotient (P : Set (A R α)) (N : ℕ) : A R α →ₐ[R] Q P N :=
  RingQuot.mkAlgHom R (relations P N)

theorem quotient_relation (P : Set (A R α)) (N : ℕ) {p : A R α} (hp : p∈P) :
    quotient P N p=0 := by
  have h := RingQuot.mkAlgHom_rel (S:=R) (show relations P N p 0 from ⟨rfl,Or.inl hp⟩)
  simpa only [quotient,map_zero] using h

theorem quotient_above (P : Set (A R α)) (N : ℕ) {p : A R α}
    (hp : p∈above wt (N+1)) : quotient P N p=0 := by
  have h := RingQuot.mkAlgHom_rel (S:=R) (show relations P N p 0 from ⟨rfl,Or.inr hp⟩)
  simpa only [quotient,map_zero] using h

def filtration (P : Set (A R α)) (N n : ℕ) : Submodule R (Q P N) :=
  (above wt n).map (quotient P N).toLinearMap

theorem filtration_antitone (P : Set (A R α)) (N : ℕ) : Antitone (filtration P N) := by
  intro m n h
  exact Submodule.map_mono (space_mono (fun _ hw => le_trans h hw))

theorem filtration_one (P : Set (A R α)) (N : ℕ) : (1 : Q P N)∈filtration P N 0 := by
  refine ⟨1,?_,map_one (quotient P N)⟩
  exact word_mem 1 (by simp)

theorem filtration_mul (P : Set (A R α)) (N m n : ℕ) {x y : Q P N}
    (hx : x∈filtration P N m) (hy : y∈filtration P N n) : x*y∈filtration P N (m+n) := by
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,rfl⟩ := hy
  exact ⟨a*b,above_mul ha hb,map_mul (quotient P N) _ _⟩

theorem filtration_terminal (P : Set (A R α)) (N : ℕ) : filtration P N (N+1)=⊥ := by
  apply eq_bot_iff.mpr
  rintro x ⟨p,hp,rfl⟩
  exact quotient_above P N hp

def fromBelow (P : Set (A R α)) (N : ℕ) : below (R:=R) (wt : α → ℕ) N →ₗ[R] Q P N :=
  (quotient P N).toLinearMap.comp (below wt N).subtype

theorem fromBelow_surjective (P : Set (A R α)) (N : ℕ) : Function.Surjective (fromBelow P N) := by
  classical
  intro x
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective R (relations P N) x
  refine ⟨⟨project (fun w => degree wt w≤N) p,project_mem _ _⟩,?_⟩
  change quotient P N (project (fun w => degree wt w≤N) p)=quotient P N p
  have hh : p-project (fun w => degree wt w≤N) p∈above wt (N+1) := by
    apply mem_space
    intro w hw
    by_contra hn
    have hle : degree wt w≤N := by omega
    exact hw (by simp only [MonoidAlgebra.coeff_sub,Finsupp.sub_apply,project_coeff,ite_eq_left hle,sub_self])
  have hz := quotient_above P N hh
  rw [map_sub] at hz
  exact (sub_eq_zero.mp hz).symm

variable [Finite α]

theorem finite_words_below (N : ℕ) : {w : FreeMonoid α | degree wt w≤N}.Finite := by
  apply Set.Finite.subset ((List.finite_length_le α N).image FreeMonoid.ofList)
  intro w hw
  exact ⟨w.toList,by simpa [degree] using hw,by simp⟩

instance finite_below (N : ℕ) : Module.Finite R (below (R:=R) (wt : α → ℕ) N) := by
  let : Fintype {w : FreeMonoid α // degree wt w≤N} := (finite_words_below (α:=α) N).fintype
  exact WordCoordinates.finite_space _

instance finite_quotient (P : Set (A R α)) (N : ℕ) : Module.Finite R (Q P N) :=
  Module.Finite.of_surjective (fromBelow P N) (fromBelow_surjective P N)

variable (P : Set (A ℝ α)) (N : ℕ)

instance normedRing : NormedRing (Q P N) := FiniteAlgebraNorm.normedRing _
instance normedAlgebra : NormedAlgebra ℝ (Q P N) := FiniteAlgebraNorm.normedAlgebra _

def nilpotentFiltration : FinitePicard.NilpotentFiltration (Q P N) where
  space := filtration P N
  antitone := filtration_antitone P N
  one_mem := filtration_one P N
  mul_mem := filtration_mul P N
  cutoff := N
  terminal := filtration_terminal P N

end TruncatedWords
end

namespace TensorFiltration
open scoped TensorProduct
open FinitePicard
variable {R A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

 def space (F : ℕ → Submodule R A) (G : ℕ → Submodule R B) (n : ℕ) : Submodule R (A ⊗[R] B) :=
  Submodule.span R {z | ∃ (i j : ℕ) (a : A) (b : B),n ≤ i + j ∧ a∈F i ∧ b∈G j ∧ z=a⊗ₜ[R]b}

 theorem tmul_mem (F : ℕ → Submodule R A) (G : ℕ → Submodule R B)
    {n i j : ℕ} {a : A} {b : B} (hn : n ≤ i + j) (ha : a∈F i) (hb : b∈G j) :
    a⊗ₜ[R]b∈space F G n := Submodule.subset_span ⟨i,j,a,b,hn,ha,hb,rfl⟩

 theorem antitone (F : ℕ → Submodule R A) (G : ℕ → Submodule R B) : Antitone (space F G) := by
  intro m n h
  apply Submodule.span_mono
  rintro z ⟨i,j,a,b,hn,ha,hb,rfl⟩
  exact ⟨i,j,a,b,le_trans h hn,ha,hb,rfl⟩

 theorem one (F : ℕ → Submodule R A) (G : ℕ → Submodule R B)
    (hF : (1:A)∈F 0) (hG : (1:B)∈G 0) : (1:A⊗[R]B)∈space F G 0 :=
  tmul_mem F G (by omega) hF hG

 theorem mul (F : ℕ → Submodule R A) (G : ℕ → Submodule R B)
    (hmF : ∀ i j {a b : A},a∈F i → b∈F j → a*b∈F (i+j))
    (hmG : ∀ i j {a b : B},a∈G i → b∈G j → a*b∈G (i+j))
    {m n : ℕ} {u v : A⊗[R]B} (hu : u∈space F G m) (hv : v∈space F G n) :
    u*v∈space F G (m+n) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨i,j,a,b,hij,ha,hb,rfl⟩ := hu
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k,l,c,d,hkl,hc,hd,rfl⟩ := hv
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem F G (by omega) (hmF i k ha hc) (hmG j l hb hd)
    | zero => simp only [mul_zero,Submodule.zero_mem]
    | add v w _ _ hv hw => rw [mul_add]; exact Submodule.add_mem _ hv hw
    | smul r v _ hv => rw [Algebra.mul_smul_comm]; exact Submodule.smul_mem _ r hv
  | zero => simp only [zero_mul,Submodule.zero_mem]
  | add u w _ _ hu hw => rw [add_mul]; exact Submodule.add_mem _ hu hw
  | smul r u _ hu => rw [Algebra.smul_mul_assoc]; exact Submodule.smul_mem _ r hu

 theorem terminal (F : ℕ → Submodule R A) (G : ℕ → Submodule R B)
    (hF : Antitone F) (hG : Antitone G) (M N : ℕ) (htF : F (M+1)=⊥) (htG : G (N+1)=⊥) :
    space F G (M+N+1)=⊥ := by
  apply eq_bot_iff.mpr
  apply Submodule.span_le.mpr
  rintro z ⟨i,j,a,b,hij,ha,hb,rfl⟩
  by_cases hi : M + 1 ≤ i
  · have hz := hF hi ha
    rw [htF,Submodule.mem_bot] at hz
    change a⊗ₜ[R]b=0
    simp only [hz,TensorProduct.zero_tmul]
  · have hj : N + 1 ≤ j := by omega
    have hz := hG hj hb
    rw [htG,Submodule.mem_bot] at hz
    change a⊗ₜ[R]b=0
    simp only [hz,TensorProduct.tmul_zero]

 theorem initial (F : ℕ → Submodule R A) (G : ℕ → Submodule R B)
    (hF : F 0=⊤) (hG : G 0=⊤) : space F G 0=⊤ := by
  apply eq_top_iff.mpr
  intro u hu
  clear hu
  induction u using TensorProduct.inductionOn with

  | tmul a b => exact tmul_mem F G (Nat.zero_le _) (by rw [hF]; trivial) (by rw [hG]; trivial)
  | add u v hu hv => exact Submodule.add_mem _ hu hv

variable {C D : Type*} [NormedRing C] [NormedRing D] [NormedAlgebra ℝ C] [NormedAlgebra ℝ D]
  [FiniteDimensional ℝ C] [FiniteDimensional ℝ D]
local instance : NormedRing (C⊗[ℝ]D) := FiniteAlgebraNorm.normedRing _
local instance : NormedAlgebra ℝ (C⊗[ℝ]D) := FiniteAlgebraNorm.normedAlgebra _

def cutoff (F : NilpotentFiltration C) (G : NilpotentFiltration D) : NilpotentFiltration (C⊗[ℝ]D) where
  space := space F.space G.space
  antitone := antitone F.space G.space
  one_mem := one F.space G.space F.one_mem G.one_mem
  mul_mem _ _ := mul F.space G.space F.mul_mem G.mul_mem
  cutoff := F.cutoff+G.cutoff
  terminal := terminal F.space G.space F.antitone G.antitone F.cutoff G.cutoff F.terminal G.terminal

end TensorFiltration

namespace TruncatedFree
open AssociativeElimination WordGrading
variable {R α : Type*} [CommRing R]
abbrev wt : α → ℕ := fun _ => 1
abbrev B (R α : Type*) [CommRing R] (N : ℕ) := below (R:=R) (wt : α → ℕ) N

def trunc (N : ℕ) : A R α →ₗ[R] B R α N :=
  (project (fun w => degree wt w≤N)).codRestrict _ (project_mem _)

@[simp] theorem trunc_val (N : ℕ) (p : A R α) :
    (trunc N p).val=project (fun w => degree wt w≤N) p := rfl

theorem trunc_above (N : ℕ) {p : A R α} (hp : p∈above wt (N+1)) : trunc N p=0 := by
  apply Subtype.ext
  exact project_eq_zero hp (by intro w hw hh; change N+1≤degree wt w at hw; omega)

theorem sub_trunc_above (N : ℕ) (p : A R α) : p-(trunc N p).val∈above wt (N+1) := by
  apply mem_space
  intro w hw
  by_contra hn
  have hle : degree wt w≤N := by change ¬N+1≤degree wt w at hn; omega
  exact hw (by simp only [MonoidAlgebra.coeff_sub,Finsupp.sub_apply,trunc_val,project_coeff,ite_eq_left hle,sub_self])

theorem all_ge_zero (p : A R α) : p∈above wt 0 := mem_space (by intros; exact Nat.zero_le _)

theorem trunc_mul_trunc_right (N : ℕ) (p q : A R α) :
    trunc N (p*(trunc N q).val)=trunc N (p*q) := by
  have hh : p*(q-(trunc N q).val)∈above wt (N+1) := by
    simpa only [Nat.zero_add] using above_mul (all_ge_zero p) (sub_trunc_above N q)
  have h := trunc_above N hh
  simp only [mul_sub,map_sub] at h
  exact (sub_eq_zero.mp h).symm

theorem trunc_mul_trunc_left (N : ℕ) (p q : A R α) :
    trunc N ((trunc N p).val*q)=trunc N (p*q) := by
  have hh : (p-(trunc N p).val)*q∈above wt (N+1) := by
    simpa only [Nat.add_zero] using above_mul (sub_trunc_above N p) (all_ge_zero q)
  have h := trunc_above N hh
  simp only [sub_mul,map_sub] at h
  exact (sub_eq_zero.mp h).symm

def action (N : ℕ) : A R α →ₐ[R] Module.End R (B R α N) where
  toFun p :=
    { toFun := fun q => trunc N (p*q.val)
      map_add' := by intros; simp only [Submodule.coe_add,mul_add,map_add]
      map_smul' := by intros; simp only [SetLike.val_smul,mul_smul_comm,map_smul,RingHom.id_apply] }
  map_one' := by
    apply LinearMap.ext
    intro q
    apply Subtype.ext
    change (trunc N (1*q.val)).val=q.val
    rw [one_mul,trunc_val,project_eq_self q.property]
  map_mul' p q := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    change (trunc N ((p*q)*u.val)).val=(trunc N (p*(trunc N (q*u.val)).val)).val
    rw [trunc_mul_trunc_right,mul_assoc]
  map_zero' := by ext q; simp
  map_add' p q := by ext u; simp only [add_mul,map_add]; rfl
  commutes' r := by
    apply LinearMap.ext
    intro q
    apply Subtype.ext
    change (trunc N (algebraMap R (A R α) r*q.val)).val=r • q.val
    rw [←Algebra.smul_def,map_smul,SetLike.val_smul,trunc_val,project_eq_self q.property]

def quotientAction (N : ℕ) : TruncatedWords.Q (∅ : Set (A R α)) N →ₐ[R] Module.End R (B R α N) :=
  RingQuot.liftAlgHom R ⟨action N,by
    rintro p q ⟨rfl,hp⟩
    rcases hp with hp|hp
    · exact False.elim hp
    · apply LinearMap.ext
      intro u
      apply Subtype.ext
      change (trunc N (p*u.val)).val=0
      have h : p*u.val∈above wt (N+1) := by
        simpa only [Nat.add_zero] using above_mul hp (all_ge_zero u.val)
      rw [trunc_above N h]
      rfl⟩

def oneVector (N : ℕ) : B R α N := ⟨1,word_mem 1 (by simp)⟩

def normal (N : ℕ) : TruncatedWords.Q (∅ : Set (A R α)) N →ₗ[R] B R α N :=
  (LinearMap.applyₗ (R:=R) (oneVector N)).comp (quotientAction N).toLinearMap

@[simp] theorem normal_quotient (N : ℕ) (p : A R α) :
    normal N (TruncatedWords.quotient ∅ N p)=trunc N p := by
  change (quotientAction N (RingQuot.mkAlgHom R _ p)) (oneVector N)=_
  simp only [quotientAction,RingQuot.liftAlgHom_mkAlgHom_apply]
  change trunc N (p*1)=_
  rw [mul_one]

theorem normal_inverse (N : ℕ) (p : B R α N) :
    normal N (TruncatedWords.fromBelow ∅ N p)=p := by
  change normal N (TruncatedWords.quotient ∅ N p.val)=p
  rw [normal_quotient]
  exact Subtype.ext (project_eq_self p.property)

def equiv (N : ℕ) : TruncatedWords.Q (∅ : Set (A R α)) N ≃ₗ[R] B R α N where
  __ := normal N
  invFun := TruncatedWords.fromBelow ∅ N
  left_inv := by
    intro q
    obtain ⟨p,rfl⟩ := TruncatedWords.fromBelow_surjective ∅ N q
    change TruncatedWords.fromBelow ∅ N (normal N (TruncatedWords.fromBelow ∅ N p))=_
    rw [normal_inverse]
  right_inv := normal_inverse N

@[simp] theorem equiv_eq_normal (N : ℕ) : (equiv (R:=R) (α:=α) N).toLinearMap=normal N := rfl

def coefficient (N : ℕ) (w : FreeMonoid α) : TruncatedWords.Q (∅ : Set (A R α)) N →ₗ[R] R :=
  (Finsupp.lapply w).comp ((MonoidAlgebra.coeffLinearEquiv R).toLinearMap.comp
    ((B R α N).subtype.comp (normal N)))

@[simp] theorem coefficient_quotient (N : ℕ) (w : FreeMonoid α) (p : A R α) :
    coefficient N w (TruncatedWords.quotient ∅ N p)=if degree wt w≤N then p.coeff w else 0 := by
  change (normal N (TruncatedWords.quotient ∅ N p)).val.coeff w=_
  rw [normal_quotient,trunc_val,project_coeff]

end TruncatedFree

namespace FilteredComparison
variable {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

structure Filtration (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] (N : ℕ) where
  step : ℕ → Submodule R V
  decreasing : Antitone step
  initial : step 0=⊤
  terminal : step (N+1)=⊥

variable {N : ℕ} (F : Filtration R V N) (G : Filtration R W N)
  (f : V →ₗ[R] W)

def Preserves : Prop := ∀ n v,v∈F.step n → f v∈G.step n

def GrInjective : Prop := ∀ n v,v∈F.step n → f v∈G.step (n+1) → v∈F.step (n+1)

def GrSurjective : Prop := ∀ n w,w∈G.step n → ∃ v,v∈F.step n ∧ w-f v∈G.step (n+1)

theorem injective (h : GrInjective F G f) : Function.Injective f := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro v hv
  have hz : f v=0 := hv
  have hm : ∀ n,v∈F.step n := by
    intro n
    induction n with
    | zero => rw [F.initial]; trivial
    | succ n ih => exact h n v ih (by rw [hz]; exact Submodule.zero_mem _)
  simpa only [F.terminal,Submodule.mem_bot] using hm (N+1)

theorem lift_step (h : GrSurjective F G f) (n k : ℕ) (w : W) (hw : w∈G.step n) :
    ∃ v,v∈F.step n ∧ w-f v∈G.step (n+k) := by
  induction k with
  | zero => exact ⟨0,Submodule.zero_mem _,by simpa only [map_zero,sub_zero,Nat.add_zero] using hw⟩
  | succ k ih =>
    obtain ⟨v,hv,he⟩ := ih
    obtain ⟨u,hu,hr⟩ := h (n+k) (w-f v) he
    refine ⟨v+u,(F.step n).add_mem hv (F.decreasing (Nat.le_add_right n k) hu),?_⟩
    convert hr using 1; first | congr 1 <;> omega | rw [map_add]; abel

theorem surjective (h : GrSurjective F G f) : Function.Surjective f := by
  intro w
  obtain ⟨v,_,hv⟩ := lift_step F G f h 0 (N+1) w (by rw [G.initial]; trivial)
  simp only [zero_add,G.terminal,Submodule.mem_bot,sub_eq_zero] at hv
  exact ⟨v,hv.symm⟩

def equivalence (hi : GrInjective F G f) (hs : GrSurjective F G f) : V ≃ₗ[R] W :=
  LinearEquiv.ofBijective f ⟨injective F G f hi,surjective F G f hs⟩

theorem inverse_preserves (hi : GrInjective F G f) (hs : GrSurjective F G f)
    (n : ℕ) (w : W) (hw : w∈G.step n) : (equivalence F G f hi hs).symm w∈F.step n := by
  have hn : ∀ k≤n,(equivalence F G f hi hs).symm w∈F.step k := by
    intro k
    induction k with
    | zero => intro _; rw [F.initial]; trivial
    | succ k ih =>
      intro hk
      apply hi k _ (ih (by omega))
      change (equivalence F G f hi hs) ((equivalence F G f hi hs).symm w)∈_
      rw [LinearEquiv.apply_symm_apply]
      exact G.decreasing hk hw
  exact hn n le_rfl

theorem comparison_raises (g : V →ₗ[R] W)
    (hi : GrInjective F G f) (hs : GrSurjective F G f)
    (he : ∀ n v,v∈F.step n → g v-f v∈G.step (n+1))
    (n : ℕ) (w : W) (hw : w∈G.step n) :
    g ((equivalence F G f hi hs).symm w)-w∈G.step (n+1) := by
  have h := he n _ (inverse_preserves F G f hi hs n w hw)
  have hf : f ((equivalence F G f hi hs).symm w)=w :=
    (equivalence F G f hi hs).apply_symm_apply w
  rwa [hf] at h

end FilteredComparison

namespace TruncatedSubstitution
open AssociativeElimination WordGrading TruncatedWords
variable {R α : Type*} [CommRing R] (N : ℕ)
local notation "Q" => TruncatedWords.Q (∅ : Set (A R α)) N
local notation "F" => filtration (∅ : Set (A R α)) N

def gen (a : α) : Q := quotient ∅ N (atom a)

theorem gen_mem (a : α) : gen N a∈F 1 :=
  ⟨atom a,word_mem (FreeMonoid.of a) (by simp [wt]),rfl⟩

theorem lift_word_mem (f : α → Q) (hf : ∀ a,f a∈F 1) (w : FreeMonoid α) :
    lift (R:=R) f (word w)∈F (degree wt w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simpa only [word_one,map_one,degree_one] using filtration_one (∅ : Set (A R α)) N
  | of_mul a w ih =>
    rw [word_mul,word_of,map_mul,lift_atom,degree_mul,degree_of]
    exact filtration_mul ∅ N 1 _ (hf a) ih

theorem lift_mem (f : α → Q) (hf : ∀ a,f a∈F 1) {n : ℕ} {p : A R α}
    (hp : p∈above wt n) : lift (R:=R) f p∈F n :=
  map_space (lift (R:=R) f).toLinearMap _ (fun w hw => filtration_antitone ∅ N hw (lift_word_mem N f hf w)) hp

def subst (f : α → Q) (hf : ∀ a,f a∈F 1) : Q →ₐ[R] Q :=
  RingQuot.liftAlgHom R ⟨lift (R:=R) f,by
    rintro p q ⟨rfl,hp⟩
    rcases hp with hp|hp
    · exact False.elim hp
    · simpa only [filtration_terminal,Submodule.mem_bot,map_zero] using lift_mem N f hf hp⟩

@[simp] theorem subst_quotient (f : α → Q) (hf : ∀ a,f a∈F 1) (p : A R α) :
    subst N f hf (quotient ∅ N p)=lift (R:=R) f p := by
  simp only [subst,quotient,RingQuot.liftAlgHom_mkAlgHom_apply]

@[simp] theorem subst_gen (f : α → Q) (hf : ∀ a,f a∈F 1) (a : α) :
    subst N f hf (gen N a)=f a := by rw [gen,subst_quotient,lift_atom]

theorem subst_preserves (f : α → Q) (hf : ∀ a,f a∈F 1) (n : ℕ) (u : Q)
    (hu : u∈F n) : subst N f hf u∈F n := by
  obtain ⟨p,hp,rfl⟩ := hu
  change subst N f hf (quotient ∅ N p)∈_
  rw [subst_quotient]
  exact lift_mem N f hf hp

theorem lift_word_difference (f g : α → Q) (hf : ∀ a,f a∈F 1) (hg : ∀ a,g a∈F 1)
    (hd : ∀ a,f a-g a∈F 2) (w : FreeMonoid α) :
    lift (R:=R) f (word w)-lift (R:=R) g (word w)∈F (degree wt w+1) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul a w ih =>
    rw [word_mul,word_of,map_mul,map_mul,lift_atom,lift_atom,degree_mul,degree_of]
    have he : f a*lift (R:=R) f (word w)-g a*lift (R:=R) g (word w)=
        (f a-g a)*lift (R:=R) g (word w)+f a*(lift (R:=R) f (word w)-lift (R:=R) g (word w)) := by
      rw [sub_mul,mul_sub]
      abel
    rw [he]
    exact (F (1+degree wt w+1)).add_mem
      (by
        simpa only [show 1+degree wt w+1=2+degree wt w by omega] using filtration_mul ∅ N 2 _ (hd a) (lift_word_mem N g hg w))
      (by simpa only [Nat.add_assoc] using filtration_mul ∅ N 1 _ (hf a) ih)

theorem lift_difference (f g : α → Q) (hf : ∀ a,f a∈F 1) (hg : ∀ a,g a∈F 1)
    (hd : ∀ a,f a-g a∈F 2) {n : ℕ} {p : A R α} (hp : p∈above wt n) :
    lift (R:=R) f p-lift (R:=R) g p∈F (n+1) :=
  map_space ((lift (R:=R) f).toLinearMap-(lift (R:=R) g).toLinearMap) _ (fun w hw =>
    filtration_antitone ∅ N (Nat.add_le_add_right hw 1) (lift_word_difference N f g hf hg hd w)) hp

@[simp] theorem lift_gen : lift (R:=R) (gen (R:=R) (α:=α) N)=quotient ∅ N := by
  apply hom_ext
  intro a
  simp only [lift_atom,gen]

theorem subst_raises (f : α → Q) (hf : ∀ a,f a∈F 1) (hd : ∀ a,f a-gen N a∈F 2)
    (n : ℕ) (u : Q) (hu : u∈F n) : subst N f hf u-u∈F (n+1) := by
  obtain ⟨p,hp,rfl⟩ := hu
  change subst N f hf (quotient ∅ N p)-quotient ∅ N p∈_
  rw [subst_quotient]
  simpa only [lift_gen] using lift_difference N f (gen N) hf (gen_mem N) hd hp

theorem filtration_initial : F 0=⊤ := by
  apply eq_top_iff.mpr
  intro u _
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective R (relations (∅ : Set (A R α)) N) u
  exact ⟨p,TruncatedFree.all_ge_zero p,rfl⟩

def filtered : FilteredComparison.Filtration R Q N where
  step := F
  decreasing := filtration_antitone ∅ N
  initial := filtration_initial N
  terminal := filtration_terminal ∅ N

theorem subst_bijective (f : α → Q) (hf : ∀ a,f a∈F 1) (hd : ∀ a,f a-gen N a∈F 2) :
    Function.Bijective (subst N f hf) := by
  have hi : FilteredComparison.GrInjective (filtered N) (filtered N) (subst N f hf).toLinearMap := by
    intro n u hu he
    change subst N f hf u∈F (n+1) at he
    change u∈F (n+1)
    have hh := (F (n+1)).sub_mem he (subst_raises N f hf hd n u hu)
    simpa only [sub_sub_cancel] using hh
  have hs : FilteredComparison.GrSurjective (filtered N) (filtered N) (subst N f hf).toLinearMap := by
    intro n u hu
    refine ⟨u,hu,?_⟩
    change u-subst N f hf u∈F (n+1)
    simpa only [neg_sub] using (F (n+1)).neg_mem (subst_raises N f hf hd n u hu)
  exact ⟨FilteredComparison.injective _ _ _ hi,FilteredComparison.surjective _ _ _ hs⟩

def equiv (f : α → Q) (hf : ∀ a,f a∈F 1) (hd : ∀ a,f a-gen N a∈F 2) : Q ≃ₐ[R] Q :=
  AlgEquiv.ofBijective (subst N f hf) (subst_bijective N f hf hd)

end TruncatedSubstitution

namespace NilpotentFreeLift
open AssociativeElimination WordGrading TruncatedWords FinitePicard
variable {α B : Type*} [NormedRing B] [NormedAlgebra ℝ B]
variable (F : NilpotentFiltration B) (f : α → B) (hf : ∀ a,f a∈F.space 1)
include hf
 theorem lift_word_mem (w : FreeMonoid α) : lift (R:=ℝ) f (word w)∈F.space (degree wt w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simpa only [word_one,map_one,degree_one] using F.one_mem
  | of_mul a w ih =>
    rw [word_mul,word_of,map_mul,lift_atom,degree_mul,degree_of]
    exact F.mul_mem 1 _ (hf a) ih
 theorem lift_mem {n : ℕ} {p : A ℝ α} (hp : p∈above wt n) : lift (R:=ℝ) f p∈F.space n :=
  map_space (lift (R:=ℝ) f).toLinearMap _ (fun w hw => F.antitone hw (lift_word_mem F f hf w)) hp
 def eval : Q (∅ : Set (A ℝ α)) F.cutoff →ₐ[ℝ] B :=
  RingQuot.liftAlgHom ℝ ⟨lift (R:=ℝ) f,by
    rintro p q ⟨rfl,hp⟩
    rcases hp with hp|hp
    · exact False.elim hp
    · simpa only [F.terminal,Submodule.mem_bot,map_zero] using lift_mem F f hf hp⟩
 @[simp] theorem eval_quotient (p : A ℝ α) : eval F f hf (quotient ∅ F.cutoff p)=lift (R:=ℝ) f p := by
  simp only [eval,quotient,RingQuot.liftAlgHom_mkAlgHom_apply]
 @[simp] theorem eval_gen (a : α) : eval F f hf (TruncatedSubstitution.gen F.cutoff a)=f a := by
  rw [TruncatedSubstitution.gen,eval_quotient,lift_atom]
 theorem eval_preserves {n : ℕ} {p : Q (∅ : Set (A ℝ α)) F.cutoff}
    (hp : p∈filtration ∅ F.cutoff n) : eval F f hf p∈F.space n := by
  obtain ⟨p,hp,rfl⟩ := hp
  change eval F f hf (quotient ∅ F.cutoff p)∈_
  rw [eval_quotient]
  exact lift_mem F f hf hp
end NilpotentFreeLift

end DeligneDrinfeld

end

end OAI
