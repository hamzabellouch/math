import Mathlib
import OAI.Probability.LogConcave.JetEstimates.CrossMoment

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
namespace TensorEnergy
open scoped BigOperators

variable {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

def Bound (A : I → J → ℝ) (C : ℝ) : Prop :=
  ∀ v : J → ℝ, (∑ i, (∑ j, A i j*v j)^2) ≤ C*∑ j, (v j)^2

lemma energy_nonneg (v : I → ℝ) : 0 ≤ ∑ i, (v i)^2 :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma dot_sq (u v : I → ℝ) :
    (∑ i, u i*v i)^2 ≤ (∑ i, (u i)^2)*(∑ i, (v i)^2) :=
  Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma bound_of_bilinear {A : I → J → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (u : I → ℝ) (v : J → ℝ), (∑ i, ∑ j, u i*A i j*v j)^2 ≤ C*(∑ i, (u i)^2)*(∑ j, (v j)^2)) :
    Bound A C := by
  intro v
  let w : I → ℝ := fun i => ∑ j, A i j*v j
  have he : (∑ i, ∑ j, w i*A i j*v j) = ∑ i, (w i)^2 := by
    simp only [mul_assoc,← Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by dsimp [w]; ring)
  have hh := h w v
  rw [he] at hh
  have hw := energy_nonneg w
  by_cases hz : (∑ i, (w i)^2) = 0
  · change (∑ i, (w i)^2) ≤ _
    rw [hz]
    exact mul_nonneg hC (energy_nonneg v)
  · have hp : 0 < ∑ i, (w i)^2 := lt_of_le_of_ne hw (Ne.symm hz)
    have hh' : (∑ i, (w i)^2)*(∑ i, (w i)^2) ≤
        (C*∑ j, (v j)^2)*(∑ i, (w i)^2) := by nlinarith [hh]
    exact (mul_le_mul_iff_left₀ hp).mp (by simpa only [mul_comm] using hh')

lemma Bound.bilinear {A : I → J → ℝ} {C : ℝ} (h : Bound A C) (u : I → ℝ) (v : J → ℝ) :
    (∑ i, ∑ j, u i*A i j*v j)^2 ≤ C*(∑ i, (u i)^2)*(∑ j, (v j)^2) := by
  simp only [mul_assoc,← Finset.mul_sum]
  exact (dot_sq u (fun i => ∑ j, A i j*v j)).trans
    ((mul_le_mul_of_nonneg_left (h v) (energy_nonneg u)).trans_eq (by ring))

lemma Bound.transpose {A : I → J → ℝ} {C : ℝ} (h : Bound A C) (hC : 0 ≤ C) :
    Bound (fun j i => A i j) C := by
  apply bound_of_bilinear hC
  intro u v
  have hh := h.bilinear v u
  rw [Finset.sum_comm] at hh
  convert hh using 1
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  · ring

lemma Bound.kronecker {A : I → J → ℝ} {B : K → L → ℝ} {C D : ℝ}
    (hA : Bound A C) (hB : Bound B D) (hC : 0 ≤ C) :
    Bound (fun (i : I × K) (j : J × L) => A i.1 j.1*B i.2 j.2) (C*D) := by
  intro v
  simp only [Fintype.sum_prod_type]
  have he (i : I) (k : K) :
      (∑ j, ∑ l, (A i j*B k l)*v (j,l)) = ∑ j, A i j*(∑ l, B k l*v (j,l)) := by
    simp only [Finset.mul_sum,mul_assoc]
  simp_rw [he]
  rw [Finset.sum_comm]
  have hh := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset K)) =>
    hA (fun j => ∑ l, B k l*v (j,l)))
  rw [← Finset.mul_sum] at hh
  conv at hh => rhs; arg 2; rw [Finset.sum_comm]
  have hg := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset J)) =>
      hB (fun l => v (j,l)))) hC
  rw [← Finset.mul_sum] at hg
  exact hh.trans (hg.trans_eq (by ring))

lemma Bound.reindex {A : I → J → ℝ} {C : ℝ} (h : Bound A C)
    (e : K ≃ I) (f : L ≃ J) : Bound (fun k l => A (e k) (f l)) C := by
  intro v
  have hh := h (v ∘ f.symm)
  rw [← e.sum_comp] at hh
  simp_rw [← f.sum_comp] at hh
  simpa only [Function.comp_def,Equiv.symm_apply_apply] using hh

lemma prod_split {N : Type*} [Fintype N] [DecidableEq N] (i : N) (f : N → ℝ) :
    (∏ j, f j) = f i * ∏ j : {j : N // j ≠ i}, f j := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)]
  congr 1
  exact Finset.prod_subtype _ (by simp) _

universe u v w
lemma bound_pi_aux (n : ℕ) : ∀ (N : Type u) [Fintype N] [DecidableEq N],
    Fintype.card N = n → ∀ (A : N → Type v) (B : N → Type w)
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (M : ∀ i, A i → B i → ℝ) (C : N → ℝ),
    (∀ i, 0 ≤ C i) → (∀ i, Bound (M i) (C i)) →
    Bound (fun (a : ∀ i, A i) (b : ∀ i, B i) => ∏ i, M i (a i) (b i)) (∏ i, C i) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro N _ _ hc A B _ _ M C hC hM
    by_cases hn : n=0
    · have : IsEmpty N := Fintype.card_eq_zero_iff.mp (hc.trans hn)
      let a : ∀ i, A i := fun i => isEmptyElim i
      let b : ∀ i, B i := fun i => isEmptyElim i
      let : Unique (∀ i, A i) := ⟨⟨a⟩,fun _ => funext (fun i => isEmptyElim i)⟩
      let : Unique (∀ i, B i) := ⟨⟨b⟩,fun _ => funext (fun i => isEmptyElim i)⟩
      intro _
      simp
    · have hp : 0<n := Nat.pos_of_ne_zero hn
      have : Nonempty N := Fintype.card_pos_iff.mp (hc ▸ hp)
      let i : N := Classical.choice this
      have hcard : Fintype.card {j : N // j ≠ i} = n-1 := by
        rw [Fintype.card_subtype_compl,Fintype.card_subtype_eq,hc]
      have hr := ih (n-1) (Nat.sub_lt hp (by norm_num)) {j : N // j ≠ i} hcard
        (fun j => A j) (fun j => B j) (fun j => M j) (fun j => C j)
        (fun j => hC j) (fun j => hM j)
      have hh := ((hM i).kronecker hr (hC i)).reindex
        (Equiv.piSplitAt i A) (Equiv.piSplitAt i B)
      rw [← prod_split] at hh
      convert hh using 1
      funext a b
      exact prod_split i (fun j => M j (a j) (b j))

lemma Bound.pi {N : Type u} [Fintype N] [DecidableEq N]
    {A : N → Type v} {B : N → Type w} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    {M : ∀ i, A i → B i → ℝ} {C : N → ℝ}
    (hC : ∀ i, 0 ≤ C i) (hM : ∀ i, Bound (M i) (C i)) :
    Bound (fun (a : ∀ i, A i) (b : ∀ i, B i) => ∏ i, M i (a i) (b i)) (∏ i, C i) :=
  bound_pi_aux _ N rfl A B M C hC hM

lemma Bound.fibers {N R S : Type*} [Fintype N] [DecidableEq N]
    [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
    (p : R → N) (q : S → N)
    {M : ∀ i, ({r : R // p r = i} → I) → ({s : S // q s = i} → J) → ℝ}
    {C : N → ℝ} (hC : ∀ i, 0 ≤ C i) (hM : ∀ i, Bound (M i) (C i)) :
    Bound (fun (a : R → I) (b : S → J) =>
      ∏ i, M i (fun r => a r) (fun s => b s)) (∏ i, C i) := by
  have hh := (Bound.pi hC hM).reindex
    (Equiv.piCongrFiberwise (γ₁ := fun _ => I) (f := p) (fun _ => Equiv.refl _))
    (Equiv.piCongrFiberwise (γ₁ := fun _ => J) (f := q) (fun _ => Equiv.refl _))
  exact hh

lemma Bound.mono {A : I → J → ℝ} {C D : ℝ} (h : Bound A C) (hCD : C ≤ D) :
    Bound A D := fun v => (h v).trans
      (mul_le_mul_of_nonneg_right hCD (energy_nonneg v))

lemma Bound.smul {A : I → J → ℝ} {C : ℝ} (h : Bound A C) (c : ℝ) :
    Bound (fun i j => c*A i j) (c^2*C) := by
  intro v
  simp only [mul_assoc,← Finset.mul_sum,mul_pow,← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left (h v) (sq_nonneg c)).trans_eq (by ring)

lemma Bound.sum {N : Type*} [Fintype N] {M : N → I → J → ℝ} {C : N → ℝ}
    (hM : ∀ n, Bound (M n) (C n)) :
    Bound (fun i j => ∑ n, M n i j) ((Fintype.card N:ℝ)*∑ n, C n) := by
  intro v
  simp only [Finset.sum_mul]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset J)) (t := (Finset.univ : Finset N))]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : N => (1:ℝ))
      (fun n => ∑ j, M n i j*v j))
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hh
  rw [← Finset.mul_sum] at hh
  conv at hh => rhs; arg 2; rw [Finset.sum_comm]
  have hh' := Finset.sum_le_sum (fun n (_ : n ∈ (Finset.univ : Finset N)) => hM n v)
  rw [← Finset.sum_mul] at hh'
  exact hh.trans ((mul_le_mul_of_nonneg_left hh' (Nat.cast_nonneg _)).trans_eq (by ring))

end TensorEnergy
end LogConcaveSampling

namespace LogConcaveSampling
namespace Appell
open MeasureTheory
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι ϑ κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ϑ] [DecidableEq ϑ]
  [Fintype κ] [DecidableEq κ]

def splitConstant (β : ℝ) (j k : ℕ) : ℝ :=
  β^(j+k)*((j.factorial:ℝ)*(k.factorial:ℝ))^2

omit [MeasurableSpace E] [BorelSpace E] in
lemma splitConstant_nonneg {β : ℝ} (hβ : 0 ≤ β) (j k : ℕ) :
    0 ≤ splitConstant β j k := by dsimp [splitConstant]; positivity

theorem crossMoment_energy (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    {β : ℝ} (hβ : 0 ≤ β) (hP : HasPoincare μ β) (b : OrthonormalBasis κ ℝ E) :
    TensorEnergy.Bound (crossMoment μ b (ι := ι) (ϑ := ϑ))
      (splitConstant β (Fintype.card ι) (Fintype.card ϑ)) := by
  apply TensorEnergy.bound_of_bilinear (splitConstant_nonneg hβ _ _)
  intro T U
  convert crossMoment_sq_bound μ hμ hβ hP b T U using 1
  dsimp [splitConstant]
  rw [pow_add]
  ring

def reducedCrossMoment (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (c : ϑ → κ) : ℝ :=
  if Fintype.card ι = 0 ∨ Fintype.card ϑ = 0 then 0 else crossMoment μ b a c

lemma reducedCrossMoment_energy (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    {β : ℝ} (hβ : 0 ≤ β) (hP : HasPoincare μ β) (b : OrthonormalBasis κ ℝ E) :
    TensorEnergy.Bound (reducedCrossMoment μ b (ι := ι) (ϑ := ϑ))
      (splitConstant β (Fintype.card ι) (Fintype.card ϑ)) := by
  unfold reducedCrossMoment
  split_ifs
  · intro v
    simp only [zero_mul,Finset.sum_const_zero,zero_pow (by norm_num : 2≠0)]
    exact mul_nonneg (splitConstant_nonneg hβ _ _) (TensorEnergy.energy_nonneg v)
  · exact crossMoment_energy μ hμ hβ hP b

omit [MeasurableSpace E] [BorelSpace E] in
lemma card_fibers {N R : Type*} [Fintype N] [DecidableEq N] [Fintype R]
    (p : R → N) : (∑ i, Fintype.card {r : R // p r=i}) = Fintype.card R := by
  simpa only [Fintype.card_sigma] using Fintype.card_congr (Equiv.sigmaFiberEquiv p)

omit [MeasurableSpace E] [BorelSpace E] in
lemma prod_fiber_factorial_le {N R : Type*} [Fintype N] [DecidableEq N] [Fintype R]
    (p : R → N) :
    (∏ i, ((Fintype.card {r : R // p r=i}).factorial:ℝ)) ≤ ((Fintype.card R).factorial:ℝ) := by
  have hh := Nat.le_of_dvd (Nat.factorial_pos _)
    (Nat.prod_factorial_dvd_factorial_sum Finset.univ (fun i => Fintype.card {r : R // p r=i}))
  rw [card_fibers p] at hh
  exact_mod_cast hh

omit [MeasurableSpace E] [BorelSpace E] in
lemma prod_splitConstant_le {N R S : Type*} [Fintype N] [DecidableEq N]
    [Fintype R] [Fintype S] (p : R → N) (q : S → N) {β : ℝ} (hβ : 0 ≤ β) :
    (∏ i, splitConstant β (Fintype.card {r : R // p r=i})
      (Fintype.card {s : S // q s=i})) ≤ splitConstant β (Fintype.card R) (Fintype.card S) := by
  simp only [splitConstant,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,
    Finset.prod_pow,Finset.sum_add_distrib,card_fibers]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hβ _)
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_mul (prod_fiber_factorial_le p) (prod_fiber_factorial_le q)
    (by positivity) (by positivity)

def crossBlockProduct {N : Type*} [Fintype N] [DecidableEq N]
    (μ : Measure E) (b : OrthonormalBasis κ ℝ E) (p : ι → N) (q : ϑ → N)
    (a : ι → κ) (c : ϑ → κ) : ℝ :=
  ∏ i, reducedCrossMoment μ b (fun j : {j : ι // p j=i} => a j)
    (fun j : {j : ϑ // q j=i} => c j)

lemma crossBlockProduct_energy {N : Type*} [Fintype N] [DecidableEq N]
    (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    {β : ℝ} (hβ : 0 ≤ β) (hP : HasPoincare μ β) (b : OrthonormalBasis κ ℝ E)
    (p : ι → N) (q : ϑ → N) :
    TensorEnergy.Bound (crossBlockProduct μ b p q)
      (splitConstant β (Fintype.card ι) (Fintype.card ϑ)) := by
  exact (TensorEnergy.Bound.fibers p q
    (fun i => splitConstant_nonneg hβ _ _)
    (fun i => reducedCrossMoment_energy μ hμ hβ hP b)).mono (prod_splitConstant_le p q hβ)

abbrev LogTerms (ι ϑ : Type*) [Fintype ι] [Fintype ϑ] :=
  (m : Fin (Fintype.card ι+Fintype.card ϑ+1)) × (ι → Fin m.val) × (ϑ → Fin m.val)

def logCoefficient (m : ℕ) : ℝ := (-1)^(m+1)/(m:ℝ)

omit [MeasurableSpace E] [BorelSpace E] in
lemma logCoefficient_sq_le (m : ℕ) : (logCoefficient m)^2 ≤ 1 := by
  unfold logCoefficient
  by_cases hm : m=0
  · simp [hm]
  · have hpos : (1:ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    rw [div_pow,pow_right_comm,(by norm_num : (-1:ℝ)^2=1),one_pow]
    apply (div_le_one (by positivity : 0 < (m:ℝ)^2)).mpr
    nlinarith

def mixedCumulant (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (c : ϑ → κ) : ℝ :=
  ∑ t : LogTerms ι ϑ, logCoefficient t.1.val * crossBlockProduct μ b t.2.1 t.2.2 a c

omit [MeasurableSpace E] [BorelSpace E] in
lemma card_logTerms_le : Fintype.card (LogTerms ι ϑ) ≤
    (Fintype.card ι+Fintype.card ϑ+1)^(Fintype.card ι+Fintype.card ϑ+1) := by
  simp only [LogTerms,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,
    ← pow_add]
  have hh := Finset.sum_le_sum (fun m (_ : m ∈
      (Finset.univ : Finset (Fin (Fintype.card ι+Fintype.card ϑ+1)))) =>
    Nat.pow_le_pow_left (Nat.le_of_lt m.isLt) (Fintype.card ι+Fintype.card ϑ))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hh
  exact hh.trans_eq (by rw [pow_succ]; exact Nat.mul_comm _ _)

theorem mixedCumulant_energy (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    {β : ℝ} (hβ : 0 ≤ β) (hP : HasPoincare μ β) (b : OrthonormalBasis κ ℝ E) :
    TensorEnergy.Bound (mixedCumulant μ b (ι := ι) (ϑ := ϑ))
      (((Fintype.card ι+Fintype.card ϑ+1:ℕ):ℝ)^(2*(Fintype.card ι+Fintype.card ϑ+1)) *
        splitConstant β (Fintype.card ι) (Fintype.card ϑ)) := by
  let C := splitConstant β (Fintype.card ι) (Fintype.card ϑ)
  have hC : 0 ≤ C := splitConstant_nonneg hβ _ _
  have hh (t : LogTerms ι ϑ) : TensorEnergy.Bound
      (fun a c => logCoefficient t.1.val * crossBlockProduct μ b t.2.1 t.2.2 a c) C :=
    ((crossBlockProduct_energy μ hμ hβ hP b t.2.1 t.2.2).smul _).mono
      ((mul_le_mul_of_nonneg_right (logCoefficient_sq_le _) hC).trans_eq (one_mul C))
  apply (TensorEnergy.Bound.sum hh).mono
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc : (Fintype.card (LogTerms ι ϑ):ℝ) ≤
      ((Fintype.card ι+Fintype.card ϑ+1:ℕ):ℝ)^(Fintype.card ι+Fintype.card ϑ+1) := by
    exact_mod_cast (card_logTerms_le (ι := ι) (ϑ := ϑ))
  have hc' := pow_le_pow_left₀ (Nat.cast_nonneg (Fintype.card (LogTerms ι ϑ))) hc 2
  have hh' := mul_le_mul_of_nonneg_right hc' hC
  rw [← pow_mul,Nat.mul_comm _ 2] at hh'
  simpa only [sq,mul_assoc] using hh'

end Appell
end LogConcaveSampling

namespace LogConcaveSampling
namespace Appell
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def HasExpMoments (μ : Measure E) : Prop := ∀ R : ℝ, Integrable (fun x : E => Real.exp (R*‖x‖)) μ

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def laplace (μ : Measure E) (h : E → F) (θ : E) : F :=
  ∫ x, Real.exp (inner ℝ θ x) • h x ∂μ

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [InnerProductSpace ℝ E] [NormedSpace ℝ F] in
lemma growth_exp_bound {h : E → F} (hg : HasGrowth h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖h x‖ ≤ C*Real.exp ‖x‖ := by
  obtain ⟨C,hC,n,hn⟩ := hg
  refine ⟨C*(1+(n.factorial:ℝ)),by positivity,fun x => ?_⟩
  have hh := (div_le_iff₀ (by positivity : (0:ℝ)<n.factorial)).mp
    (Real.pow_div_factorial_le_exp ‖x‖ (norm_nonneg x) n)
  have he : 1 ≤ Real.exp ‖x‖ := Real.one_le_exp (norm_nonneg x)
  have ht := mul_le_mul_of_nonneg_left (add_le_add he hh) hC
  exact (hn x).trans (ht.trans_eq (by ring))

omit [SecondCountableTopology E] in
lemma HasExpMoments.integrable_laplace {μ : Measure E} (hμ : HasExpMoments μ)
    {h : E → F} (hh : AEStronglyMeasurable h μ) (hg : HasGrowth h) (θ : E) :
    Integrable (fun x => Real.exp (inner ℝ θ x) • h x) μ := by
  obtain ⟨C,hC,hg⟩ := growth_exp_bound hg
  apply ((hμ (‖θ‖+1)).const_mul C).mono'
    (((continuous_const.inner continuous_id).rexp).aestronglyMeasurable.smul hh)
  filter_upwards [] with x
  change ‖Real.exp (inner ℝ θ x) • h x‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have he := mul_le_mul (Real.exp_le_exp.mpr (real_inner_le_norm θ x))
    (hg x) (norm_nonneg _) (Real.exp_pos _).le
  exact he.trans_eq (by rw [show Real.exp (‖θ‖*‖x‖)*(C*Real.exp ‖x‖) =
    C*(Real.exp (‖θ‖*‖x‖)*Real.exp ‖x‖) by ring,← Real.exp_add]; congr 2; ring)

omit [SecondCountableTopology E] in
lemma HasExpMoments.hasMoments {μ : Measure E} (hμ : HasExpMoments μ) : HasMoments μ := by
  intro n
  have hg : HasGrowth (fun x : E => ‖x‖^n) :=
    (HasGrowth.lipschitz (LipschitzWith.id : LipschitzWith 1 (id : E → E))).norm.pow n
  simpa only [inner_zero_left,Real.exp_zero,one_smul,Pi.pow_apply] using
    hμ.integrable_laplace (continuous_norm.pow n).aestronglyMeasurable hg 0

def inserted (h : E → F) (x : E) : E →L[ℝ] F := (innerSL ℝ x).smulRight (h x)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma continuous_inserted {h : E → F} (hh : Continuous h) : Continuous (inserted h) :=
  isBoundedBilinearMap_smulRight.continuous.comp ((innerSL ℝ).continuous.prodMk hh)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma growth_inserted {h : E → F} (hg : HasGrowth h) : HasGrowth (inserted h) := by
  obtain ⟨C,hC,n,hn⟩ := hg
  refine ⟨2*C,by positivity,n+1,fun x => ?_⟩
  have hb : ‖inserted h x‖ ≤ ‖x‖*‖h x‖ := by
    simp [inserted,ContinuousLinearMap.norm_smulRight_apply]
  have hp := pow_le_one_add_pow_add (norm_nonneg x) 1 n
  rw [pow_one,Nat.add_comm 1 n] at hp
  have hh := mul_le_mul_of_nonneg_left (hn x) (norm_nonneg x)
  have hh' := hb.trans hh
  have hp' : ‖x‖*‖x‖^n=‖x‖^(n+1) := (pow_succ' _ _).symm
  nlinarith [mul_le_mul_of_nonneg_left hp hC,mul_nonneg hC (pow_nonneg (norm_nonneg x) (n+1)),congrArg (fun z : ℝ => C*z) hp']

lemma hasFDerivAt_laplace {μ : Measure E} (hμ : HasExpMoments μ)
    {h : E → F} (hh : Continuous h) (hg : HasGrowth h) (θ : E) :
    HasFDerivAt (laplace μ h) (laplace μ (inserted h) θ) θ := by
  obtain ⟨C,hC,hg'⟩ := growth_exp_bound (growth_inserted hg)
  let M := ‖θ‖+1
  let b : E → ℝ := fun x => C*Real.exp ((M+1)*‖x‖)
  have hd (x t : E) : HasFDerivAt (fun z : E => Real.exp (inner ℝ z x) • h x)
      (Real.exp (inner ℝ t x) • inserted h x) t := by
    have hh := ((innerSL ℝ x).hasFDerivAt (x := t)).exp.smul_const (h x)
    convert hh using 1
    · funext z; simp only [innerSL_apply_apply,real_inner_comm z x]
    · ext z; simp [inserted,real_inner_comm,smul_smul]
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun t x => Real.exp (inner ℝ t x) • inserted h x)
    (bound := b) (Metric.ball_mem_nhds θ (show (0:ℝ)<1 by norm_num))
  · exact Eventually.of_forall fun t => (hμ.integrable_laplace hh.aestronglyMeasurable hg t).aestronglyMeasurable
  · exact hμ.integrable_laplace hh.aestronglyMeasurable hg θ
  · exact (hμ.integrable_laplace (continuous_inserted hh).aestronglyMeasurable (growth_inserted hg) θ).aestronglyMeasurable
  · filter_upwards [] with x t ht
    have htm : ‖t‖ ≤ M := by
      have hb : ‖t-θ‖<1 := by simpa [dist_eq_norm] using ht
      have hn := norm_add_le (t-θ) θ
      simp only [sub_add_cancel] at hn
      dsimp [M]; linarith
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    have he := (real_inner_le_norm t x).trans (mul_le_mul_of_nonneg_right htm (norm_nonneg x))
    have h := mul_le_mul (Real.exp_le_exp.mpr he) (hg' x) (norm_nonneg _) (Real.exp_pos _).le
    exact h.trans_eq (by dsimp [b]; rw [show Real.exp (M*‖x‖)*(C*Real.exp ‖x‖) =
      C*(Real.exp (M*‖x‖)*Real.exp ‖x‖) by ring,← Real.exp_add]; congr 2; ring)
  · exact (hμ (M+1)).const_mul C
  · exact Eventually.of_forall fun x t _ => hd x t

lemma contDiff_laplace {μ : Measure E} (hμ : HasExpMoments μ)
    {h : E → F} (hh : Continuous h) (hg : HasGrowth h) :
    ContDiff ℝ (⊤ : ℕ∞) (laplace μ h) := by
  apply contDiff_infty.mpr
  intro n
  induction n generalizing F with
  | zero => exact contDiff_zero.mpr (show Differentiable ℝ (laplace μ h) from
      fun θ => (hasFDerivAt_laplace hμ hh hg θ).differentiableAt).continuous
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_fderiv]
    refine ⟨fun θ => (hasFDerivAt_laplace hμ hh hg θ).differentiableAt,by simp,?_⟩
    have he : fderiv ℝ (laplace μ h) = laplace μ (inserted h) := by
      funext θ; exact (hasFDerivAt_laplace hμ hh hg θ).fderiv
    rw [he]
    exact ih (continuous_inserted hh) (growth_inserted hg)

omit [SecondCountableTopology E] in
lemma laplace_one_pos {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) (θ : E) : 0 < laplace μ (fun _ => (1:ℝ)) θ := by
  exact (integral_pos_iff_support_of_nonneg (fun x => by
    simp only [smul_eq_mul,mul_one]; exact (Real.exp_pos _).le)
    (hμ.integrable_laplace aestronglyMeasurable_const (HasGrowth.const (1:ℝ)) θ)).2
    (by simp [Function.support,Real.exp_ne_zero])

end Appell
end LogConcaveSampling

namespace LogConcaveSampling
namespace JetCalculus
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*}

def dir (v : E) (f : E → ℝ) : E → ℝ := fun x => fderiv ℝ f x v

def jet (v : ι → E) : List ι → (E → ℝ) → (E → ℝ)
  | [], f => f
  | i::l, f => dir (v i) (jet v l f)

lemma smooth_dir {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : E) :
    ContDiff ℝ (⊤ : ℕ∞) (dir v f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma smooth_jet {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : ι → E) (l : List ι) :
    ContDiff ℝ (⊤ : ℕ∞) (jet v l f) := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact smooth_dir ih _

lemma dir_add {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (v : E) :
    dir v (fun x => f x+g x) = fun x => dir v f x+dir v g x := by
  funext x
  change (fderiv ℝ (f+g) x) v = _
  rw [fderiv_add (hf x) (hg x)]
  rfl

lemma dir_mul {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (v : E) :
    dir v (fun x => f x*g x) = fun x => dir v f x*g x+f x*dir v g x := by
  funext x
  change (fderiv ℝ (f*g) x) v = _
  rw [((hf x).hasFDerivAt.mul (hg x).hasFDerivAt).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,dir]
  ring

lemma dir_sum {κ : Type*} (s : Finset κ) {f : κ → E → ℝ}
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) (v : E) :
    dir v (fun x => ∑ i ∈ s, f i x) = fun x => ∑ i ∈ s, dir v (f i) x := by
  funext x
  simp only [dir,(HasFDerivAt.fun_sum (fun i hi => (hf i hi x).hasFDerivAt)).fderiv,
    sum_apply]

lemma jet_add {f g : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : ι → E) (l : List ι) :
    jet v l (fun x => f x+g x) = fun x => jet v l f x+jet v l g x := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [jet,ih]
    exact dir_add ((smooth_jet hf v l).differentiable (by simp))
      ((smooth_jet hg v l).differentiable (by simp)) _

lemma jet_sum {κ : Type*} (s : Finset κ) {f : κ → E → ℝ}
    (hf : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (f i)) (v : ι → E) (l : List ι) :
    jet v l (fun x => ∑ i ∈ s, f i x) = fun x => ∑ i ∈ s, jet v l (f i) x := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [jet,ih]
    exact dir_sum s (fun j hj => (smooth_jet (hf j hj) v l).differentiable (by simp)) _

lemma jet_const (v : ι → E) (l : List ι) (c : ℝ) :
    jet v l (fun _ => c) = if l=[] then (fun _ => c) else (fun _ => 0) := by
  induction l with
  | nil => simp [jet]
  | cons i l ih =>
    simp only [jet,ih,List.cons_ne_nil,↓reduceIte]
    split_ifs <;> funext x <;> simp [dir]

section
variable [DecidableEq ι]
lemma filter_insert_of_not_mem (l : List ι) (i : ι) (s : Finset ι) (hi : i ∉ l) :
    l.filter (fun j => j ∈ insert i s) = l.filter (fun j => j ∈ s) := by
  apply List.filter_congr
  intro j hj
  have hji : j ≠ i := by intro h; subst j; exact hi hj
  simp [hji]

lemma filter_not_insert_of_not_mem (l : List ι) (i : ι) (s : Finset ι) (hi : i ∉ l) :
    l.filter (fun j => j ∉ insert i s) = l.filter (fun j => j ∉ s) := by
  apply List.filter_congr
  intro j hj
  have hji : j ≠ i := by intro h; subst j; exact hi hj
  simp [hji]

theorem jet_mul {f g : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : ι → E) (l : List ι) (hl : l.Nodup) :
    jet v l (fun x => f x*g x) = fun x =>
      ∑ s ∈ l.toFinset.powerset,
        jet v (l.filter (fun i => i ∈ s)) f x *
          jet v (l.filter (fun i => i ∉ s)) g x := by
  induction l with
  | nil => simp [jet]
  | cons i l ih =>
    have hi := (List.nodup_cons.mp hl).1
    have hl' := (List.nodup_cons.mp hl).2
    rw [jet,ih hl',dir_sum _ (fun s hs =>
      ((smooth_jet hf v _).mul (smooth_jet hg v _)).differentiable (by simp))]
    funext x
    simp only [List.toFinset_cons,Finset.sum_powerset_insert (by simpa using hi : i ∉ l.toFinset)]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    have his : i ∉ s := fun h => hi (List.mem_toFinset.mp ((Finset.mem_powerset.mp hs) h))
    rw [dir_mul ((smooth_jet hf v _).differentiable (by simp))
      ((smooth_jet hg v _).differentiable (by simp))]
    simp only [List.filter_cons,Finset.mem_insert_self,decide_true,↓reduceIte,
      his,decide_false,Bool.false_eq_true,not_false_eq_true,Finset.mem_insert_self,
      not_true_eq_false,filter_insert_of_not_mem l i s hi,filter_not_insert_of_not_mem l i s hi,jet]
    ring
end
end JetCalculus
end LogConcaveSampling
namespace LogConcaveSampling
namespace JetCalculus
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*}

lemma jet_append (v : ι → E) (l k : List ι) (f : E → ℝ) :
    jet v (l++k) f = jet v l (jet v k f) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.cons_append,jet,ih]

lemma dir_const_mul {f : E → ℝ} (hf : Differentiable ℝ f) (v : E) (c : ℝ) :
    dir v (fun x => c*f x) = fun x => c*dir v f x := by
  funext x
  change (fderiv ℝ (fun x => c*f x) x) v = _
  rw [((hf x).hasFDerivAt.const_mul c).fderiv]
  simp [dir]

lemma jet_const_mul {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v : ι → E) (l : List ι) (c : ℝ) :
    jet v l (fun x => c*f x) = fun x => c*jet v l f x := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [jet,ih]
    exact dir_const_mul ((smooth_jet hf v l).differentiable (by simp)) _ _

lemma jet_sub {f g : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : ι → E) (l : List ι) :
    jet v l (fun x => f x-g x) = fun x => jet v l f x-jet v l g x := by
  rw [show (fun x => f x-g x) = (fun x => f x+(-1)*g x) by funext x; ring,
    jet_add hf (contDiff_const.mul hg),jet_const_mul hg]
  funext x; ring

lemma filter_length_add (l : List ι) (p : ι → Bool) :
    (l.filter p).length+(l.filter (fun i => !(p i))).length=l.length := by
  induction l with
  | nil => simp
  | cons i l ih =>
    cases hp : p i <;> simp only [List.filter_cons, hp, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega

section
variable [DecidableEq ι]

lemma jet_pow_zero {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v : ι → E) (m : ℕ) (l : List ι) (hl : l.Nodup) {x : E}
    (hx : f x=0) (hm : l.length < m) : jet v l (fun x => (f x)^m) x=0 := by
  induction m generalizing l with
  | zero => omega
  | succ m ih =>
    rw [show (fun x => (f x)^(m+1)) = (fun x => f x*(f x)^m) by funext y; rw [pow_succ'],
      jet_mul hf (hf.pow m) v l hl]
    apply Finset.sum_eq_zero
    intro s hs
    by_cases hs0 : s=∅
    · subst s; simp [jet,hx]
    · have hlpos : 0 < (l.filter (fun j => j ∈ s)).length := by
        obtain ⟨j,hj⟩ := Finset.nonempty_iff_ne_empty.mpr hs0
        have hjl : j ∈ l := List.mem_toFinset.mp ((Finset.mem_powerset.mp hs) hj)
        exact List.length_pos_iff.mpr (fun hz => by
          have hmem : j ∈ l.filter (fun j => j ∈ s) := by simp [hjl,hj]
          rw [hz] at hmem; simp at hmem)
      have hlen := filter_length_add l (fun j => decide (j ∈ s))
      have hlen' : (l.filter (fun j => j ∉ s)).length < m := by
        simpa only [← decide_not] using (show (l.filter (fun j => !(decide (j ∈ s)))).length < m by omega)
      rw [ih _ (hl.filter _) hlen',mul_zero]

lemma jet_pow_mul_zero {f g : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : ι → E) (m : ℕ) (l : List ι)
    (hl : l.Nodup) {x : E} (hx : f x=0) (hm : l.length < m) :
    jet v l (fun x => (f x)^m*g x) x=0 := by
  rw [jet_mul (hf.pow m) hg v l hl]
  apply Finset.sum_eq_zero
  intro s hs
  rw [jet_pow_zero hf v m _ (hl.filter _) hx
    ((List.length_filter_le _ _).trans_lt hm),zero_mul]
end
end JetCalculus
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
