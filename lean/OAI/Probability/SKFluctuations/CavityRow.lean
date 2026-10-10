import Mathlib
import OAI.Probability.SKFluctuations.MarkedAttachPreserves

namespace OAI

/-! Cavity Row. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace Cavity

 
def oldEdge {n : ℕ} (e : Edge n) : Edge (n+1) :=
  ⟨(e.val.1.castSucc, e.val.2.castSucc), e.property⟩

 
def rowEdge {n : ℕ} (i : Fin n) : Edge (n+1) :=
  ⟨(i.castSucc, Fin.last n), Fin.castSucc_lt_last i⟩

def joinEdge {n : ℕ} : Edge n ⊕ Fin n → Edge (n+1)
  | Sum.inl e => oldEdge e
  | Sum.inr i => rowEdge i

theorem joinEdge_injective (n : ℕ) : Function.Injective (@joinEdge n) := by
  intro a b h
  cases a with
  | inl e =>
    cases b with
    | inl f =>
      congr 1
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext
      · exact congrArg (fun z : Edge (n+1) => z.val.1.val) h
      · exact congrArg (fun z : Edge (n+1) => z.val.2.val) h
    | inr i =>
      have he := congrArg (fun z : Edge (n+1) => z.val.2.val) h
      exact (Nat.ne_of_lt e.val.2.isLt he).elim
  | inr i =>
    cases b with
    | inl e =>
      have he := congrArg (fun z : Edge (n+1) => z.val.2.val) h
      exact (Nat.ne_of_lt e.val.2.isLt he.symm).elim
    | inr j =>
      congr 1
      apply Fin.ext
      exact congrArg (fun z : Edge (n+1) => z.val.1.val) h

theorem joinEdge_surjective (n : ℕ) : Function.Surjective (@joinEdge n) := by
  intro e
  have hfirst : e.val.1.val < n := by
    have h := e.property
    have hj := e.val.2.isLt
    omega
  by_cases hlast : e.val.2.val < n
  · refine ⟨Sum.inl ⟨(⟨e.val.1.val,hfirst⟩,⟨e.val.2.val,hlast⟩),e.property⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> rfl
  · refine ⟨Sum.inr ⟨e.val.1.val,hfirst⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · rfl
    · dsimp [joinEdge,rowEdge]
      have hj := e.val.2.isLt
      omega

noncomputable def edgeEquiv (n : ℕ) : Edge n ⊕ Fin n ≃ Edge (n+1) :=
  Equiv.ofBijective joinEdge ⟨joinEdge_injective n,joinEdge_surjective n⟩

theorem sum_edges {n : ℕ} (f : Edge (n+1) → ℝ) :
    ∑ e, f e = (∑ e : Edge n, f (oldEdge e)) + ∑ i : Fin n, f (rowEdge i) := by
  rw [← (edgeEquiv n).sum_comp f]
  exact Fintype.sum_sum_type _

 
def restDisorder {n : ℕ} (g : Disorder (n+1)) : Disorder n := fun e => g (oldEdge e)
def rowDisorder {n : ℕ} (g : Disorder (n+1)) : Fin n → ℝ := fun i => g (rowEdge i)
def restSpin {n : ℕ} (σ : Spin (n+1)) : Spin n := fun i => σ i.castSucc

def rowField (beta : ℝ) (n : ℕ) (g : Fin n → ℝ) (σ : Spin n) : ℝ :=
  beta / Real.sqrt (n+1 : ℕ) * ∑ i, g i * spinValue (σ i)

 
def restHamiltonian (beta : ℝ) (n : ℕ) (g : Disorder n) (σ : Spin n) : ℝ :=
  beta / Real.sqrt (n+1 : ℕ) *
    ∑ e : Edge n, g e * spinValue (σ e.val.1) * spinValue (σ e.val.2)

theorem hamiltonian_one_site (beta : ℝ) (n : ℕ) (g : Disorder (n+1))
    (σ : Spin (n+1)) :
    hamiltonian beta (n+1) g σ =
      restHamiltonian beta n (restDisorder g) (restSpin σ) +
      spinValue (σ (Fin.last n)) * rowField beta n (rowDisorder g) (restSpin σ) := by
  unfold hamiltonian
  rw [sum_edges]
  simp only [oldEdge,rowEdge,restHamiltonian,rowField,restDisorder,rowDisorder,restSpin,
    ]
  rw [← Finset.sum_mul]
  ring

 

def restBeta (beta : ℝ) (n : ℕ) : ℝ := beta * Real.sqrt n / Real.sqrt (n+1 : ℕ)

theorem restHamiltonian_eq (beta : ℝ) {n : ℕ} (hn : 0 < n) (g : Disorder n) (σ : Spin n) :
    restHamiltonian beta n g σ = hamiltonian (restBeta beta n) n g σ := by
  have hs : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (Nat.cast_pos.2 hn))
  unfold restHamiltonian hamiltonian restBeta
  congr 1
  field_simp

 

theorem disorderLaw_one_site (n : ℕ) :
    MeasurePreserving (fun g : Disorder (n+1) => (restDisorder g,rowDisorder g))
      (disorderLaw (n+1))
      ((disorderLaw n).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)) := by
  have h₁ := (measurePreserving_piCongrLeft
    (fun _ : Edge (n+1) => gaussianReal 0 1) (edgeEquiv n)).symm
  have h₂ := measurePreserving_sumPiEquivProdPi
    (fun _ : Edge n ⊕ Fin n => gaussianReal 0 1)
  exact h₂.comp h₁

 
def joinSpin {n : ℕ} (p : Spin n × Bool) : Spin (n+1) :=
  Fin.lastCases p.2 p.1

@[simp] theorem joinSpin_old {n : ℕ} (p : Spin n × Bool) (i : Fin n) :
    joinSpin p i.castSucc = p.1 i := by simp [joinSpin]

@[simp] theorem joinSpin_last {n : ℕ} (p : Spin n × Bool) :
    joinSpin p (Fin.last n) = p.2 := by simp [joinSpin]

def spinEquiv (n : ℕ) : Spin n × Bool ≃ Spin (n+1) where
  toFun := joinSpin
  invFun σ := (restSpin σ, σ (Fin.last n))
  left_inv p := by ext i <;> simp [restSpin]
  right_inv σ := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [restSpin]

theorem sum_spins {n : ℕ} (f : Spin (n+1) → ℝ) :
    ∑ σ, f σ = ∑ τ : Spin n, (f (joinSpin (τ,false)) + f (joinSpin (τ,true))) := by
  rw [← (spinEquiv n).sum_comp f, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [spinEquiv,Equiv.coe_fn_mk,Fintype.sum_bool]
  ring

 

theorem partitionFunction_one_site (beta : ℝ) (n : ℕ) (g : Disorder (n+1)) :
    partitionFunction beta (n+1) g = (2:ℝ)^(-(n:ℤ)) *
      ∑ σ : Spin n, Real.exp (restHamiltonian beta n (restDisorder g) σ) *
        Real.cosh (rowField beta n (rowDisorder g) σ) := by
  unfold partitionFunction
  rw [sum_spins]
  have hrest (σ : Spin n) (s : Bool) : restSpin (joinSpin (σ,s)) = σ := by
    funext i
    simp [restSpin]
  simp_rw [hamiltonian_one_site,hrest,joinSpin_last]
  simp only [spinValue,Bool.false_eq_true,↓reduceIte,neg_one_mul,one_mul]
  have hc (a b : ℝ) : Real.exp (a + -b) + Real.exp (a+b) = 2*(Real.exp a*Real.cosh b) := by
    rw [Real.cosh_eq,Real.exp_add,Real.exp_add]
    ring
  simp_rw [hc]
  rw [← Finset.mul_sum,← mul_assoc]
  congr 1
  rw [Nat.cast_add,Nat.cast_one,neg_add, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
  norm_num
  ring

 
def deletedOverlap (n : ℕ) (σ τ : Spin (n+1)) : ℝ :=
  (∑ i : Fin n, spinValue (σ i.castSucc)*spinValue (τ i.castSucc))/(n+1 : ℕ)

theorem deletedOverlap_eq (n : ℕ) (σ τ : Spin (n+1)) :
    deletedOverlap n σ τ = orderedOverlap (n+1) σ τ -
      spinValue (σ (Fin.last n))*spinValue (τ (Fin.last n))/(n+1 : ℕ) := by
  rw [orderedOverlap,Fin.sum_univ_castSucc]
  unfold deletedOverlap
  ring

theorem deletedOverlap_self (n : ℕ) (σ : Spin (n+1)) :
    deletedOverlap n σ σ = (n:ℝ)/(n+1 : ℕ) := by
  simp [deletedOverlap,spinValue_sq]

theorem abs_deletedOverlap_sub (n : ℕ) (σ τ : Spin (n+1)) :
    |deletedOverlap n σ τ - orderedOverlap (n+1) σ τ| = 1/(n+1 : ℕ) := by
  rw [deletedOverlap_eq]
  have ha (s : Bool) : |spinValue s| = 1 := by cases s <;> norm_num [spinValue]
  have hs : orderedOverlap (n+1) σ τ -
      spinValue (σ (Fin.last n))*spinValue (τ (Fin.last n))/(n+1 : ℕ) -
      orderedOverlap (n+1) σ τ =
      -(spinValue (σ (Fin.last n))*spinValue (τ (Fin.last n))/(n+1 : ℕ)) := by ring
  rw [hs,abs_neg,abs_div,abs_mul,ha,ha,abs_of_nonneg (Nat.cast_nonneg _) ,one_mul]

 

def rowInteractionCoefficient (n : ℕ) (σ : Spin (n+1)) (i : Fin n) : ℝ :=
  spinValue (σ (Fin.last n))*spinValue (σ i.castSucc)/Real.sqrt (n+1 : ℕ)

theorem rowInteraction_covariance (n : ℕ) (σ τ : Spin (n+1)) (b : ℝ) :
    (∑ i : Fin n, b*rowInteractionCoefficient n σ i*rowInteractionCoefficient n τ i) =
      spinValue (σ (Fin.last n))*spinValue (τ (Fin.last n))*b*deletedOverlap n σ τ := by
  have hs : (Real.sqrt (n+1 : ℕ))^2 = (n+1 : ℕ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have he (i : Fin n) :
      b*rowInteractionCoefficient n σ i*rowInteractionCoefficient n τ i =
        (spinValue (σ (Fin.last n))*spinValue (τ (Fin.last n))*b/(n+1 : ℕ))*
          (spinValue (σ i.castSucc)*spinValue (τ i.castSucc)) := by
    unfold rowInteractionCoefficient
    calc
      _ = (spinValue (σ (Fin.last n))*spinValue (τ (Fin.last n))*b/
          (Real.sqrt (n+1 : ℕ))^2)*
            (spinValue (σ i.castSucc)*spinValue (τ i.castSucc)) := by ring
      _ = _ := by rw [hs]
  simp_rw [he]
  rw [← Finset.mul_sum]
  unfold deletedOverlap
  ring

 

def actualRowClock (n : ℕ) (b h : ℝ) (σ τ : Spin (n+1)) : ℝ :=
  h+b*deletedOverlap n σ τ

theorem actualRowClock_error (n : ℕ) (b h S : ℝ) (σ τ : Spin (n+1)) :
    actualRowClock n b h σ τ - (h+b*S) = b*(deletedOverlap n σ τ-S) := by
  unfold actualRowClock
  ring

theorem actualRowClock_error_full (n : ℕ) (b h S : ℝ) (σ τ : Spin (n+1)) :
    actualRowClock n b h σ τ - (h+b*S) =
      b*(orderedOverlap (n+1) σ τ-S) -
        b*spinValue (σ (Fin.last n))*spinValue (τ (Fin.last n))/(n+1 : ℕ) := by
  rw [actualRowClock_error,deletedOverlap_eq]
  ring

theorem actualRow_diagonal (n : ℕ) (b h : ℝ) (σ : Spin (n+1)) :
    actualRowClock n b h σ σ = h+b*(n:ℝ)/(n+1 : ℕ) := by
  rw [actualRowClock,deletedOverlap_self]
  ring

 

abbrev RowCoordinate (n : ℕ) := Fin n ⊕ Bool

def mixedCoefficient (n : ℕ) (σ : Spin (n+1)) : RowCoordinate n → ℝ
  | Sum.inl i => rowInteractionCoefficient n σ i
  | Sum.inr _ => spinValue (σ (Fin.last n))

 

def mixedVariance (n : ℕ) (t b h K : ℝ) : RowCoordinate n → ℝ
  | Sum.inl _ => t*b
  | Sum.inr false => t*h
  | Sum.inr true => (1-t)*K

theorem mixedVariance_nonneg (n : ℕ) {t b h K : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hb : 0 ≤ b) (hh : 0 ≤ h) (hK : 0 ≤ K) :
    ∀ j, 0 ≤ mixedVariance n t b h K j := by
  intro j
  cases j with
  | inl i => exact mul_nonneg ht.1 hb
  | inr s => cases s
             · exact mul_nonneg ht.1 hh
             · exact mul_nonneg (sub_nonneg.2 ht.2) hK

def mixedVarianceNN (n : ℕ) (t b h K : ℝ) : RowCoordinate n → ℝ≥0 :=
  fun j => Real.toNNReal (mixedVariance n t b h K j)

theorem mixedVarianceNN_coe (n : ℕ) {t b h K : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hb : 0 ≤ b) (hh : 0 ≤ h) (hK : 0 ≤ K)
    (j : RowCoordinate n) :
    (mixedVarianceNN n t b h K j : ℝ) = mixedVariance n t b h K j :=
  Real.coe_toNNReal _ (mixedVariance_nonneg n ht hb hh hK j)

def mixedRowClock (n : ℕ) (t b h K : ℝ) (σ τ : Spin (n+1)) : ℝ :=
  (1-t)*K+t*actualRowClock n b h σ τ

theorem mixedRow_covariance (n : ℕ) (t b h K : ℝ) (σ τ : Spin (n+1)) :
    (∑ j : RowCoordinate n,
      mixedVariance n t b h K j*mixedCoefficient n σ j*mixedCoefficient n τ j) =
    spinValue (σ (Fin.last n))*spinValue (τ (Fin.last n))*mixedRowClock n t b h K σ τ := by
  rw [Fintype.sum_sum_type]
  simp only [mixedVariance,mixedCoefficient,Fintype.sum_bool]
  rw [rowInteraction_covariance]
  unfold mixedRowClock actualRowClock
  ring

@[simp] theorem mixedRowClock_zero (n : ℕ) (b h K : ℝ) (σ τ : Spin (n+1)) :
    mixedRowClock n 0 b h K σ τ = K := by simp [mixedRowClock]

@[simp] theorem mixedRowClock_one (n : ℕ) (b h K : ℝ) (σ τ : Spin (n+1)) :
    mixedRowClock n 1 b h K σ τ = actualRowClock n b h σ τ := by
  simp [mixedRowClock]

theorem mixedRowClock_full_path (n : ℕ) (t b h S : ℝ) (σ τ : Spin (n+1)) :
    mixedRowClock n t b h (h+b*S) σ τ =
      h+b*S+t*b*(deletedOverlap n σ τ-S) := by
  unfold mixedRowClock actualRowClock
  ring

 

theorem mixedRow_covariance_posSemidefinite {A : Type*} [Fintype A]
    (n : ℕ) {t b h K : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hb : 0 ≤ b) (hh : 0 ≤ h) (hK : 0 ≤ K) (σ : A → Spin (n+1)) (c : A → ℝ) :
    0 ≤ ∑ a, ∑ d, c a*c d*
      (spinValue (σ a (Fin.last n))*spinValue (σ d (Fin.last n))*
        mixedRowClock n t b h K (σ a) (σ d)) := by
  simp_rw [← mixedRow_covariance]
  simp_rw [Finset.mul_sum]
  have hs : (∑ a, ∑ d, ∑ j : RowCoordinate n,
      c a*c d*(mixedVariance n t b h K j*mixedCoefficient n (σ a) j*
        mixedCoefficient n (σ d) j)) =
      ∑ j : RowCoordinate n, ∑ a, ∑ d,
      c a*c d*(mixedVariance n t b h K j*mixedCoefficient n (σ a) j*
        mixedCoefficient n (σ d) j) := by
    calc
      _ = ∑ a, ∑ j : RowCoordinate n, ∑ d,
          c a*c d*(mixedVariance n t b h K j*mixedCoefficient n (σ a) j*
            mixedCoefficient n (σ d) j) := by
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hs]
  have he (j : RowCoordinate n) :
      (∑ a, ∑ d, c a*c d*(mixedVariance n t b h K j*
          mixedCoefficient n (σ a) j*mixedCoefficient n (σ d) j)) =
      mixedVariance n t b h K j*(∑ a, c a*mixedCoefficient n (σ a) j)^2 := by
    rw [pow_two,Finset.sum_mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  simp_rw [he]
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (mixedVariance_nonneg n ht hb hh hK j) (sq_nonneg _)

 

def relocatedClock {J : Type*} [LinearOrder J] (U : J) (l : ℝ) (f : J → ℝ)
    (u : J) : ℝ := if u < U then l*f u else f u

theorem relocatedClock_monotone {J : Type*} [LinearOrder J] (U : J) {l : ℝ}
    (hl : l ∈ Set.Icc (0:ℝ) 1) {f : J → ℝ}
    (hf : Monotone f) (hf0 : ∀ u, 0 ≤ f u) : Monotone (relocatedClock U l f) := by
  intro u v huv
  by_cases hu : u < U <;> by_cases hv : v < U
  · exact (by simpa [relocatedClock,hu,hv] using mul_le_mul_of_nonneg_left (hf huv) hl.1)
  · simp only [relocatedClock,hu,hv,↓reduceIte]
    exact (mul_le_of_le_one_left (hf0 u) hl.2).trans (hf huv)
  · exact (hu (lt_of_le_of_lt huv hv)).elim
  · simpa [relocatedClock,hu,hv] using hf huv

theorem relocatedClock_nonneg {J : Type*} [LinearOrder J] (U : J) {l : ℝ}
    (hl : 0 ≤ l) {f : J → ℝ} (hf : ∀ u, 0 ≤ f u) (u : J) :
    0 ≤ relocatedClock U l f u := by
  by_cases h : u < U <;> simp only [relocatedClock,h,↓reduceIte]
  · exact mul_nonneg hl (hf u)
  · exact hf u

theorem relocatedClock_le {J : Type*} [LinearOrder J] (U : J) {l : ℝ}
    (hl : l ≤ 1) {f : J → ℝ} (hf : ∀ u, 0 ≤ f u) (u : J) :
    relocatedClock U l f u ≤ f u := by
  by_cases h : u < U <;> simp only [relocatedClock,h,↓reduceIte]
  · exact mul_le_of_le_one_left (hf u) hl
  · exact le_rfl

@[simp] theorem relocatedClock_one {J : Type*} [LinearOrder J]
    (U : J) (f : J → ℝ) : relocatedClock U 1 f = f := by
  funext u
  simp [relocatedClock]

 

theorem relocated_mixedRowClock {J : Type*} [LinearOrder J]
    (n : ℕ) (U u : J) (l t : ℝ) (b h S : J → ℝ) (σ τ : Spin (n+1)) :
    relocatedClock U l (fun v => mixedRowClock n t (b v) (h v)
        (h v+b v*S v) σ τ) u =
      relocatedClock U l (fun v => h v+b v*S v) u +
      t*relocatedClock U l (fun v => b v*(deletedOverlap n σ τ-S v)) u := by
  by_cases hu : u < U
  all_goals simp only [relocatedClock,hu,↓reduceIte,mixedRowClock_full_path]; ring

 
theorem relocatedRow_hasDerivAt_t {J : Type*} [LinearOrder J]
    (n : ℕ) (U u : J) (l t : ℝ) (b h S : J → ℝ) (σ τ : Spin (n+1)) :
    HasDerivAt (fun v => relocatedClock U l (fun q =>
      mixedRowClock n v (b q) (h q) (h q+b q*S q) σ τ) u)
      (relocatedClock U l (fun q => b q*(deletedOverlap n σ τ-S q)) u) t := by
  simp_rw [relocated_mixedRowClock]
  have hd : HasDerivAt (fun v : ℝ =>
      v*relocatedClock U l (fun q => b q*(deletedOverlap n σ τ-S q)) u)
      (relocatedClock U l (fun q => b q*(deletedOverlap n σ τ-S q)) u) t := by
    simpa only [id_eq,one_mul] using (hasDerivAt_id t).mul_const
      (relocatedClock U l (fun q => b q*(deletedOverlap n σ τ-S q)) u)
  exact hd.const_add _

 

theorem relocatedRow_hasDerivAt_l {J : Type*} [LinearOrder J]
    (n : ℕ) (U u : J) (l t : ℝ) (b h S : J → ℝ) (σ τ : Spin (n+1)) :
    HasDerivAt (fun v => relocatedClock U v (fun q =>
      mixedRowClock n t (b q) (h q) (h q+b q*S q) σ τ) u)
      (if u < U then h u+b u*S u+t*b u*(deletedOverlap n σ τ-S u) else 0) l := by
  by_cases hu : u < U
  · simp only [relocatedClock,hu,↓reduceIte,mixedRowClock_full_path]
    simpa using (hasDerivAt_id l).mul_const
      (h u+b u*S u+t*b u*(deletedOverlap n σ τ-S u))
  · simp only [relocatedClock,hu,↓reduceIte]
    exact hasDerivAt_const _ _

 

theorem mixedVariance_monotone {J : Type*} [Preorder J]
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    {b h K : J → ℝ} (hb : Monotone b) (hh : Monotone h) (hK : Monotone K)
    (j : RowCoordinate n) : Monotone (fun u => mixedVariance n t (b u) (h u) (K u) j) := by
  cases j with
  | inl i => exact fun _ _ huv => mul_le_mul_of_nonneg_left (hb huv) ht.1
  | inr s => cases s
             · exact fun _ _ huv => mul_le_mul_of_nonneg_left (hh huv) ht.1
             · exact fun _ _ huv => mul_le_mul_of_nonneg_left (hK huv) (sub_nonneg.2 ht.2)

 

theorem scalarClock_monotone {J : Type*} [Preorder J]
    {b h S : J → ℝ} (hb : Monotone b) (hh : Monotone h) (hS : Monotone S)
    (hb0 : ∀ u, 0 ≤ b u) (hS0 : ∀ u, 0 ≤ S u) :
    Monotone (fun u => h u+b u*S u) := by
  intro u v huv
  exact add_le_add (hh huv) (mul_le_mul (hb huv) (hS huv) (hS0 u) (hb0 v))

 

def relocatedVariance {J : Type*} [LinearOrder J] (n : ℕ) (U : J)
    (l t : ℝ) (b h K : J → ℝ) (u : J) (j : RowCoordinate n) : ℝ :=
  relocatedClock U l (fun v => mixedVariance n t (b v) (h v) (K v) j) u

theorem relocatedVariance_monotone {J : Type*} [LinearOrder J] (n : ℕ) (U : J)
    {l t : ℝ} (hl : l ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1)
    {b h K : J → ℝ} (hb : Monotone b) (hh : Monotone h) (hK : Monotone K)
    (hb0 : ∀ u, 0 ≤ b u) (hh0 : ∀ u, 0 ≤ h u) (hK0 : ∀ u, 0 ≤ K u)
    (j : RowCoordinate n) : Monotone (fun u => relocatedVariance n U l t b h K u j) := by
  exact relocatedClock_monotone U hl (mixedVariance_monotone n ht hb hh hK j)
    (fun u => mixedVariance_nonneg n ht (hb0 u) (hh0 u) (hK0 u) j)

theorem relocatedVariance_increment_nonneg {J : Type*} [LinearOrder J]
    (n : ℕ) (U : J) {l t : ℝ} (hl : l ∈ Set.Icc (0:ℝ) 1)
    (ht : t ∈ Set.Icc (0:ℝ) 1) {b h K : J → ℝ}
    (hb : Monotone b) (hh : Monotone h) (hK : Monotone K)
    (hb0 : ∀ u, 0 ≤ b u) (hh0 : ∀ u, 0 ≤ h u) (hK0 : ∀ u, 0 ≤ K u)
    {u v : J} (huv : u ≤ v) (j : RowCoordinate n) :
    0 ≤ relocatedVariance n U l t b h K v j-relocatedVariance n U l t b h K u j :=
  sub_nonneg.2 (relocatedVariance_monotone n U hl ht hb hh hK hb0 hh0 hK0 j huv)

theorem relocatedRow_covariance {J : Type*} [LinearOrder J]
    (n : ℕ) (U u : J) (l t : ℝ) (b h K : J → ℝ) (σ τ : Spin (n+1)) :
    (∑ j : RowCoordinate n, relocatedVariance n U l t b h K u j*
      mixedCoefficient n σ j*mixedCoefficient n τ j) =
    spinValue (σ (Fin.last n))*spinValue (τ (Fin.last n))*
      relocatedClock U l (fun v => mixedRowClock n t (b v) (h v) (K v) σ τ) u := by
  by_cases hu : u < U
  · simp only [relocatedVariance,relocatedClock,hu,↓reduceIte]
    have hm : (∑ j : RowCoordinate n, l*mixedVariance n t (b u) (h u) (K u) j*
        mixedCoefficient n σ j*mixedCoefficient n τ j) =
        l*∑ j : RowCoordinate n, mixedVariance n t (b u) (h u) (K u) j*
          mixedCoefficient n σ j*mixedCoefficient n τ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hm,mixedRow_covariance]
    ring
  · simpa only [relocatedVariance,relocatedClock,hu,↓reduceIte] using
      mixedRow_covariance n t (b u) (h u) (K u) σ τ

 

theorem relocatedVariance_at_cut {J : Type*} [LinearOrder J] (n : ℕ) (U : J)
    (l t : ℝ) (b h K : J → ℝ) (j : RowCoordinate n) :
    relocatedVariance n U l t b h K U j = mixedVariance n t (b U) (h U) (K U) j := by
  simp [relocatedVariance,relocatedClock]

end Cavity
end SKFluctuations

end

end OAI
