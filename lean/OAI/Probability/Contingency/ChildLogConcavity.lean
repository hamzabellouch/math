import Mathlib
import OAI.Probability.Contingency.LawComposition
import OAI.Probability.Contingency.RootTransport

namespace OAI

/-! Child Log Concavity. -/

noncomputable section

open scoped BigOperators
open Filter
open scoped BigOperators
open QuadraticMap Filter

namespace Contingency

 
theorem bool_signature_determinant (M : Bool → Bool → ℝ)
    (hs : sigPos (matrixForm M) ≤ 1) (hm : M true false = M false true)
    (ha : 0 < M true true) :
    M true true * M false false ≤ M true false ^ 2 := by
  let e : Bool → ℝ := fun b => if b then 1 else 0
  let v : Bool → ℝ := fun b => if b then 0 else 1
  have he : matrixForm M e = M true true := by
    simp [matrixForm_apply, e]
  have hv : matrixForm M v = M false false := by
    simp [matrixForm_apply, v]
  have he' : 0 < matrixForm M e := he ▸ ha
  have hve : (matrixForm M).associated v e = M true false := by
    rw [QuadraticMap.associated_apply]
    norm_num
    simp [matrixForm_apply,e,v,hm]
    ring
  have h := positive_projection (matrixForm M) hs e v he'
  rw [he,hv,hve] at h
  have := (le_div_iff₀ ha).mp h
  nlinarith

def childProfile (C j : ℤ) : Bool → ℤ := fun b => if b then j else C-j

 

theorem signature_child_logconcave (C : ℕ) (f : (Bool → ℤ) → ℝ)
    (hp : PositiveSlice f (fun _ => (C:ℤ)) C)
    (hs : HasSignature f (fun _ => (C:ℤ)) C)
    (j : ℤ) (hj : 1 ≤ j) (hjC : j < C) :
    f (childProfile C (j-1)) * f (childProfile C (j+1)) ≤
      f (childProfile C j)^2 := by
  let p : Bool → ℤ := fun b => if b then j+1 else (C:ℤ)-j+1
  have hb : InBox (fun _ => (C:ℤ)) p := by
    intro b; cases b <;> dsimp [p] <;> omega
  have ht : (∑ b, p b) = (C:ℤ)+2 := by simp [p]; omega
  have hrem (i k : Bool) : removePair p i k =
      childProfile C (j+1 - (if i then 1 else 0) - (if k then 1 else 0)) := by
    funext b
    cases i <;> cases k <;> cases b <;> simp [removePair,p,childProfile] <;> omega
  have ha : 0 < f (childProfile C (j-1)) := by
    apply hp.1
    · intro b; cases b <;> dsimp [childProfile] <;> omega
    · simp [childProfile]
  have h := bool_signature_determinant (twoRemoval f p) (hs p hb ht)
    (by simp only [twoRemoval]; rw [removePair_comm])
    (by simpa [twoRemoval,hrem] using ha)
  simpa [twoRemoval,hrem] using h

 

theorem positive_logconcave_min (f : ℤ → ℝ) (a b j : ℤ)
    (haj : a ≤ j) (hjb : j ≤ b)
    (hp : ∀ i ∈ Finset.Icc a b, 0 < f i)
    (hl : ∀ i, a < i → i < b → f (i-1)*f (i+1) ≤ f i ^ 2) :
    min (f a) (f b) ≤ f j := by
  classical
  by_contra hh
  have hh' : f j < min (f a) (f b) := lt_of_not_ge hh
  obtain ⟨k,hk,hmin⟩ := Finset.exists_min_image (Finset.Icc a b) f
    ⟨j,Finset.mem_Icc.mpr ⟨haj,hjb⟩⟩
  let A := (Finset.Icc a b).filter (fun i => f i = f k)
  have hA : A.Nonempty := ⟨k,by simp [A,hk]⟩
  let i := A.min' hA
  have hi : i ∈ A := Finset.min'_mem A hA
  have hi' := Finset.mem_filter.mp hi
  have hib := Finset.mem_Icc.mp hi'.1
  have hik : f i = f k := hi'.2
  have hfi : f i < min (f a) (f b) := by
    rw [hik]; exact lt_of_le_of_lt (hmin j (Finset.mem_Icc.mpr ⟨haj,hjb⟩)) hh'
  have hia : a < i := by
    have hne : i ≠ a := by intro h; rw [h] at hfi; exact (not_lt_of_ge (min_le_left _ _)) hfi
    omega
  have hib' : i < b := by
    have hne : i ≠ b := by intro h; rw [h] at hfi; exact (not_lt_of_ge (min_le_right _ _)) hfi
    omega
  have himem : i-1 ∈ Finset.Icc a b := Finset.mem_Icc.mpr (by omega)
  have hinmem : i+1 ∈ Finset.Icc a b := Finset.mem_Icc.mpr (by omega)
  have hprev : f i < f (i-1) := by
    have hle : f i ≤ f (i-1) := hik ▸ hmin (i-1) himem
    apply lt_of_le_of_ne hle
    intro he
    have hm : i-1 ∈ A := Finset.mem_filter.mpr ⟨himem,he.symm.trans hik⟩
    have := Finset.min'_le A (i-1) hm
    change i ≤ i-1 at this
    omega
  have hnext : f i ≤ f (i+1) := hik ▸ hmin (i+1) hinmem
  have hpos := hp i hi'.1
  have hloc := hl i hia hib'
  have hx := mul_lt_mul_of_pos_right hprev hpos
  have hy := mul_le_mul_of_nonneg_left hnext (le_of_lt (lt_trans hpos hprev))
  nlinarith

 
theorem signature_child_min (C : ℕ) (f : (Bool → ℤ) → ℝ)
    (hp : PositiveSlice f (fun _ => (C:ℤ)) C)
    (hs : HasSignature f (fun _ => (C:ℤ)) C)
    (a b j : ℤ) (ha : 0 ≤ a) (haj : a ≤ j) (hjb : j ≤ b) (hb : b ≤ C) :
    min (f (childProfile C a)) (f (childProfile C b)) ≤ f (childProfile C j) := by
  apply positive_logconcave_min (fun i => f (childProfile C i)) a b j haj hjb
  · intro i hi
    have hi' := Finset.mem_Icc.mp hi
    apply hp.1
    · intro k; cases k <;> dsimp [childProfile] <;> omega
    · simp [childProfile]
  · intro i hi hi'
    exact signature_child_logconcave C f hp hs i (by omega) (by omega)

 

theorem zero_child_min (C : ℕ) (f : ℝ → (Bool → ℤ) → ℝ)
    (hc : ∀ x, Continuous (fun η => f η x))
    (hp : ∀ η, 0 < η → η < 1 → PositiveSlice (f η) (fun _ => (C:ℤ)) C)
    (hs : ∀ η, 0 < η → η < 1 → HasSignature (f η) (fun _ => (C:ℤ)) C)
    (a b j : ℤ) (ha : 0 ≤ a) (haj : a ≤ j) (hjb : j ≤ b) (hb : b ≤ C) :
    min (f 0 (childProfile C a)) (f 0 (childProfile C b)) ≤ f 0 (childProfile C j) := by
  apply le_of_tendsto_of_tendsto
    (((hc _).continuousAt.min (hc _).continuousAt).comp softSequence_tendsto)
    ((hc _).continuousAt.tendsto.comp softSequence_tendsto)
  exact Filter.Eventually.of_forall fun k => signature_child_min C (f (softSequence k))
    (hp _ (softSequence_range k).1 (softSequence_range k).2)
    (hs _ (softSequence_range k).1 (softSequence_range k).2) a b j ha haj hjb hb

end Contingency

 

 

open scoped BigOperators

namespace Contingency
section FiniteVariance
variable {α : Type*} [Fintype α]

noncomputable def totalWeight (w : α → ℝ) : ℝ := ∑ x, w x
noncomputable def weightedMean (w H : α → ℝ) : ℝ := (∑ x, w x*H x) / totalWeight w
noncomputable def weightedVariance (w H : α → ℝ) : ℝ :=
  ∑ x, w x * (H x-weightedMean w H)^2

theorem centered_sum (w H : α → ℝ) (hw : totalWeight w ≠ 0) :
    (∑ x, w x*(H x-weightedMean w H))=0 := by
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul]
  change (∑ x, w x*H x) - totalWeight w*((∑ x, w x*H x)/totalWeight w) = 0
  field_simp
  ring

theorem variance_translate (w H : α → ℝ) (hw : totalWeight w ≠ 0) (a : ℝ) :
    (∑ x, w x*(H x-a)^2) =
      weightedVariance w H + totalWeight w*(weightedMean w H-a)^2 := by
  have h (x : α) : w x*(H x-a)^2 =
      w x*(H x-weightedMean w H)^2 +
      2*(weightedMean w H-a)*(w x*(H x-weightedMean w H)) +
      w x*(weightedMean w H-a)^2 := by ring
  simp only [h,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul]
  rw [centered_sum w H hw]
  simp [weightedVariance,totalWeight]

theorem variance_secondMoment (w H : α → ℝ) (hw : totalWeight w ≠ 0) :
    weightedVariance w H = (∑ x, w x*H x^2) -
      (∑ x, w x*H x)^2 / totalWeight w := by
  have h := variance_translate w H hw 0
  simp only [sub_zero] at h
  rw [weightedMean] at h
  have he : totalWeight w*((∑ x, w x*H x)/totalWeight w)^2 =
      (∑ x, w x*H x)^2 / totalWeight w := by field_simp
  rw [he] at h
  linarith

theorem variance_pair_formula (w H : α → ℝ) (hw : totalWeight w ≠ 0) :
    weightedVariance w H =
      (∑ a, ∑ b, w a*w b*(H a-H b)^2) / (2*totalWeight w) := by
  have hexp (a b : α) : w a*w b*(H a-H b)^2 =
      (w a*H a^2)*w b + w a*(w b*H b^2) -2*(w a*H a)*(w b*H b) := by ring
  simp only [hexp,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    ← Finset.mul_sum,← Finset.sum_mul]
  rw [variance_secondMoment w H hw]
  unfold totalWeight at *
  field_simp [hw]
  ring

theorem variance_nonneg (w H : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    0 ≤ weightedVariance w H :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (sq_nonneg _)

 

theorem variance_le_card_sq (w H : α → ℝ) (hw : 0 < totalWeight w)
    (B : ℝ) (hB : 0 ≤ B)
    (hp : ∀ a b, w a*w b/totalWeight w*(H a-H b)^2 ≤ B) :
    weightedVariance w H ≤ (Fintype.card α:ℝ)^2*B := by
  rw [variance_pair_formula w H hw.ne']
  have hb : (∑ a, ∑ b, w a*w b*(H a-H b)^2) ≤
      (Fintype.card α:ℝ)^2*(totalWeight w*B) := by
    calc
      _ ≤ ∑ a : α, ∑ b : α, totalWeight w*B := by
        apply Finset.sum_le_sum; intro a ha
        apply Finset.sum_le_sum; intro b hb
        have h := (div_le_iff₀ hw).mp (show w a*w b*(H a-H b)^2/totalWeight w ≤ B by
          simpa only [div_mul_eq_mul_div] using hp a b)
        nlinarith
      _ = _ := by simp; ring
  apply (div_le_iff₀ (mul_pos (by norm_num) hw)).mpr
  have hc : 0 ≤ (Fintype.card α:ℝ)^2 := sq_nonneg _
  nlinarith [mul_nonneg hc hB]

end FiniteVariance

 
theorem interval_square_bound (H : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    (H a-H b)^2 ≤ (b-a:ℕ)*(∑ j ∈ Finset.Ico a b, (H j-H (j+1))^2) := by
  have htel : (∑ j ∈ Finset.Ico a b, (H j-H (j+1))) = H a-H b := by
    calc
      _ = -(∑ j ∈ Finset.Ico a b, (H (j+1)-H j)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl; intro j hj; ring
      _ = H a-H b := by rw [Finset.sum_Ico_sub H hab]; ring
  rw [← htel]
  calc
    _ ≤ (∑ j ∈ Finset.Ico a b, (1:ℝ)) *
        ∑ j ∈ Finset.Ico a b, (H j-H (j+1))^2 := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      · intros; norm_num
      · intros; positivity
      · intros; simp
    _ = _ := by simp

 

theorem child_pair_bound (U : ℕ) (z H : ℕ → ℝ) (Z A E : ℝ)
    (hZ : 0 < Z) (hz : ∀ j ≤ U, 0 ≤ z j) (hzZ : ∀ j ≤ U, z j ≤ Z)
    (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hmin : ∀ a b j, a ≤ j → j ≤ b → b ≤ U → min (z a) (z b) ≤ z j)
    (hadj : ∀ j < U, min (z j) (z (j+1))*(H j-H (j+1))^2 ≤ A*E)
    (a b : ℕ) (hab : a ≤ b) (hbU : b ≤ U) :
    z a*z b/Z*(H a-H b)^2 ≤ (U:ℝ)^2*A*E := by
  have haU := hab.trans hbU
  have hzmin : 0 ≤ min (z a) (z b) := le_min (hz a haU) (hz b hbU)
  have hpmin : z a*z b/Z ≤ min (z a) (z b) := by
    apply le_min
    · apply (div_le_iff₀ hZ).mpr
      exact mul_le_mul_of_nonneg_left (hzZ b hbU) (hz a haU)
    · apply (div_le_iff₀ hZ).mpr
      nlinarith [mul_le_mul_of_nonneg_right (hzZ a haU) (hz b hbU)]
  have hedge (j : ℕ) (hj : j ∈ Finset.Ico a b) :
      min (z a) (z b)*(H j-H (j+1))^2 ≤ A*E := by
    have hj' := Finset.mem_Ico.mp hj
    have hm : min (z a) (z b) ≤ min (z j) (z (j+1)) := by
      apply le_min
      · exact hmin a b j hj'.1 (by omega) hbU
      · exact hmin a b (j+1) (by omega) (by omega) hbU
    exact (mul_le_mul_of_nonneg_right hm (sq_nonneg _)).trans (hadj j (by omega))
  have hs : min (z a) (z b)*(∑ j ∈ Finset.Ico a b, (H j-H (j+1))^2) ≤
      ((b-a:ℕ):ℝ)*(A*E) := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ j ∈ Finset.Ico a b, A*E := Finset.sum_le_sum hedge
      _ = _ := by simp
  have hlen : ((b-a:ℕ):ℝ) ≤ U := by exact_mod_cast (show b-a ≤ U by omega)
  have hlen0 : (0:ℝ) ≤ ((b-a:ℕ):ℝ) := Nat.cast_nonneg _
  have hlenSq : (((b-a:ℕ):ℝ))^2 ≤ (U:ℝ)^2 := by
    exact sq_le_sq₀ hlen0 (Nat.cast_nonneg U) |>.mpr hlen
  calc
    _ ≤ min (z a) (z b)*(H a-H b)^2 := mul_le_mul_of_nonneg_right hpmin (sq_nonneg _)
    _ ≤ min (z a) (z b)*(((b-a:ℕ):ℝ)*∑ j ∈ Finset.Ico a b, (H j-H (j+1))^2) :=
      mul_le_mul_of_nonneg_left (interval_square_bound H a b hab) hzmin
    _ = ((b-a:ℕ):ℝ)*(min (z a) (z b)*∑ j ∈ Finset.Ico a b, (H j-H (j+1))^2) := by ring
    _ ≤ ((b-a:ℕ):ℝ)*(((b-a:ℕ):ℝ)*(A*E)) := mul_le_mul_of_nonneg_left hs hlen0
    _ ≤ (U:ℝ)^2*A*E := by nlinarith [mul_le_mul_of_nonneg_right hlenSq (mul_nonneg hA hE)]

end Contingency

 

 

open scoped BigOperators
namespace Contingency.FiniteChain

 
structure Chain (V : Type*) [Fintype V] where
  π : V → ℝ
  P : V → V → ℝ
  positive : ∀ x, 0 < π x
  normalized : ∑ x, π x = 1
  nonneg : ∀ x y, 0 ≤ P x y
  stochastic : ∀ x, ∑ y, P x y = 1
  reversible : ∀ x y, π x*P x y = π y*P y x
  lazy : ∀ x, 1/2 ≤ P x x

namespace Chain
noncomputable section

variable {V : Type*} [Fintype V] (C : Chain V)

def mean (f : V → ℝ) : ℝ := ∑ x, C.π x*f x
def inner (f g : V → ℝ) : ℝ := ∑ x, C.π x*f x*g x
def normSq (f : V → ℝ) : ℝ := ∑ x, C.π x*f x^2
def step (f : V → ℝ) (x : V) : ℝ := ∑ y, C.P x y*f y
def energy (f : V → ℝ) : ℝ := (∑ x, ∑ y, C.π x*C.P x y*(f x-f y)^2)/2

theorem stationary (y : V) : (∑ x, C.π x*C.P x y)=C.π y := by
  simp_rw [C.reversible]
  rw [← Finset.mul_sum,C.stochastic,mul_one]

theorem normSq_nonneg (f : V → ℝ) : 0≤C.normSq f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (C.positive x).le (sq_nonneg _)

theorem inner_self (f : V → ℝ) : C.inner f f=C.normSq f := by
  simp only [inner,normSq,pow_two,mul_assoc]

theorem step_mean (f : V → ℝ) : C.mean (C.step f)=C.mean f := by
  simp only [mean,step,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc,← Finset.sum_mul,C.stationary]

theorem step_selfadjoint (f g : V → ℝ) : C.inner f (C.step g)=C.inner (C.step f) g := by
  simp only [inner,step,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro y _
  calc
    C.π y*f y*(C.P y x*g x) = (C.π y*C.P y x)*f y*g x := by ring
    _ = _ := by rw [C.reversible]; ring

theorem inner_comm (f g : V → ℝ) : C.inner f g=C.inner g f := by
  unfold inner
  apply Finset.sum_congr rfl; intro x _; ring

theorem edge_sums_left (f : V → ℝ) :
    (∑ x, ∑ y, C.π x*C.P x y*f x^2)=C.normSq f := by
  simp only [mul_right_comm (C.π _) (C.P _ _),← Finset.mul_sum,C.stochastic,mul_one,normSq]

theorem edge_sums_right (f : V → ℝ) :
    (∑ x, ∑ y, C.π x*C.P x y*f y^2)=C.normSq f := by
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul,C.stationary,normSq]

theorem edge_cross (f g : V → ℝ) :
    (∑ x, ∑ y, C.π x*C.P x y*f x*g y)=C.inner f (C.step g) := by
  simp only [inner,step,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro y _; ring

theorem energy_identity (f : V → ℝ) :
    C.energy f=C.normSq f-C.inner f (C.step f) := by
  have h (x y) : C.π x*C.P x y*(f x-f y)^2 =
      C.π x*C.P x y*f x^2+C.π x*C.P x y*f y^2 -
        2*(C.π x*C.P x y*f x*f y) := by ring
  simp only [energy,h,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [C.edge_sums_left,C.edge_sums_right,C.edge_cross]
  ring

theorem step_positive (f : V → ℝ) : 0≤C.inner f (C.step f) := by
  classical
  have hn : 0≤∑ x, ∑ y, C.π x*(C.P x y-if x=y then 1/2 else 0)*(f x+f y)^2 := by
    apply Finset.sum_nonneg; intro x _
    apply Finset.sum_nonneg; intro y _
    apply mul_nonneg
    · apply mul_nonneg (C.positive x).le
      by_cases h : x=y
      · subst y; simp only [ite_true]; linarith [C.lazy x]
      · simp only [ite_eq_right h,sub_zero]; exact C.nonneg x y
    · exact sq_nonneg _
  have he : (∑ x, ∑ y, C.π x*(C.P x y-if x=y then 1/2 else 0)*(f x+f y)^2) =
      2*C.inner f (C.step f) := by
    have h (x y) : C.π x*(C.P x y-if x=y then 1/2 else 0)*(f x+f y)^2 =
        (C.π x*C.P x y*f x^2 + C.π x*C.P x y*f y^2 +
          2*(C.π x*C.P x y*f x*f y)) -
        (if x=y then 2*(C.π x*f x^2) else 0) := by
      by_cases hh : x=y
      · subst y; simp only [ite_true]; ring
      · simp only [ite_eq_right hh]; ring
    simp only [h,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    rw [C.edge_sums_left,C.edge_sums_right,C.edge_cross]
    simp only [normSq,← Finset.mul_sum]; ring
  rw [he] at hn
  linarith

 

theorem step_cauchy (f g : V → ℝ) :
    (C.inner f (C.step g))^2 ≤ C.inner f (C.step f)*C.inner g (C.step g) := by
  have hh (t : ℝ) : 0 ≤ C.inner f (C.step f)*t^2 +
      2*C.inner f (C.step g)*t+C.inner g (C.step g) := by
    have h := C.step_positive (fun x => t*f x+g x)
    have he : C.inner (fun x => t*f x+g x) (C.step (fun x => t*f x+g x)) =
        C.inner f (C.step f)*t^2 +
        (C.inner f (C.step g)+C.inner g (C.step f))*t+C.inner g (C.step g) := by
      simp only [inner,step,Finset.mul_sum,Finset.sum_mul,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro y _
      ring
    rw [he,C.inner_comm g (C.step f),← C.step_selfadjoint f g] at h
    nlinarith only [h]
  have hd := discrim_le_zero (by
    intro t
    simpa only [pow_two] using hh t)
  unfold discrim at hd
  nlinarith only [hd]

end
end Chain
end Contingency.FiniteChain

 

 

open scoped BigOperators
namespace Contingency.FiniteChain.Chain
noncomputable section
variable {V : Type*} [Fintype V] (C : Chain V)

def variance (f : V → ℝ) : ℝ := ∑ x, C.π x*(f x-C.mean f)^2

theorem variance_centered (f : V → ℝ) (h : C.mean f=0) : C.variance f=C.normSq f := by
  simp only [variance,h,sub_zero,normSq]

theorem gap_inner (K : ℝ) (hK : 1≤K)
    (hvar : ∀ f : V → ℝ, C.variance f ≤ K*C.energy f)
    (f : V → ℝ) (hf : C.mean f=0) :
    C.inner f (C.step f) ≤ (1-1/K)*C.normSq f := by
  have h := hvar f
  rw [C.variance_centered f hf,C.energy_identity] at h
  have hk0 : 0<K := by linarith
  apply (mul_le_mul_iff_left₀ hk0).mp
  have he : (1-1/K)*C.normSq f*K=(K-1)*C.normSq f := by field_simp [hk0.ne']
   
  change C.inner f (C.step f)*K ≤ _
  rw [he]
  nlinarith only [h]

theorem gap_normSq (K : ℝ) (hK : 1≤K)
    (hvar : ∀ f : V → ℝ, C.variance f ≤ K*C.energy f)
    (f : V → ℝ) (hf : C.mean f=0) :
    C.normSq (C.step f) ≤ (1-1/K)^2*C.normSq f := by
  have hr : 0≤1-1/K := by
    have : 1/K≤(1:ℝ) := (div_le_one (by linarith)).mpr hK
    linarith
  have hg : C.mean (C.step f)=0 := by rw [C.step_mean,hf]
  have hb := C.step_cauchy f (C.step f)
  rw [C.step_selfadjoint,C.inner_self] at hb
  have hp := mul_le_mul (C.gap_inner K hK hvar f hf)
    (C.gap_inner K hK hvar (C.step f) hg) (C.step_positive (C.step f))
    (mul_nonneg hr (C.normSq_nonneg f))
  have hn := C.normSq_nonneg (C.step f)
  by_cases hz : C.normSq (C.step f)=0
  · rw [hz]; exact mul_nonneg (sq_nonneg _) (C.normSq_nonneg f)
  · have hh : 0<C.normSq (C.step f) := lt_of_le_of_ne hn (Ne.symm hz)
    nlinarith only [hb,hp,hh]

def iterate : ℕ → (V → ℝ) → V → ℝ
  | 0, f => f
  | t+1, f => C.step (iterate t f)

theorem iterate_mean (t : ℕ) (f : V → ℝ) : C.mean (C.iterate t f)=C.mean f := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [iterate,C.step_mean] using ih

theorem iterate_normSq (K : ℝ) (hK : 1≤K)
    (hvar : ∀ f : V → ℝ, C.variance f ≤ K*C.energy f)
    (t : ℕ) (f : V → ℝ) (hf : C.mean f=0) :
    C.normSq (C.iterate t f) ≤ (1-1/K)^(2*t)*C.normSq f := by
  induction t with
  | zero => simp [iterate]
  | succ t ih =>
    have hg := C.gap_normSq K hK hvar (C.iterate t f) (by rw [C.iterate_mean,hf])
    have hi := mul_le_mul_of_nonneg_left ih (sq_nonneg (1-1/K))
    simp only [iterate]
    calc
      _ ≤ (1-1/K)^2*C.normSq (C.iterate t f) := hg
      _ ≤ (1-1/K)^2*((1-1/K)^(2*t)*C.normSq f) := hi
      _ = _ := by rw [show 2*(t+1)=2+2*t by omega,pow_add]; ring

 
def law [DecidableEq V] : ℕ → V → V → ℝ
  | 0, x, y => if x=y then 1 else 0
  | t+1, x, y => ∑ z, law t x z*C.P z y

def initialDensity [DecidableEq V] (x y : V) : ℝ :=
  (if x=y then 1 else 0)/C.π x-1

theorem density_mean [DecidableEq V] (x : V) : C.mean (C.initialDensity x)=0 := by
  simp only [mean,initialDensity,mul_sub,mul_one,Finset.sum_sub_distrib]
  rw [C.normalized]
  simp only [ite_div,mul_ite,mul_zero,zero_div,Finset.sum_ite_eq,
    Finset.mem_univ,ite_true]
  field_simp [(C.positive x).ne']
  ring

theorem density_normSq [DecidableEq V] (x : V) :
    C.normSq (C.initialDensity x)=1/C.π x-1 := by
  have h (y) : C.π y*(C.initialDensity x y)^2 =
      (if x=y then 1/C.π x-2 else 0)+C.π y := by
    by_cases hh : x=y
    · subst y
      simp only [initialDensity,ite_true]
      field_simp [(C.positive x).ne']
      ring
    · simp [initialDensity,hh]
  simp only [normSq,h,Finset.sum_add_distrib,Finset.sum_ite_eq,
    Finset.mem_univ,ite_true,C.normalized]
  ring

theorem density_law [DecidableEq V] (t : ℕ) (x y : V) :
    C.π y*(1+C.iterate t (C.initialDensity x) y)=C.law t x y := by
  induction t generalizing y with
  | zero =>
    by_cases h : x=y
    · subst y
      simp [iterate,initialDensity,law,(C.positive x).ne']
    · simp [iterate,initialDensity,law,h]
  | succ t ih =>
    simp only [iterate,step,law]
    calc
      _ = ∑ z, C.π y*C.P y z*(1+C.iterate t (C.initialDensity x) z) := by
        simp only [mul_add,mul_one,Finset.sum_add_distrib,← Finset.mul_sum,C.stochastic]
        simp only [mul_assoc,← Finset.mul_sum]
      _ = ∑ z, (C.π z*(1+C.iterate t (C.initialDensity x) z))*C.P z y := by
        apply Finset.sum_congr rfl; intro z _
        rw [C.reversible]; ring
      _ = _ := by simp_rw [ih]

 
def tv [DecidableEq V] (t : ℕ) (x : V) : ℝ :=
  (∑ y, |C.law t x y-C.π y|)/2

theorem tv_density [DecidableEq V] (t : ℕ) (x : V) :
    C.tv t x = (∑ y, C.π y*|C.iterate t (C.initialDensity x) y|)/2 := by
  unfold tv
  congr 1
  apply Finset.sum_congr rfl; intro y _
  rw [← C.density_law]
  have he : C.π y*(1+C.iterate t (C.initialDensity x) y)-C.π y=
      C.π y*C.iterate t (C.initialDensity x) y := by ring
  rw [he,abs_mul,abs_of_pos (C.positive y)]

theorem weighted_abs_sq (f : V → ℝ) :
    (∑ x, C.π x*|f x|)^2 ≤ C.normSq f := by
  calc
    _ ≤ (∑ x, C.π x)*(∑ x, C.π x*f x^2) := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      · intro x _; exact (C.positive x).le
      · intro x _; exact mul_nonneg (C.positive x).le (sq_nonneg _)
      · intro x _; rw [mul_pow,sq_abs]; nlinarith only []
    _ = _ := by rw [C.normalized,one_mul]; rfl

theorem tv_sq [DecidableEq V] (t : ℕ) (x : V) :
    (C.tv t x)^2 ≤ C.normSq (C.iterate t (C.initialDensity x))/4 := by
  rw [C.tv_density]
  have h := C.weighted_abs_sq (C.iterate t (C.initialDensity x))
  nlinarith only [h]

 

theorem mixing_bound [DecidableEq V] (K : ℝ) (hK : 1≤K)
    (hvar : ∀ f : V → ℝ, C.variance f ≤ K*C.energy f)
    (t : ℕ) (x : V) :
    C.tv t x ≤ (C.π x)⁻¹*Real.exp (-(t:ℝ)/K) := by
  have hk0 : 0<K := by linarith
  have hr : 0≤1-1/K := by
    have : 1/K≤(1:ℝ) := (div_le_one hk0).mpr hK
    linarith
  have he := pow_le_pow_left₀ hr (Real.one_sub_le_exp_neg (1/K)) (2*t)
  have hexp : Real.exp (-(1/K))^(2*t)=(Real.exp (-(t:ℝ)/K))^2 := by
    rw [← Real.exp_nat_mul,← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp] at he
  have hn := C.iterate_normSq K hK hvar t (C.initialDensity x) (C.density_mean x)
  have hp := mul_le_mul_of_nonneg_right he (C.normSq_nonneg (C.initialDensity x))
  rw [C.density_normSq] at hn hp
  have hπ : C.π x≤1 := by
    calc
      _ ≤ ∑ y, C.π y := Finset.single_le_sum (fun y _ => (C.positive y).le) (Finset.mem_univ x)
      _ = 1 := C.normalized
  have hi : 1≤(C.π x)⁻¹ := (one_le_inv₀ (C.positive x)).mpr hπ
  have hic : (1/C.π x-1)/4≤((C.π x)⁻¹)^2 := by
    simp only [one_div]
    nlinarith only [hi,sq_nonneg ((C.π x)⁻¹-1)]
  have he0 : 0≤(Real.exp (-(t:ℝ)/K))^2 := sq_nonneg _
  have hfinal := mul_le_mul_of_nonneg_right hic he0
  have htv := C.tv_sq t x
  have hi0 : 0≤C.tv t x := by unfold tv; positivity
  have hout0 : 0≤(C.π x)⁻¹*Real.exp (-(t:ℝ)/K) := by positivity
  apply (sq_le_sq₀ hi0 hout0).mp
  nlinarith only [htv,hn,hp,hfinal]

theorem mixing_bound_min [DecidableEq V] (K : ℝ) (hK : 1≤K)
    (hvar : ∀ f : V → ℝ, C.variance f ≤ K*C.energy f)
    (pmin : ℝ) (hpmin : 0<pmin) (hmin : ∀ x, pmin≤C.π x)
    (t : ℕ) (x : V) :
    C.tv t x ≤ pmin⁻¹*Real.exp (-(t:ℝ)/K) := by
  apply (C.mixing_bound K hK hvar t x).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact inv_anti₀ hpmin (hmin x)

end
end Contingency.FiniteChain.Chain

end

end OAI
