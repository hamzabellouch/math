import OAI.Analysis.Littlewood.Matching

namespace OAI

universe uΩ uI uΛ uK uA uJ uY

namespace AsymptoticallyMinimalLittlewood
namespace Packing
noncomputable section
open scoped BigOperators
open Finset

section Average
variable {Ω : Type uΩ} [Fintype Ω] [Nonempty Ω]

def avg (f : Ω → ℝ) : ℝ := (∑ ω, f ω)/(Fintype.card Ω)

lemma avg_const (c : ℝ) : avg (fun _ : Ω ↦ c) = c := by
  simp [avg, Fintype.card_ne_zero]
omit [Nonempty Ω] in
lemma avg_add (f g : Ω → ℝ) : avg (fun ω ↦ f ω+g ω)=avg f+avg g := by
  simp [avg,Finset.sum_add_distrib,add_div]
omit [Nonempty Ω] in
lemma avg_sub (f g : Ω → ℝ) : avg (fun ω ↦ f ω-g ω)=avg f-avg g := by
  simp [avg,Finset.sum_sub_distrib,sub_div]
omit [Nonempty Ω] in
lemma avg_mul_const (f : Ω → ℝ) (c : ℝ) : avg (fun ω ↦ f ω*c)=avg f*c := by
  simp [avg,← Finset.sum_mul]; ring
omit [Nonempty Ω] in
lemma avg_const_mul (c : ℝ) (f : Ω → ℝ) : avg (fun ω ↦ c*f ω)=c*avg f := by
  simpa only [mul_comm c] using avg_mul_const f c
omit [Nonempty Ω] in
lemma avg_mono {f g : Ω → ℝ} (h : ∀ ω, f ω≤g ω) : avg f≤avg g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ ↦ h ω)) (Nat.cast_nonneg _)
lemma avg_nonneg {f : Ω → ℝ} (h : ∀ ω, 0≤f ω) : 0≤avg f := by
  simpa only [avg_const] using avg_mono h
omit [Nonempty Ω] in
lemma avg_sum {I : Type uI} (S : Finset I) (f : I → Ω → ℝ) :
    avg (fun ω ↦ ∑ i ∈ S, f i ω)=∑ i ∈ S, avg (f i) := by
  dsimp [avg]
  rw [Finset.sum_comm,Finset.sum_div]
omit [Nonempty Ω] in
lemma avg_abs {f : Ω → ℝ} : |avg f|≤avg (fun ω ↦ |f ω|) := by
  have hc : |(Fintype.card Ω : ℝ)|=(Fintype.card Ω : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
  rw [avg,abs_div,hc]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)
lemma exists_le_avg (f : Ω → ℝ) : ∃ ω, f ω≤avg f := by
  have he : (∑ ω, f ω) = ∑ _ω : Ω, avg f := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,avg]
    field_simp
  obtain ⟨ω,_,h⟩ := Finset.exists_le_of_sum_le (Finset.univ_nonempty (α := Ω)) he.le
  exact ⟨ω,h⟩

omit [Nonempty Ω] in
lemma avg_comm {Λ : Type uΛ} [Fintype Λ] [Nonempty Λ] (f : Ω → Λ → ℝ) :
    avg (fun ω ↦ avg (f ω))=avg (fun x ↦ avg (fun ω ↦ f ω x)) := by
  dsimp [avg]
  simp only [← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

omit [Nonempty Ω] in
lemma avg_prod_type {Λ : Type uΛ} [Fintype Λ] [Nonempty Λ] (f : Ω × Λ → ℝ) :
    avg f = avg (fun ω ↦ avg (fun x ↦ f (ω,x))) := by
  simp only [avg,Fintype.card_prod,Nat.cast_mul,Fintype.sum_prod_type,← Finset.sum_div]
  ring

lemma avg_prod_coordinate {K : Type uK} {A : Type uA} [Fintype K] [DecidableEq K] [Fintype A] [Nonempty A]
    (f : K → A → ℝ) : avg (fun ω : K → A ↦ ∏ k, f k (ω k)) = ∏ k, avg (f k) := by
  dsimp [avg]
  rw [← Fintype.prod_sum,Finset.prod_div_distrib]
  simp

lemma avg_prod_injective {K : Type uK} {J : Type uJ} {A : Type uA} [Fintype K] [DecidableEq K] [Fintype J] [Fintype A]
    [Nonempty A] (κ : J → K) (hκ : Function.Injective κ) (f : J → A → ℝ) :
    avg (fun ω : K → A ↦ ∏ j, f j (ω (κ j))) = ∏ j, avg (f j) := by
  classical
  let g : K → A → ℝ := fun k a ↦ if h : ∃ j, κ j=k then f h.choose a else 1
  have hg (j : J) (a : A) : g (κ j) a=f j a := by
    dsimp [g]
    split_ifs with h
    · congr 1
      exact hκ h.choose_spec
    · exact (h ⟨j,rfl⟩).elim
  have hprod (ω : K → A) : (∏ k, g k (ω k)) = ∏ j, f j (ω (κ j)) := by
    symm
    apply Fintype.prod_of_injective κ hκ
    · intro k hk
      simp [g,show ¬∃j, κ j=k from hk]
    · intro j
      exact (hg j (ω (κ j))).symm
  have hprod' : (∏ k, avg (g k)) = ∏ j, avg (f j) := by
    symm
    apply Fintype.prod_of_injective κ hκ
    · intro k hk
      simp [g,show ¬∃j,κ j=k from hk,avg_const]
    · intro j
      exact congrArg avg (funext (fun a ↦ (hg j a).symm))
  rw [← hprod']
  convert avg_prod_coordinate g using 1
  exact congrArg avg (funext (fun ω ↦ (hprod ω).symm))

/-- Good configurations contribute exactly c; all bad configurations carry
only a bounded contribution. This is the uniform first/second moment input. -/
lemma avg_error_on_bad (f : Ω → ℝ) (good : Ω → Prop) [DecidablePred good]
    {c : ℝ} (hc : 0≤c) (hc1 : c≤1) (hf : ∀ ω, 0≤f ω ∧ f ω≤1)
    (he : ∀ ω, good ω → f ω=c) :
    |avg f-c| ≤ avg (fun ω ↦ if good ω then 0 else 1) := by
  rw [← avg_const (Ω := Ω) c,← avg_sub]
  exact avg_abs.trans (avg_mono (fun ω ↦ by
    by_cases h : good ω
    · simp [h,he ω h]
    · simp only [h,ite_false]
      rw [abs_le]
      constructor <;> linarith [(hf ω).1,(hf ω).2]))

lemma avg_square_error {Z : Ω → ℝ} {p a : ℝ} (hp : 0≤p) (hp1 : p≤1)
    (hmean : |avg Z-p|≤a) (hsecond : |avg (fun ω ↦ Z ω^2)-p^2|≤a) :
    avg (fun ω ↦ (Z ω-p)^2) ≤ 3*a := by
  have he : avg (fun ω ↦ (Z ω-p)^2) =
      avg (fun ω ↦ Z ω^2)-2*p*avg Z+p^2 := by
    calc
      _ = avg (fun ω ↦ Z ω^2-(2*p)*Z ω+p^2) := by congr 1; funext ω; ring
      _ = _ := by rw [avg_add,avg_sub,avg_const_mul,avg_const]
  rw [he]
  have ha : 0≤a := (abs_nonneg _).trans hmean
  have hm := (abs_le.mp hmean).1
  have hs := (abs_le.mp hsecond).2
  nlinarith

omit [Nonempty Ω] in
lemma avg_chebyshev {Z : Ω → ℝ} (p : ℝ) {t : ℝ} (ht : 0<t) :
    avg (fun ω ↦ if t≤|Z ω-p| then 1 else 0) ≤
      avg (fun ω ↦ (Z ω-p)^2)/t^2 := by
  rw [le_div_iff₀ (sq_pos_of_pos ht),← avg_mul_const]
  apply avg_mono
  intro ω
  split_ifs with h
  · nlinarith [sq_abs (Z ω-p)]
  · simp only [zero_mul]; positivity

omit [Nonempty Ω] in
lemma avg_mul_avg {Λ : Type uΛ} [Fintype Λ] [Nonempty Λ]
    (f : Ω → ℝ) (g : Λ → ℝ) :
    avg f*avg g = avg (fun x : Ω × Λ ↦ f x.1*g x.2) := by
  rw [avg_prod_type]
  simp_rw [avg_const_mul,avg_mul_const]

omit [Nonempty Ω] in
lemma avg_square {Y : Type uY} [Fintype Y] [Nonempty Y] (f : Y → Ω → ℝ) :
    avg (fun ω ↦ (avg (fun y ↦ f y ω))^2) =
      avg (fun yy : Y × Y ↦ avg (fun ω ↦ f yy.1 ω*f yy.2 ω)) := by
  simp_rw [pow_two,avg_mul_avg]
  exact avg_comm _

/-- Unconditional moments suffice: pruning all atypical candidate centers
only enlarges the deleted set, so no conditional-probability axiom is used. -/
lemma moments_from_good {Y : Type uY} [Fintype Y] [Nonempty Y]
    (f : Y → Ω → ℝ) (good : Y → Prop) (good₂ : Y × Y → Prop)
    [DecidablePred good] [DecidablePred good₂] {p a : ℝ}
    (hp : 0≤p) (hp1 : p≤1) (hf : ∀ y ω, 0≤f y ω ∧ f y ω≤1)
    (hfirst : ∀ y, good y → avg (f y)=p)
    (hsecond : ∀ yy, good₂ yy → avg (fun ω ↦ f yy.1 ω*f yy.2 ω)=p^2)
    (hbad : avg (fun y ↦ if good y then 0 else 1)≤a)
    (hbad₂ : avg (fun yy ↦ if good₂ yy then 0 else 1)≤a) :
    avg (fun ω ↦ (avg (fun y ↦ f y ω)-p)^2) ≤ 3*a := by
  have hb (y) : 0≤avg (f y) ∧ avg (f y)≤1 :=
    ⟨avg_nonneg (fun ω ↦ (hf y ω).1),by
      rw [← avg_const (Ω := Ω) 1]; exact avg_mono (fun ω ↦ (hf y ω).2)⟩
  have hb₂ (yy : Y × Y) : 0≤avg (fun ω ↦ f yy.1 ω*f yy.2 ω) ∧
      avg (fun ω ↦ f yy.1 ω*f yy.2 ω)≤1 := by
    constructor
    · exact avg_nonneg (fun ω ↦ mul_nonneg (hf _ _).1 (hf _ _).1)
    · rw [← avg_const (Ω := Ω) 1]
      exact avg_mono (fun ω ↦ (mul_le_of_le_one_left (hf _ _).1 (hf _ _).2).trans (hf _ _).2)
  apply avg_square_error hp hp1
  · rw [avg_comm]
    exact (avg_error_on_bad _ good hp hp1 hb hfirst).trans hbad
  · rw [avg_square]
    exact (avg_error_on_bad _ good₂ (sq_nonneg _) (by nlinarith) hb₂ hsecond).trans hbad₂

lemma exists_few_bad_centers {I : Type uI} [Fintype I] (Z : I → Ω → ℝ)
    (p : ℝ) {t a : ℝ} (ht : 0<t)
    (hZ : ∀ i, avg (fun ω ↦ (Z i ω-p)^2)≤a) :
    ∃ ω, ((Finset.univ.filter (fun i ↦ t≤|Z i ω-p|)).card : ℝ) ≤
      Fintype.card I*a/t^2 := by
  classical
  let W : Ω → ℝ := fun ω ↦ ∑ i : I, if t≤|Z i ω-p| then 1 else 0
  obtain ⟨ω,hω⟩ := exists_le_avg W
  refine ⟨ω,?_⟩
  have he : ((Finset.univ.filter (fun i ↦ t≤|Z i ω-p|)).card : ℝ)=W ω := by
    simp [W,Finset.sum_boole]
  rw [he]
  apply hω.trans
  dsimp [W]
  rw [avg_sum]
  calc
    _ ≤ ∑ _i : I, a/t^2 := Finset.sum_le_sum (fun i _ ↦
      (avg_chebyshev p ht).trans (div_le_div_of_nonneg_right (hZ i) (sq_nonneg t)))
    _ = _ := by simp; ring

omit [Nonempty Ω] in
lemma avg_indicator {P : Ω → Prop} [DecidablePred P] :
    avg (fun ω ↦ if P ω then 1 else 0) =
      ((Finset.univ.filter P).card : ℝ)/Fintype.card Ω := by
  simp [avg,Finset.sum_boole]

omit [Nonempty Ω] in
lemma avg_bad_union {I : Type uI} (S : Finset I) (P : I → Ω → Prop)
    [∀ i, DecidablePred (P i)] :
    avg (fun ω ↦ if ∃ i∈S, P i ω then 1 else 0) ≤
      ∑ i∈S, avg (fun ω ↦ if P i ω then 1 else 0) := by
  classical
  rw [← avg_sum]
  apply avg_mono
  intro ω
  split_ifs with h
  · obtain ⟨i,hi,hP⟩ := h
    exact (show (1 : ℝ) ≤ (if P i ω then 1 else 0) by simp [hP]).trans
      (Finset.single_le_sum (f := fun j ↦ if P j ω then (1 : ℝ) else 0)
        (fun j _ ↦ by split_ifs <;> norm_num) hi)
  · exact Finset.sum_nonneg (fun j _ ↦ by split_ifs <;> norm_num)

end Average
end
end Packing
end AsymptoticallyMinimalLittlewood

end OAI
