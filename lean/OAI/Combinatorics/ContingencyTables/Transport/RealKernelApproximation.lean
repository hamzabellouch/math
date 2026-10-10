import OAI.Combinatorics.ContingencyTables.Transport.RationalWalks
import OAI.Combinatorics.ContingencyTables.Transport.MetropolisChain

namespace OAI

/-! # Accumulating rational implementation errors against a real kernel

The exact companion weights may be real. The implemented probabilities
are rational; comparison takes place after their canonical real cast.
-/

namespace ContingencyTables.RealKernelApproximation
open scoped BigOperators Classical
open CommonBasesFPRAS ResidualMixture FirstSuccess

noncomputable section
variable {X Y : Type*} [Fintype X] [Fintype Y]

def distance (p q : X → ℝ) : ℝ := (∑ x,|p x-q x|)/2

lemma distance_nonneg (p q : X → ℝ) : 0 ≤ distance p q :=
  div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)

lemma distance_triangle (p q r : X → ℝ) : distance p r ≤ distance p q+distance q r := by
  have h := Finset.sum_le_sum (fun x (_ : x∈Finset.univ) => abs_sub_le (p x) (q x) (r x))
  simp only [Finset.sum_add_distrib] at h
  unfold distance
  linarith

lemma distance_event (p q : X → ℝ) (hmass : ∑ x,p x=∑ x,q x) (S : Finset X) :
    |(∑ x∈S,p x)-(∑ x∈S,q x)| ≤ distance p q := by
  have hz : (∑ x ∈ S, (p x-q x))+(∑ x ∈ Sᶜ, (p x-q x))=0 := by
    rw [Finset.sum_add_sum_compl,Finset.sum_sub_distrib,hmass,sub_self]
  have hc : (∑ x ∈ Sᶜ, (p x-q x))= -(∑ x ∈ S, (p x-q x)) := by linarith
  have ha := Finset.abs_sum_le_sum_abs (fun x => p x-q x) S
  have hb := Finset.abs_sum_le_sum_abs (fun x => p x-q x) Sᶜ
  rw [hc,abs_neg] at hb
  have hs := add_le_add ha hb
  rw [Finset.sum_add_sum_compl] at hs
  rw [←Finset.sum_sub_distrib]
  unfold distance
  linarith

lemma distance_push (K : FiniteKernel X Y) (p q : X → ℝ) :
    distance (K.push p) (K.push q) ≤ distance p q := by
  have hp (y : Y) : |K.push p y-K.push q y| ≤ ∑ x, |p x-q x| * K.P x y := by
    unfold FiniteKernel.push
    rw [←Finset.sum_sub_distrib]
    have h := Finset.abs_sum_le_sum_abs
      (fun x => p x*K.P x y-q x*K.P x y) Finset.univ
    simpa only [←sub_mul,abs_mul,abs_of_nonneg (K.nonnegative _ _)] using h
  have hs := Finset.sum_le_sum (fun y (_ : y∈Finset.univ) => hp y)
  have ht : (∑ y,∑ x, |p x-q x| * K.P x y) ≤ ∑ x,|p x-q x| := by
    rw [Finset.sum_comm]
    simp only [←Finset.mul_sum]
    exact Finset.sum_le_sum (fun x _ => by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (K.substochastic x) (abs_nonneg (p x-q x)))
  unfold distance
  exact div_le_div_of_nonneg_right (hs.trans ht) (by norm_num)

lemma distance_push_rows (K L : FiniteKernel X Y) (p : X → ℝ)
    (hp : ∀ x,0 ≤ p x) :
    distance (K.push p) (L.push p) ≤ ∑ x,p x*distance (K.P x) (L.P x) := by
  have hb (y : Y) : |K.push p y-L.push p y| ≤ ∑ x,p x*|K.P x y-L.P x y| := by
    unfold FiniteKernel.push
    rw [←Finset.sum_sub_distrib]
    have h := Finset.abs_sum_le_sum_abs
      (fun x => p x*K.P x y-p x*L.P x y) Finset.univ
    simpa only [←mul_sub,abs_mul,abs_of_nonneg (hp _)] using h
  have hs := Finset.sum_le_sum (fun y (_ : y∈Finset.univ) => hb y)
  rw [Finset.sum_comm] at hs
  simp only [←Finset.mul_sum] at hs
  unfold distance
  simpa only [Finset.sum_div,mul_div_assoc] using
    div_le_div_of_nonneg_right hs (by norm_num : (0:ℝ)≤2)

lemma distance_push_two (K L : FiniteKernel X Y) (p q : X → ℝ)
    (hp : ∀ x,0 ≤ p x) (hmass : ∑ x,p x=1) (η : ℝ)
    (hη : ∀ x,distance (K.P x) (L.P x) ≤ η) :
    distance (K.push p) (L.push q) ≤ distance p q+η := by
  have hr : distance (K.push p) (L.push p) ≤ η := by
    calc
      _ ≤ ∑ x,p x*distance (K.P x) (L.P x) := distance_push_rows K L p hp
      _ ≤ ∑ x,p x*η := Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hη x) (hp x))
      _ = η := by rw [←Finset.sum_mul,hmass,one_mul]
  have ht := distance_triangle (K.push p) (L.push p) (L.push q)
  have hc := distance_push L p q
  linarith

def rationalKernel (K : X → RationalLaw Y) : FiniteKernel X Y where
  P x y := ((K x).mass y:ℝ)
  nonnegative x y := by exact_mod_cast (K x).nonnegative y
  substochastic x := by
    have h := congrArg (fun z : ℚ => (z:ℝ)) (K x).total
    simpa only [Rat.cast_sum,Rat.cast_one] using h.le

lemma rationalKernel_push (K : X → RationalLaw Y) (p : RationalLaw X) :
    (rationalKernel K).push (fun x => (p.mass x:ℝ))=
      fun y => ((bindLaw p K).mass y:ℝ) := by
  funext y
  simp only [rationalKernel,FiniteKernel.push,bindLaw,Rat.cast_sum,Rat.cast_mul]

variable [DecidableEq X]

/-- Each realized step may use fresh approximate oracle calls. A uniform
real row error adds once per actual step against the exact real chain. -/
theorem walk_distance (Q : X → RationalLaw X) (K : FiniteKernel X X)
    (η : ℝ) (hη : ∀ x,distance ((rationalKernel Q).P x) (K.P x) ≤ η)
    (x : X) (n : ℕ) :
    distance (fun y => ((walkLaw Q x n).mass y:ℝ)) ((K.power n).P x) ≤ n*η := by
  induction n with
  | zero =>
    simp only [walkLaw,FiniteKernel.power,Nat.cast_zero,zero_mul,distance]
    apply le_of_eq
    apply div_eq_zero_iff.mpr
    left
    apply Finset.sum_eq_zero
    intro y _
    by_cases h : x=y
    · subst y; simp [pointLaw,FiniteKernel.identity]
    · simp [pointLaw,FiniteKernel.identity,h,Ne.symm h]
  | succ n ih =>
    have hm : (∑ y,((walkLaw Q x n).mass y:ℝ))=1 := by
      exact_mod_cast (walkLaw Q x n).total
    have ht := distance_push_two (rationalKernel Q) K
      (fun y => ((walkLaw Q x n).mass y:ℝ)) ((K.power n).P x)
      (fun y => by exact_mod_cast (walkLaw Q x n).nonnegative y) hm η hη
    rw [rationalKernel_push] at ht
    change distance (fun y => ((walkLaw Q x (n+1)).mass y:ℝ)) ((K.power (n+1)).P x) ≤ _ at ht
    exact ht.trans (by push_cast; linarith)

end
end ContingencyTables.RealKernelApproximation

end OAI
