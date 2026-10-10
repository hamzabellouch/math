import OAI.Combinatorics.HadwigerCounterexample.RectangleRegularity

namespace OAI

/-! # Four Corner Views -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Matrix Function
open scoped BigOperators
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]

abbrev Corn := Bool × Bool

def criss (E : A ≃ B × C) (p : A × A) (x : Corn) :=
  E.symm ((onSide (Prod.map E E p) x.1).1,(onSide (Prod.map E E p) x.2).2)
def quart (E : A≃B×C) (U : Wgt A) (p : A×A) :=
  ∏ i:Corn,U (criss E p i)

omit [Fintype A] [Fintype B] [Fintype C] in
theorem criss_pair (p : A × A) (a b : Bool) (E : A≃ B × C) :
    E (criss E p (a,b))=((E (onSide p a)).1,(E (onSide p b)).2) := by
  cases a <;> cases b <;> simp [criss,onSide]

variable {E : A≃ B × C}

def spread (U : Wgt (B× C)) (i : (B×C) × B×C) :=
  U (i.1.1,i.1.2)*U (i.1.1,i.2.2)* (U (i.2.1,i.1.2)*U (i.2.1,i.2.2))

theorem quart_shift (E : A ≃ B×C) (U : Wgt A) (p : Wgt A) :
    avg (pairW p p) (quart E U) =
      avg (pairW (mapW p E) (mapW p E)) (spread (U∘E.symm)) := by
  classical
  rw [←map_pair_law,mapW_avg]
  refine avg_congr fun x hx => ?_
  unfold quart spread
  rw [Fintype.prod_prod_type,Fintype.prod_bool,Fintype.prod_bool,Fintype.prod_bool]
  rfl

set_option maxHeartbeats 800000 in
theorem quart_small (E : A ≃ B×C) (U : Wgt A) (u : Wgt A) (p : Wgt B) (q : Wgt C)
    (he : mapW u E=pairW p q) (hp : IsLaw p) (hq : IsLaw q)
    (h : ∀ i,|U i|≤1) (δ : ℝ) (hh : thinCut u U (Prod.fst ∘ E) (Prod.snd ∘ E) δ) :
    |avg (pairW u u) (quart E U)|≤δ := by
  rw [quart_shift,he, pairW_avg,avg_avg]
  let T := U∘E.symm
  have ht (y : B × C) :
      |avg (pairW p q) (fun i => spread T (i,y))|≤δ := by
    let f j := T (j,y.2); let g i := T (y.1,i)*T y
    have he' (i) :
        spread T (E i,y)=U i*(f (E i).1*g (E i).2) := by
      simp only [spread,T,f,g,Function.comp_apply]
      rw [show E.symm ((E i).1,(E i).2)=i from E.symm_apply_apply _]; cases y; ring
    have hU x : |g x|≤1 := by
      unfold g; rw [abs_mul]; exact (mul_le_mul (h _) (h _) (abs_nonneg _) zero_le_one).trans_eq
        (by ring)
    rw [← he,mapW_avg]; simp_rw [he']
    exact hh f (fun i=>h _) _ hU
  have hu := pairW_law hp hq
  exact (abs_avg_le hu.nz).trans (hu.avg_le ht)

set_option maxHeartbeats 800000 in
theorem spread_gain (u : Wgt B) (v : Wgt C) (f : Wgt (B×C)) (hu : IsLaw u) (hv : IsLaw v)
    (p : Wgt B) (q : Wgt C) (hp : ∀ i,|p i|≤1) (hq : ∀ i,|q i|≤1):
    |avg (pairW u v) (fun i=> f i*(p i.1*q i.2))|^4 ≤
      avg (pairW (pairW u v) (pairW u v)) (spread f) := by
  classical
  let U := fun i => avg v (fun j => f (i,j)*q j)
  let T : Wgt (B×C) := fun i=> f i*(p i.1*q i.2)
  have h :
      avg (pairW u v) T =dip u p U := by
    unfold T U dip; rw [pairW_avg]; simp_rw [mul_left_comm _ (p _),avg_mul']
  have h0 (x y : ℝ) (hx:|x|≤1) (hy:|y|≤1) : |x*y|≤1 := by rw [abs_mul]; exact
    (mul_le_mul hx hy (abs_nonneg _) zero_le_one).trans_eq (by ring)
  have hh {A : Type} [Fintype A] {w : Wgt A} (hw : IsLaw w) (p q : Wgt A)
      (hp : ∀ i,|p i|≤1) :
      dip w p q ^2 ≤ ode w q := by
    have he : ode w p≤1 := (ode_upper hw.sub _ 1 hp).trans_eq (by ring)
    apply le_trans _ ((mul_le_mul_of_nonneg_right he (ode_nonneg hw.nz q)).trans_eq (one_mul _))
    simpa only [dip,ode,pow_two] using avg_CS hw.nz p q
  let V := pairW v v
  have hV := pairW_law hv hv
  let Y (j : C×C) (i:B) := f (i,j.1)*f (i,j.2)
  let W (j) := avg u (Y j)
  let Q (j : C×C) := q j.1*q j.2
  have he : ode u U=dip V Q W := by
    have hi i : U i*U i=avg V (fun j => Q j*Y j i) := by
      unfold U
      rw [avg_prod]; apply avg_congr; intro j _
      unfold Q Y; ring
    unfold ode dip; simp_rw [hi]; rw [avg_avg]; simp_rw [avg_mul']; rfl
  let D (j : C×C) (i : B× B) := Y j i.1*Y j i.2
  have hw : ode V W= avg (pairW (pairW u v) (pairW u v)) (spread f) := by
    have hi j : W j*W j=avg (pairW u u) (fun i => D j i) := avg_prod u _ _
    unfold ode dip; simp_rw [hi]; unfold V; simp_rw [pairW_avg]
    conv_rhs => rw [avg_avg]
    apply avg_congr; intro i _
    conv_rhs =>

      skip
    unfold D Y spread

    conv_lhs => rw [avg_avg]
    refine avg_congr fun i _ => ?_
    rw [avg_avg]
  change |avg (pairW u v) T|^4≤ _
  rw [h,←hw,show |dip u p U|^4=(dip u p U^2)^2 by rw [show |dip u p U|^4=(|dip u p U|^2)^2 by ring,
    sq_abs]]
  apply (pow_le_pow_left₀ (sq_nonneg _) (hh hu p U hp) 2).trans
  rw [he]
  exact hh hV Q W (fun i=>h0 _ _ (hq _) (hq _))

theorem quart_CS (E : A≃ B×C) (U : Wgt A) (u : Wgt A) (p : Wgt B) (q : Wgt C)
    (he : mapW u E=pairW p q) (hp : IsLaw p) (hq : IsLaw q)
    (f : Wgt B) (g : Wgt C) (hf : ∀ i,|f i|≤1) (hg : ∀ i,|g i|≤1) :
    |avg u (fun i=>U i*(f (E i).1*g (E i).2))|^4 ≤ avg (pairW u u) (quart E U) := by
  have hh := spread_gain p q (U∘E.symm) hp hq f g hf hg
  rw [quart_shift]
  rw [← he,mapW_avg] at hh
  simp only [Function.comp_apply,Equiv.symm_apply_apply] at hh
  exact hh
end HadwigerCounterexample

end

end OAI
