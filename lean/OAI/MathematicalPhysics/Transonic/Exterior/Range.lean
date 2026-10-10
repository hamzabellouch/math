import OAI.MathematicalPhysics.Transonic.Exterior.Trace

namespace OAI

section
noncomputable section
namespace SepticProfile.FixedInterval

def intersect (a b : Box) : Box :=
  let l := max (a.center-a.radius) (b.center-b.radius)
  let u := min (a.center+a.radius) (b.center+b.radius)
  ⟨(l+u)/2,(u-l)/2+2⟩

lemma holds_intersect {Q : ℤ} {a b : Box} {x : ℝ}
    (ha : Holds Q a x) (hb : Holds Q b x) : Holds Q (intersect a b) x := by
  let l := max (a.center-a.radius) (b.center-b.radius)
  let u := min (a.center+a.radius) (b.center+b.radius)
  have hlo : (l:ℝ)≤(Q:ℝ)*x := by
    simp only [l,Int.cast_max,Int.cast_sub,max_le_iff]
    exact ⟨(bounds ha).1,(bounds hb).1⟩
  have hup : (Q:ℝ)*x≤(u:ℝ) := by
    simp only [u,Int.cast_min,Int.cast_add,le_min_iff]
    exact ⟨(bounds ha).2,(bounds hb).2⟩
  have hc := quotient_bounds (l+u) 2 (by norm_num)
  have hr := quotient_bounds (u-l) 2 (by norm_num)
  have hc1 : (((l+u)/2:ℤ):ℝ)*2≤(l:ℝ)+u := by exact_mod_cast hc.1
  have hc2 : (l:ℝ)+u<((((l+u)/2:ℤ):ℝ)+1)*2 := by exact_mod_cast hc.2
  have hr2 : (u:ℝ)-l<((((u-l)/2:ℤ):ℝ)+1)*2 := by exact_mod_cast hr.2
  change |(Q:ℝ)*x-(((l+u)/2:ℤ):ℝ)|≤(((u-l)/2+2:ℤ):ℝ)
  push_cast
  rw [abs_le];constructor <;> linarith

lemma holds_of_bound {Q : ℤ} {a : Box} {x : ℝ}
    (hlo : (a.center:ℝ)-a.radius≤(Q:ℝ)*x)
    (hhi : (Q:ℝ)*x≤(a.center:ℝ)+a.radius) : Holds Q a x := by
  rw [Holds,abs_le];constructor <;> linarith

lemma holds_root {Q : ℤ} (hQ : 0<Q) {b r : Box} {x A d : ℝ}
    (hb : Holds Q b x) (hx : 0<x) (hd : 0≤d) (he : x*d^73=A)
    (hr : 0≤r.center-r.radius) (hrad : 0≤r.radius)
    (hlo : (((b.center+b.radius:ℤ):ℝ)/Q)*(((r.center-r.radius:ℤ):ℝ)/Q)^73≤A)
    (hhi : A≤(((b.center-b.radius:ℤ):ℝ)/Q)*(((r.center+r.radius:ℤ):ℝ)/Q)^73) :
    Holds Q r d := by
  have hQ' : (0:ℝ)<Q := by exact_mod_cast hQ
  have hr' : (0:ℝ)≤(((r.center-r.radius:ℤ):ℝ)/Q) := by
    exact div_nonneg (by exact_mod_cast hr) hQ'.le
  have hblo : (((b.center-b.radius:ℤ):ℝ)/Q)≤x := by
    rw [div_le_iff₀ hQ'];push_cast;linarith [(bounds hb).1]
  have hbhi : x≤(((b.center+b.radius:ℤ):ℝ)/Q) := by
    rw [le_div_iff₀ hQ'];push_cast;linarith [(bounds hb).2]
  have hdlo : (((r.center-r.radius:ℤ):ℝ)/Q)≤d := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (73:ℕ)≠0) hd
    have hh := mul_le_mul_of_nonneg_right hbhi (pow_nonneg hr' 73)
    apply (mul_le_mul_iff_of_pos_left hx).mp
    rw [he]
    exact hh.trans hlo
  have hdhi : d≤(((r.center+r.radius:ℤ):ℝ)/Q) := by
    have hrr : 0≤(((r.center+r.radius:ℤ):ℝ)/Q) := by
      apply div_nonneg _ hQ'.le
      have hrR : (0:ℝ)≤r.radius := by exact_mod_cast hrad
      have hrL : (0:ℝ)≤(r.center:ℝ)-r.radius := by exact_mod_cast hr
      push_cast;linarith
    apply le_of_pow_le_pow_left₀ (by norm_num : (73:ℕ)≠0) hrr
    apply (mul_le_mul_iff_of_pos_left hx).mp
    rw [he]
    exact hhi.trans (mul_le_mul_of_nonneg_right hblo (pow_nonneg hrr 73))
  apply holds_of_bound
  · have := (div_le_iff₀ hQ').mp hdlo;push_cast at this;linarith
  · have := (le_div_iff₀ hQ').mp hdhi;push_cast at this;linarith

lemma powers_enclosed {Q : ℤ} (hQ : 0<Q) (p : ℕ → Box) (r : Box) (d : ℝ)
    (hr : Holds Q r d) (hp0 : p 0=ExteriorJet.oneBox Q)
    (hp : ∀ j, j<73 → p (j+1)=mul Q (p j) r) :
    ∀ j, j≤73 → Holds Q (p j) (d^j) := by
  intro j hj
  induction j with
  | zero => rw [pow_zero,hp0];exact ExteriorJet.holds_oneBox Q
  | succ j ih =>
    rw [hp j (by omega),pow_succ]
    exact holds_mul hQ (ih (by omega)) hr

lemma normalized_monomials {Q : ℤ} (hQ : 0<Q)
    (b : ℕ → ℝ) (rat up w rd : ℕ → Box) (d : ℝ) (root amp : Box)
    (hroot : Holds Q root d)
    (hu : ∀ j, 1≤j → j≤73 → Holds Q (up j) (b j*d^j))
    (hr : ∀ j, 2≤j → j≤73 → Holds Q (rat j) (b j/b (j-1)))
    (hb : ∀ j, 1≤j → j≤73 → b j≠0) (hd : d≠0)
    (ha : w 73=amp) (ham : Holds Q amp (b 73*d^73))
    (hrd : ∀ j, 2≤j → j≤73 → rd j=mul Q (rat j) root)
    (hrpos : ∀ j, 2≤j → j≤73 → 0<(rd j).center-(rd j).radius)
    (hw : ∀ j, 1≤j → j<73 → w j=intersect (up j) (ExteriorJet.divBox Q (w (j+1)) (rd (j+1)))) :
    ∀ j, 1≤j → j≤73 → Holds Q (w j) (b j*d^j) := by
  intro j hj hjN
  induction h : 73-j using Nat.strong_induction_on generalizing j with
  | h n ih =>
    by_cases he : j=73
    · subst j;rw [ha];exact ham
    · have hjlt : j<73 := by omega
      have hnext := ih (73-(j+1)) (by omega) (j+1) (by omega) (by omega) rfl
      rw [hw j hj hjlt]
      apply holds_intersect (hu j hj hjN)
      have hrec : b j*d^j=(b (j+1)*d^(j+1))/((b (j+1)/b j)*d) := by
        rw [pow_succ];field_simp [hb j hj hjN,hb (j+1) (by omega) (by omega),hd]
      rw [hrec]
      apply holds_div hQ hnext
      · rw [hrd (j+1) (by omega) (by omega)]
        apply holds_mul hQ _ hroot
        simpa only [Nat.add_sub_cancel] using hr (j+1) (by omega) (by omega)
      · exact hrpos (j+1) (by omega) (by omega)

/-- Backward Horner recurrence; after `n` steps this is evaluation of the suffix. -/
def hornerBox (Q : ℤ) (a : ℕ → Box) (x : Box) (lo : ℕ) : ℕ → Box
  | 0 => zero
  | n+1 => add (a lo) (mul Q x (hornerBox Q a x (lo+1) n))

def hornerValue (a : ℕ → ℝ) (x : ℝ) (lo : ℕ) : ℕ → ℝ
  | 0 => 0
  | n+1 => a lo+x*hornerValue a x (lo+1) n

lemma holds_horner {Q : ℤ} (hQ : 0<Q) (a : ℕ → Box) (b : ℕ → ℝ)
    (x : Box) (t : ℝ) (ht : Holds Q x t) (lo n : ℕ)
    (hb : ∀ j, lo≤j → j<lo+n → Holds Q (a j) (b j)) :
    Holds Q (hornerBox Q a x lo n) (hornerValue b t lo n) := by
  induction n generalizing lo with
  | zero => exact holds_zero Q
  | succ n ih =>
    apply holds_add (hb lo le_rfl (by omega))
    exact holds_mul hQ ht (ih (lo+1) (fun j hj hj' => hb j (by omega) (by omega)))

lemma hornerValue_sum (a : ℕ → ℝ) (x : ℝ) (lo n : ℕ) :
    hornerValue a x lo n=∑ j∈Finset.range n, a (lo+j)*x^j := by
  induction n generalizing lo with
  | zero => simp [hornerValue]
  | succ n ih =>
    rw [hornerValue,ih,Finset.sum_range_succ']
    simp only [Nat.add_zero,pow_zero,mul_one,Finset.mul_sum]
    conv_rhs => rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [show lo+(i+1)=lo+1+i by omega,pow_succ]
    ring

end SepticProfile.FixedInterval

end
end

end OAI
