import Mathlib
import OAI.Computability.QuantumFactoring.QuantumCore

namespace OAI

section
open scoped BigOperators


/-! Bounded Euclidean recovery of the manuscript's nearest-bin labels.
The denominator bound is logarithmic, never a search through B labels. -/
namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- Euclid's finite convergent recurrence, entirely natural/rational arithmetic. -/
def euclidConvergent (a b : ℕ) : ℕ → ℚ
  | 0 => (a/b:ℕ)
  | k+1 => (a/b:ℕ)+(euclidConvergent b (a%b) k)⁻¹

lemma euclidConvergent_zero_pair (k : ℕ) : ∀ b,
    euclidConvergent 0 b k=0 ∧ euclidConvergent b 0 k=0 := by
  induction k with
  | zero => intro b; simp [euclidConvergent]
  | succ k ih =>
    intro b
    constructor <;> simp [euclidConvergent,(ih b).1,(ih b).2]

lemma euclidConvergent_zero_left (b k : ℕ) : euclidConvergent 0 b k=0 :=
  (euclidConvergent_zero_pair k b).1

lemma euclidConvergent_zero_right (a k : ℕ) : euclidConvergent a 0 k=0 :=
  (euclidConvergent_zero_pair k a).2

lemma real_floor_ratio (a b : ℕ) : ⌊(a:ℝ)/b⌋ = ((a/b:ℕ):ℤ) := by
  have hf := Rat.floor_cast (α:=ℝ) ((a:ℚ)/b)
  simp only [Rat.cast_div,Rat.cast_natCast] at hf
  rw [hf,Rat.floor_natCast_div_natCast]
  norm_cast

lemma euclidConvergent_real (a b k : ℕ) :
    euclidConvergent a b k = Real.convergent ((a:ℝ)/b) k := by
  induction k generalizing a b with
  | zero =>
    simp only [euclidConvergent,Real.convergent_zero,real_floor_ratio]
    norm_cast
  | succ k ih =>
    rw [euclidConvergent,Real.convergent_succ,real_floor_ratio,
      Int.fract_div_natCast_eq_div_natCast_mod,inv_div,← ih]
    congr 1

lemma ratio_euclid (a b : ℕ) :
    (a:ℚ)/b = (a/b:ℕ)+((b:ℚ)/((a%b:ℕ):ℚ))⁻¹ := by
  have h := Int.floor_add_fract ((a:ℚ)/b)
  rw [Rat.floor_natCast_div_natCast,Int.fract_div_natCast_eq_div_natCast_mod] at h
  simpa only [Int.cast_natCast,← Int.natCast_ediv,inv_div] using h.symm

/-- Two Euclidean steps halve the denominator; the zero remainder is treated
separately, since natural remainder by zero is not zero. -/
lemma euclid_two_halving {b r : ℕ} (hr : 0<r) (hrb : r<b) : 2*(b%r)<b := by
  by_cases h : 2*r ≤ b
  · have hm := Nat.mod_lt b hr
    omega
  · have hb : b<2*r := by omega
    have hmod : b%r=b-r := by
      apply Nat.mod_eq_sub_mod hrb.le |>.trans
      exact Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    omega

/-- At most twice the denominator bit bound suffices, including rational
termination and all later convergents. -/
lemma euclidConvergent_terminal (s a b h : ℕ) (hb : b<2^s) :
    euclidConvergent a b (2*s+h) = (a:ℚ)/b := by
  induction s generalizing a b h with
  | zero =>
    have : b=0 := by simpa using hb
    subst b
    simp [euclidConvergent_zero_right]
  | succ s ih =>
    by_cases hb0 : b=0
    · subst b
      simp [euclidConvergent_zero_right]
    have hbpos : 0<b := Nat.pos_of_ne_zero hb0
    by_cases h0 : a%b=0
    · have he : 2*(s+1)+h = (2*s+h+1)+1 := by omega
      rw [he,euclidConvergent,h0,euclidConvergent_zero_right,inv_zero,add_zero]
      simpa [h0] using (ratio_euclid a b).symm
    · have hr : 0<a%b := Nat.pos_of_ne_zero h0
      have hh := euclid_two_halving hr (Nat.mod_lt a hbpos)
      have hb' : b%(a%b)<2^s := by
        rw [pow_succ] at hb
        omega
      have he : 2*(s+1)+h = (2*s+h+1)+1 := by omega
      rw [he,euclidConvergent,euclidConvergent,ih _ _ h hb']
      rw [← ratio_euclid b (a%b),← ratio_euclid a b]

/-- Every possible convergent is already in this polynomial-size list. -/
lemma euclidConvergent_bounded {s a b k : ℕ} (hb : b<2^s) :
    ∃ i ≤ 2*s, euclidConvergent a b k = euclidConvergent a b i := by
  by_cases hk : k≤2*s
  · exact ⟨k,hk,rfl⟩
  · refine ⟨2*s,le_rfl,?_⟩
    obtain ⟨h,rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_ge hk)
    rw [euclidConvergent_terminal s a b h hb]
    simpa using (euclidConvergent_terminal s a b 0 hb).symm

lemma bin_error_div {Q d j : ℕ} (hd : 0<d) (hQ : 0<Q) :
    |(bin Q d j:ℝ)/Q-(j:ℝ)/d| ≤ 1/(2*(Q:ℝ)) := by
  have hQ' : (0:ℝ)<Q := by exact_mod_cast hQ
  have he : (bin Q d j:ℝ)/Q-(j:ℝ)/d = binError Q d j/(Q:ℝ) := by
    unfold binError
    field_simp
  rw [he,abs_div,abs_of_pos hQ',div_le_iff₀ hQ']
  have hh : 1/(2*(Q:ℝ))*(Q:ℝ)=1/2 := by field_simp
  rw [hh]
  exact binError_bound hd

/-- Legendre recovery with an explicit O(log Q) search bound. -/
lemma bin_has_bounded_convergent {Q d j s : ℕ}
    (hd : 0<d) (hQ : d^2<Q) (hsize : Q<2^s) (hcop : Nat.Coprime j d) :
    ∃ i ≤ 2*s, euclidConvergent (bin Q d j) Q i = (j:ℚ)/d := by
  have hdq : ((j:ℚ)/d).den=d := by
    have hh := Rat.den_div_eq_of_coprime (a:=(j:ℤ)) (b:=(d:ℤ))
      (by exact_mod_cast hd) (by simpa using hcop)
    apply Int.ofNat_inj.mp
    simpa only [Int.cast_natCast] using hh
  have hQ0 : 0<Q := lt_of_le_of_lt (Nat.zero_le _) hQ
  have ha := bin_error_div (j:=j) hd hQ0
  have hs : 1/(2*(Q:ℝ)) < 1/(2*(d:ℝ)^2) := by
    apply one_div_lt_one_div_of_lt
    · positivity
    · have hh : (d:ℝ)^2<(Q:ℝ) := by exact_mod_cast hQ
      linarith
  obtain ⟨k,hk⟩ := Real.exists_rat_eq_convergent
    (ξ:=(bin Q d j:ℝ)/Q) (q:=(j:ℚ)/d) (by
      simpa only [hdq,Rat.cast_div,Rat.cast_natCast] using ha.trans_lt hs)
  rw [← euclidConvergent_real] at hk
  obtain ⟨i,hi,hei⟩ := euclidConvergent_bounded (k:=k) hsize
  exact ⟨i,hi,hei.symm.trans hk.symm⟩


lemma bin_mul_bounds {Q d j : ℕ} (hd : 0<d) :
    2*bin Q d j*d ≤ 2*j*Q+d ∧ 2*j*Q ≤ 2*bin Q d j*d+d := by
  have h₁ : bin Q d j*(2*d) ≤ 2*j*Q+d := Nat.div_mul_le_self _ _
  have h₂ : 2*j*Q+d < (bin Q d j+1)*(2*d) := by
    have hr := Nat.mod_lt (2*j*Q+d) (by omega : 0<2*d)
    have he := Nat.mod_add_div (2*j*Q+d) (2*d)
    change (2*j*Q+d)%(2*d)+(2*d)*bin Q d j=2*j*Q+d at he
    nlinarith
  constructor <;> nlinarith

lemma bin_lt {Q d j : ℕ} (hd : 0<d) (hdQ : d≤Q) (hj : j<d) : bin Q d j<Q := by
  unfold bin
  apply (Nat.div_lt_iff_lt_mul (by omega : 0<2*d)).2
  have hh := Nat.mul_le_mul_right (2*Q) (show j+1≤d by omega)
  nlinarith

lemma same_bin_cross {Q d e j i : ℕ} (hd : 0<d) (he : 0<e)
    (hQ : d*e<Q) (hbin : bin Q d j=bin Q e i) : j*e=i*d := by
  obtain ⟨hd₁,hd₂⟩ := bin_mul_bounds (Q:=Q) (j:=j) hd
  obtain ⟨he₁,he₂⟩ := bin_mul_bounds (Q:=Q) (j:=i) he
  rw [← hbin] at he₁ he₂
  have hde₁ := Nat.mul_le_mul_right e hd₁
  have hde₂ := Nat.mul_le_mul_right e hd₂
  have hed₁ := Nat.mul_le_mul_right d he₁
  have hed₂ := Nat.mul_le_mul_right d he₂
  apply le_antisymm
  · by_contra hh
    have hh' : i*d+1≤j*e := by omega
    have hh'' := Nat.mul_le_mul_right (2*Q) hh'
    nlinarith
  · by_contra hh
    have hh' : j*e+1 ≤ i*d := by omega
    have hh'' := Nat.mul_le_mul_right (2*Q) hh'
    nlinarith

lemma same_bin_unique {Q d e j i : ℕ} (hd : 0<d) (he : 0<e)
    (hQ : d*e<Q) (hj : Nat.Coprime j d) (hi : Nat.Coprime i e)
    (hbin : bin Q d j=bin Q e i) : d=e ∧ j=i := by
  have hc := same_bin_cross hd he hQ hbin
  have heq : (j:ℚ)/d=(i:ℚ)/e := by
    apply (div_eq_div_iff (by positivity : (d:ℚ)≠0) (by positivity : (e:ℚ)≠0)).2
    exact_mod_cast hc
  have hh := Rat.div_int_inj (a:=(j:ℤ)) (b:=(d:ℤ)) (c:=(i:ℤ)) (d:=(e:ℤ))
    (by exact_mod_cast hd) (by exact_mod_cast he)
    (by simpa using hj) (by simpa using hi) (by simpa only [Int.cast_natCast] using heq)
  exact ⟨Int.ofNat_inj.mp hh.2,Int.ofNat_inj.mp hh.1⟩

/-- All label checks precede evaluation of any retention expression. -/
def IsBinLabel (Q B k : ℕ) (l : ℕ×ℕ) : Prop :=
  0<l.1 ∧ l.1<B ∧ l.2<l.1 ∧ Nat.Coprime l.2 l.1 ∧ bin Q l.1 l.2=k

instance (Q B k : ℕ) (l : ℕ×ℕ) : Decidable (IsBinLabel Q B k l) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def rationalLabel (q : ℚ) : ℕ×ℕ := (q.den,q.num.toNat)

lemma rationalLabel_reduced {d j : ℕ} (hd : 0<d) (hcop : Nat.Coprime j d) :
    rationalLabel ((j:ℚ)/d)=(d,j) := by
  have hn := Rat.num_div_eq_of_coprime (a:=(j:ℤ)) (b:=(d:ℤ))
    (by exact_mod_cast hd) (by simpa using hcop)
  have hd' := Rat.den_div_eq_of_coprime (a:=(j:ℤ)) (b:=(d:ℤ))
    (by exact_mod_cast hd) (by simpa using hcop)
  apply Prod.ext
  · apply Int.ofNat_inj.mp
    simpa only [rationalLabel,Int.cast_natCast] using hd'
  · simp only [rationalLabel,Int.cast_natCast] at hn ⊢
    rw [hn,Int.toNat_natCast]

/-- Search only the polynomially many Euclidean convergents. Rational labels
not satisfying the exact bin rule are rejected, not rounded into a candidate. -/
def recoveredLabels (s Q B k : ℕ) : List (ℕ×ℕ) :=
  ((List.range (2*s+1)).map (fun i => rationalLabel (euclidConvergent k Q i))).filter
    (fun l => decide (IsBinLabel Q B k l))

lemma mem_recoveredLabels {s Q B k : ℕ} {l : ℕ×ℕ} :
    l ∈ recoveredLabels s Q B k ↔
      IsBinLabel Q B k l ∧ ∃ i≤2*s, rationalLabel (euclidConvergent k Q i)=l := by
  simp only [recoveredLabels,List.mem_filter,List.mem_map,List.mem_range,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨i,hi,he⟩,hl⟩
    exact ⟨hl,i,by omega,he⟩
  · rintro ⟨hl,i,hi,he⟩
    exact ⟨⟨i,by omega,he⟩,hl⟩

lemma recoveredLabels_complete {s Q B k d j : ℕ}
    (hQ : B^2≤Q) (hsize : Q<2^s) (hl : IsBinLabel Q B k (d,j)) :
    (d,j) ∈ recoveredLabels s Q B k := by
  obtain ⟨hd,hdB,hjd,hcop,hbin⟩ := hl
  have hdQ : d^2<Q := by nlinarith
  obtain ⟨i,hi,he⟩ := bin_has_bounded_convergent hd hdQ hsize hcop
  apply mem_recoveredLabels.mpr
  refine ⟨⟨hd,hdB,hjd,hcop,hbin⟩,i,hi,?_⟩
  rw [← hbin,he,rationalLabel_reduced hd hcop]

lemma IsBinLabel.unique {Q B k : ℕ} {l r : ℕ×ℕ} (hQ : B^2≤Q)
    (hl : IsBinLabel Q B k l) (hr : IsBinLabel Q B k r) : l=r := by
  have hp : l.1*r.1<Q := by
    have h₁ := hl.2.1
    have h₂ := hr.2.1
    nlinarith [hl.1,hr.1]
  exact Prod.ext
    (same_bin_unique hl.1 hr.1 hp hl.2.2.2.1 hr.2.2.2.1
      (hl.2.2.2.2.trans hr.2.2.2.2.symm)).1
    (same_bin_unique hl.1 hr.1 hp hl.2.2.2.1 hr.2.2.2.1
      (hl.2.2.2.2.trans hr.2.2.2.2.symm)).2

/-- The operational decoder either returns the unique exact bin label or rejects. -/
def recoverLabel (s Q B k : ℕ) : Option (ℕ×ℕ) :=
  (recoveredLabels s Q B k).head?

lemma recoveredLabels_length (s Q B k : ℕ) :
    (recoveredLabels s Q B k).length ≤ 2*s+1 := by
  exact (List.length_filter_le _ _).trans_eq (by simp)

lemma recoverLabel_sound {s Q B k : ℕ} {l : ℕ×ℕ}
    (h : recoverLabel s Q B k=some l) : IsBinLabel Q B k l := by
  obtain ⟨ys,hy⟩ := List.head?_eq_some_iff.mp h
  have hm : l ∈ recoveredLabels s Q B k := by rw [hy]; simp
  exact (mem_recoveredLabels.mp hm).1

lemma recoverLabel_complete {s Q B k : ℕ} {l : ℕ×ℕ}
    (hQ : B^2≤Q) (hsize : Q<2^s) (hl : IsBinLabel Q B k l) :
    recoverLabel s Q B k=some l := by
  have hm := recoveredLabels_complete hQ hsize hl
  unfold recoverLabel
  cases he : recoveredLabels s Q B k with
  | nil => simp [he] at hm
  | cons r rs =>
    have hr : IsBinLabel Q B k r := (mem_recoveredLabels.mp (by rw [he]; simp)).1
    simpa only [List.head?_cons] using congrArg some (hr.unique hQ hl)

lemma recoverLabel_iff {s Q B k : ℕ} {l : ℕ×ℕ}
    (hQ : B^2≤Q) (hsize : Q<2^s) :
    recoverLabel s Q B k=some l ↔ IsBinLabel Q B k l :=
  ⟨recoverLabel_sound,recoverLabel_complete hQ hsize⟩

end ExactQuantumFactoring.OrderTrial


end

end OAI
