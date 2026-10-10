import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.DyadicHarmonic01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
end

 

namespace HarmonicTranslation
open scoped BigOperators
noncomputable section

section FiniteWeights
variable {ι : Type*} [DecidableEq ι]

def mass (p : ι →₀ ℝ) : ℝ := p.sum (fun _ a => a)
def eval (p : ι →₀ ℝ) (f : ι → ℝ) : ℝ := p.sum (fun i a => a*f i)
def l1 (p : ι →₀ ℝ) : ℝ := p.sum (fun _ a => |a|)

omit [DecidableEq ι] in
lemma mass_sub (p q : ι →₀ ℝ) : mass (p-q) = mass p-mass q :=
  Finsupp.sum_sub_index (fun _ _ _ => rfl)

omit [DecidableEq ι] in
lemma eval_sub (p q : ι →₀ ℝ) (f : ι → ℝ) : eval (p-q) f = eval p f-eval q f :=
  Finsupp.sum_sub_index (fun _ _ _ => sub_mul _ _ _)

omit [DecidableEq ι] in
lemma mass_nonneg (p : ι →₀ ℝ) (hp : ∀ i, 0 ≤ p i) : 0 ≤ mass p :=
  Finset.sum_nonneg (fun i _ => hp i)

omit [DecidableEq ι] in
lemma eval_bound (p : ι →₀ ℝ) (f : ι → ℝ) {B : ℝ} (hf : ∀ i, |f i| ≤ B) :
    |eval p f| ≤ l1 p * B := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i ∈ p.support, |p i| * B := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

 

theorem l1_le_twice_edge (p q : ι →₀ ℝ) (E : Finset ι)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hm : mass q = mass p)
    (hedge : ∀ i, i ∉ E → p i ≤ q i) :
    l1 (q-p) ≤ 2 * ∑ i ∈ E, p i := by
  let S := p.support ∪ q.support ∪ E
  have hpS : p.support ⊆ S := fun i hi => Finset.mem_union_left _ (Finset.mem_union_left _ hi)
  have hqS : q.support ⊆ S := fun i hi => Finset.mem_union_left _ (Finset.mem_union_right _ hi)
  have hdS : (q-p).support ⊆ S := (Finsupp.support_sub ..).trans (by
    intro i hi
    rcases Finset.mem_union.mp hi with h|h
    · exact hqS h
    · exact hpS h)
  have hmass : (∑ i ∈ S, (q i - p i)) = 0 := by
    rw [Finset.sum_sub_distrib,← q.sum_of_support_subset hqS (fun _ a => a) (by simp),
      ← p.sum_of_support_subset hpS (fun _ a => a) (by simp)]
    exact sub_eq_zero.mpr hm
  have hpoint (i : ι) : |q i-p i| ≤ q i-p i + 2*(if i ∈ E then p i else 0) := by
    by_cases hi : i ∈ E
    · simp only [hi,ite_true]
      rw [abs_le]
      constructor <;> linarith [hp i,hq i]
    · simp only [hi,ite_false,mul_zero,add_zero]
      exact le_of_eq (abs_of_nonneg (sub_nonneg.mpr (hedge i hi)))
  rw [l1,(q-p).sum_of_support_subset hdS (fun _ a => |a|) (by simp)]
  calc
    _ ≤ ∑ i ∈ S, (q i-p i + 2*(if i ∈ E then p i else 0)) := by
      apply Finset.sum_le_sum
      intro i _
      exact hpoint i
    _ = 2 * ∑ i ∈ E, p i := by
      rw [Finset.sum_add_distrib,hmass,zero_add,← Finset.mul_sum]
      congr 1
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext i
        simp only [Finset.mem_filter,Finset.mem_union,S]
        tauto
      · intro _ _; rfl

end FiniteWeights

def shift (h : ℤ) (p : ℤ →₀ ℝ) : ℤ →₀ ℝ := p.mapDomain (fun n => n+h)

@[simp] lemma shift_apply (h n : ℤ) (p : ℤ →₀ ℝ) : shift h p n = p (n-h) := by
  have hh := Finsupp.mapDomain_apply_of_injective (f := fun n : ℤ => n+h)
    (fun a b hab => add_right_cancel hab) p (n-h)
  simpa only [shift,sub_add_cancel] using hh

@[simp] lemma mass_shift (h : ℤ) (p : ℤ →₀ ℝ) : mass (shift h p) = mass p := by
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

lemma eval_shift (h : ℤ) (p : ℤ →₀ ℝ) (f : ℤ → ℝ) :
    eval (shift h p) f = eval p (fun n => f (n+h)) := by
  exact Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul ..)

@[simp] lemma shift_zero (p : ℤ →₀ ℝ) : shift 0 p = p := by ext n; simp
@[simp] lemma shift_shift (h k : ℤ) (p : ℤ →₀ ℝ) : shift h (shift k p) = shift (h+k) p := by
  ext n
  simp only [shift_apply]
  congr 1
  ring

lemma shift_sub (h : ℤ) (p q : ℤ →₀ ℝ) : shift h (p-q) = shift h p-shift h q := by
  ext n
  simp

lemma l1_shift (h : ℤ) (p : ℤ →₀ ℝ) : l1 (shift h p) = l1 p := by
  unfold l1 shift
  rw [Finsupp.sum_mapDomain_index_inj (fun a b hab => add_right_cancel hab)]

 
def raw (X W : ℕ) : ℤ →₀ ℝ := by
  classical
  exact Finsupp.onFinset (Finset.Ico (X : ℤ) (X^2 : ℤ))
    (fun n => if (X : ℤ) ≤ n ∧ n < (X^2 : ℤ) ∧ IsCoprime n (W : ℤ)
      then (n : ℝ)⁻¹ else 0) (by
      intro n hn
      split_ifs at hn with h
      · exact Finset.mem_Ico.mpr ⟨h.1,h.2.1⟩
      · exact (hn rfl).elim)

@[simp] lemma raw_apply (X W : ℕ) (n : ℤ) : raw X W n =
    if (X : ℤ) ≤ n ∧ n < (X^2 : ℤ) ∧ IsCoprime n (W : ℤ) then (n : ℝ)⁻¹ else 0 := by
  classical
  rfl

lemma raw_nonneg {X W : ℕ} (_hX : 0 < X) (n : ℤ) : 0 ≤ raw X W n := by
  classical
  rw [raw_apply]
  split_ifs with h
  · exact inv_nonneg.mpr (by exact_mod_cast le_trans (Int.natCast_nonneg _) h.1)
  · exact le_rfl

lemma raw_le_inv {X W : ℕ} (hX : 0 < X) (n : ℤ) : raw X W n ≤ (X : ℝ)⁻¹ := by
  classical
  rw [raw_apply]
  split_ifs with h
  · exact inv_anti₀ (by exact_mod_cast hX) (by exact_mod_cast h.1)
  · positivity

lemma raw_outside_lower {X W : ℕ} {n : ℤ} (hn : n < X) : raw X W n = 0 := by
  classical
  simp only [raw_apply,not_le.mpr hn,false_and,ite_false]

 

lemma outside_edge {X W : ℕ} (hX : 0 < X) {h : ℤ} (hh : 0 ≤ h) (hW : (W : ℤ) ∣ h)
    (n : ℤ) (hn : n ∉ Finset.Ico (X : ℤ) ((X : ℤ)+h)) :
    raw X W n ≤ shift h (raw X W) n := by
  classical
  rw [shift_apply,raw_apply]
  split_ifs with hgood
  · have hnL : (X : ℤ)+h ≤ n := by
      have := mt Finset.mem_Ico.mpr hn
      omega
    have hprev : (X : ℤ) ≤ n-h ∧ n-h < (X^2 : ℤ) ∧ IsCoprime (n-h) (W : ℤ) := by
      obtain ⟨t,rfl⟩ := hW
      refine ⟨by omega,by omega,?_⟩
      have hi := hgood.2.2.add_mul_right_left (-t)
      rw [show n-(W : ℤ)*t = n+(-t)*(W : ℤ) by ring]
      exact hi
    rw [raw_apply,ite_eq_left hprev]
    exact inv_anti₀ (by exact_mod_cast (show (0:ℤ) < n-h by omega)) (by exact_mod_cast (show n-h ≤ n by omega))
  · exact raw_nonneg hX _

 
theorem raw_translation_nonneg {X W : ℕ} (hX : 0 < X) {h : ℤ}
    (hh : 0 ≤ h) (hW : (W : ℤ) ∣ h) :
    l1 (shift h (raw X W)-raw X W) ≤ 2 * (h : ℝ) / X := by
  have hb := l1_le_twice_edge (raw X W) (shift h (raw X W))
    (Finset.Ico (X : ℤ) ((X : ℤ)+h)) (raw_nonneg hX)
    (fun n => by simpa using raw_nonneg (W := W) hX (n-h)) (mass_shift ..)
    (outside_edge hX hh hW)
  have hs : (∑ n ∈ Finset.Ico (X : ℤ) ((X : ℤ)+h), raw X W n) ≤
      (h : ℝ) / X := by
    apply (Finset.sum_le_sum (fun n _ => raw_le_inv hX n)).trans_eq
    simp only [Finset.sum_const,nsmul_eq_mul,Int.card_Ico,add_sub_cancel_left]
    rw [show (h.toNat : ℝ) = (h : ℝ) by exact_mod_cast Int.toNat_of_nonneg hh]
    rw [div_eq_mul_inv]
  simpa only [mul_div_assoc] using hb.trans (mul_le_mul_of_nonneg_left hs (by norm_num))

lemma l1_neg (p : ℤ →₀ ℝ) : l1 (-p) = l1 p := by
  unfold l1
  rw [Finsupp.sum_neg_index (fun _ => abs_zero)]
  simp only [abs_neg]

lemma l1_sub_comm (p q : ℤ →₀ ℝ) : l1 (p-q) = l1 (q-p) := by
  rw [← l1_neg,neg_sub]

lemma l1_translation_neg (p : ℤ →₀ ℝ) (h : ℤ) :
    l1 (shift (-h) p-p) = l1 (shift h p-p) := by
  rw [← l1_shift h,shift_sub,shift_shift,add_neg_cancel,shift_zero,l1_sub_comm]

theorem raw_translation {X W : ℕ} (hX : 0 < X) {h : ℤ} (hW : (W : ℤ) ∣ h) :
    l1 (shift h (raw X W)-raw X W) ≤ 2 * |(h : ℝ)| / X := by
  rcases le_total 0 h with hh|hh
  · simpa only [abs_of_nonneg (show (0:ℝ) ≤ h by exact_mod_cast hh)] using
      raw_translation_nonneg hX hh hW
  · have hi := raw_translation_nonneg hX (neg_nonneg.mpr hh) (dvd_neg.mpr hW)
    rw [l1_translation_neg] at hi
    simpa only [Int.cast_neg,abs_of_nonpos (show (h : ℝ) ≤ 0 by exact_mod_cast hh)] using hi

lemma sum_le_mass (p : ℤ →₀ ℝ) (hp : ∀ n, 0 ≤ p n) (E : Finset ℤ) :
    (∑ n ∈ E, p n) ≤ mass p := by
  rw [mass,p.sum_of_support_subset (Finset.subset_union_left (s₂ := E))
    (fun _ a => a) (by simp)]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right (fun n _ _ => hp n)

 

theorem raw_mass_lower {X W : ℕ} (hW : 0 < W) (hX : 2*W+2 ≤ X) :
    (2*(W : ℝ))⁻¹ ≤ mass (raw X W) := by
  classical
  have hX0 : 0 < X := by omega
  let f : ℕ → ℤ := fun k => 1+(W : ℤ)*((X : ℤ)+k)
  have hf : Function.Injective f := by
    intro a b hab
    have hWi : (W : ℤ) ≠ 0 := by exact_mod_cast hW.ne'
    have hh : (a : ℤ) = b := by
      apply add_left_cancel (a := (X : ℤ))
      apply mul_left_cancel₀ hWi
      exact add_left_cancel hab
    exact_mod_cast hh
  have hwR : (0 : ℝ) < W := by exact_mod_cast hW
  have hxR : (0 : ℝ) < X := by exact_mod_cast hX0
  have hpoint (k : ℕ) (hk : k ∈ Finset.range X) :
      (2*(W : ℝ)*X)⁻¹ ≤ raw X W (f k) := by
    have hkX := Finset.mem_range.mp hk
    have hL : (X : ℤ) ≤ f k := by
      dsimp [f]
      have hi : (1:ℤ) ≤ W := by exact_mod_cast hW
      have hj : (0:ℤ) ≤ k := Int.natCast_nonneg k
      have hn : (0:ℤ) ≤ X := Int.natCast_nonneg X
      nlinarith
    have hU : f k ≤ 2*(W : ℤ)*X := by
      dsimp [f]
      have hi : (1:ℤ) ≤ W := by exact_mod_cast hW
      have hj : (k : ℤ)+1 ≤ X := by exact_mod_cast hkX
      nlinarith
    have hUX : 2*(W : ℤ)*X < (X : ℤ)^2 := by
      have hi : 2*(W : ℤ)+2 ≤ X := by exact_mod_cast hX
      have hj : (0:ℤ) < X := by exact_mod_cast hX0
      nlinarith
    have hc : IsCoprime (f k) (W : ℤ) := by
      have hi := (isCoprime_one_left (x := (W : ℤ))).add_mul_right_left ((X : ℤ)+k)
      simpa only [f,mul_comm] using hi
    rw [raw_apply,ite_eq_left ⟨hL,hU.trans_lt hUX,hc⟩]
    exact inv_anti₀ (by exact_mod_cast (show (0:ℤ) < f k by omega))
      (by exact_mod_cast hU)
  calc
    _ = (X : ℝ) * (2*(W : ℝ)*X)⁻¹ := by field_simp
    _ = ∑ k ∈ Finset.range X, (2*(W : ℝ)*X)⁻¹ := by simp
    _ ≤ ∑ k ∈ Finset.range X, raw X W (f k) := Finset.sum_le_sum hpoint
    _ = ∑ n ∈ (Finset.range X).image f, raw X W n :=
      (Finset.sum_image (fun _ _ _ _ h => hf h)).symm
    _ ≤ mass (raw X W) := sum_le_mass _ (raw_nonneg hX0) _

 

def law (X W : ℕ) : ℤ →₀ ℝ := (mass (raw X W))⁻¹ • raw X W

lemma mass_smul (c : ℝ) (p : ℤ →₀ ℝ) : mass (c • p) = c * mass p := by
  unfold mass
  rw [Finsupp.sum_smul_index (fun _ => rfl)]
  exact Finset.mul_sum .. |>.symm

lemma l1_smul (c : ℝ) (p : ℤ →₀ ℝ) : l1 (c • p) = |c| * l1 p := by
  unfold l1
  rw [Finsupp.sum_smul_index (fun _ => abs_zero)]
  simp only [abs_mul]
  exact Finset.mul_sum .. |>.symm

lemma shift_smul (h : ℤ) (c : ℝ) (p : ℤ →₀ ℝ) : shift h (c • p) = c • shift h p := by
  ext n
  simp

lemma mass_law {X W : ℕ} (hW : 0 < W) (hX : 2*W+2 ≤ X) : mass (law X W) = 1 := by
  have hp : 0 < mass (raw X W) :=
    (inv_pos.mpr (by positivity : (0:ℝ) < 2*W)).trans_le (raw_mass_lower hW hX)
  rw [law,mass_smul,inv_mul_cancel₀ hp.ne']

 

theorem law_translation {X W : ℕ} (hW : 0 < W) (hX : 2*W+2 ≤ X)
    {h : ℤ} (hh : (W : ℤ) ∣ h) :
    l1 (shift h (law X W)-law X W) ≤ 4*(W : ℝ)*|(h : ℝ)|/X := by
  have hX0 : 0 < X := by omega
  have hm := raw_mass_lower hW hX
  have hp : 0 < mass (raw X W) :=
    (inv_pos.mpr (by positivity : (0:ℝ) < 2*W)).trans_le hm
  have hinv : (mass (raw X W))⁻¹ ≤ 2*(W : ℝ) := by
    have hi := inv_anti₀ (by positivity : (0:ℝ) < (2*(W : ℝ))⁻¹) hm
    simpa only [inv_inv] using hi
  rw [law,shift_smul,← smul_sub,l1_smul,abs_of_pos (inv_pos.mpr hp)]
  calc
    _ ≤ (2*(W : ℝ)) * (2*|(h : ℝ)|/X) :=
      mul_le_mul hinv (raw_translation hX0 hh) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
        (by positivity)
    _ = _ := by ring

end
end HarmonicTranslation

end

end OAI
