import OAI.Probability.RadialTransition.ScaleSequence

namespace OAI

noncomputable section
open scoped BigOperators NNReal
open Set Filter
namespace RadialTransition

def reversePrefix (v : ℝ) (f : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => v
  | n+1 => prepend (f n) (reversePrefix v f n)
@[simp] lemma reversePrefix_zero (v : ℝ) (f : ℕ → ℝ) : reversePrefix v f 0=(fun _ => v) := rfl
@[simp] lemma reversePrefix_succ (v : ℝ) (f : ℕ → ℝ) (n : ℕ) :
    reversePrefix v f (n+1)=prepend (f n) (reversePrefix v f n) := rfl
lemma reversePrefix_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (n : ℕ) : ∀ j, 0 ≤ reversePrefix 0 f n j := by
  induction n with
  | zero => exact fun _ => le_rfl
  | succ n ih => exact prepend_nonneg (hf n) ih
lemma reversePrefix_range {R : ℕ → ℝ} (hR : ∀ n, 1 ≤ R n) (n : ℕ) : ∀ j, 1 ≤ reversePrefix 1 R n j := by
  induction n with
  | zero => exact fun _ => le_rfl
  | succ n ih => exact prepend_range (hR n) ih
lemma reversePrefix_range_le {R : ℕ → ℝ} {M : ℝ} (hM : 1 ≤ M) {n : ℕ}
    (hR : ∀ j, j<n → R j ≤ M) : ∀ j, reversePrefix 1 R n j ≤ M := by
  induction n with
  | zero => exact fun _ => hM
  | succ n ih =>
    intro j
    cases j with
    | zero => exact hR n (by omega)
    | succ j => exact ih (fun i hi => hR i (by omega)) j
lemma summable_reversePrefix (f : ℕ → ℝ) (n : ℕ) : Summable (reversePrefix 0 f n) := by
  induction n with
  | zero => exact summable_zero
  | succ n ih => exact summable_prepend _ ih
lemma tsum_reversePrefix (f : ℕ → ℝ) (n : ℕ) :
    (∑' j, reversePrefix 0 f n j)=∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih => rw [reversePrefix_succ,tsum_prepend _ (summable_reversePrefix f n),Finset.sum_range_succ,ih,add_comm]
lemma attractionProfile_reversePrefix {a R : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n)
    (n : ℕ) (r : ℝ) : attractionProfile (reversePrefix 0 a n) (reversePrefix 1 R n) r=
      ∑ j ∈ Finset.range n, a j*scaledBumpProfile (R j) r := by
  induction n with
  | zero => simp [attractionProfile]
  | succ n ih =>
    rw [reversePrefix_succ,reversePrefix_succ,attractionProfile_prepend (reversePrefix_nonneg ha n)
      (reversePrefix_range hR n) (summable_reversePrefix a n),Finset.sum_range_succ,ih,add_comm]

def cutMass (f : ℕ → ℝ) (n j : ℕ) : ℝ := if j<n then f j else 0
lemma cutMass_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (n : ℕ) : ∀ j, 0 ≤ cutMass f n j := by
  intro j; dsimp [cutMass]; split
  · exact hf j
  · exact le_rfl
lemma cutMass_le {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (n j : ℕ) : cutMass f n j ≤ f j := by
  dsimp [cutMass]; split <;> simp_all
lemma summable_cutMass (f : ℕ → ℝ) (n : ℕ) : Summable (cutMass f n) := by
  apply summable_of_ne_finset_zero (s := Finset.range n)
  intro j hj
  simp only [Finset.mem_range,not_lt] at hj
  simp [cutMass,not_lt.mpr hj]
lemma tsum_cutMass (f : ℕ → ℝ) (n : ℕ) : (∑' j, cutMass f n j)=∑ j ∈ Finset.range n, f j := by
  rw [tsum_eq_sum (s := Finset.range n) (fun j hj => by simp_all [cutMass])]
  apply Finset.sum_congr rfl
  intro j hj
  simp [cutMass,Finset.mem_range.mp hj]
lemma attractionProfile_cutMass (a R : ℕ → ℝ) (n : ℕ) (r : ℝ) : attractionProfile (cutMass a n) R r=
      ∑ j ∈ Finset.range n, a j*scaledBumpProfile (R j) r := by
  unfold attractionProfile
  rw [tsum_eq_sum (s := Finset.range n) (fun j hj => by simp_all [cutMass])]
  apply Finset.sum_congr rfl
  intro j hj
  simp [cutMass,Finset.mem_range.mp hj]
lemma familyPotential_reverse_cut {a R : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n)
    (t : ℝ) (n : ℕ) : familyPotential t (reversePrefix 0 a n) (reversePrefix 1 R n)=
      familyPotential t (cutMass a n) R := by
  funext r
  simp only [familyPotential,attractionProfile_reversePrefix ha hR,attractionProfile_cutMass]
lemma reversePrefix_admissible {t A : ℝ} {a R : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n)
    (hs : Summable a) (hA : ∑' n, a n ≤ A) (n : ℕ) :
    AdmissibleFamily t A (reversePrefix 0 a n) (reversePrefix 1 R n) := by
  refine ⟨reversePrefix_nonneg ha n,reversePrefix_range hR n,summable_reversePrefix a n,?_⟩
  rw [tsum_reversePrefix]
  exact (hs.sum_le_tsum _ (fun j _ => ha j)).trans hA
lemma cutMass_difference {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (n : ℕ) :
    (∑' j, |a j-cutMass a n j|)=(∑' j, a j)-∑ j ∈ Finset.range n, a j := by
  have he : (fun j => |a j-cutMass a n j|)=(fun j => a j-cutMass a n j) := by
    funext j
    exact abs_of_nonneg (sub_nonneg.mpr (cutMass_le ha n j))
  rw [he,hs.tsum_sub (summable_cutMass a n),tsum_cutMass]
lemma tendsto_cutMass_difference {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a) :
    Tendsto (fun n => ∑' j, |a j-cutMass a n j|) atTop (nhds 0) := by
  simp_rw [cutMass_difference ha hs]
  simpa using (tendsto_const_nhds (x := ∑' j, a j)).sub hs.hasSum.tendsto_sum_nat
lemma grandPressure_reversePrefix_tendsto {t A β h : ℝ} {a R : ℕ → ℝ}
    (ht : 1 ≤ t) (hβ : 0 < β) (had : AdmissibleFamily t A a R)
    (hrow : 2197*t*bumpIntegral⁻¹*A ≤ (t^2/8)/8) :
    Tendsto (fun n => grandPressure (familyPotential t (reversePrefix 0 a n) (reversePrefix 1 R n)) t β h)
      atTop (nhds (grandPressure (familyPotential t a R) t β h)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero_norm (a := fun n => familyPressureLipschitz t β h * ∑' j, |a j-cutMass a n j|)
  · intro n
    simpa only [Real.norm_eq_abs,abs_abs,familyPotential_reverse_cut had.1 had.2.1] using grandPressure_family_difference ht hβ (cutMass_nonneg had.1 n) had.1 had.1 had.2.1
      (summable_cutMass a n) had.2.2.1 had.2.2.1 (cutMass_le had.1 n) (fun _ => le_rfl)
      (admissible_row (by linarith) had hrow)
  · simpa using (tendsto_cutMass_difference had.1 had.2.2.1).const_mul (familyPressureLipschitz t β h)

end RadialTransition
end

end OAI
