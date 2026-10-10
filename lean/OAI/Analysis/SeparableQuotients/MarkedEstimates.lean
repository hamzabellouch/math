import OAI.Analysis.SeparableQuotients.WindowCharges

namespace OAI

noncomputable section

namespace SeparableQuotient.FiniteVectors
open scoped Classical ENNReal
universe u
variable {ι : Type u} [Fintype ι]

def vec (p : ℝ≥0∞) (v : ι → ℝ) : lp (fun _ : ι => ℝ) p := ⟨v, Memℓp.all v⟩

@[simp] lemma vec_apply (p : ℝ≥0∞) (v : ι → ℝ) (i : ι) : vec p v i = v i := rfl
@[simp] lemma vec_zero (p : ℝ≥0∞) : vec p (0 : ι → ℝ) = 0 := rfl
@[simp] lemma vec_add (p : ℝ≥0∞) (v w : ι → ℝ) : vec p (v+w) = vec p v+vec p w := rfl
@[simp] lemma vec_smul (p : ℝ≥0∞) (c : ℝ) (v : ι → ℝ) : vec p (c • v) = c • vec p v := rfl

lemma norm_rpow {p : ℝ≥0∞} (hp : 0 < p.toReal) (v : ι → ℝ) :
    ‖vec p v‖^p.toReal = ∑ i, |v i|^p.toReal := by
  rw [lp.norm_rpow_eq_tsum hp, tsum_fintype]
  simp only [vec_apply, Real.norm_eq_abs]

lemma norm_le {p : ℝ≥0∞} (hp : 0 < p.toReal) (v : ι → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (h : ∑ i, |v i|^p.toReal ≤ K^p.toReal) : ‖vec p v‖ ≤ K := by
  apply (Real.rpow_le_rpow_iff (lp.norm_nonneg' (vec p v)) hK hp).mp
  rw [norm_rpow hp]
  exact h

lemma sum_rpow_larger (v : ι → ℝ) (p r K : ℝ) (hp : 0 < p) (hpr : p ≤ r) (hK : 0 ≤ K)
    (hv : ∑ i, |v i|^p ≤ K^p) : ∑ i, |v i|^r ≤ K^r := by
  have hi (i : ι) : |v i| ≤ K := by
    apply (Real.rpow_le_rpow_iff (abs_nonneg _) hK hp).mp
    exact (Finset.single_le_sum (fun j _ => Real.rpow_nonneg (abs_nonneg (v j)) p) (Finset.mem_univ i)).trans hv
  calc
    _ = ∑ i, |v i|^p * |v i|^(r-p) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Real.rpow_add' (abs_nonneg _) (by linarith : p+(r-p) ≠ 0)]
      congr 1
      ring
    _ ≤ ∑ i, |v i|^p * K^(r-p) := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) (hi i) (sub_nonneg.mpr hpr)) (Real.rpow_nonneg (abs_nonneg _) _))
    _ = (∑ i, |v i|^p) * K^(r-p) := (Finset.sum_mul ..).symm
    _ ≤ K^p * K^(r-p) := mul_le_mul_of_nonneg_right hv (Real.rpow_nonneg hK _)
    _ = K^r := by
      rw [← Real.rpow_add' hK (by linarith : p+(r-p) ≠ 0)]
      congr 1
      ring

lemma norm_mono_exponent {p r : ℝ≥0∞} (hp : 0 < p.toReal) (hpr : p.toReal ≤ r.toReal)
    (v : ι → ℝ) : ‖vec r v‖ ≤ ‖vec p v‖ := by
  apply norm_le (hp.trans_le hpr) _ _ (lp.norm_nonneg' (vec p v))
  exact sum_rpow_larger v p.toReal r.toReal _ hp hpr (lp.norm_nonneg' (vec p v)) (le_of_eq (norm_rpow hp v).symm)

lemma norm_const {p : ℝ≥0∞} (hp : 0 < p.toReal) (c : ℝ) :
    ‖vec p (fun _ : ι => c)‖ = |c| * (Fintype.card ι : ℝ)^(1/p.toReal) := by
  apply (Real.rpow_left_inj (lp.norm_nonneg' (vec p (fun _ : ι => c))) (by positivity) hp.ne').mp
  rw [norm_rpow hp, Real.mul_rpow (abs_nonneg _) (by positivity),
    ← Real.rpow_mul (Nat.cast_nonneg _), one_div_mul_cancel hp.ne', Real.rpow_one]
  simp [mul_comm]

lemma norm_le_card {p : ℝ≥0∞} (hp : 0 < p.toReal) (v : ι → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ i, |v i| ≤ K) : ‖vec p v‖ ≤ K * (Fintype.card ι : ℝ)^(1/p.toReal) := by
  have hn : p ≠ 0 := by intro hh; simp [hh] at hp
  calc
    _ ≤ ‖vec p (fun _ : ι => K)‖ := lp.norm_mono hn (fun i => by simpa [Real.norm_eq_abs, abs_of_nonneg hK] using h i)
    _ = _ := by rw [norm_const hp, abs_of_nonneg hK]

lemma norm_mask_le {p : ℝ≥0∞} (hp : p ≠ 0) (v : ι → ℝ) (s : Finset ι) :
    ‖vec p (fun i => if i ∈ s then v i else 0)‖ ≤ ‖vec p v‖ := by
  apply lp.norm_mono hp
  intro i
  by_cases hi : i ∈ s <;> simp [hi]

end SeparableQuotient.FiniteVectors

namespace SeparableQuotient.FiniteVectors
open scoped Classical ENNReal
universe u v
variable {ι : Type u} [Fintype ι] {β : Type v} [Fintype β]

lemma norm_eq_rpow {p : ℝ≥0∞} (hp : 0 < p.toReal) (v : ι → ℝ) :
    ‖vec p v‖ = (∑ i, |v i|^p.toReal)^(1/p.toReal) := by
  rw [← norm_rpow hp, ← Real.rpow_mul (lp.norm_nonneg' _), mul_one_div_cancel hp.ne', Real.rpow_one]

lemma sum_abs_le_norm (p : ℝ) (hp : 1 < p) (v : ι → ℝ) :
    ∑ i, |v i| ≤ ‖vec (ENNReal.ofReal p) v‖ * (Fintype.card ι : ℝ)^(1-1/p) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have he : 0 < 1-1/p := sub_pos.mpr ((div_lt_one hp0).mpr hp)
  have hc : Real.HolderConjugate p (1/(1-1/p)) := {
    inv_add_inv_eq_inv := by simp [one_div]
    left_pos := hp0
    right_pos := by positivity }
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ (f := fun i => |v i|)
    (g := fun _ => (1 : ℝ)) hc (fun i _ => abs_nonneg _) (fun _ _ => zero_le_one)
  simpa only [mul_one, Real.one_rpow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    one_div_one_div, norm_eq_rpow (by simpa only [ENNReal.toReal_ofReal hp0.le] using hp0 : 0 < (ENNReal.ofReal p).toReal),
    ENNReal.toReal_ofReal hp0.le] using h

/-- Eight marked entries per row imply the precise uniform marked charge,
using only the actual column Hölder bound. -/
lemma marked_norm_bound (q : ℝ) (hq : 1 < q) (r : ℝ≥0∞) (hqr : q ≤ r.toReal)
    (a : β → ℝ) (ha : ∑ b, |a b|^q ≤ 1) (marks : β → Finset ι)
    (hmarks : ∀ b, (marks b).card ≤ 8) (M : ι → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hcolumn : ∀ i, M i ≤ 2 * (∑ b, if i ∈ marks b then |a b|^q else 0)^(1/q)) :
    ‖vec r M‖ ≤ 16 ∧ ∑ i, M i ≤ 16*(Fintype.card ι : ℝ)^(1-1/q) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  let H (i : ι) : ℝ := ∑ b, if i ∈ marks b then |a b|^q else 0
  have hH (i : ι) : 0 ≤ H i := by apply Finset.sum_nonneg; intro b _; split_ifs <;> positivity
  have hHsum : ∑ i, H i ≤ 8 := by
    dsimp only [H]
    rw [Finset.sum_comm]
    calc
      _ = ∑ b, ((marks b).card : ℝ) * |a b|^q := by
        apply Finset.sum_congr rfl
        intro b _
        simp
      _ ≤ ∑ b, 8 * |a b|^q := Finset.sum_le_sum (fun b _ =>
        mul_le_mul_of_nonneg_right (by exact_mod_cast hmarks b) (Real.rpow_nonneg (abs_nonneg _) _))
      _ = 8 * ∑ b, |a b|^q := (Finset.mul_sum ..).symm
      _ ≤ 8 := by linarith
  have hpow (i : ι) : |M i|^q ≤ 2^q * H i := by
    rw [abs_of_nonneg (hM i)]
    calc
      _ ≤ (2*H i^(1/q))^q := Real.rpow_le_rpow (hM i) (hcolumn i) hq0.le
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (hH i) _),
          ← Real.rpow_mul (hH i), one_div_mul_cancel hq0.ne', Real.rpow_one]
  have hbound : ‖vec (ENNReal.ofReal q) M‖ ≤ 2*(8 : ℝ)^(1/q) := by
    apply norm_le (by simpa only [ENNReal.toReal_ofReal hq0.le] using hq0 : 0 < (ENNReal.ofReal q).toReal) _ _ (by positivity)
    rw [ENNReal.toReal_ofReal hq0.le, Real.mul_rpow (by norm_num) (by positivity),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8), one_div_mul_cancel hq0.ne', Real.rpow_one]
    exact (Finset.sum_le_sum (fun i _ => hpow i)).trans (by rw [← Finset.mul_sum]; gcongr)
  have h16 : ‖vec (ENNReal.ofReal q) M‖ ≤ 16 := by
    apply hbound.trans
    have he : 1/q ≤ 1 := (div_le_one hq0).mpr hq.le
    have hh : (8 : ℝ)^(1/q) ≤ 8 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 8) he
    linarith
  refine ⟨(norm_mono_exponent (by simpa only [ENNReal.toReal_ofReal hq0.le] using hq0 : 0 < (ENNReal.ofReal q).toReal)
    (by simpa only [ENNReal.toReal_ofReal hq0.le] using hqr) M).trans h16, ?_⟩
  simpa only [abs_of_nonneg (hM _)] using (sum_abs_le_norm q hq M).trans
    (mul_le_mul_of_nonneg_right h16 (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end SeparableQuotient.FiniteVectors

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology

noncomputable def ThinnedWindows.markedCharge {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (i : s) : ℝ :=
  ∑ b, if i.val ∈ w.marks e hm s b then |(e.coefficient b : ℝ)| *|w.middleEval e b i| else 0

lemma ThinnedWindows.markedCharge_nonneg {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (i : s) :
    0 ≤ w.markedCharge e hm s i := by
  apply Finset.sum_nonneg
  intro b _
  split_ifs <;> positivity

lemma ThinnedWindows.marked_column {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (i : s) :
    w.markedCharge e hm s i ≤
      2*(∑ b, if i.val ∈ w.marks e hm s b then |(e.coefficient b : ℝ)|^f.q else 0)^(1/f.q) := by
  let c (b : Fin e.length) : ℝ := if i.val ∈ w.marks e hm s b then e.coefficient b else 0
  have he (b : Fin e.length) : |c b| *|w.middleEval e b i| =
      if i.val ∈ w.marks e hm s b then |(e.coefficient b : ℝ)| *|w.middleEval e b i| else 0 := by
    dsimp [c]
    split_ifs <;> simp
  have hp (b : Fin e.length) : |c b|^f.q =
      if i.val ∈ w.marks e hm s b then |(e.coefficient b : ℝ)|^f.q else 0 := by
    dsimp [c]
    split_ifs
    · rfl
    · rw [abs_zero, Real.zero_rpow]
      exact ne_of_gt (show 0 < f.q from zero_lt_one.trans (Parameters.q_bounds f.s_ge_two).1)
  calc
    _ = ∑ b, |c b| *|w.middleEval e b i| := by simp only [he, markedCharge]
    _ ≤ (∑ b, |c b|^f.q)^(1/f.q)*‖w.blocks.embed i‖ :=
      TypeII.window_column_bound e hm (w.lower i) (w.upper i) c (w.blocks.embed i)
    _ ≤ (∑ b, |c b|^f.q)^(1/f.q)*2 :=
      mul_le_mul_of_nonneg_left (w.upper_norm i) (Real.rpow_nonneg (Finset.sum_nonneg (fun _ _ => by positivity)) _)
    _ = _ := by simp only [hp]; ring

lemma ThinnedWindows.marked_vector_bounds {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) :
    ‖vec f.exponent (w.markedCharge e hm s)‖ ≤ 16 ∧
      (∑ i : s, w.markedCharge e hm s i) ≤ 16*(s.card : ℝ)^(1-1/f.q) := by
  let marks (b : Fin e.length) : Finset s := (w.marks e hm s b).subtype (· ∈ s)
  have hmarks (b : Fin e.length) : (marks b).card ≤ 8 := by
    rw [show (marks b).card = ((w.marks e hm s b).filter (· ∈ s)).card by simp only [marks,Finset.card_subtype]]
    exact (Finset.card_filter_le _ _).trans (w.marks_card e hm s b)
  have hh := marked_norm_bound f.q (Parameters.q_bounds f.s_ge_two).1 f.exponent
    (by simpa only [Family.exponent_toReal,Family.q,Family.r] using (Parameters.q_bounds f.s_ge_two).2.1.le)
    (fun b => (e.coefficient b : ℝ)) e.bound marks hmarks (w.markedCharge e hm s)
    (w.markedCharge_nonneg e hm s) (fun i => by simpa only [marks,Finset.mem_subtype] using w.marked_column e hm s i)
  simpa only [Fintype.card_coe] using hh

end SeparableQuotient.ActualSpace

end

end OAI
