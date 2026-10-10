import Mathlib
import OAI.Probability.Perceptron.Variational.FiniteFieldModel

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

structure BoundedField (H : ℝ) where
  toFun : Time → ℝ
  monotone : Monotone toFun
  nonneg : ∀ u, 0 ≤ toFun u
  le_bound : ∀ u, toFun u ≤ H

instance {H : ℝ} : CoeFun (BoundedField H) (fun _ => Time → ℝ) := ⟨BoundedField.toFun⟩

lemma BoundedField.measurable {H : ℝ} (f : BoundedField H) : Measurable f := f.monotone.measurable

lemma BoundedField.bound_nonneg {H : ℝ} (f : BoundedField H) : 0 ≤ H := (f.nonneg 0).trans (f.le_bound 0)

lemma BoundedField.integrable {H : ℝ} (f : BoundedField H) : Integrable f timeLaw := by
  apply Integrable.mono' (integrable_const H) f.measurable.aestronglyMeasurable
  exact ae_of_all _ (fun u => by simpa only [Real.norm_eq_abs,abs_of_nonneg (f.nonneg u)] using f.le_bound u)

def roundLower (N : ℕ) (x : ℝ) : ℝ := (⌊(N+1:ℕ)*x⌋₊:ℝ)/(N+1:ℕ)

lemma roundLower_nonneg (N : ℕ) (x : ℝ) : 0 ≤ roundLower N x := by unfold roundLower; positivity

lemma roundLower_monotone (N : ℕ) : Monotone (roundLower N) := by
  intro x y hxy
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.floor_mono (mul_le_mul_of_nonneg_left hxy (by positivity))

lemma roundLower_le (N : ℕ) {x : ℝ} (hx : 0 ≤ x) : roundLower N x ≤ x := by
  unfold roundLower
  rw [div_le_iff₀ (by positivity : (0:ℝ)<(N+1:ℕ))]
  simpa only [mul_comm] using Nat.floor_le (mul_nonneg (by positivity) hx)

lemma sub_roundLower_lt (N : ℕ) {x : ℝ} (_hx : 0 ≤ x) : x-roundLower N x < 1/(N+1:ℕ) := by
  have h := Nat.lt_floor_add_one ((N+1:ℕ)*x)
  unfold roundLower
  rw [sub_lt_iff_lt_add,← add_div,lt_div_iff₀ (by positivity : (0:ℝ)<(N+1:ℕ))]
  simpa only [mul_comm,add_comm] using h

lemma roundLower_measurable (N : ℕ) : Measurable (roundLower N) := (roundLower_monotone N).measurable

def BoundedField.round {H : ℝ} (f : BoundedField H) (N : ℕ) : BoundedField H where
  toFun := fun u => roundLower N (f u)
  monotone := (roundLower_monotone N).comp f.monotone
  nonneg := fun u => roundLower_nonneg N (f u)
  le_bound := fun u => (roundLower_le N (f.nonneg u)).trans (f.le_bound u)

lemma BoundedField.round_error {H : ℝ} (f : BoundedField H) (N : ℕ) (u : Time) :
    |f.round N u-f u| ≤ 1/(N+1:ℕ) := by
  change |roundLower N (f u)-f u| ≤ _
  rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (roundLower_le N (f.nonneg u)))]
  exact (sub_roundLower_lt N (f.nonneg u)).le

lemma BoundedField.round_finite {H : ℝ} (f : BoundedField H) (N : ℕ) :
    (Set.range (f.round N)).Finite := by
  let T := (Finset.range (⌊(N+1:ℕ)*H⌋₊+1)).image (fun k : ℕ => (k:ℝ)/(N+1:ℕ))
  apply T.finite_toSet.subset
  rintro x ⟨u,rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨⌊(N+1:ℕ)*f u⌋₊,?_,rfl⟩
  apply Finset.mem_range.mpr
  exact Nat.lt_succ_of_le (Nat.floor_mono (mul_le_mul_of_nonneg_left (f.le_bound u) (by positivity)))

def BoundedField.roundModel {H : ℝ} (f : BoundedField H) (N : ℕ) : FiniteFieldModel (f.round N) :=
  Classical.choice (exists_finiteFieldModel _ (f.round N).measurable (f.round_finite N))

lemma BoundedField.round_abs_integral {H : ℝ} (f : BoundedField H) (N : ℕ) :
    (∫ u, |f.round N u-f u| ∂timeLaw) ≤ 1/(N+1:ℕ) := by
  have h := integral_mono ((f.round N).integrable.sub f.integrable).abs
    (integrable_const (1/(N+1:ℕ):ℝ)) (f.round_error N)
  simpa using h


def quantileTrial (q : Time → Time) : Trial where
  toFun := fun t => timeLaw.real {u | q u ≤ t}
  monotone := by
    intro s t hst
    exact measureReal_mono (fun u hu => hu.trans hst)
  measurable := by
    apply Monotone.measurable
    intro s t hst
    exact measureReal_mono (fun u hu => hu.trans hst)
  nonneg := fun _ => measureReal_nonneg
  le_one := by
    intro t
    simp

def quantileTail (q : Time → Time) (t : ℝ) : ℝ :=
  ∫ u, 1-max (q u:ℝ) t ∂timeLaw

lemma quantileTrial_eq_integral (q : Time → Time) (hq : Measurable q) (t : Time) :
    quantileTrial q t=∫ u, (if q u ≤ t then (1:ℝ) else 0) ∂timeLaw := by
  change timeLaw.real {u | q u ≤ t}=∫ u, {u | q u ≤ t}.indicator (fun _ => (1:ℝ)) u ∂timeLaw
  rw [integral_indicator (measurableSet_le hq measurable_const),integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one]

lemma tailIntegral_quantileTrial (q : Time → Time) (hq : Measurable q) (t : Time) :
    tailIntegral (quantileTrial q) t=quantileTail q (t:ℝ) := by
  have hm : Measurable (fun p : Time×Time => if q p.2 ≤ p.1 then (1:ℝ) else 0) :=
    measurable_const.ite (measurableSet_le (hq.comp measurable_snd) measurable_fst) measurable_const
  have hi : Integrable (fun p : Time×Time => if q p.2 ≤ p.1 then (1:ℝ) else 0)
      ((timeLaw.restrict (Ici t)).prod timeLaw) := by
    apply Integrable.mono' (integrable_const (1:ℝ)) hm.aestronglyMeasurable
    exact ae_of_all _ fun p => by split_ifs <;> norm_num
  unfold tailIntegral
  simp_rw [quantileTrial_eq_integral q hq]
  rw [integral_integral_swap hi]
  simp_rw [timeTail_atom_integral (q _) t 1,one_mul]
  rfl

lemma quantileTail_integrable (q : Time → Time) (hq : Measurable q) (t : ℝ) :
    Integrable (fun u => 1-max (q u:ℝ) t) timeLaw := by
  have hm : Measurable (fun u => 1-max (q u:ℝ) t) :=
    measurable_const.sub ((measurable_subtype_coe.comp hq).max measurable_const)
  apply Integrable.mono' (integrable_const (2+|t|)) hm.aestronglyMeasurable
  exact ae_of_all _ fun u => by
    rw [Real.norm_eq_abs]
    have hq0 := (q u).2.1
    have hq1 := (q u).2.2
    have ha : |max (q u:ℝ) t| ≤ 1+|t| := by
      rcases le_total (q u:ℝ) t with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h,abs_of_nonneg hq0]; nlinarith [abs_nonneg t]
    have hb := abs_sub 1 (max (q u:ℝ) t)
    norm_num at hb
    linarith

lemma quantileTail_lower (q : Time → Time) (hq : Measurable q) {B t : ℝ}
    (hb : ∀ᵐ u ∂timeLaw, (q u:ℝ) ≤ B) (ht : t ≤ B) :
    1-B ≤ quantileTail q t := by
  have h := integral_mono_ae (integrable_const (1-B)) (quantileTail_integrable q hq t)
    (hb.mono fun u hu => sub_le_sub_left (max_le hu ht) 1)
  simpa [quantileTail] using h

lemma quantileTail_upper (q : Time → Time) (hq : Measurable q) (t : ℝ) :
    quantileTail q t ≤ 1-t := by
  have h := integral_mono (quantileTail_integrable q hq t) (integrable_const (1-t))
    (fun u => sub_le_sub_left (le_max_right (q u:ℝ) t) 1)
  simpa [quantileTail] using h

lemma quantileTail_of_le (q : Time → Time) {t : ℝ} (ht : ∀ᵐ u ∂timeLaw, (q u:ℝ) ≤ t) :
    quantileTail q t=1-t := by
  unfold quantileTail
  calc
    _ = ∫ _ : Time, (1-t) ∂timeLaw := integral_congr_ae (ht.mono fun u hu => by rw [max_eq_right hu])
    _ = _ := by simp

lemma quantileTail_lipschitz (q : Time → Time) (hq : Measurable q) :
    LipschitzWith 1 (quantileTail q) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [Real.dist_eq,Real.dist_eq,NNReal.coe_one,one_mul]
  unfold quantileTail
  rw [← integral_sub (quantileTail_integrable q hq s) (quantileTail_integrable q hq t)]
  calc
    _ ≤ ∫ u, |(1-max (q u:ℝ) s)-(1-max (q u:ℝ) t)| ∂timeLaw := abs_integral_le_integral_abs
    _ ≤ ∫ _ : Time, |s-t| ∂timeLaw := by
      apply integral_mono ((quantileTail_integrable q hq s).sub (quantileTail_integrable q hq t)).abs (integrable_const _)
      intro u
      have h := (LipschitzWith.id.const_max (q u:ℝ)).dist_le_mul s t
      simp only [Real.dist_eq,NNReal.coe_one,one_mul] at h
      change |(1-max (q u:ℝ) s)-(1-max (q u:ℝ) t)| ≤ _
      rw [show (1-max (q u:ℝ) s)-(1-max (q u:ℝ) t)=max (q u:ℝ) t-max (q u:ℝ) s by ring,abs_sub_comm]
      exact h
    _ = _ := by simp

end SphericalPerceptronFreeEnergy
end

end OAI
