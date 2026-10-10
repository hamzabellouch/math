import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkRadialIBP
import OAI.Probability.Perceptron.Cavity.BulkSingleEmpiricalLimit

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators BoundedContinuousFunction Topology

lemma bulkReplicaMean_sub_bounded (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (F G : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hF : Measurable (Function.uncurry F)) (hG : Measurable (Function.uncurry G))
    (A B : ℝ) (hA : ∀ a x,|F a x|≤A) (hB : ∀ a x,|G a x|≤B) :
    bulkReplicaMean n M f v r (fun a x => F a x-G a x)=
      bulkReplicaMean n M f v r F-bulkReplicaMean n M f v r G := by
  rw [bulkReplicaMean_annealed _ _ _ _ _ _ (hF.sub hG) (A+B)
    (fun a x => (abs_sub _ _).trans (add_le_add (hA a x) (hB a x))),
    bulkReplicaMean_annealed _ _ _ _ _ _ hF A hA,
    bulkReplicaMean_annealed _ _ _ _ _ _ hG B hB]
  exact integral_sub (bulkReplicaPrefix_integrable _ _ _ _ _ F hF A hA)
    (bulkReplicaPrefix_integrable _ _ _ _ _ G hG B hB)

def bulkRadialRow (n M : ℕ) (f : Jet3) (j : Fin M) (a : BulkDisorder (n+1) M) := freshRadial (n+1) f (WithLp.toLp 2 (a.1 j))
def bulkSecondRow (n M : ℕ) (f : Jet3) (j : Fin M) (a : BulkDisorder (n+1) M) := freshSecond (n+1) f (WithLp.toLp 2 (a.1 j))
def bulkRadialPairRow (n M : ℕ) (f : Jet3) (j : Fin M) (a : BulkDisorder (n+1) M) := freshRadialPair (n+1) f (WithLp.toLp 2 (a.1 j))

lemma bulkFreshRow_measurable (n M r : ℕ) (j : Fin M) :
    Measurable (fun p : BulkDisorder (n+1) M×(Fin r→NormalizedSpin (n+1)) => (WithLp.toLp 2 (p.1.1 j),p.2)) :=
  (((PiLp.continuous_toLp 2 _).measurable.comp ((measurable_pi_apply j).comp
    (measurable_fst.comp measurable_fst))).prodMk measurable_snd)

lemma bulkRadialRow_measurable (n M : ℕ) (f : Jet3) (j : Fin M) :
    Measurable (Function.uncurry (bulkRadialRow n M f j)) :=
  (freshRadial_measurable (n+1) f).comp (bulkFreshRow_measurable n M 1 j)
lemma bulkSecondRow_measurable (n M : ℕ) (f : Jet3) (j : Fin M) :
    Measurable (Function.uncurry (bulkSecondRow n M f j)) :=
  by unfold bulkSecondRow freshSecond Function.uncurry; fun_prop
lemma bulkRadialPairRow_measurable (n M : ℕ) (f : Jet3) (j : Fin M) :
    Measurable (Function.uncurry (bulkRadialPairRow n M f j)) :=
  by unfold bulkRadialPairRow freshRadialPair spinOverlap Function.uncurry; fun_prop

def Jet3.radialMark (f : Jet3) (hf : HasCompactSupport (f.d1 : ℝ→ℝ)) : ℝ→ᵇℝ :=
  ofCompactSupport (fun z => z*f.d1 z) (continuous_id.mul f.d1.continuous) hf.mul_left

lemma bulkRadialRow_bound (n M : ℕ) (f : Jet3) (hf : HasCompactSupport (f.d1 : ℝ→ℝ))
    (j : Fin M) (a : BulkDisorder (n+1) M) (x : Fin 1→NormalizedSpin (n+1)) :
    |bulkRadialRow n M f j a x|≤‖f.radialMark hf‖ := (f.radialMark hf).norm_coe_le_norm _

lemma bulk_radial_difference (n M : ℕ) (f : Jet3) (hf : HasCompactSupport (f.d1 : ℝ→ℝ)) (v : ℕ→ℝ) (j : Fin M) :
    bulkReplicaMean n M f.f v 1 (fun a x => bulkSecondRow n M f j a x-bulkRadialRow n M f j a x)=
      bulkReplicaMean n M f.f v 2 (bulkRadialPairRow n M f j) := by
  rw [bulkReplicaMean_sub_bounded n M 1 f.f v _ _ (bulkSecondRow_measurable n M f j)
    (bulkRadialRow_measurable n M f j) (‖f.d2‖+‖f.d1‖^2) ‖f.radialMark hf‖
    (fun a x => freshSecond_bound _ _ _ _) (bulkRadialRow_bound n M f hf j)]
  have hi : bulkReplicaMean n M f.f v 1 (bulkRadialRow n M f j)=
    bulkReplicaMean n M f.f v 1 (bulkSecondRow n M f j)-bulkReplicaMean n M f.f v 2 (bulkRadialPairRow n M f j) := by
    cases M with
    | zero => exact Fin.elim0 j
    | succ M => exact bulk_radial_row_ibp n M f v j
  linarith

lemma bulk_radial_sum_eq (n M : ℕ) (f : Jet3) (a : BulkDisorder (n+1) M) (x : Fin 1→NormalizedSpin (n+1)) :
    bulkC (n+1) M f a.1 (x 0)+bulkB (n+1) M f a.1 (x 0) (x 0)=
      ((n+1:ℕ):ℝ)⁻¹*∑ j : Fin M,(bulkSecondRow n M f j a x-bulkRadialRow n M f j a x) := by
  simp only [bulkC,bulkB,bulkSecondRow,bulkRadialRow,freshSecond,freshRadial,
    EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
  rw [←mul_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma bulk_radial_pair_sum_eq (n M : ℕ) (f : Jet3) (a : BulkDisorder (n+1) M) (x : Fin 2→NormalizedSpin (n+1)) :
    spinOverlap (x 0) (x 1)*bulkB (n+1) M f a.1 (x 0) (x 1)=
      ((n+1:ℕ):ℝ)⁻¹*∑ j : Fin M,bulkRadialPairRow n M f j a x := by
  simp only [bulkB,bulkRadialPairRow,freshRadialPair,EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct,star_trivial]
  rw [mul_left_comm,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma bulk_radial_sum_identity (n M : ℕ) (f : Jet3)
    (hf : HasCompactSupport (f.d1 : ℝ→ℝ)) (v : ℕ→ℝ) :
    bulkReplicaMean n M f.f v 1 (fun a x => bulkC (n+1) M f a.1 (x 0)+
      bulkB (n+1) M f a.1 (x 0) (x 0))=
    bulkReplicaMean n M f.f v 2 (fun a x => spinOverlap (x 0) (x 1)*
      bulkB (n+1) M f a.1 (x 0) (x 1)) := by
  simp_rw [bulk_radial_sum_eq,bulk_radial_pair_sum_eq]
  rw [bulkReplicaMean_const_mul,bulkReplicaMean_const_mul]
  congr 1
  rw [bulkReplicaMean_sum n M 1 f.f v Finset.univ (fun j a x => bulkSecondRow n M f j a x-bulkRadialRow n M f j a x)
      (fun j _ => (bulkSecondRow_measurable n M f j).sub (bulkRadialRow_measurable n M f j))
      (fun _ => ‖f.d2‖+‖f.d1‖^2+‖f.radialMark hf‖)
      (fun _ _ => by positivity) (fun j _ a x => (abs_sub _ _).trans
        (add_le_add (freshSecond_bound _ _ _ _) (bulkRadialRow_bound n M f hf j a x))),
    bulkReplicaMean_sum n M 2 f.f v Finset.univ (bulkRadialPairRow n M f)
      (fun j _ => bulkRadialPairRow_measurable n M f j) (fun _ => ‖f.d1‖^2)
      (fun _ _ => by positivity) (fun j _ a x => freshRadialPair_bound _ _ _ _)]
  exact Finset.sum_congr rfl fun j _ => bulk_radial_difference n M f hf v j

lemma bulkReplicaMean_add_bounded (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (F G : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hF : Measurable (Function.uncurry F)) (hG : Measurable (Function.uncurry G))
    (A B : ℝ) (hA : ∀ a x,|F a x|≤A) (hB : ∀ a x,|G a x|≤B) :
    bulkReplicaMean n M f v r (fun a x => F a x+G a x)=
      bulkReplicaMean n M f v r F+bulkReplicaMean n M f v r G := by
  rw [bulkReplicaMean_annealed _ _ _ _ _ _ (hF.add hG) (A+B)
    (fun a x => (abs_add_le _ _).trans (add_le_add (hA a x) (hB a x))),
    bulkReplicaMean_annealed _ _ _ _ _ _ hF A hA,
    bulkReplicaMean_annealed _ _ _ _ _ _ hG B hB]
  exact integral_add (bulkReplicaPrefix_integrable _ _ _ _ _ F hF A hA)
    (bulkReplicaPrefix_integrable _ _ _ _ _ G hG B hB)

lemma bulkReplicaMean_mean_square_le (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (F : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hF : Measurable (Function.uncurry F)) (A : ℝ) (hA : 0≤A) (hb : ∀ a x,|F a x|≤A) (c : ℝ) :
    (bulkReplicaMean n M f v r F-c)^2≤
      bulkReplicaMean n M f v r (fun a x => (F a x-c)^2) := by
  rw [bulkReplicaMean_centered_square n M f v r F hF A hA hb c]
  have hme : Measurable (fun p : BulkDisorder (n+1) M×(ℕ→NormalizedSpin (n+1)) => F p.1 (fun i : Fin r=>p.2 i.val)) :=
    hF.comp (measurable_fst.prodMk (Measurable.of_eval fun coordinate =>
      (measurable_pi_apply coordinate.val).comp measurable_snd))
  have hp : MemLp (fun p => F p.1 (fun i : Fin r=>p.2 i.val)) 2 (bulkAnnealedReplicaLaw n M f v) :=
    MemLp.of_bound hme.aestronglyMeasurable A (ae_of_all _ fun p=>by simpa only [Real.norm_eq_abs] using hb p.1 (fun i=>p.2 i.val))
  have hvv := variance_nonneg (fun p => F p.1 (fun i : Fin r=>p.2 i.val)) (bulkAnnealedReplicaLaw n M f v)
  rw [variance_eq_sub hp] at hvv
  rw [bulkReplicaMean_annealed n M f v r F hF A hb,
    bulkReplicaMean_annealed n M f v r (fun a x => (F a x)^2) (hF.pow_const 2) (A^2)
      (fun a x => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb a x) 2)]
  simp only [Pi.pow_apply] at hvv
  nlinarith

lemma bulkReplicaMean_L2_tendsto (N M : ℕ→ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℕ→ℝ) (r : ℕ)
    (F : (n : ℕ)→BulkDisorder (N n+1) (M n)→(Fin r→NormalizedSpin (N n+1))→ℝ)
    (hF : ∀ n,Measurable (Function.uncurry (F n))) (A : ℕ→ℝ) (hA : ∀ n,0≤A n)
    (hb : ∀ n a x,|F n a x|≤A n) (c : ℝ)
    (hl : Tendsto (fun n=>bulkReplicaMean (N n) (M n) f (v n) r (fun a x => (F n a x-c)^2)) atTop (𝓝 0)) :
    Tendsto (fun n=>bulkReplicaMean (N n) (M n) f (v n) r (F n)) atTop (𝓝 c) := by
  have hb' n : |bulkReplicaMean (N n) (M n) f (v n) r (F n)-c|≤
      Real.sqrt (bulkReplicaMean (N n) (M n) f (v n) r (fun a x => (F n a x-c)^2)) := by
    have he := bulkReplicaMean_mean_square_le (N n) (M n) r f (v n) (F n) (hF n) (A n) (hA n) (hb n) c
    exact Real.abs_le_sqrt he
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  exact squeeze_zero (fun n=>abs_nonneg _) hb' (by simpa only [Real.sqrt_zero] using hl.sqrt)

end SphericalPerceptronFreeEnergy
end

end OAI
