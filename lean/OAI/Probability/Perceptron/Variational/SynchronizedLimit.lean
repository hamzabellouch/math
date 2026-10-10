import Mathlib
import OAI.Probability.Perceptron.Interpolation.ArrayLimitGeometry
import OAI.Probability.Perceptron.Variational.LabelResponse
import OAI.Probability.Perceptron.Variational.CompactGGDensity
import OAI.Probability.Perceptron.Variational.CompactGGEvents

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

section

lemma source_contact_limit_exchangeable (k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : (n : ℕ) → Fin (n+1) → ℕ) (h : ℕ → Fin (k+1) → ℝ)
    (u : (n : ℕ) → Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℕ → ℝ≥0)
    (s : ℕ→ℕ) {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) (e : Equiv.Perm ℕ) :
    MeasurePreserving (compactRelabel (K:=CompactJointOverlap) e) (ν : Measure _) (ν : Measure _) :=
  compact_exchangeability_limit hlim e (fun n => sourceGibbsArray_exchangeable
    (s n) k f (p (s n)) (d (s n)) (h (s n)) (u (s n)) z (t (s n)) e)

variable (k : ℕ) (f : ℝ →ᵇ ℝ) (p d : ℕ → ℕ) (z : Fin k → ℝ)
variable (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
variable (t : ℕ → ℝ≥0) (h : ℕ → Fin (k+1) → ℝ)
variable (hh0 : ∀ n l, 0≤h n l) (hh : ∀ n, Monotone (h n))
variable (u : (n : ℕ) → Fin (n+1) → ℝ)
variable (hu : ∀ n, u n ∈ Icc (fun _ => 1) (fun _ => 2))
variable (hmin : ∀ n, IsMinOn (fun v => quadraticBoxPenalty (sourcePenaltyWeight (n+1)) v-
  sourceExpectedPressure n k f (fun j => p j.val) (fun j => d j.val) (h n) z (t n) v)
  (Icc (fun _ : Fin (n+1) => 1) (fun _ => 2)) (u n))
variable {H T : ℝ} (hH : 0≤H) (hhH : ∀ n, h n 0≤H) (ht : ∀ n, (t n:ℝ)≤T)
variable (hcover : ∀ a b : ℕ, 1≤a+b → ∃ j, p j=a ∧ d j=b)

include hz hz0 hz1 hh0 hh hu hmin hH hhH ht hcover
lemma source_contact_limit_no_crossing {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    {s : ℕ → ℕ} (hs : StrictMono s)
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f
      (fun a => p a.val) (fun a => d a.val) (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    ∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _),
      ¬ ((Q 0 1).1.val < (Q 0 2).1.val ∧ (Q 0 2).2.val < (Q 0 1).2.val) := by
  obtain ⟨hR,hT⟩ := sourceGibbsArray_limit_gram k f (fun _ a => p a.val)
    (fun _ a => d a.val) h u z t s hlim
  exact compact_gg_no_crossing ν
    (source_contact_limit_exchangeable k f (fun _ a => p a.val) (fun _ a => d a.val) h u z t s hlim)
    (source_contact_limit_joint_gg k f p d z hz hz0 hz1 t h hh0 hh u hu hmin hH hhH ht hs hlim hcover)
    hR hT

lemma source_contact_synchronized_subsequence :
    ∃ (ν : ProbabilityMeasure (CompactArray CompactJointOverlap)) (s : ℕ → ℕ),
      StrictMono s ∧
      Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (fun a => p a.val) (fun a => d a.val)
        (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν) ∧
      JointGhirlandaGuerra (compactRealLaw ν) ∧
      PairedSwapInvariant (compactRealLaw ν) ∧
      (∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _),
        ¬ ((Q 0 1).1.val < (Q 0 2).1.val ∧ (Q 0 2).2.val < (Q 0 1).2.val)) := by
  obtain ⟨ν,s,hs,hlim⟩ := compact_array_law_subsequence (fun n => sourceGibbsArrayLaw n k f
    (fun a => p a.val) (fun a => d a.val) (h n) (u n) z (t n))
  refine ⟨ν,s,hs,hlim,?_,?_,?_⟩
  · exact compactRealLaw_gg ν (source_contact_limit_joint_gg k f p d z hz hz0 hz1 t h
      hh0 hh u hu hmin hH hhH ht hs hlim hcover)
  · exact compactRealLaw_exchangeable ν (source_contact_limit_exchangeable k f
      (fun _ a => p a.val) (fun _ a => d a.val) h u z t s hlim)
  · exact source_contact_limit_no_crossing k f p d z hz hz0 hz1 t h hh0 hh u hu hmin hH hhH ht hcover hs hlim

end

lemma sourceGibbsArray_label_moment (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (h w : Fin (k+1)→ℝ)
    (hh0 : ∀ l, 0≤h l) (hh : Monotone h) (hw : ∀ l, 0<w l) (hw1 : ∑ l, w l=1)
    (u : Fin (n+1)→ℝ) (j : Fin (n+1)) (hp : p j=0) (hu : u j≠0) (t : ℝ≥0) :
    (∫ Q : CompactArray CompactJointOverlap, ((Q 1 0).2.val)^(d j) ∂sourceGibbsArrayLaw n k f p d h u (stepCumulative w) t)=
      ∑ l, w l*((l.val:ℝ)/(k+1:ℕ))^(d j) := by
  let F : CompactBlock CompactJointOverlap 2→ℝ := fun Q => ((Q 1 0).2.val)^(d j)
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hB : ∀ Q, |F Q|≤1 := by
    intro Q
    dsimp [F]
    rw [abs_pow,abs_of_nonneg (Q 1 0).2.property.1]
    exact pow_le_one₀ (Q 1 0).2.property.1 (Q 1 0).2.property.2
  have he := sourceGibbsArray_block_integral n k f p d h hh0 hh u (stepCumulative w) t 2 hF hB
  change (∫ Q : CompactArray CompactJointOverlap, ((Q 1 0).2.val)^(d j) ∂sourceGibbsArrayLaw n k f p d h u (stepCumulative w) t)=_ at he
  rw [he]
  exact source_label_moment n k f p d h w hh0 hh hw hw1 u j hp hu t

lemma source_array_limit_label_moments (k : ℕ) (f : ℝ →ᵇ ℝ) (p d : ℕ→ℕ)
    (w : Fin (k+1)→ℝ) (hw : ∀ l, 0<w l) (hw1 : ∑ l, w l=1)
    (h : ℕ→Fin (k+1)→ℝ) (hh0 : ∀ n l, 0≤h n l) (hh : ∀ n, Monotone (h n))
    (u : (n : ℕ)→Fin (n+1)→ℝ) (hu : ∀ n j, u n j≠0) (t : ℕ→ℝ≥0)
    (hcover : ∀ b : ℕ, 0<b → ∃ j, p j=0 ∧ d j=b)
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ→ℕ} (hs : StrictMono s)
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (fun j => p j.val)
      (fun j => d j.val) (h (s n)) (u (s n)) (stepCumulative w) (t (s n))) atTop (𝓝 ν))
    (b : ℕ) : (∫ Q : CompactArray CompactJointOverlap, ((Q 1 0).2.val)^b ∂ν)=∑ l, w l*((l.val:ℝ)/(k+1:ℕ))^b := by
  by_cases hb : b=0
  · subst b
    simp [hw1]
  obtain ⟨j,hp,hd⟩ := hcover b (Nat.pos_of_ne_zero hb)
  let F : CompactArray CompactJointOverlap →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun Q => ((Q 1 0).2.val)^b,by fun_prop⟩
  have hI := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction F).tendsto ν |>.comp hlim
  have hconst : ∀ᶠ n in atTop, (∫ Q : CompactArray CompactJointOverlap, F Q ∂sourceGibbsArrayLaw (s n) k f (fun j => p j.val)
      (fun j => d j.val) (h (s n)) (u (s n)) (stepCumulative w) (t (s n)))=
        ∑ l, w l*((l.val:ℝ)/(k+1:ℕ))^b := by
    filter_upwards [eventually_ge_atTop j] with n hn
    have hn' : j<s n+1 := by have hsn : n ≤ s n := hs.le_apply; omega
    simpa only [F,BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk,hd] using
      sourceGibbsArray_label_moment (s n) k f (fun a => p a.val) (fun a => d a.val)
        (h (s n)) w (hh0 (s n)) (hh (s n)) hw hw1 (u (s n)) ⟨j,hn'⟩ hp (hu _ _) (t (s n))
  exact tendsto_nhds_unique hI (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hconst))

def sourceLabelLevel (k : ℕ) (l : Fin (k+1)) : unitInterval :=
  ⟨(l.val:ℝ)/(k+1:ℕ),by constructor; positivity; exact (div_le_one (by positivity)).mpr (by exact_mod_cast l.isLt.le)⟩

def sourceLabelLaw (k : ℕ) (w : Fin (k+1)→ℝ) : Measure unitInterval :=
  ∑ l, ENNReal.ofReal (w l) • Measure.dirac (sourceLabelLevel k l)

lemma sourceLabelLaw_probability (k : ℕ) (w : Fin (k+1)→ℝ)
    (hw : ∀ l, 0≤w l) (hw1 : ∑ l, w l=1) : IsProbabilityMeasure (sourceLabelLaw k w) := by
  constructor
  simp only [sourceLabelLaw,Measure.finsetSum_apply,Measure.smul_apply,Measure.dirac_apply_of_mem
    (mem_univ _),smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun l _ => hw l),hw1,ENNReal.ofReal_one]

lemma sourceLabelLaw_integral (k : ℕ) (w : Fin (k+1)→ℝ) (hw : ∀ l, 0≤w l)
    (g : unitInterval→ℝ) (hg : Measurable g) :
    (∫ x, g x ∂sourceLabelLaw k w)=∑ l, w l*g (sourceLabelLevel k l) := by
  unfold sourceLabelLaw
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure,integral_dirac' g _ hg.stronglyMeasurable,
      ENNReal.toReal_ofReal (hw _),smul_eq_mul]
  · intro l _
    exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

lemma source_label_law_of_moments (k : ℕ) (w : Fin (k+1)→ℝ)
    (hw : ∀ l, 0≤w l) (hw1 : ∑ l, w l=1)
    (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hm : ∀ b : ℕ, (∫ Q : CompactArray CompactJointOverlap, ((Q 1 0).2.val)^b ∂ν)=
      ∑ l, w l*((l.val:ℝ)/(k+1:ℕ))^b) :
    (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 1 0).2)=sourceLabelLaw k w := by
  let := sourceLabelLaw_probability k w hw hw1
  have hmeas : Measurable (fun Q : CompactArray CompactJointOverlap => (Q 1 0).2) := by fun_prop
  let m (b : ℕ) : unitInterval →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x : unitInterval => x.val^b,by fun_prop⟩
  apply measure_eq_of_additive_test_family m
  · ext x; simp [m]
  · intro a b; ext x; simp [m,pow_add]
  · intro x y hxy
    refine ⟨1,?_⟩
    simpa only [m,BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk,pow_one,
      ne_eq,Subtype.val_inj] using hxy
  · intro b
    rw [integral_map hmeas.aemeasurable (m b).continuous.aestronglyMeasurable,
      sourceLabelLaw_integral k w hw (m b) (m b).measurable]
    exact hm b

theorem source_array_limit_label_law (k : ℕ) (f : ℝ →ᵇ ℝ) (p d : ℕ→ℕ)
    (w : Fin (k+1)→ℝ) (hw : ∀ l, 0<w l) (hw1 : ∑ l, w l=1)
    (h : ℕ→Fin (k+1)→ℝ) (hh0 : ∀ n l, 0≤h n l) (hh : ∀ n, Monotone (h n))
    (u : (n : ℕ)→Fin (n+1)→ℝ) (hu : ∀ n j, u n j≠0) (t : ℕ→ℝ≥0)
    (hcover : ∀ b : ℕ, 0<b → ∃ j, p j=0 ∧ d j=b)
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ→ℕ} (hs : StrictMono s)
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (fun j => p j.val)
      (fun j => d j.val) (h (s n)) (u (s n)) (stepCumulative w) (t (s n))) atTop (𝓝 ν)) :
    (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 1 0).2)=sourceLabelLaw k w := by
  apply source_label_law_of_moments k w (fun l => (hw l).le) hw1 ν
  exact source_array_limit_label_moments k f p d w hw hw1 h hh0 hh u hu t hcover hs hlim

end SphericalPerceptronFreeEnergy

end

end OAI
