import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkMarkedArray
import OAI.Probability.Perceptron.Cavity.BulkSingleLimit

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction

lemma bulkSingleAverage_first_limit (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (α c : ℝ) (w : ℝ→ᵇℝ)
    (hd : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    (ht : Tendsto (fun n => ∫ p,bulkFreshNumerator (s n) (M (s n)) 1 g.f (v (s n))
      1 (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>(1:ℝ→ᵇℝ))) p /
      bulkFreshDenominator (s n) (M (s n)) g.f (v (s n)) p^1
        ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop (𝓝 c)) :
    Tendsto (fun n => bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 1
      (bulkSingleAverage (s n) (M (s n)+2) w)) atTop (𝓝 (α*c)) := by
  simp_rw [bulkSingleAverage_first]
  exact hd.mul ht

lemma bulkSingleAverage_second_limit (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (hs : Tendsto s atTop atTop) (α c : ℝ) (w : ℝ→ᵇℝ)
    (hd : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    (ht : Tendsto (fun n => ∫ p,bulkFreshNumerator (s n) (M (s n)) 1 g.f (v (s n))
      1 (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>w)) p /
      bulkFreshDenominator (s n) (M (s n)) g.f (v (s n)) p^1
        ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop (𝓝 (c^2))) :
    Tendsto (fun n => bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 1
      (fun a x => (bulkSingleAverage (s n) (M (s n)+2) w a x)^2)) atTop (𝓝 ((α*c)^2)) := by
  have hfac := bulk_density_factors M s hs α hd
  have herr : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)^2*
      bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 1 (fun a x =>
        (singleFieldMark w (bulkPatternFields ((Fin.last (M (s n))).castSucc) a x))^2)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) (by simpa only [zero_mul] using hfac.1.mul_const (‖w‖^2))
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0≤((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)^2)]
    exact mul_le_mul_of_nonneg_left (bulkSingleAverage_diagonal_bound (s n) (M (s n)) g.f w (v (s n))) (by positivity)
  simp_rw [bulkSingleAverage_second]
  simpa only [zero_add,mul_pow] using herr.add (hfac.2.mul ht)

theorem bulk_single_empirical_limits (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (hs : Tendsto s atTop atTop) (α : ℝ)
    (hd : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect (bulkJointLaw ν) r i G a=0)
    (hgeo : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
    (w : ℝ→ᵇℝ) : ∃ c : ℝ, |c|≤‖w‖ ∧
      Tendsto (fun n => bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 1
        (bulkSingleAverage (s n) (M (s n)+2) w)) atTop (𝓝 (α*c)) ∧
      Tendsto (fun n => bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 1
        (fun a x => (bulkSingleAverage (s n) (M (s n)+2) w a x)^2)) atTop (𝓝 ((α*c)^2)) := by
  obtain ⟨c,hc,ht⟩ := bulk_single_limit_exists M g v s hlim hGG hgeo hn w
  refine ⟨c,hc,?_,?_⟩
  · apply bulkSingleAverage_first_limit M g v s α c w hd
    simpa [secondPairMark,pairMarkPower] using ht false
  · apply bulkSingleAverage_second_limit M g v s hs α c w hd
    simpa [secondPairMark,pairMarkPower] using ht true

abbrev bulkAnnealedReplicaLaw (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :=
  annealedInfiniteReplicaMeasure (bulkSpinKernel n M) (bulkDisorderLaw (n+1) M)
    (bulkGibbsHamiltonian n M f v) (bulkGibbsHamiltonian_measurable n M f v)

lemma bulkReplicaMean_annealed (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ)
    (G : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hG : Measurable (Function.uncurry G)) (C : ℝ) (hb : ∀ a x,|G a x|≤C) :
    bulkReplicaMean n M f v r G =
      ∫ p,G p.1 (fun i => p.2 i.val) ∂bulkAnnealedReplicaLaw n M f v := by
  symm
  exact annealedInfiniteReplica_marked_prefix (bulkSpinKernel n M) (bulkDisorderLaw (n+1) M)
    (bulkGibbsHamiltonian n M f v) (bulkGibbsHamiltonian_measurable n M f v)
    (ae_of_all _ (bulkHamiltonian_exp_integrable n M f v)) r hG hb

lemma bulkReplicaPrefix_integrable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ)
    (G : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hG : Measurable (Function.uncurry G)) (C : ℝ) (hb : ∀ a x,|G a x|≤C) :
    Integrable (fun p => G p.1 (fun i => p.2 i.val)) (bulkAnnealedReplicaLaw n M f v) := by
  have hm : Measurable (fun p : BulkDisorder (n+1) M×(ℕ→NormalizedSpin (n+1)) => G p.1 (fun i => p.2 i.val)) :=
    hG.comp (measurable_fst.prodMk (Measurable.of_eval fun coordinate =>
      (measurable_pi_apply coordinate.val).comp measurable_snd))
  apply Integrable.of_bound hm.aestronglyMeasurable C
  exact ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hb p.1 (fun i => p.2 i.val)

lemma bulkReplicaMean_centered_square (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ)
    (G : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hG : Measurable (Function.uncurry G)) (C : ℝ) (hC : 0≤C) (hb : ∀ a x,|G a x|≤C) (c : ℝ) :
    bulkReplicaMean n M f v r (fun a x => (G a x-c)^2)=
      bulkReplicaMean n M f v r (fun a x => (G a x)^2)-2*c*bulkReplicaMean n M f v r G+c^2 := by
  have hsq : ∀ a x,|(G a x)^2|≤C^2 := fun a x => by
    rw [abs_pow]; exact (sq_le_sq₀ (abs_nonneg _) hC).mpr (hb a x)
  have hcent : ∀ a x,|(G a x-c)^2|≤(C+|c|)^2 := fun a x => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub (G a x) c).trans (add_le_add (hb a x) le_rfl)) 2
  rw [bulkReplicaMean_annealed _ _ _ _ _ _ ((hG.sub_const c).pow_const 2) _ hcent,
    bulkReplicaMean_annealed _ _ _ _ _ _ (hG.pow_const 2) _ hsq,
    bulkReplicaMean_annealed _ _ _ _ _ _ hG _ hb]
  have hg := bulkReplicaPrefix_integrable n M f v r G hG C hb
  have hg2 := bulkReplicaPrefix_integrable n M f v r (fun a x => (G a x)^2) (hG.pow_const 2) (C^2) hsq
  simp_rw [sub_sq]
  have h₁ : Integrable (fun p => (G p.1 (fun i => p.2 i.val))^2-2*G p.1 (fun i => p.2 i.val)*c)
      (bulkAnnealedReplicaLaw n M f v) := hg2.sub ((hg.const_mul 2).mul_const c)
  have h₂ : Integrable (fun p => 2*G p.1 (fun i => p.2 i.val)*c)
      (bulkAnnealedReplicaLaw n M f v) := (hg.const_mul 2).mul_const c
  rw [integral_add h₁ (integrable_const (μ:=bulkAnnealedReplicaLaw n M f v) (c^2)),
    integral_sub hg2 h₂,integral_mul_const,integral_const_mul]
  simp
  ring

def Jet3.dilationMark (g : Jet3) (hg : HasCompactSupport (g.d1 : ℝ→ℝ)) : ℝ→ᵇℝ :=
  g.d2-ofCompactSupport (fun z => z*g.d1 z)
    (continuous_id.mul g.d1.continuous) hg.mul_left

@[simp] lemma Jet3.dilationMark_apply (g : Jet3) (hg : HasCompactSupport (g.d1 : ℝ→ℝ)) (z : ℝ) :
    g.dilationMark hg z=g.d2 z-z*g.d1 z := rfl

lemma bulkC_singleAverage (n M : ℕ) (g : Jet3) (hg : HasCompactSupport (g.d1 : ℝ→ℝ))
    (a : BulkDisorder (n+1) M) (x : Fin 1→NormalizedSpin (n+1)) :
    bulkC (n+1) M g a.1 (x 0)=bulkSingleAverage n M (g.dilationMark hg) a x := by
  rfl

lemma bulkB_diagonal_singleAverage (n M : ℕ) (g : Jet3)
    (a : BulkDisorder (n+1) M) (x : Fin 1→NormalizedSpin (n+1)) :
    bulkB (n+1) M g a.1 (x 0) (x 0)=bulkSingleAverage n M (g.d1*g.d1) a x := by
  rfl

theorem bulk_single_L2_concentration (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (hs : Tendsto s atTop atTop) (α : ℝ)
    (hd : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect (bulkJointLaw ν) r i G a=0)
    (hgeo : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
    (w : ℝ→ᵇℝ) : ∃ c : ℝ, |c|≤‖w‖ ∧
      Tendsto (fun n => bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 1
        (fun a x => (bulkSingleAverage (s n) (M (s n)+2) w a x-α*c)^2)) atTop (𝓝 0) := by
  obtain ⟨c,hc,h1,h2⟩ := bulk_single_empirical_limits M g v s hs α hd hlim hGG hgeo hn w
  refine ⟨c,hc,?_⟩
  have he n := bulkReplicaMean_centered_square (s n) (M (s n)+2) g.f (v (s n)) 1
    (bulkSingleAverage (s n) (M (s n)+2) w) (bulkSingleAverage_measurable _ _ _) _
    (by positivity : 0≤((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)*‖w‖)
    (bulkSingleAverage_bound _ _ _) (α*c)
  simp_rw [he]
  convert (h2.sub (h1.const_mul (2*(α*c)))).add_const ((α*c)^2) using 1
  ring_nf

theorem bulk_diagonal_C_concentration (M : ℕ→ℕ) (g : Jet3)
    (hg : HasCompactSupport (g.d1 : ℝ→ℝ)) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (hs : Tendsto s atTop atTop) (α : ℝ)
    (hd : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect (bulkJointLaw ν) r i G a=0)
    (hgeo : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val) :
    (∃ d : ℝ, |d|≤|α| * ‖g.d1‖^2 ∧
      Tendsto (fun n => bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 1
        (fun a x => (bulkB (s n+1) (M (s n)+2) g a.1 (x 0) (x 0)-d)^2)) atTop (𝓝 0)) ∧
    (∃ c : ℝ, |c|≤|α| * ‖g.dilationMark hg‖ ∧
      Tendsto (fun n => bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 1
        (fun a x => (bulkC (s n+1) (M (s n)+2) g a.1 (x 0)-c)^2)) atTop (𝓝 0)) := by
  constructor
  · obtain ⟨c,hc,ht⟩ := bulk_single_L2_concentration M g v s hs α hd hlim hGG hgeo hn (g.d1*g.d1)
    refine ⟨α*c,?_,?_⟩
    · rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hc.trans (norm_mul_le _ _)) (abs_nonneg α)).trans_eq (by ring)
    · exact ht
  · obtain ⟨c,hc,ht⟩ := bulk_single_L2_concentration M g v s hs α hd hlim hGG hgeo hn (g.dilationMark hg)
    refine ⟨α*c,?_,?_⟩
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left hc (abs_nonneg α)
    · exact ht

end SphericalPerceptronFreeEnergy
end

end OAI
