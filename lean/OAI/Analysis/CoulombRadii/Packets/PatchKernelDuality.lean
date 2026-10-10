import Mathlib
import OAI.Analysis.CoulombRadii.Packets.MasterKernelDuality
import OAI.Analysis.CoulombRadii.ThomasFermi.PatchNegativeCost

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
namespace Coulomb

theorem master_kernel_patch_gap (g : 𝓢(NeutralAtom.Position,ℝ))
    (hg : ∀ z, 1<‖z‖ → g z=0) (hm : (∫ z, g z^2)=1) :
    ∃ C : ℝ, 0<C ∧ ∀ {c r₀ s : ℝ}, 0<c → 0<r₀ → 0<s →
    c*(1+NeutralAtom.packetExponent)*s^NeutralAtom.packetExponent≤1/4 →
    ∀ {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
      {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
      (hn : ∀ j, 20*a≤‖S.position j-y‖),
    4*NeutralAtom.packetWidth c r₀ s y<t-4*b →
    ∀ (spin : Spins m) (x : Configuration m),
      (∫ z, (retainedFineDensity b (patchRetained y t b x) (position x) z-
        localTFDensity measurableSet_ball (coreTFField S (u.coreSlice spin x).normalized
          measurableSet_ball ha (patch_nucleus_separation S ha hb ht y hn)) z)*
            NeutralAtom.packetKernel g c r₀ s z y)^2≤
      (C/(NeutralAtom.packetWidth c r₀ s y)^5)*patchSliceTFGap S u ha hb ht y hn spin x := by
  obtain ⟨C,hC,H⟩ := NeutralAtom.master_kernel_coulomb_duality g hg hm
  refine ⟨2*C,by positivity,?_⟩
  intro c r₀ s hc hr hs hq J m k S u a b t ha hb ht y hn hball spin x
  let Ω := Metric.ball y (t-4*b)
  let W := coreTFField S (u.coreSlice spin x).normalized measurableSet_ball ha
    (patch_nucleus_separation S ha hb ht y hn)
  let ρ := localTFDensity measurableSet_ball W
  let σ := retainedFineDensity b (patchRetained y t b x) (position x)
  have hσ : MemLp σ TFExponent (volume.restrict Ω) := retainedFineDensity_memLp hb _ _
  have hρ : MemLp ρ TFExponent volume := tfDensity_memLp measurableSet_ball
    (localTFMinimizer_nonneg measurableSet_ball W)
  have hσs : ∀ z∉Ω, σ z=0 := retainedFineDensity_patch_support hb y t x
  have hρs : ∀ z∉Ω, ρ z=0 := fun z hz => tfDensity_eq_zero _ hz
  have hd := hσ.sub (hρ.restrict (s := Ω))
  have hds : ∀ z∉Ω, σ z-ρ z=0 := fun z hz => by rw [hσs z hz,hρs z hz,sub_self]
  have HH := H hc hr hs hq y measurableSet_ball (fun z => σ z-ρ z) hd hds
    (fun z hz => show z∈Ω from (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt hball)))
  have Hgap := rawTF_gap_coulomb measurableSet_ball
    (coreScreenedField S (u.coreSlice spin x).normalized) W
    (coreTFField_coe S _ measurableSet_ball ha (patch_nucleus_separation S ha hb ht y hn)) hσ
    (Eventually.of_forall (fun z => retainedFineDensity_nonneg b _ _ z)) hσs
  have Hmul := mul_le_mul_of_nonneg_left Hgap
    (show 0≤C/(NeutralAtom.packetWidth c r₀ s y)^5 by
      have hw := NeutralAtom.packetWidth_pos hc hr hs y
      positivity)
  apply HH.trans
  convert Hmul using 1
  dsimp only [σ,ρ,W,patchSliceTFGap]
  ring

end Coulomb

namespace NeutralAtom

theorem kernel_sum_matching {n : ℕ} (K : Position → ℝ) (y : Position)
    {R A d : ℝ} (hA : 0 ≤ A) (hd : 0 ≤ d)
    (hs : ∀ z, R < ‖z-y‖ → K z=0)
    (hL : ∀ z v, |K z-K v| ≤ A*‖z-v‖)
    (x v : Configuration n) (hv : ∀ i, ‖x i-v i‖ ≤ d) :
    |(∑ i, K (x i))-(∑ i, K (v i))| ≤
      (A*d)*rawCount (Metric.closedBall y (R+d)) v := by
  rw [←Finset.sum_sub_distrib,rawCount,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : v i ∈ Metric.closedBall y (R+d)
  · rw [indicator_of_mem hi,mul_one]
    exact (hL _ _).trans (mul_le_mul_of_nonneg_left (hv i) hA)
  · rw [indicator_of_notMem hi,mul_zero]
    have hvi : R+d < ‖v i-y‖ := by
      simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hi
    have hxi : R < ‖x i-y‖ := by
      have htri := norm_sub_le_norm_sub_add_norm_sub (v i) (x i) y
      rw [norm_sub_rev (v i) (x i)] at htri
      linarith [hv i]
    rw [hs _ hxi,hs _ (by linarith),sub_self,abs_zero]

theorem kernel_sum_matching_permuted {n : ℕ} (K : Position → ℝ) (y : Position)
    {R A d : ℝ} (hA : 0 ≤ A) (hd : 0 ≤ d)
    (hs : ∀ z, R < ‖z-y‖ → K z=0)
    (hL : ∀ z v, |K z-K v| ≤ A*‖z-v‖)
    (x v : Configuration n) (p : Equiv.Perm (Fin n))
    (hv : ∀ i, ‖x (p i)-v i‖ ≤ d) :
    |(∑ i, K (x i))-(∑ i, K (v i))| ≤
      (A*d)*rawCount (Metric.closedBall y (R+d)) v := by
  have hh := kernel_sum_matching K y hA hd hs hL (x ∘ p) v hv
  have he := Equiv.sum_comp p (fun i => K (x i))
  simp only [Function.comp_apply] at hh
  rw [he] at hh
  exact hh

theorem master_kernel_matching (g : 𝓢(Position,ℝ))
    (hg : ∀ x, 1 < ‖x‖ → g x=0) (hm : (∫ x, g x^2)=1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {c r₀ s : ℝ}, 0<c → 0<r₀ → 0<s →
    c*(1+packetExponent)*s^packetExponent ≤ 1/4 →
    ∀ {n : ℕ} (y : Position) {d : ℝ}, 0≤d →
    ∀ (x v : Configuration n) (p : Equiv.Perm (Fin n)),
    (∀ i, ‖x (p i)-v i‖ ≤ d) →
    |(∑ i, packetKernel g c r₀ s (x i) y)-
      (∑ i, packetKernel g c r₀ s (v i) y)| ≤
      (C/(packetWidth c r₀ s y)^4*d)*
        rawCount (Metric.closedBall y (2*packetWidth c r₀ s y+d)) v := by
  obtain ⟨C,hC,hK⟩ := master_kernel_estimates g hg hm
  refine ⟨C,hC,?_⟩
  intro c r₀ s hc hr hs hq n y d hd x v p hp
  obtain ⟨hsp,ham,hL,hi,hma⟩ := hK hc hr hs hq y
  apply kernel_sum_matching_permuted _ y (by positivity) hd ?_ hL x v p hp
  intro z hz
  by_contra hn
  have hh := hsp z hn
  rw [norm_sub_rev] at hh
  linarith

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
namespace Coulomb

lemma fineKernel_test_integrable {b B : ℝ} (hb : 0<b) (K : Space → ℝ)
    (hKm : Measurable K) (hB : ∀ z, |K z|≤B) (w : Space) :
    Integrable (fun z => fineKernel b (z-w)*K z) :=
  (fineKernel_shift_integrable hb w).mul_bdd hKm.aestronglyMeasurable
    (Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hB z))

lemma fineKernel_test_matching {b A B : ℝ} (hb : 0<b) (hA : 0≤A)
    (K : Space → ℝ) (hKm : Measurable K) (hB : ∀ z, |K z|≤B)
    (hL : ∀ z v, |K z-K v|≤A*‖z-v‖) (w : Space) :
    |(∫ z, fineKernel b (z-w)*K z)-K w|≤A*(2*b) := by
  have hi := fineKernel_test_integrable hb K hKm hB w
  have hc := (fineKernel_shift_integrable hb w).mul_const (K w)
  have he : (∫ z, fineKernel b (z-w)*K z)-K w =
      ∫ z, fineKernel b (z-w)*(K z-K w) := by
    rw [show (fun z => fineKernel b (z-w)*(K z-K w))=
      (fun z => fineKernel b (z-w)*K z-fineKernel b (z-w)*K w) by funext z; ring,
      integral_sub hi hc,integral_mul_const,fineKernel_shift_integral hb,one_mul]
  rw [he]
  calc
    _≤∫ z, |fineKernel b (z-w)*(K z-K w)| := abs_integral_le_integral_abs
    _≤∫ z, fineKernel b (z-w)*(A*(2*b)) := by
      apply integral_mono
      · simpa only [Pi.sub_apply,Real.norm_eq_abs,mul_sub] using (hi.sub hc).norm
      · exact (fineKernel_shift_integrable hb w).mul_const _
      · intro z
        dsimp only
        rw [abs_mul,abs_of_nonneg (fineKernel_nonneg ..)]
        by_cases hz : fineKernel b (z-w)=0
        · simp only [hz,zero_mul,le_refl]
        · have hs : ‖z-w‖≤2*b := le_of_not_gt (fun hh => hz (fineKernel_eq_zero_of_two_mul_lt hb _ hh))
          exact mul_le_mul_of_nonneg_left ((hL z w).trans (mul_le_mul_of_nonneg_left hs hA)) (fineKernel_nonneg ..)
    _=A*(2*b) := by rw [integral_mul_const,fineKernel_shift_integral hb,one_mul]

lemma fineKernel_test_zero_far {b R : ℝ} (hb : 0<b) (K : Space → ℝ) (y w : Space)
    (hs : ∀ z, R<‖z-y‖ → K z=0) (hw : R+2*b<‖w-y‖) :
    (∫ z, fineKernel b (z-w)*K z)=0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with z
  change fineKernel b (z-w)*K z=0
  by_cases hz : fineKernel b (z-w)=0
  · simp only [hz,zero_mul]
  have hn : ‖z-w‖≤2*b := le_of_not_gt (fun hh => hz (fineKernel_eq_zero_of_two_mul_lt hb _ hh))
  have htri := norm_sub_le_norm_sub_add_norm_sub w z y
  rw [norm_sub_rev w z] at htri
  rw [hs z (by linarith),mul_zero]

theorem patchFine_kernel_matching {n : ℕ} {b t R A B : ℝ} (hb : 0<b) (hA : 0≤A)
    (hretain : R+2*b<t-7*b) (K : Space → ℝ) (hKm : Measurable K)
    (hB : ∀ z, |K z|≤B) (y : Space)
    (hs : ∀ z, R<‖z-y‖ → K z=0)
    (hL : ∀ z v, |K z-K v|≤A*‖z-v‖) (x : Configuration n) :
    |(∫ z, retainedFineDensity b (patchRetained y t b x) (position x) z*K z)-
      ∑ i, K (position x i)| ≤
      (A*(2*b))*localCount (Metric.closedBall y (R+2*b)) x := by
  let r := patchRetained y t b x
  have hsum : (∑ i, K (position x i))=∑ i∈r, K (position x i) := by
    apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro i _ hi
    apply hs
    by_contra hh
    apply hi
    apply (patchRetained_mem ..).mpr
    have hn : ‖position x i-y‖≤R := le_of_not_gt hh
    linarith
  simp only [retainedFineDensity,Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => fineKernel_test_integrable hb K hKm hB _),hsum,←Finset.sum_sub_distrib]
  calc
    _≤∑ i∈r, |(∫ z, fineKernel b (z-position x i)*K z)-K (position x i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _≤∑ i∈r, (A*(2*b))*(Metric.closedBall y (R+2*b)).indicator (fun _ => (1:ℝ)) (position x i) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : position x i ∈ Metric.closedBall y (R+2*b)
      · rw [indicator_of_mem hi,mul_one]
        exact fineKernel_test_matching hb hA K hKm hB hL _
      · rw [indicator_of_notMem hi,mul_zero]
        have hn : R+2*b<‖position x i-y‖ := by
          simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hi
        rw [fineKernel_test_zero_far hb K y _ hs hn,hs _ (by linarith),sub_self,abs_zero]
    _≤∑ i, (A*(2*b))*(Metric.closedBall y (R+2*b)).indicator (fun _ => (1:ℝ)) (position x i) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i _ _
      exact mul_nonneg (by positivity) (indicator_nonneg (fun _ _ => by norm_num) _)
    _=(A*(2*b))*localCount (Metric.closedBall y (R+2*b)) x := by
      rw [localCount,Finset.mul_sum]

end Coulomb

end

end OAI
