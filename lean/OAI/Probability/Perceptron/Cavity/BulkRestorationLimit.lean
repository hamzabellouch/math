import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkMarkedMoments
import OAI.Probability.Perceptron.Cavity.BulkRestoredObservables

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction

def twoFreshDisorderLaw (N M : ℕ) : Measure (TwoFreshDisorder N M) :=
  (bulkDisorderLaw N M).prod ((stdGaussian (EuclideanSpace ℝ (Fin N))).prod
    (stdGaussian (EuclideanSpace ℝ (Fin N))))
instance (N M : ℕ) : IsProbabilityMeasure (twoFreshDisorderLaw N M) := by
  unfold twoFreshDisorderLaw
  infer_instance

def bulkFreshCompactDenominator (n M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (p : TwoFreshDisorder (n+1) M) : Icc (Real.exp (-(2*‖f‖))) (Real.exp (2*‖f‖)) :=
  ⟨bulkFreshDenominator n M f v p,bulkFreshDenominator_mem n M f v p⟩
lemma bulkFreshCompactDenominator_measurable (n M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ) :
    Measurable (bulkFreshCompactDenominator n M f v) :=
  (bulkFreshDenominator_measurable n M f v).subtype_mk

lemma bulkFreshNumerator_integrable (n M r : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (F : CompactBlock CompactOverlap r →ᵇ ℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    (P : Measure (TwoFreshDisorder (n+1) M)) [IsFiniteMeasure P] :
    Integrable (bulkFreshNumerator n M r f v F Ψ Φ) P := by
  apply Integrable.of_bound (bulkFreshNumerator_measurable n M r f v F Ψ Φ).aestronglyMeasurable
    (‖F‖*‖restorationMarkTest r f Ψ 0‖*‖restorationMarkTest r f Φ 0‖)
  exact ae_of_all _ fun p => by
    simpa only [Real.norm_eq_abs] using bulkFreshNumerator_bound n M r f v F Ψ Φ p

lemma bulkFresh_weighted_integrable (n M r : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (F : CompactBlock CompactOverlap r →ᵇ ℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    (k : ℕ) :
    Integrable (fun p => bulkFreshNumerator n M r f v F Ψ Φ p * bulkFreshDenominator n M f v p^k)
      (twoFreshDisorderLaw (n+1) M) := by
  let T : C(Icc (Real.exp (-(2*‖f‖))) (Real.exp (2*‖f‖)),ℝ) :=
    ⟨fun z => z.val^k,continuous_subtype_val.pow k⟩
  exact weighted_compact_integrable (twoFreshDisorderLaw (n+1) M)
    (bulkFreshNumerator n M r f v F Ψ Φ) (bulkFreshNumerator_measurable n M r f v F Ψ Φ)
    (bulkFreshCompactDenominator n M f v) (bulkFreshCompactDenominator_measurable n M f v)
    _ (by positivity) (bulkFreshNumerator_bound n M r f v F Ψ Φ) T

lemma bulkFresh_annealed_polynomial (n M r : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (F : CompactBlock CompactOverlap r →ᵇ ℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) (k : ℕ) :
    (∫ p, bulkFreshNumerator n M r f v F Ψ Φ p * bulkFreshDenominator n M f v p^k
      ∂twoFreshDisorderLaw (n+1) M) =
      ∫ Q, (restorationBlockTest r F k * freshMarkedCompactBlockKernel (restorationMarkTest r f Ψ k) *
        freshMarkedCompactBlockKernel (restorationMarkTest r f Φ k)) (compactBlock (r+k) Q)
        ∂bulkGibbsArrayLaw n M f v := by
  rw [twoFreshDisorderLaw,integral_prod _ (bulkFresh_weighted_integrable n M r f v F Ψ Φ k)]
  simp_rw [mul_comm (bulkFreshNumerator n M r f v F Ψ Φ _),bulkFresh_polynomial_moment]
  exact bulk_twoFresh_block n M (r+k) f v (restorationBlockTest r F k)
    (restorationMarkTest r f Ψ k) (restorationMarkTest r f Φ k)

lemma bulkFresh_moment_tendsto (M : ℕ → ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℕ → ℝ) (s : ℕ → ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hν : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) f (v (s n))) atTop (𝓝 ν))
    (r : ℕ) (F : CompactBlock CompactOverlap r →ᵇ ℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) (k : ℕ) :
    Tendsto (fun n => ∫ p, bulkFreshNumerator (s n) (M (s n)) r f (v (s n)) F Ψ Φ p *
      bulkFreshDenominator (s n) (M (s n)) f (v (s n)) p^k ∂twoFreshDisorderLaw (s n+1) (M (s n)))
      atTop (𝓝 (∫ Q, (restorationBlockTest r F k * freshMarkedCompactBlockKernel (restorationMarkTest r f Ψ k) *
        freshMarkedCompactBlockKernel (restorationMarkTest r f Φ k)) (compactBlock (r+k) Q) ∂ν)) := by
  simp_rw [bulkFresh_annealed_polynomial]
  exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    ((restorationBlockTest r F k * freshMarkedCompactBlockKernel (restorationMarkTest r f Ψ k) *
      freshMarkedCompactBlockKernel (restorationMarkTest r f Φ k)).compContinuous
        ⟨compactBlock (r+k), compactBlock_continuous (r+k)⟩)).continuousAt.tendsto.comp hν

lemma bulkFresh_exact_restoration (n M r : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (F : CompactBlock CompactOverlap r →ᵇ ℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    (a : BulkDisorder (n+1) (M+2)) :
    gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) (M+2) f v a.1 a.2) r
      (bulkMarkedTest (n+1) r F Ψ Φ (bulkSeparateTwo (n+1) M a).2) =
      bulkFreshNumerator n M r f v F Ψ Φ (bulkSeparateTwo (n+1) M a) /
        bulkFreshDenominator n M f v (bulkSeparateTwo (n+1) M a)^r := by
  rw [bulk_replica_restore_two]
  congr 1
  apply congrArg (gibbsReplicaMean (unitSphereLaw (n+1))
    (bulkHamiltonian (n+1) M f v (bulkSeparateTwo (n+1) M a).1.1 (bulkSeparateTwo (n+1) M a).1.2) r)
  funext x
  have h := restorationReplicaTest_twoMarks f F Ψ Φ (bulkSeparateTwo (n+1) M a).2.1
      (bulkSeparateTwo (n+1) M a).2.2 0 x
  simp only [restorationReplicaTest,restorationBlockTest,mul_assoc,bulkMarkedTest] at h ⊢
  convert h using 1

lemma bulkFresh_annealed_restoration (n M r : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (F : CompactBlock CompactOverlap r →ᵇ ℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) :
    (∫ a, gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) (M+2) f v a.1 a.2) r
      (bulkMarkedTest (n+1) r F Ψ Φ (bulkSeparateTwo (n+1) M a).2) ∂bulkDisorderLaw (n+1) (M+2)) =
      ∫ p, bulkFreshNumerator n M r f v F Ψ Φ p / bulkFreshDenominator n M f v p^r
        ∂twoFreshDisorderLaw (n+1) M := by
  simp_rw [bulkFresh_exact_restoration]
  have hp := bulkSeparateTwo_preserving (n+1) M
  let g : TwoFreshDisorder (n+1) M → ℝ := fun p =>
    bulkFreshNumerator n M r f v F Ψ Φ p / bulkFreshDenominator n M f v p^r
  have hg : AEStronglyMeasurable g (twoFreshDisorderLaw (n+1) M) :=
    (((bulkFreshNumerator_measurable n M r f v F Ψ Φ).div
      ((bulkFreshDenominator_measurable n M f v).pow_const r)).aestronglyMeasurable)
  change (∫ a, g (bulkSeparateTwo (n+1) M a) ∂bulkDisorderLaw (n+1) (M+2)) =
    ∫ p, g p ∂twoFreshDisorderLaw (n+1) M
  have hg' : AEStronglyMeasurable g
      ((bulkDisorderLaw (n+1) (M+2)).map (bulkSeparateTwo (n+1) M)) := by
    rw [hp.map_eq]
    exact hg
  have he := integral_map hp.measurable.aemeasurable hg'
  exact he.symm.trans (by rw [hp.map_eq]; rfl)

lemma bulkReplicaMean_sum (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    {ι : Type*} (s : Finset ι)
    (G : ι→BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hG : ∀ i∈s,Measurable (Function.uncurry (G i)))
    (D : ι→ℝ) (hD : ∀ i∈s,0≤D i) (hb : ∀ i∈s,∀ a x,|G i a x|≤D i) :
    bulkReplicaMean n M f v r (fun a x => ∑ i∈s,G i a x)=
      ∑ i∈s,bulkReplicaMean n M f v r (G i) := by
  unfold bulkReplicaMean
  have hH : Measurable (Function.uncurry (fun a : BulkDisorder (n+1) M => bulkHamiltonian (n+1) M f v a.1 a.2)) :=
    (bulkHamiltonian_continuous (n+1) M f v).measurable
  have he (a : BulkDisorder (n+1) M) :
      gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r
        (fun x => ∑ i∈s,G i a x)=
      ∑ i∈s,gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r (G i a) :=
    gibbsReplicaMean_sum_of_integrable (unitSphereLaw (n+1)) s
      (show Measurable (fun x => bulkHamiltonian (n+1) M f v a.1 a.2 x) from hH.of_uncurry_left)
      (bulkHamiltonian_exp_integrable n M f v a) (fun i hi => (hG i hi).of_uncurry_left)
      (fun i hi x => hb i hi a x)
  simp_rw [he]
  exact integral_finsetSum s fun i hi => kernel_replicaMean_bounded_integrable (bulkSpinKernel n M)
    (bulkDisorderLaw (n+1) M) hH (hG i hi) (hD i hi) (hb i hi)

lemma bulkReplicaMean_const_mul (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (G : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ) (c : ℝ) :
    bulkReplicaMean n M f v r (fun a x => c*G a x)=c*bulkReplicaMean n M f v r G := by
  unfold bulkReplicaMean
  simp_rw [replicaMean_const_mul]
  exact integral_const_mul _ _

lemma bulkReplicaMean_bound (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (G : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hG : Measurable (Function.uncurry G)) {C : ℝ} (_hC : 0≤C) (hb : ∀ a x,|G a x|≤C) :
    |bulkReplicaMean n M f v r G|≤C := by
  have hb' : ∀ᵐ a ∂bulkDisorderLaw (n+1) M,
      ‖gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r (G a)‖≤C := by
    refine ae_of_all _ fun a => ?_
    rw [Real.norm_eq_abs]
    exact gibbsReplicaMean_bound_of_integrable (unitSphereLaw (n+1))
      ((bulkHamiltonian_continuous _ _ _ _).measurable.comp (measurable_const.prodMk measurable_id))
      hG.of_uncurry_left (bulkHamiltonian_exp_integrable n M f v a) (hb a)
  simpa [bulkReplicaMean] using
    norm_integral_le_of_norm_le_const hb'

lemma bulk_two_row_exchange (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ)
    (G : (Fin r→NormalizedSpin (n+1))→ℝ) (hG : Measurable G)
    (T U : (Fin r→ℝ)→ℝ) (hT : Measurable T) (hU : Measurable U)
    (i j k l : Fin M) (hij : i≠j) (hkl : k≠l) :
    bulkReplicaMean n M f v r (fun a x => G x*T (bulkPatternFields i a x)*U (bulkPatternFields j a x))=
      bulkReplicaMean n M f v r (fun a x => G x*T (bulkPatternFields k a x)*U (bulkPatternFields l a x)) := by
  classical
  let p : Bool→Fin M := fun b => if b then k else l
  let q : Bool→Fin M := fun b => if b then i else j
  have hp : Function.Injective p := by
    intro b c h
    cases b <;> cases c <;> simp_all [p,Ne.symm hkl]
  have hq : Function.Injective q := by
    intro b c h
    cases b <;> cases c <;> simp_all [q,Ne.symm hij]
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair p q hp hq
  have hek : e k=i := by simpa [p,q] using he true
  have hel : e l=j := by simpa [p,q] using he false
  have hm : Measurable (Function.uncurry (fun a x => G x*T (bulkPatternFields k a x)*U (bulkPatternFields l a x))) :=
    ((hG.comp measurable_snd).mul (hT.comp (bulkPatternFields_measurable _ _ _ _))).mul
      (hU.comp (bulkPatternFields_measurable _ _ _ _))
  have ht := bulkReplicaMean_permute n M f v r e _ hm
  change bulkReplicaMean n M f v r (fun a x =>
    G x*T (fun i => ∑ t,a.1 (e k) t*(x i).val t)*U (fun i => ∑ t,a.1 (e l) t*(x i).val t))=_ at ht
  rw [hek,hel] at ht
  exact ht

lemma bulk_pattern_sum_first (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (G : (Fin r→NormalizedSpin (n+1))→ℝ) (hG : Measurable G)
    (T : (Fin r→ℝ)→ℝ) (hT : Measurable T)
    {C D : ℝ} (hC : 0≤C) (hD : 0≤D) (hGC : ∀ x,|G x|≤C) (hTD : ∀ z,|T z|≤D)
    (j : Fin M) :
    bulkReplicaMean n M f v r (fun a x => G x*∑ i,T (bulkPatternFields i a x))=
      M*bulkReplicaMean n M f v r (fun a x => G x*T (bulkPatternFields j a x)) := by
  simp_rw [Finset.mul_sum]
  rw [bulkReplicaMean_sum n M r f v Finset.univ _
    (fun i _ => (hG.comp measurable_snd).mul (hT.comp (bulkPatternFields_measurable _ _ _ _)))
    (fun _=>C*D) (fun _ _ => mul_nonneg hC hD)
    (fun _ _ a x => by simpa only [abs_mul] using mul_le_mul (hGC x) (hTD _) (abs_nonneg _) hC)]
  simp_rw [bulk_row_exchange n M f v r G hG T hT _ j]
  simp

lemma bulk_pattern_sum_second (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (G : (Fin r→NormalizedSpin (n+1))→ℝ) (hG : Measurable G)
    (T : (Fin r→ℝ)→ℝ) (hT : Measurable T)
    {C D : ℝ} (hC : 0≤C) (hD : 0≤D) (hGC : ∀ x,|G x|≤C) (hTD : ∀ z,|T z|≤D)
    (k l : Fin M) (hkl : k≠l) :
    bulkReplicaMean n M f v r (fun a x => G x*(∑ i,T (bulkPatternFields i a x))^2)=
      M*bulkReplicaMean n M f v r (fun a x => G x*(T (bulkPatternFields k a x))^2)+
      M*((M:ℝ)-1)*bulkReplicaMean n M f v r
        (fun a x => G x*T (bulkPatternFields k a x)*T (bulkPatternFields l a x)) := by
  classical
  let W := fun i j (a : BulkDisorder (n+1) M) (x : Fin r→NormalizedSpin (n+1)) =>
    G x*T (bulkPatternFields i a x)*T (bulkPatternFields j a x)
  have hm (i j) : Measurable (Function.uncurry (W i j)) :=
    ((hG.comp measurable_snd).mul (hT.comp (bulkPatternFields_measurable _ _ _ _))).mul
      (hT.comp (bulkPatternFields_measurable _ _ _ _))
  have hb (i j) (a : BulkDisorder (n+1) M) (x : Fin r→NormalizedSpin (n+1)) :
      |W i j a x|≤C*D*D := by
    dsimp [W]; rw [abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul (hGC x) (hTD _) (abs_nonneg _) hC)
      (hTD _) (abs_nonneg _) (mul_nonneg hC hD)
  have hf : (fun a x => G x*(∑ i,T (bulkPatternFields i a x))^2)=
      (fun a x => ∑ i : Fin M,∑ j : Fin M,W i j a x) := by
    funext a x
    simp only [sq,Finset.sum_mul,Finset.mul_sum,W,mul_assoc]
    rw [Finset.sum_comm]
  rw [hf]
  rw [bulkReplicaMean_sum n M r f v Finset.univ (fun i a x => ∑ j,W i j a x)
    (fun i _ => Finset.measurable_sum _ fun j _ => hm i j)
    (fun _ => M*(C*D*D)) (fun _ _ => by positivity)
    (fun i _ a x => (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun j _ => hb i j a x).trans_eq (by simp)))]
  simp_rw [bulkReplicaMean_sum n M r f v Finset.univ (W _)
    (fun j _ => hm _ j) (fun _=>C*D*D) (fun _ _ => by positivity) (fun j _ a x => hb _ j a x)]
  let d := bulkReplicaMean n M f v r (fun a x => G x*(T (bulkPatternFields k a x))^2)
  let o := bulkReplicaMean n M f v r (W k l)
  have he (i j : Fin M) : bulkReplicaMean n M f v r (W i j)=
      o+if i=j then d-o else 0 := by
    by_cases hij : i=j
    · subst j
      rw [ite_eq_left rfl]
      have h := bulk_row_exchange n M f v r G hG (fun z => (T z)^2) (hT.pow_const 2) i k
      dsimp [W]
      simp only [sq,mul_assoc] at h ⊢
      change _=o+(d-o)
      rw [show o+(d-o)=d by ring]
      simpa only [d,sq,mul_assoc] using h
    · rw [ite_eq_right hij,add_zero]
      exact bulk_two_row_exchange n M f v r G hG T T hT hT i j k l hij hkl
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  dsimp [d,o,W]
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
