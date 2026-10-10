import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkConcentration
import OAI.Probability.Perceptron.Pressure.SphericalPatternDirection
import OAI.Probability.Perceptron.Cavity.BulkFreshRestore

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma replicaMean_param_integrable_dominated {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (μ : Measure S) [IsProbabilityMeasure μ] (ν : Measure Ω) (r : ℕ)
    {H : Ω→S→ℝ} {F : Ω→(Fin r→S)→ℝ}
    (hH : Measurable (Function.uncurry H)) (hF : Measurable (Function.uncurry F))
    {D : Ω→ℝ} (hD : Integrable D ν) (hD0 : ∀ a,0≤D a) (hb : ∀ a x,|F a x|≤D a) :
    Integrable (fun a => gibbsReplicaMean μ (H a) r (F a)) ν := by
  apply hD.mono' (measurable_replicaMean_param μ hH hF).aestronglyMeasurable
  exact ae_of_all _ fun a => by
    rw [Real.norm_eq_abs]
    exact tiltMean_bound_general _ (replicaPotential_measurable hH.of_uncurry_left r)
      hF.of_uncurry_left (hD0 a) (hb a)

lemma bulkReplicaMean_sum_dominated (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    {ι : Type*} (s : Finset ι)
    (F : ι→BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hF : ∀ i∈s,Measurable (Function.uncurry (F i)))
    (D : ι→BulkDisorder (n+1) M→ℝ) (hD : ∀ i∈s,Integrable (D i) (bulkDisorderLaw (n+1) M))
    (hD0 : ∀ i∈s,∀ a,0≤D i a) (hb : ∀ i∈s,∀ a x,|F i a x|≤D i a) :
    bulkReplicaMean n M f v r (fun a x => ∑ i∈s,F i a x)=
      ∑ i∈s,bulkReplicaMean n M f v r (F i) := by
  have hH := (bulkHamiltonian_continuous (n+1) M f v).measurable
  unfold bulkReplicaMean
  have he (a : BulkDisorder (n+1) M) := gibbsReplicaMean_sum_of_integrable
    (unitSphereLaw (n+1)) s (bulkHamiltonian_section_measurable _ _ _ _ a) (bulkHamiltonian_exp_integrable n M f v a)
    (fun i hi => (hF i hi).of_uncurry_left) (fun i hi x => hb i hi a x)
  simp_rw [he]
  exact integral_finsetSum s fun i hi => replicaMean_param_integrable_dominated _ _ r hH
    (hF i hi) (hD i hi) (hD0 i hi) (hb i hi)

def bulkPatternSize {N M : ℕ} (j : Fin M) (a : BulkDisorder N M) : ℝ := ∑ i,|a.1 j i|

lemma bulkPatternSize_integrable (N M : ℕ) (j : Fin M) :
    Integrable (bulkPatternSize (N:=N) j) (bulkDisorderLaw N M) := by
  apply (integrable_finsetSum _ fun i _ => ?_)
  have hr : Integrable (fun b : Fin N→ℝ => |b i|) (Measure.pi fun _ => gaussianReal 0 1) :=
    ((measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i).integrable_comp
      measurable_id.norm.aestronglyMeasurable).mpr
        (((memLp_id_gaussianReal (μ:=0) (v:=1) 1).integrable (by norm_num)).norm)
  have ha := ((measurePreserving_eval (fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1) j).integrable_comp
    ((measurable_pi_apply i).norm.aestronglyMeasurable)).mpr hr
  exact ha.comp_fst _

lemma bulkPatternFields_bound {N M r : ℕ} (j : Fin M) (a : BulkDisorder N M)
    (x : Fin r→NormalizedSpin N) (i : Fin r) : |bulkPatternFields j a x i|≤bulkPatternSize j a := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro t _
  rw [abs_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (normalizedSpin_coord_bound (x i) t) (abs_nonneg (a.1 j t))

def bulkTangentPattern {N M : ℕ} (f : Jet3) (G : ℝ→ᵇℝ) (j : Fin M)
    (a : BulkDisorder N M) (x : Fin 2→NormalizedSpin N) : ℝ :=
  G (spinOverlap (x 0) (x 1))*f.d1 (bulkPatternFields j a x 0)*
    (bulkPatternFields j a x 1-spinOverlap (x 0) (x 1)*bulkPatternFields j a x 0)

lemma bulkTangentPattern_measurable (N M : ℕ) (f : Jet3) (G : ℝ→ᵇℝ) (j : Fin M) :
    Measurable (Function.uncurry (bulkTangentPattern (N:=N) f G j)) := by
  have hc : Continuous (Function.uncurry (bulkTangentPattern (N:=N) f G j)) := by
    unfold bulkTangentPattern bulkPatternFields spinOverlap Function.uncurry
    fun_prop
  exact hc.measurable

lemma bulkTangentPattern_bound {N M : ℕ} (f : Jet3) (G : ℝ→ᵇℝ) (j : Fin M)
    (a : BulkDisorder N M) (x : Fin 2→NormalizedSpin N) :
    |bulkTangentPattern f G j a x|≤2*‖G‖*‖f.d1‖*bulkPatternSize j a := by
  have hD : 0≤bulkPatternSize j a := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hd : |bulkPatternFields j a x 1-spinOverlap (x 0) (x 1)*bulkPatternFields j a x 0|≤2*bulkPatternSize j a := by
    apply (abs_sub _ _).trans
    rw [abs_mul]
    have hm := mul_le_mul (spinOverlap_abs_le (x 0) (x 1)) (bulkPatternFields_bound j a x 0) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    linarith [bulkPatternFields_bound j a x 1]
  unfold bulkTangentPattern
  rw [abs_mul,abs_mul]
  apply (mul_le_mul (mul_le_mul (G.norm_coe_le_norm _) (f.d1.norm_coe_le_norm _) (abs_nonneg _) (norm_nonneg _)) hd (abs_nonneg _) (by positivity)).trans_eq
  ring

lemma bulkTangentPattern_integrable (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (G : ℝ→ᵇℝ) (j : Fin M) :
    Integrable (fun a : BulkDisorder (n+1) M => gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f.f v a.1 a.2) 2 (bulkTangentPattern f G j a)) (bulkDisorderLaw (n+1) M) := by
  exact replicaMean_param_integrable_dominated _ _ 2 (bulkHamiltonian_continuous _ _ _ _).measurable
    (bulkTangentPattern_measurable _ _ _ _ _) ((bulkPatternSize_integrable (n+1) M j).const_mul (2*‖G‖*‖f.d1‖))
    (fun a => mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => abs_nonneg _))
    (bulkTangentPattern_bound f G j)


def freshTangent (N : ℕ) (f : Jet3) (G : ℝ→ᵇℝ)
    (b : Spin N) (x : Fin 2→NormalizedSpin N) : ℝ :=
  G (spinOverlap (x 0) (x 1))*f.d1 (inner ℝ (x 0).val b)*
    (inner ℝ (x 1).val b-spinOverlap (x 0) (x 1)*inner ℝ (x 0).val b)

def freshTangentPair (N : ℕ) (f : Jet3) (G : ℝ→ᵇℝ)
    (b : Spin N) (x : Fin 2→NormalizedSpin N) : ℝ :=
  G (spinOverlap (x 0) (x 1))*f.d1 (inner ℝ (x 0).val b)*f.d1 (inner ℝ (x 1).val b)*
    (1-spinOverlap (x 0) (x 1)^2)

def freshTangentTriple (N : ℕ) (f : Jet3) (G : ℝ→ᵇℝ)
    (b : Spin N) (x : Fin 3→NormalizedSpin N) : ℝ :=
  G (spinOverlap (x 1) (x 2))*f.d1 (inner ℝ (x 1).val b)*f.d1 (inner ℝ (x 0).val b)*
    (spinOverlap (x 2) (x 0)-spinOverlap (x 1) (x 2)*spinOverlap (x 1) (x 0))

lemma freshTangent_measurable (N : ℕ) (f : Jet3) (G : ℝ→ᵇℝ) :
    Measurable (Function.uncurry (freshTangent N f G)) := by
  have hc : Continuous (Function.uncurry (freshTangent N f G)) := by
    unfold freshTangent spinOverlap Function.uncurry; fun_prop
  exact hc.measurable

lemma freshTangentPair_measurable (N : ℕ) (f : Jet3) (G : ℝ→ᵇℝ) :
    Measurable (Function.uncurry (freshTangentPair N f G)) := by
  have hc : Continuous (Function.uncurry (freshTangentPair N f G)) := by
    unfold freshTangentPair spinOverlap Function.uncurry; fun_prop
  exact hc.measurable

lemma freshTangentTriple_measurable (N : ℕ) (f : Jet3) (G : ℝ→ᵇℝ) :
    Measurable (Function.uncurry (freshTangentTriple N f G)) := by
  have hc : Continuous (Function.uncurry (freshTangentTriple N f G)) := by
    unfold freshTangentTriple spinOverlap Function.uncurry; fun_prop
  exact hc.measurable

lemma normalizedSpin_inner_bound {N : ℕ} (x : NormalizedSpin N) (b : Spin N) :
    |inner ℝ x.val b|≤‖b‖ := by
  have hx : ‖x.val‖=1 := by simp
  simpa only [hx,one_mul] using abs_real_inner_le_norm x.val b

lemma freshTangent_bound (N : ℕ) (f : Jet3) (G : ℝ→ᵇℝ) (b : Spin N) (x : Fin 2→NormalizedSpin N) :
    |freshTangent N f G b x|≤2*‖G‖*‖f.d1‖*‖b‖ := by
  have hd : |inner ℝ (x 1).val b-spinOverlap (x 0) (x 1)*inner ℝ (x 0).val b|≤2*‖b‖ := by
    apply (abs_sub _ _).trans
    rw [abs_mul]
    have hm := mul_le_mul (spinOverlap_abs_le (x 0) (x 1)) (normalizedSpin_inner_bound (x 0) b)
      (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    linarith [normalizedSpin_inner_bound (x 1) b]
  unfold freshTangent
  rw [abs_mul,abs_mul]
  apply (mul_le_mul (mul_le_mul (G.norm_coe_le_norm _) (f.d1.norm_coe_le_norm _) (abs_nonneg _) (norm_nonneg _)) hd (abs_nonneg _) (by positivity)).trans_eq
  ring

lemma freshTangentPair_bound (N : ℕ) (f : Jet3) (G : ℝ→ᵇℝ) (b : Spin N) (x : Fin 2→NormalizedSpin N) :
    |freshTangentPair N f G b x|≤2*‖G‖*‖f.d1‖^2 := by
  have hd : |1-spinOverlap (x 0) (x 1)^2|≤2 := by
    apply (abs_sub _ _).trans
    have := pow_le_pow_left₀ (abs_nonneg _) (spinOverlap_abs_le (x 0) (x 1)) 2
    simp only [abs_one,abs_pow,one_pow] at this ⊢
    linarith
  unfold freshTangentPair
  rw [abs_mul,abs_mul,abs_mul]
  apply (mul_le_mul (mul_le_mul (mul_le_mul (G.norm_coe_le_norm _) (f.d1.norm_coe_le_norm _) (abs_nonneg _) (norm_nonneg _))
    (f.d1.norm_coe_le_norm _) (abs_nonneg _) (by positivity)) hd (abs_nonneg _) (by positivity)).trans_eq
  ring

lemma freshTangentTriple_bound (N : ℕ) (f : Jet3) (G : ℝ→ᵇℝ) (b : Spin N) (x : Fin 3→NormalizedSpin N) :
    |freshTangentTriple N f G b x|≤2*‖G‖*‖f.d1‖^2 := by
  have hd : |spinOverlap (x 2) (x 0)-spinOverlap (x 1) (x 2)*spinOverlap (x 1) (x 0)|≤2 := by
    apply (abs_sub _ _).trans
    rw [abs_mul]
    have hm := mul_le_mul (spinOverlap_abs_le (x 1) (x 2)) (spinOverlap_abs_le (x 1) (x 0))
      (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    linarith [spinOverlap_abs_le (x 2) (x 0)]
  unfold freshTangentTriple
  rw [abs_mul,abs_mul,abs_mul]
  apply (mul_le_mul (mul_le_mul (mul_le_mul (G.norm_coe_le_norm _) (f.d1.norm_coe_le_norm _) (abs_nonneg _) (norm_nonneg _))
    (f.d1.norm_coe_le_norm _) (abs_nonneg _) (by positivity)) hd (abs_nonneg _) (by positivity)).trans_eq
  ring

lemma bulkFreshReplicaMean_integrable (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (F : Spin (n+1)→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hF : Measurable (Function.uncurry F)) {D : Spin (n+1)→ℝ}
    (hD : Integrable D (stdGaussian (Spin (n+1)))) (hD0 : ∀ b,0≤D b) (hb : ∀ b x,|F b x|≤D b) :
    Integrable (fun p : BulkDisorder (n+1) M×Spin (n+1) =>
      gibbsReplicaMean (unitSphereLaw (n+1))
        (fun x => bulkHamiltonian (n+1) M f v p.1.1 p.1.2 x+f (inner ℝ x.val p.2)) r (F p.2))
      ((bulkDisorderLaw (n+1) M).prod (stdGaussian (Spin (n+1)))) := by
  apply replicaMean_param_integrable_dominated _ _ r _ _ (hD.comp_snd _) (fun p => hD0 p.2) (fun p x => hb p.2 x)
  · exact ((bulkHamiltonian_continuous (n+1) M f v).measurable.comp (measurable_fst.fst.prodMk measurable_snd)).add
      (f.continuous.measurable.comp (measurable_snd.subtype_val.inner measurable_fst.snd))
  · exact hF.comp (measurable_fst.snd.prodMk measurable_snd)

lemma bulkReplicaMean_last_integral (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (F : Spin (n+1)→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hF : Measurable (Function.uncurry F)) {D : Spin (n+1)→ℝ}
    (hD : Integrable D (stdGaussian (Spin (n+1)))) (hD0 : ∀ b,0≤D b) (hb : ∀ b x,|F b x|≤D b) :
    bulkReplicaMean n (M+1) f v r (fun a x => F (bulkSeparateLast (n+1) M a).2 x)=
      ∫ a : BulkDisorder (n+1) M, ∫ b : Spin (n+1),
        gibbsReplicaMean (unitSphereLaw (n+1))
          (fun x => bulkHamiltonian (n+1) M f v a.1 a.2 x+f (inner ℝ x.val b)) r (F b)
          ∂stdGaussian (Spin (n+1)) ∂bulkDisorderLaw (n+1) M := by
  let H := fun p : BulkDisorder (n+1) M×Spin (n+1) =>
    fun x : NormalizedSpin (n+1) => bulkHamiltonian (n+1) M f v p.1.1 p.1.2 x+f (inner ℝ x.val p.2)
  have hH : Measurable (Function.uncurry H) := by
    exact ((bulkHamiltonian_continuous (n+1) M f v).measurable.comp (measurable_fst.fst.prodMk measurable_snd)).add
      (f.continuous.measurable.comp (measurable_snd.subtype_val.inner measurable_fst.snd))
  have hFm : Measurable (Function.uncurry (fun p : BulkDisorder (n+1) M×Spin (n+1) => F p.2)) :=
    hF.comp (measurable_fst.snd.prodMk measurable_snd)
  have hm := measurable_replicaMean_param (unitSphereLaw (n+1)) hH hFm
  have hi := bulkFreshReplicaMean_integrable n M r f v F hF hD hD0 hb
  have he := integral_map (μ := bulkDisorderLaw (n+1) (M+1)) (bulkSeparateLast_preserving (n+1) M).measurable.aemeasurable hm.aestronglyMeasurable
  rw [(bulkSeparateLast_preserving (n+1) M).map_eq] at he
  change (∫ a : BulkDisorder (n+1) (M+1),
    gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) (M+1) f v a.1 a.2) r
      (F (bulkSeparateLast (n+1) M a).2) ∂bulkDisorderLaw (n+1) (M+1))=_
  calc
    _ = ∫ a : BulkDisorder (n+1) (M+1),
        gibbsReplicaMean (unitSphereLaw (n+1)) (H (bulkSeparateLast (n+1) M a)) r
          (F (bulkSeparateLast (n+1) M a).2) ∂bulkDisorderLaw (n+1) (M+1) := by
      apply integral_congr_ae
      exact ae_of_all _ fun a => by
        have hham : bulkHamiltonian (n+1) (M+1) f v a.1 a.2 = H (bulkSeparateLast (n+1) M a) := by
          funext x
          exact bulkHamiltonian_last (n+1) M f v a x
        exact congrArg (fun h => gibbsReplicaMean (unitSphereLaw (n+1)) h r (F (bulkSeparateLast (n+1) M a).2)) hham
    _ = ∫ p : BulkDisorder (n+1) M×Spin (n+1),
        gibbsReplicaMean (unitSphereLaw (n+1)) (H p) r (F p.2)
          ∂(bulkDisorderLaw (n+1) M).prod (stdGaussian (Spin (n+1))) := he.symm
    _ = _ := integral_prod _ hi

lemma fresh_tangent_ibp (n : ℕ) (f : Jet3) (G : ℝ→ᵇℝ)
    {h : NormalizedSpin (n+1)→ℝ} (hh : Measurable h) {A : ℝ} (hA : 0≤A) (hb : ∀ x,|h x|≤A) :
    (∫ b : Spin (n+1), gibbsReplicaMean (unitSphereLaw (n+1))
      (fun x => h x+f.f (inner ℝ x.val b)) 2 (freshTangent (n+1) f G b) ∂stdGaussian (Spin (n+1))) =
    ∫ b : Spin (n+1), gibbsReplicaMean (unitSphereLaw (n+1))
      (fun x => h x+f.f (inner ℝ x.val b)) 2 (freshTangentPair (n+1) f G b)-
      2*gibbsReplicaMean (unitSphereLaw (n+1))
      (fun x => h x+f.f (inner ℝ x.val b)) 3 (freshTangentTriple (n+1) f G b) ∂stdGaussian (Spin (n+1)) := by
  have hH : Measurable (Function.uncurry (fun b : Spin (n+1) => fun x : NormalizedSpin (n+1) => h x+f.f (inner ℝ x.val b))) :=
    (hh.comp measurable_snd).add (f.f.measurable.comp (measurable_snd.subtype_val.inner measurable_fst))
  have h1 := measurable_replicaMean_param (unitSphereLaw (n+1)) hH (freshTangent_measurable (n+1) f G)
  have h2 := measurable_replicaMean_param (unitSphereLaw (n+1)) hH (freshTangentPair_measurable (n+1) f G)
  have h3 := measurable_replicaMean_param (unitSphereLaw (n+1)) hH (freshTangentTriple_measurable (n+1) f G)
  have h23 : AEStronglyMeasurable (fun b : Spin (n+1) =>
      gibbsReplicaMean (unitSphereLaw (n+1)) (fun x => h x+f.f (inner ℝ x.val b)) 2 (freshTangentPair (n+1) f G b)-
      2*gibbsReplicaMean (unitSphereLaw (n+1)) (fun x => h x+f.f (inner ℝ x.val b)) 3 (freshTangentTriple (n+1) f G b))
      (Measure.map (WithLp.toLp 2) (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1)) :=
    (h2.sub (h3.const_mul 2)).aestronglyMeasurable
  rw [←map_pi_eq_stdGaussian,integral_map (PiLp.continuous_toLp 2 _).measurable.aemeasurable h1.aestronglyMeasurable,
    integral_map (PiLp.continuous_toLp 2 _).measurable.aemeasurable h23]
  have he := spherical_pattern_direction_ibp (unitSphereLaw (n+1)) f G hh hA hb
  unfold freshTangent freshTangentPair freshTangentTriple
  convert he using 1 <;>
    simp only [gaussianField,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,mul_comm]

lemma bulk_tangent_last_ibp (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (G : ℝ→ᵇℝ) :
    bulkReplicaMean n (M+1) f.f v 2 (fun a => freshTangent (n+1) f G (bulkSeparateLast (n+1) M a).2) =
      bulkReplicaMean n (M+1) f.f v 2 (fun a => freshTangentPair (n+1) f G (bulkSeparateLast (n+1) M a).2)-
      2*bulkReplicaMean n (M+1) f.f v 3 (fun a => freshTangentTriple (n+1) f G (bulkSeparateLast (n+1) M a).2) := by
  have hD : Integrable (fun b : Spin (n+1) => 2*‖G‖*‖f.d1‖*‖b‖) (stdGaussian (Spin (n+1))) :=
    ((((IsGaussian.memLp_id (stdGaussian (Spin (n+1))) 2 (by simp)).norm).integrable (by norm_num))).const_mul _
  have hC : (0:ℝ)≤2*‖G‖*‖f.d1‖^2 := by positivity
  rw [bulkReplicaMean_last_integral n M 2 f.f v _ (freshTangent_measurable _ _ _) hD (fun _ => by positivity) (freshTangent_bound _ _ _),
    bulkReplicaMean_last_integral n M 2 f.f v _ (freshTangentPair_measurable _ _ _) (integrable_const _) (fun _ => hC) (freshTangentPair_bound _ _ _),
    bulkReplicaMean_last_integral n M 3 f.f v _ (freshTangentTriple_measurable _ _ _) (integrable_const _) (fun _ => hC) (freshTangentTriple_bound _ _ _)]
  let P := fun p : BulkDisorder (n+1) M×Spin (n+1) => gibbsReplicaMean (unitSphereLaw (n+1))
    (fun x => bulkHamiltonian (n+1) M f.f v p.1.1 p.1.2 x+f.f (inner ℝ x.val p.2)) 2
      (freshTangentPair (n+1) f G p.2)
  let T := fun p : BulkDisorder (n+1) M×Spin (n+1) => gibbsReplicaMean (unitSphereLaw (n+1))
    (fun x => bulkHamiltonian (n+1) M f.f v p.1.1 p.1.2 x+f.f (inner ℝ x.val p.2)) 3
      (freshTangentTriple (n+1) f G p.2)
  have hiP : Integrable P ((bulkDisorderLaw (n+1) M).prod (stdGaussian (Spin (n+1)))) :=
    bulkFreshReplicaMean_integrable n M 2 f.f v _ (freshTangentPair_measurable _ _ _)
      (integrable_const _) (fun _ => hC) (freshTangentPair_bound _ _ _)
  have hiT : Integrable T ((bulkDisorderLaw (n+1) M).prod (stdGaussian (Spin (n+1)))) :=
    bulkFreshReplicaMean_integrable n M 3 f.f v _ (freshTangentTriple_measurable _ _ _)
      (integrable_const _) (fun _ => hC) (freshTangentTriple_bound _ _ _)
  calc
    _ = ∫ a : BulkDisorder (n+1) M, ∫ b : Spin (n+1), P (a,b)-2*T (a,b)
        ∂stdGaussian (Spin (n+1)) ∂bulkDisorderLaw (n+1) M := by
      apply integral_congr_ae
      exact ae_of_all _ fun a => fresh_tangent_ibp n f G
        (bulkHamiltonian_section_measurable _ _ _ _ a)
        (show 0≤M*‖f.f‖+bulkFeatureBound (n+1) v*‖a.2‖ by unfold bulkFeatureBound; positivity)
        (bulkHamiltonian_bound (n+1) M f.f v a)
    _ = _ := by
      have hiPT : Integrable (fun p => P p-2*T p) ((bulkDisorderLaw (n+1) M).prod (stdGaussian (Spin (n+1)))) :=
        hiP.sub (hiT.const_mul 2)
      rw [←integral_prod _ hiPT,integral_sub hiP (hiT.const_mul 2),integral_const_mul,
        integral_prod _ hiP,integral_prod _ hiT]

lemma bulkReplicaMean_row_eq_last (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (j : Fin (M+1))
    (F : Spin (n+1)→(Fin r→NormalizedSpin (n+1))→ℝ) (hF : Measurable (Function.uncurry F)) :
    bulkReplicaMean n (M+1) f v r (fun a => F (WithLp.toLp 2 (a.1 j))) =
      bulkReplicaMean n (M+1) f v r (fun a => F (bulkSeparateLast (n+1) M a).2) := by
  classical
  have hm : Measurable (Function.uncurry (fun a : BulkDisorder (n+1) (M+1) => F (bulkSeparateLast (n+1) M a).2)) :=
    hF.comp (((bulkSeparateLast_preserving (n+1) M).measurable.snd.comp measurable_fst).prodMk measurable_snd)
  have he := bulkReplicaMean_permute n (M+1) f v r (Equiv.swap j (Fin.last M))
    (fun a => F (bulkSeparateLast (n+1) M a).2) hm
  simpa only [bulkSeparateLast,bulkPermutePatterns,Equiv.swap_apply_right] using he

lemma bulk_tangent_row_ibp (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (G : ℝ→ᵇℝ) (j : Fin (M+1)) :
    bulkReplicaMean n (M+1) f.f v 2 (bulkTangentPattern f G j) =
      bulkReplicaMean n (M+1) f.f v 2 (fun a => freshTangentPair (n+1) f G (WithLp.toLp 2 (a.1 j)))-
      2*bulkReplicaMean n (M+1) f.f v 3 (fun a => freshTangentTriple (n+1) f G (WithLp.toLp 2 (a.1 j))) := by
  have he : (bulkTangentPattern (N:=n+1) f G j)=
    (fun a : BulkDisorder (n+1) (M+1) => freshTangent (n+1) f G (WithLp.toLp 2 (a.1 j))) := by
    funext a x
    simp only [bulkTangentPattern,bulkPatternFields,freshTangent,
      EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
  rw [he,bulkReplicaMean_row_eq_last _ _ _ _ _ _ _ (freshTangent_measurable _ _ _),
    bulkReplicaMean_row_eq_last _ _ _ _ _ _ _ (freshTangentPair_measurable _ _ _),
    bulkReplicaMean_row_eq_last _ _ _ _ _ _ _ (freshTangentTriple_measurable _ _ _)]
  exact bulk_tangent_last_ibp n M f v G

end SphericalPerceptronFreeEnergy
end

end OAI
