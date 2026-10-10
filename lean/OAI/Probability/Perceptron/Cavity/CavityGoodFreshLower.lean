import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityFiniteIncrement
import OAI.Probability.Perceptron.Cavity.CavityUncappedLimit

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction

lemma cavity_good_fresh_fullLog_lower (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) {α : ℝ} (hα : 0<α)
    (g : Jet3) (hg : HasCompactSupport (g.d1 : ℝ→ℝ))
    (G : CavityGoodParameters α g.f) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop,∀ δ : ℝ,0<δ→∀ᶠ n : ℕ in atTop,
      ∀ v∈bulkJointGoodSet α g.f G.J n,
      (k+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖-δ≤
        cavityBulkFullLog k (cavityFreshCount α n (k+1)) n (patternCount α (n+1)) g v := by
  filter_upwards [cavity_good_fullLog_lower P hB hα g hg G ε hε] with k hk
  intro δ hδ
  let D:=⌈((k+1:ℕ):ℝ)*α+1⌉₊
  have h : ∀ᶠ n : ℕ in atTop,∀ d∈Finset.range (D+1),
      |(d:ℝ)-(k+1:ℕ)*α|≤1→∀ v∈bulkJointGoodSet α g.f G.J n,
      (k+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖-δ≤
        cavityBulkFullLog k d n (patternCount α (n+1)) g v := by
    apply (eventually_all_finset _).mpr
    intro d _
    by_cases hd : |(d:ℝ)-(k+1:ℕ)*α|≤1
    · exact (hk d hd δ hδ).mono (fun _n hn _=>hn)
    · exact Eventually.of_forall (fun _ h=>False.elim (hd h))
  filter_upwards [h] with n hn
  exact hn _ (Finset.mem_range.mpr (Nat.lt_succ_of_le (cavity_fresh_count hα.le n (k+1)).2.2))
    (cavity_fresh_count hα.le n (k+1)).2.1


def cavityOriginalIncrement (α : ℝ) (f : ℝ→ᵇℝ) (n k : ℕ) (v : ℕ→ℝ) : ℝ :=
  bulkExpectedLog (n+(k+1)) (patternCount α (n+(k+1)+1)) f v-
    bulkExpectedLog n (patternCount α (n+1)) f v

lemma cavity_original_increment_error {α : ℝ} (hα : 0≤α) (k : ℕ) (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ n : ℕ in atTop,∀ v : ℕ→ℝ,(∀ p,|v (p+1)|≤2)→
      Real.log (cavityShellMass k)-α*‖g.dilationMark h1‖/2-δ+
        cavityBulkFullLog k (cavityFreshCount α n (k+1)) n (patternCount α (n+1)) g v≤
      cavityOriginalIncrement α g.f n k v := by
  let KC:=α*‖g.dilationMark h1‖
  let D:=⌈((k+1:ℕ):ℝ)*α+1⌉₊
  let E:=fun n=>cavityUniformError n k (patternCount α (n+1)) D g h1 h2 h3 2 KC
  have hE : Tendsto E atTop (𝓝 0):=cavityUniformError_tendsto k D _ g h1 h2 h3 2 KC (cavity_count_density hα)
  have he:=((cavitySphereLaw_shell_log_tendsto k).sub_const (KC/2)).sub hE
  simp only [sub_zero] at he
  have hev:=he.eventually (Ioi_mem_nhds (show Real.log (cavityShellMass k)-KC/2-δ<
    Real.log (cavityShellMass k)-KC/2 by linarith))
  filter_upwards [hev,cavityShell_probability_eventually k,eventually_ge_atTop (2*((k+1)+1))] with n hn hp hN
  intro v hv
  have hK : (patternCount α (n+1):ℝ)/(n+1:ℕ)*‖g.dilationMark h1‖≤KC := by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (div_le_iff₀ (by positivity : (0:ℝ)<(n+1:ℕ))).mpr (cavity_count_bounds hα (n+1)).2
  have hinc:=cavity_finite_increment_uniform n k (patternCount α (n+1)) (cavityFreshCount α n (k+1)) D
    g h1 h2 h3 (by omega) hp v (by norm_num : (0:ℝ)≤2) hv (cavity_fresh_count hα n (k+1)).2.2 hK
  rw [(cavity_fresh_count hα n (k+1)).1] at hinc
  have heq : n+1+(k+1)=n+(k+1)+1:=by omega
  rw [heq] at hinc
  change _≤cavityOriginalIncrement α g.f n k v at hinc
  dsimp only [E,KC] at hn hinc
  linarith

lemma cavity_original_increment_background {α : ℝ} (hα : 0≤α) (k : ℕ) (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) :
    ∃ A : ℝ,∀ᶠ n : ℕ in atTop,∀ v : ℕ→ℝ,(∀ p,|v (p+1)|≤2)→
      A≤cavityOriginalIncrement α g.f n k v := by
  let KC:=α*‖g.dilationMark h1‖
  let D:=⌈((k+1:ℕ):ℝ)*α+1⌉₊
  refine ⟨Real.log (cavityShellMass k)-KC/2-1-D*‖g.f‖-(k+1:ℕ)*KC/2,?_⟩
  filter_upwards [cavity_original_increment_error hα k g h1 h2 h3 (by norm_num : (0:ℝ)<1)] with n hn
  intro v hv
  have hC : ∀ (a : BulkDisorder (n+1) (patternCount α (n+1))) x,
      |bulkC (n+1) (patternCount α (n+1)) g a.1 x|≤KC := by
    intro a x
    apply (bulkC_bound n _ g h1 a x).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (div_le_iff₀ (by positivity : (0:ℝ)<(n+1:ℕ))).mpr (cavity_count_bounds hα (n+1)).2
  have hlow:=cavityBulkFullLog_lower k (cavityFreshCount α n (k+1)) n _ g h1 v hC
  have hd : (cavityFreshCount α n (k+1):ℝ)≤D := by exact_mod_cast (cavity_fresh_count hα n (k+1)).2.2
  have hdn:=mul_le_mul_of_nonneg_right hd (norm_nonneg g.f)
  have hi:=hn v hv
  dsimp only [KC] at *
  linarith

lemma cavity_original_increment_good (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) {α : ℝ} (hα : 0<α) (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) (G : CavityGoodParameters α g.f)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop,∀ δ : ℝ,0<δ→∀ᶠ n : ℕ in atTop,∀ v∈bulkJointGoodSet α g.f G.J n,
      Real.log (cavityShellMass k)-α*‖g.dilationMark h1‖/2+
        (k+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖-δ≤
      cavityOriginalIncrement α g.f n k v := by
  filter_upwards [cavity_good_fresh_fullLog_lower P hB hα g h1 G ε hε] with k hk
  intro δ hδ
  filter_upwards [hk (δ/2) (by positivity),cavity_original_increment_error hα.le k g h1 h2 h3
    (show 0<δ/2 by positivity)] with n hn he
  intro v hv
  have hv2 : ∀ p,|v (p+1)|≤(2:ℝ) := by
    intro p
    exact abs_le.mpr ⟨by linarith [(hv.2 (p+1)).1],(hv.2 (p+1)).2⟩
  have hlo:=hn v hv
  have hi:=he v hv2
  linarith


lemma bulkExpectedLog_parameter_measurable (n M : ℕ) (f : ℝ→ᵇℝ) :
    Measurable (bulkExpectedLog n M f) := by
  have hm : Measurable (fun p : (ℕ→ℝ)×BulkDisorder (n+1) M=>
      bulkLogPartition n M f p.1 p.2.1 p.2.2) := by
    simp_rw [bulkLogPartition_eq]
    simpa only [tiltPartition,one_mul] using
      (bulkHamiltonian_parameter_continuous (n+1) M f).measurable.exp.stronglyMeasurable.integral_prod_right'.measurable.log
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma bulkExpectedLog_box_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (hv : ∀ p,|v (p+1)|≤2) :
    |bulkExpectedLog n M f v|≤M*‖f‖+2*|bulkScale (n+1)| *
      ∫ a : BulkDisorder (n+1) M,‖a.2‖ ∂bulkDisorderLaw (n+1) M := by
  have hb : bulkFeatureBound (n+1) v≤2*|bulkScale (n+1)| := by
    have hh:=bulkFeatureBound_sq_le (n+1) v (by norm_num : (0:ℝ)≤2) hv
    have hs:=sq_abs (bulkScale (n+1))
    nlinarith [Real.sqrt_nonneg (∑ p,bulkAmplitude (n+1) v p^2),abs_nonneg (bulkScale (n+1))]
  let Q:=bulkDisorderLaw (n+1) M
  have hi : Integrable (fun a : BulkDisorder (n+1) M=>
      M*‖f‖+2*|bulkScale (n+1)| *‖a.2‖) Q :=
    (integrable_const _).add ((bulkMarkNorm_integrable (n+1) M).const_mul _)
  calc
    _≤∫ a : BulkDisorder (n+1) M,|bulkLogPartition n M f v a.1 a.2| ∂Q := abs_integral_le_integral_abs
    _≤∫ a : BulkDisorder (n+1) M,M*‖f‖+2*|bulkScale (n+1)| *‖a.2‖ ∂Q := by
      apply integral_mono ((bulkLogPartition_memLp n M f v).integrable (by norm_num)).abs hi
      intro a
      exact (bulkLogPartition_bound n M f v a).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right hb (norm_nonneg a.2)))
    _=_ := by rw [integral_add (integrable_const _) ((bulkMarkNorm_integrable (n+1) M).const_mul _),integral_const_mul]; simp [integral_const_mul]

lemma bulkExpectedLog_parameter_integrable (n M : ℕ) (f : ℝ→ᵇℝ) :
    Integrable (bulkExpectedLog n M f) bulkParameterLaw := by
  apply Integrable.of_bound (bulkExpectedLog_parameter_measurable n M f).aestronglyMeasurable
    (M*‖f‖+2*|bulkScale (n+1)| *∫ a : BulkDisorder (n+1) M,‖a.2‖ ∂bulkDisorderLaw (n+1) M)
  filter_upwards [bulkParameterLaw_ae] with v hv
  rw [Real.norm_eq_abs]
  exact bulkExpectedLog_box_bound n M f v (fun p=>abs_le.mpr ⟨by linarith [(hv (p+1)).1],(hv (p+1)).2⟩)

def cavityAveragedLog (α : ℝ) (f : ℝ→ᵇℝ) (n : ℕ) : ℝ :=
  ∫ v,bulkExpectedLog n (patternCount α (n+1)) f v ∂bulkParameterLaw

lemma cavityAveragedLog_sub (α : ℝ) (f : ℝ→ᵇℝ) (n k : ℕ) :
    cavityAveragedLog α f (n+(k+1))-cavityAveragedLog α f n=
      ∫ v,cavityOriginalIncrement α f n k v ∂bulkParameterLaw :=
  (integral_sub (bulkExpectedLog_parameter_integrable _ _ f)
    (bulkExpectedLog_parameter_integrable _ _ f)).symm

lemma integral_good_bad_lower {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {F : X→ℝ} (hF : Integrable F μ)
    {s : Set X} (hs : MeasurableSet s) {A B : ℝ}
    (hA : ∀ᵐ x ∂μ,A≤F x) (hB : ∀ x∈s,B≤F x) :
    B+(A-B)*μ.real sᶜ≤∫ x,F x ∂μ := by
  have hi : Integrable (fun x=>B+sᶜ.indicator (fun _=>A-B) x) μ :=
    (integrable_const _).add ((integrable_const _).indicator hs.compl)
  have he : (∫ x,B+sᶜ.indicator (fun _=>A-B) x ∂μ)=B+(A-B)*μ.real sᶜ := by
    rw [integral_add (integrable_const _) ((integrable_const _).indicator hs.compl)]
    simp [integral_indicator_const,hs.compl,smul_eq_mul,mul_comm]
  rw [←he]
  apply integral_mono_ae hi hF
  filter_upwards [hA] with x hx
  by_cases hxs : x∈s
  · simpa [hxs] using hB x hxs
  · simpa [hxs] using hx

lemma cavity_averaged_increment_good (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) {α : ℝ} (hα : 0<α) (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) (G : CavityGoodParameters α g.f)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop,∀ δ : ℝ,0<δ→∀ᶠ n : ℕ in atTop,
      Real.log (cavityShellMass k)-α*‖g.dilationMark h1‖/2+
        (k+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖-δ≤
      cavityAveragedLog α g.f (n+(k+1))-cavityAveragedLog α g.f n := by
  filter_upwards [cavity_original_increment_good P hB hα g h1 h2 h3 G hε] with k hk
  intro δ hδ
  obtain ⟨A,hA⟩:=cavity_original_increment_background hα.le k g h1 h2 h3
  let B:=Real.log (cavityShellMass k)-α*‖g.dilationMark h1‖/2+
    (k+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖-δ/2
  have ht : Tendsto (fun n=>(A-B)*bulkParameterLaw.real (bulkJointGoodSet α g.f G.J n)ᶜ) atTop (𝓝 0) := by
    simpa only [mul_zero] using G.mass.const_mul (A-B)
  have he:=ht.eventually (Ioi_mem_nhds (show -δ/2<0 by linarith))
  filter_upwards [hk (δ/2) (by positivity),hA,he] with n hn ha he
  have hl:=integral_good_bad_lower bulkParameterLaw
    ((bulkExpectedLog_parameter_integrable _ _ g.f).sub (bulkExpectedLog_parameter_integrable _ _ g.f))
    (G.measurable n) (A:=A) (B:=B) (F:=cavityOriginalIncrement α g.f n k)
    (by
      filter_upwards [bulkParameterLaw_ae] with v hv
      exact ha v (fun p=>abs_le.mpr ⟨by linarith [(hv (p+1)).1],(hv (p+1)).2⟩)) hn
  rw [←cavityAveragedLog_sub] at hl
  dsimp only [B] at hl he
  linarith


end SphericalPerceptronFreeEnergy
end

end OAI
