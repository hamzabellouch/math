import Mathlib
import OAI.Probability.Ballisticity.Estimates.RawPairRetention
import OAI.Probability.Ballisticity.Estimates.BufferFirstFailure

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma hitWord_dirac_le_hitKernel {d : ℕ} (ω : Environment d) (x : Lattice d)
    {S T : Set (Lattice d)} (_ : Disjoint S T) (w : HitWord x S T) :
    ENNReal.ofReal (wordWeight ω x w.val) • Measure.dirac (wordPath x w.val w.val.length) ≤
      hitKernel S T (ω,x) := by
  intro U
  have hU := (Set.to_countable U).measurableSet
  rw [Measure.smul_apply,smul_eq_mul]
  by_cases hu : wordPath x w.val w.val.length ∈ U
  · rw [Measure.dirac_apply' _ hU,Set.indicator_of_mem hu,Pi.one_apply,mul_one]
    rw [hitKernel_apply]
    apply le_trans _ (ENNReal.le_tsum w.val.length)
    rw [←quenched_wordCylinder]
    apply measure_mono
    intro X hX
    exact ⟨⟨(hitWord_prefix x S T w hX).1,by simpa only [hX _ le_rfl] using hu⟩,
      (hitWord_prefix x S T w hX).2⟩
  · rw [Measure.dirac_apply' _ hU,Set.indicator_of_notMem hu,mul_zero]
    exact bot_le

lemma elliptic_hitWord_dirac_le_hitKernel {d : ℕ} (ω : Environment d) (x : Lattice d)
    {κ : ℝ≥0} (hκ : ∀ y e, κ ≤ (ω y).1 e)
    {S T : Set (Lattice d)} (hST : Disjoint S T) (w : HitWord x S T) :
    (κ : ℝ≥0∞)^w.val.length • Measure.dirac (wordPath x w.val w.val.length) ≤
      hitKernel S T (ω,x) := by
  have hw := ENNReal.ofReal_le_ofReal (wordWeight_lower ω hκ x w.val)
  simp only [ENNReal.ofReal_pow κ.coe_nonneg,ENNReal.ofReal_coe_nnreal] at hw
  intro U
  exact (mul_le_mul_left hw ((Measure.dirac _) U)).trans ((hitWord_dirac_le_hitKernel ω x hST w) U)

lemma wordPath_lateral_script_end {d : ℕ} (e f : Direction d) (x : Lattice d) (m : ℕ) :
    wordPath x (List.replicate m f ++ [e]) (m+1) = x+m • step f+step e := by
  induction m generalizing x with
  | zero => simp [wordPath]
  | succ m ih =>
    simp only [List.replicate_succ,List.cons_append,wordPath,ih,succ_nsmul]
    abel

lemma wordPath_lateral_script_prefix {d : ℕ} (e f : Direction d) (x : Lattice d)
    (m j : ℕ) (hj : j ≤ m) :
    wordPath x (List.replicate m f ++ [e]) j = x+j • step f := by
  induction m generalizing x j with
  | zero =>
    have : j=0 := by omega
    subst j
    simp
  | succ m ih =>
    cases j with
    | zero => simp
    | succ j =>
      simp only [List.replicate_succ,List.cons_append,wordPath,
        ih (x+step f) j (by omega),succ_nsmul]
      abel

lemma signedHeight_add_nsmul_other {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (x : Lattice d) (m : ℕ) : signedHeight e (x+m • step f)=signedHeight e x := by
  induction m with
  | zero => simp
  | succ m ih => rw [succ_nsmul,←add_assoc,signedHeight_add_step_other e f hef,ih]

noncomputable def bufferRestoreWord {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (x : Lattice d) (m : ℕ) : HitWord x
      (Strip (realPosition (step e)) x 1) (Upper (realPosition (step e)) x 1) := by
  refine ⟨List.replicate m f ++ [e],?_,?_⟩
  · simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil,
      zero_add,wordPath_lateral_script_end]
    change dot (realPosition x) (realPosition (step e))+1 ≤
      dot (realPosition (x+m • step f+step e)) (realPosition (step e))
    simp only [signedHeight_projection,signedHeight_add_step_self,
      signedHeight_add_nsmul_other e f hef,Int.cast_add,Int.cast_one]
    exact le_rfl
  · intro j hj
    have hjm : j ≤ m := by simpa only [List.length_append,List.length_replicate,
      List.length_cons,List.length_nil,zero_add,Nat.lt_succ_iff] using hj
    rw [wordPath_lateral_script_prefix e f x m j hjm]
    change dot (realPosition x) (realPosition (step e)) ≤
      dot (realPosition (x+j • step f)) (realPosition (step e)) ∧
      dot (realPosition (x+j • step f)) (realPosition (step e)) <
      dot (realPosition x) (realPosition (step e))+1
    simp only [signedHeight_projection,signedHeight_add_nsmul_other e f hef]
    exact ⟨le_rfl,by norm_num⟩

lemma elliptic_lateral_script {d : ℕ} (ω : Environment d) (e f : Direction d)
    (hef : e.1 ≠ f.1) (x : Lattice d) (m : ℕ) {κ : ℝ≥0}
    (hκ : ∀ y u, κ ≤ (ω y).1 u) :
    (κ : ℝ≥0∞)^(m+1) • Measure.dirac (x+m • step f+step e) ≤
      hitKernel (Strip (realPosition (step e)) x 1) (Upper (realPosition (step e)) x 1) (ω,x) := by
  have hh := elliptic_hitWord_dirac_le_hitKernel ω x hκ (disjoint_strip_upper _ _ _)
    (bufferRestoreWord e f hef x m)
  simpa only [bufferRestoreWord,List.length_append,List.length_replicate,List.length_cons,
    List.length_nil,zero_add,wordPath_lateral_script_end] using hh
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def pairRestore {d : ℕ} (e f : Direction d) (m : ℕ) (x : Lattice d × Lattice d) :
    Lattice d × Lattice d := (x.1+step e,x.2+m • step f+step e)

lemma pairRestore_gap {d : ℕ} (e f : Direction d) (m : ℕ) (x : Lattice d × Lattice d) :
    signedCoordinate f ((pairRestore e f m x).2-(pairRestore e f m x).1) =
      signedCoordinate f (x.2-x.1)+m := by
  simp only [pairRestore,signedCoordinate_sub,signedCoordinate_add,signedCoordinate_nsmul,
    signedCoordinate_step_self,mul_one]
  ring

lemma pairRestore_height {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (m : ℕ) (a : ℝ) (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a) :
    pairRestore e f m x ∈ PairAtHeight (realPosition (step e)) (a+1) := by
  have h1 := hx.1
  have h2 := hx.2
  simp only [signedHeight_projection] at h1 h2
  constructor
  · change dot (realPosition (x.1+step e)) (realPosition (step e))=a+1
    simp only [signedHeight_projection,signedHeight_add_step_self,Int.cast_add,Int.cast_one,h1]
  · change dot (realPosition (x.2+m • step f+step e)) (realPosition (step e))=a+1
    simp only [signedHeight_projection,signedHeight_add_step_self,
      signedHeight_add_nsmul_other e f hef,Int.cast_add,Int.cast_one,h2]

lemma rawPairEndpointLaw_restoration {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (m : ℕ) (ω : Environment d) (x : Lattice d × Lattice d)
    {κ : ℝ≥0} (hκ : ∀ y u, κ ≤ (ω y).1 u) :
    (κ : ℝ≥0∞)^(m+2) • Measure.dirac (pairRestore e f m x) ≤
      rawPairEndpointLaw (realPosition (step e)) 1 ω x := by
  have h1 := elliptic_lateral_script ω e f hef x.1 0 hκ
  simp only [zero_nsmul,add_zero,zero_add,pow_one] at h1
  have h2 := elliptic_lateral_script ω e f hef x.2 m hκ
  have hfinite (y : Lattice d) : IsFiniteMeasure
      (hitKernel (Strip (realPosition (step e)) y 1) (Upper (realPosition (step e)) y 1) (ω,y)) :=
    ⟨lt_of_le_of_lt (hitKernel_total_le_one (disjoint_strip_upper _ _ _) _) ENNReal.one_lt_top⟩
  let := hfinite x.1
  let := hfinite x.2
  have hh := Measure.prod_mono h1 h2
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,Measure.dirac_prod_dirac] at hh
  have hp : (κ : ℝ≥0∞)*(κ : ℝ≥0∞)^(m+1)=(κ : ℝ≥0∞)^(m+2) := by simpa only [Nat.add_assoc] using (pow_succ' (κ : ℝ≥0∞) (m+1)).symm
  rw [hp] at hh
  simpa only [rawPairEndpointLaw,pairRestore,Nat.cast_one] using hh

noncomputable def bufferRestorationLaw {d : ℕ} (e f : Direction d) (m : ℕ)
    (π : Measure (Lattice d × Lattice d)) (κ : ℝ≥0) : Measure (Lattice d × Lattice d) :=
  (κ : ℝ≥0∞)^(m+2) • π.map (pairRestore e f m)

lemma bufferRestorationLaw_le {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (m : ℕ) (ω : Environment d) (π : Measure (Lattice d × Lattice d))
    {κ : ℝ≥0} (hκ : ∀ y u, κ ≤ (ω y).1 u) :
    bufferRestorationLaw e f m π κ ≤ rawPairMixture (realPosition (step e)) 1 π ω := by
  intro U
  have hU := (Set.to_countable U).measurableSet
  have hm : Measurable (pairRestore e f m) := measurable_of_countable _
  rw [bufferRestorationLaw,Measure.smul_apply,smul_eq_mul,Measure.map_apply hm hU,
    rawPairMixture_apply]
  have he : (κ : ℝ≥0∞)^(m+2)*π ((pairRestore e f m) ⁻¹' U) =
      ∫⁻ x, ((κ : ℝ≥0∞)^(m+2) • Measure.dirac (pairRestore e f m x)) U ∂π := by
    simp only [Measure.smul_apply,smul_eq_mul,Measure.dirac_apply' _ hU]
    rw [lintegral_const_mul _ (measurable_of_countable _)]
    congr 1
    rw [←lintegral_indicator_one (hm hU)]
    apply lintegral_congr
    intro x
    by_cases hx : pairRestore e f m x ∈ U <;> simp [hx]
  rw [he]
  exact lintegral_mono fun x => (rawPairEndpointLaw_restoration e f hef m ω x hκ) U

lemma bufferRestorationLaw_mass {d : ℕ} (e f : Direction d) (m : ℕ)
    (π : Measure (Lattice d × Lattice d)) [IsProbabilityMeasure π] (κ : ℝ≥0) :
    bufferRestorationLaw e f m π κ Set.univ = (κ : ℝ≥0∞)^(m+2) := by
  simp [bufferRestorationLaw,Measure.map_apply (measurable_of_countable _)]

lemma bufferRestorationLaw_support {d : ℕ} (e f : Direction d) (m : ℕ)
    (π : Measure (Lattice d × Lattice d)) (κ : ℝ≥0) (z : ℝ)
    (hπ : ∀ᵐ x ∂π, z ≤ signedCoordinate f (x.2-x.1)) :
    ∀ᵐ x ∂bufferRestorationLaw e f m π κ, z+m ≤ signedCoordinate f (x.2-x.1) := by
  unfold bufferRestorationLaw
  apply Measure.ae_smul_measure
  rw [ae_map_iff (measurable_of_countable _).aemeasurable
    (measurableSet_le measurable_const (measurable_of_countable _))]
  filter_upwards [hπ] with x hx
  rw [pairRestore_gap]
  linarith

lemma bufferRestorationLaw_height {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (m : ℕ) (π : Measure (Lattice d × Lattice d)) (κ : ℝ≥0) (a : ℝ)
    (hπ : ∀ᵐ x ∂π, x ∈ PairAtHeight (realPosition (step e)) a) :
    ∀ᵐ x ∂bufferRestorationLaw e f m π κ, x ∈ PairAtHeight (realPosition (step e)) (a+1) := by
  unfold bufferRestorationLaw
  apply Measure.ae_smul_measure
  rw [ae_map_iff (measurable_of_countable _).aemeasurable (Set.to_countable _).measurableSet]
  filter_upwards [hπ] with x hx
  exact pairRestore_height e f hef m a x hx

lemma bufferRestorationLaw_measurable {d : ℕ} (e f : Direction d) (m : ℕ) (κ : ℝ≥0) :
    Measurable (fun π : Measure (Lattice d × Lattice d) => bufferRestorationLaw e f m π κ) := by
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [bufferRestorationLaw,Measure.smul_apply,smul_eq_mul,
    Measure.map_apply (measurable_of_countable _) hU]
  exact measurable_const.mul (Measure.measurable_coe ((measurable_of_countable _) hU))
end DirectionalTransience

end

end

end OAI
