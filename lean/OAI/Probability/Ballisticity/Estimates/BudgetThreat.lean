import Mathlib
import OAI.Probability.Ballisticity.Estimates.BudgetClipping

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma regularPath_translate_zero {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    {X : Path d} (hX : X ∈ RegularPath ℓ x) :
    (fun n => X n-x) ∈ RegularPath ℓ 0 := by
  refine ⟨by simp only [hX.1,sub_self],?_,?_⟩
  · intro n
    obtain ⟨g,hg⟩ := hX.2.1 n
    refine ⟨g,?_⟩
    dsimp only
    rw [hg]
    abel
  · change X ∈ (fun Z : Path d => fun n => Z n-x) ⁻¹' TransientPaths ℓ
    rw [transientPaths_translation]
    exact hX.2.2

lemma regular_noDrop_hit {d : ℕ} (e : Direction d) (x : Lattice d)
    {X : Path d} (hX : X ∈ RegularPath (realPosition (step e)) x)
    (hD : X ∈ NoDrop (realPosition (step e)) x) (H : ℕ) :
    X ∈ Hit (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) := by
  by_cases hH : H=0
  · subst H
    exact Set.mem_iUnion.mpr ⟨0,⟨by simp [Upper,hX.1],fun i hi => by omega⟩⟩
  · have hY := regularPath_translate_zero _ x hX
    obtain ⟨n,hn⟩ := noDrop_firstLayerHit_exists e (fun n => X n-x)
      hY.1 hY.2.1 hY.2.2 (Nat.pos_of_ne_zero hH)
    apply Set.mem_iUnion.mpr
    refine ⟨n,⟨?_,?_⟩⟩
    · change dot (realPosition x) (realPosition (step e))+(H:ℝ) ≤
        dot (realPosition (X n)) (realPosition (step e))
      rw [signedHeight_projection,signedHeight_projection]
      have hh := hn.1
      simp only [signedHeight_sub'] at hh
      exact_mod_cast (show signedHeight e x+(H:ℤ) ≤ signedHeight e (X n) by omega)
    · intro i hi
      refine ⟨hD i,?_⟩
      rw [signedHeight_projection,signedHeight_projection]
      have hh := hn.2 i hi
      simp only [signedHeight_sub'] at hh
      exact_mod_cast (show signedHeight e (X i) < signedHeight e x+(H:ℤ) by omega)

lemma regular_noDrop_word_record {d : ℕ} (e : Direction d) (x : Lattice d)
    {X : Path d} (hX : X ∈ RegularPath (realPosition (step e)) x)
    (hD : X ∈ NoDrop (realPosition (step e)) x) (H s : ℕ) (hs : s ≤ H)
    (w : HitWord x (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H))
    (hw : X ∈ wordCylinder x w.val) :
    wordFirstHitPosition e x s w.val-x =
      recordIndexPosition (realPosition (step e)) s (fun n => X n-x) := by
  by_cases hs0 : s=0
  · subst s
    simp only [wordFirstHitPosition,wordFirstHitTime_zero,wordPath_zero,
      sub_self,recordIndexPosition,recordIndexTime_zero,hX.1]
  · have hY := regularPath_translate_zero _ x hX
    have hYD : (fun n => X n-x) ∈ NoDrop (realPosition (step e)) 0 := by
      change X ∈ (fun Z : Path d => fun n => Z n-x) ⁻¹' NoDrop _ 0
      rwa [noDrop_translation,add_zero]
    obtain ⟨n,hn⟩ := noDrop_firstLayerHit_exists e (fun n => X n-x)
      hY.1 hY.2.1 hY.2.2 (Nat.pos_of_ne_zero hs0)
    have hnlen : n ≤ w.val.length := by
      by_contra! hgt
      have hh := hn.2 _ hgt
      dsimp only at hh
      rw [hw _ le_rfl,signedHeight_sub',wordPath_hit_exact] at hh
      omega
    have hrec := firstLayerHit_recordPrefix e (fun n => X n-x) hY.1 hYD
      hY.2.1 (Nat.pos_of_ne_zero hs0) hn
    have ht := recordOrZeroPrefix_wordFirstHit e x X hX.1 hX.2.1 w.val hw s n hnlen
      (by simpa only [RecordOrZeroPrefix,ite_eq_right hs0] using hrec)
    simp only [wordFirstHitPosition,ht,recordIndexPosition,
      firstLayerHit_recordIndexTime e _ hY.1 hYD hY.2.1 (Nat.pos_of_ne_zero hs0) hn,
      hw n hnlen]

def WordEnvelope {d : ℕ} (e f : Direction d) (x : Lattice d)
    (H : ℕ) (b : ℕ → ℝ) (z : ℝ) (w : List (Direction d)) : Prop :=
  ∀ s ≤ H, |relativeWordDisplacement e f x s w-b s| ≤ z

lemma good_noDrop_le_WordEnvelope {d : ℕ} (e f : Direction d) (x : Lattice d)
    (ω : Environment d) (hreg : ∀ᵐ X ∂quenchedKernel (ω,x), X ∈ RegularPath (realPosition (step e)) x)
    (H h : ℕ) (hh : h ≤ H) (b : ℕ → ℝ) (z : ℝ) :
    relativeGoodMass (realPosition (step e)) (MedianTubeFailure (realPosition (step e)) f b H z) ω x ≤
      (rawWordLaw (realPosition (step e)) h ω x).real {w | WordEnvelope e f x h b z w} := by
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  rw [rawWordLaw,Measure.map_apply measurable_subtype_coe (Set.to_countable _).measurableSet,
    successfulWordLaw_event ω x _ _ (disjoint_strip_upper _ _ _)]
  apply measure_mono_ae
  filter_upwards [hreg] with X hX
  intro hgood
  obtain ⟨w,hw⟩ := (hitWord_cover x _ _ X hX.1 hX.2.1).mp (regular_noDrop_hit e x hX hgood.2 h)
  refine Set.mem_iUnion.mpr ⟨⟨w,?_⟩,hw⟩
  intro s hs
  change |signedCoordinate f (wordFirstHitPosition e x s w.val-x)- b s| ≤ z
  rw [regular_noDrop_word_record e x hX hgood.2 h s hs w hw]
  exact le_of_not_gt fun hbad => hgood.1 ⟨s,hs.trans hh,hbad⟩

lemma tupleEnvelope_budget {d k : ℕ} (e f : Direction d) (x : Fin k → Lattice d)
    (H : ℕ) (b : ℕ → ℝ) (z : ℝ) (w : Fin k → List (Direction d))
    (hw : ∀ j, WordEnvelope e f (x j) H b z (w j)) :
    TupleRelativeBudget e f x H (2*z) w := by
  intro s hs i j
  calc
    _ = |(relativeWordDisplacement e f (x i) s (w i)-b s)-
      (relativeWordDisplacement e f (x j) s (w j)-b s)| := by congr 1; ring
    _ ≤ _ := (abs_sub _ _).trans (by linarith [hw i s hs,hw j s hs])

lemma tupleGood_le_relativeBudget {d k : ℕ} (e f : Direction d)
    (ω : Environment d) (hreg : ∀ x, ∀ᵐ X ∂quenchedKernel (ω,x), X ∈ RegularPath (realPosition (step e)) x)
    (H h : ℕ) (hh : h ≤ H) (b : ℕ → ℝ) (z : ℝ) (x : Fin k → Lattice d) :
    (∏ j, relativeGoodMass (realPosition (step e)) (MedianTubeFailure (realPosition (step e)) f b H z) ω (x j)) ≤
      (relativeBudgetWordLaw e f h (2*z) ω x).real Set.univ := by
  calc
    _ ≤ ∏ j, (rawWordLaw (realPosition (step e)) h ω (x j)).real
        {w | WordEnvelope e f (x j) h b z w} :=
      Finset.prod_le_prod₀ (fun _ _ => measureReal_nonneg)
        (fun j _ => good_noDrop_le_WordEnvelope e f (x j) ω (hreg _) H h hh b z)
    _ = (rawTupleWordLaw (realPosition (step e)) h ω x).real
        {w | ∀ j, WordEnvelope e f (x j) h b z (w j)} := by
      have he := Measure.pi_pi (fun j => rawWordLaw (realPosition (step e)) h ω (x j))
        (fun j => {w | WordEnvelope e f (x j) h b z w})
      have hr := congrArg ENNReal.toReal he
      simpa only [rawTupleWordLaw,Set.pi,Set.mem_univ,forall_true_left,Set.mem_ofPred,
        ENNReal.toReal_prod,Measure.real] using hr.symm
    _ ≤ _ := by
      rw [relativeBudgetWordLaw,measureReal_restrict_apply MeasurableSet.univ,Set.univ_inter]
      exact measureReal_mono fun w hw => tupleEnvelope_budget e f x h b z w hw

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def relativeBadMass {d : ℕ} (ℓ : Vector d) (A : Set (Path d))
    (ω : Environment d) (x : Lattice d) : ℝ := relativeGoodMass ℓ Aᶜ ω x

lemma relativeBadMass_eq {d : ℕ} (ℓ : Vector d) (A : Set (Path d))
    (ω : Environment d) (x : Lattice d) : relativeBadMass ℓ A ω x =
      (quenchedKernel (ω,x)).real (((fun X : Path d => fun n => X n-x) ⁻¹' A) ∩ NoDrop ℓ x) := by
  simp only [relativeBadMass,relativeGoodMass,compl_compl]

lemma good_add_bad_noDrop {d : ℕ} (ℓ : Vector d) (A : Set (Path d)) (hA : MeasurableSet A)
    (ω : Environment d) (x : Lattice d) :
    relativeGoodMass ℓ A ω x + relativeBadMass ℓ A ω x = (noDropQuenched ℓ x ω).toReal := by
  have ht : MeasurableSet ((fun X : Path d => fun n => X n-x) ⁻¹' A) := hA.preimage (by fun_prop)
  have he : NoDrop ℓ x \ ((fun X : Path d => fun n => X n-x) ⁻¹' A) =
      ((fun X : Path d => fun n => X n-x) ⁻¹' Aᶜ) ∩ NoDrop ℓ x := by
    ext X
    change (X ∈ NoDrop ℓ x ∧ ¬ (fun n => X n-x) ∈ A) ↔
      (¬ (fun n => X n-x) ∈ A) ∧ X ∈ NoDrop ℓ x
    tauto
  simpa only [relativeGoodMass,relativeBadMass_eq,noDropQuenched,he,
    Set.inter_comm,Measure.real] using
      (measureReal_sdiff_add_inter (μ := quenchedKernel (ω,x)) (s := NoDrop ℓ x) ht)

lemma relativeBadMass_nonneg {d : ℕ} (ℓ : Vector d) (A : Set (Path d))
    (ω : Environment d) (x : Lattice d) : 0 ≤ relativeBadMass ℓ A ω x := measureReal_nonneg

lemma relativeBadMass_le_one {d : ℕ} (ℓ : Vector d) (A : Set (Path d))
    (ω : Environment d) (x : Lattice d) : relativeBadMass ℓ A ω x ≤ 1 := measureReal_le_one

lemma relativeGoodMass_le_noDrop {d : ℕ} (ℓ : Vector d) (A : Set (Path d))
    (ω : Environment d) (x : Lattice d) : relativeGoodMass ℓ A ω x ≤ (noDropQuenched ℓ x ω).toReal :=
  measureReal_mono Set.inter_subset_right

lemma measurable_relativeBadMass {d : ℕ} (ℓ : Vector d) (A : Set (Path d)) (hA : MeasurableSet A) :
    Measurable (Function.uncurry (relativeBadMass ℓ A)) := measurable_relativeGoodMass ℓ Aᶜ hA.compl

lemma relativeBadMass_mean {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (A : Set (Path d)) (hA : MeasurableSet A) (x : Lattice d) :
    (∫ ω, relativeBadMass ℓ A ω x ∂environmentLaw ν) = (annealedLaw ν).real (A ∩ NoDrop ℓ 0) := by
  let F : Environment d → ℝ := fun ω => (quenchedKernel (ω,0)).real (A ∩ NoDrop ℓ 0)
  have hF : Measurable F := ((Kernel.measurable_coe quenchedKernel
    (hA.inter (measurableSet_noDrop ℓ 0))).comp (measurable_id.prodMk measurable_const)).ennreal_toReal
  have he (ω : Environment d) : relativeBadMass ℓ A ω x = F (fun y => ω (x+y)) := by
    simpa only [relativeBadMass,F,compl_compl] using relativeGoodMass_translation ℓ Aᶜ hA.compl ω x
  simp_rw [he]
  have hm : Measurable (fun ω : Environment d => fun y => ω (x+y)) := by fun_prop
  rw [← integral_map hm.aemeasurable hF.aestronglyMeasurable,environment_translation]
  change (∫ ω, (quenchedKernel (ω,0) (A ∩ NoDrop ℓ 0)).toReal ∂environmentLaw ν) = _
  rw [Measure.real,annealed_apply ν (hA.inter (measurableSet_noDrop ℓ 0))]
  exact integral_toReal ((Kernel.measurable_coe quenchedKernel (hA.inter (measurableSet_noDrop ℓ 0))).comp
    (measurable_id.prodMk measurable_const)).aemeasurable (ae_of_all _ fun _ => measure_lt_top _ _)

noncomputable def tupleBadMass {d k : ℕ} (ℓ : Vector d) (A : Set (Path d))
    (π : Measure (Fin k → Lattice d)) (ω : Environment d) : ℝ :=
  ∫ x, ∑ j, relativeBadMass ℓ A ω (x j) ∂π

lemma measurable_sum_relativeBadMass {d k : ℕ} (ℓ : Vector d) (A : Set (Path d)) (hA : MeasurableSet A) :
    Measurable (fun p : Environment d × (Fin k → Lattice d) => ∑ j, relativeBadMass ℓ A p.1 (p.2 j)) := by
  apply Finset.measurable_sum
  intro j _
  exact (measurable_relativeBadMass ℓ A hA).comp
    (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))

lemma sum_relativeBadMass_bounds {d k : ℕ} (ℓ : Vector d) (A : Set (Path d))
    (ω : Environment d) (x : Fin k → Lattice d) :
    0 ≤ ∑ j, relativeBadMass ℓ A ω (x j) ∧ ∑ j, relativeBadMass ℓ A ω (x j) ≤ k := by
  exact ⟨Finset.sum_nonneg (fun _ _ => relativeBadMass_nonneg _ _ _ _),
    (Finset.sum_le_sum (fun _ _ => relativeBadMass_le_one _ _ _ _)).trans_eq (by simp)⟩

lemma tupleBadMass_nonneg {d k : ℕ} (ℓ : Vector d) (A : Set (Path d))
    (π : Measure (Fin k → Lattice d)) (ω : Environment d) : 0 ≤ tupleBadMass ℓ A π ω :=
  integral_nonneg fun x => (sum_relativeBadMass_bounds ℓ A ω x).1

lemma measurable_tupleBadMass {d k : ℕ} (ℓ : Vector d) (A : Set (Path d)) (hA : MeasurableSet A)
    (π : Measure (Fin k → Lattice d)) [IsFiniteMeasure π] : Measurable (tupleBadMass ℓ A π) :=
  (measurable_sum_relativeBadMass ℓ A hA).stronglyMeasurable.integral_prod_right'.measurable

lemma integrable_sum_relativeBadMass {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (A : Set (Path d)) (hA : MeasurableSet A)
    (π : Measure (Fin k → Lattice d)) [IsFiniteMeasure π] :
    Integrable (fun p : Environment d × (Fin k → Lattice d) => ∑ j, relativeBadMass ℓ A p.1 (p.2 j))
      ((environmentLaw ν).prod π) := by
  apply (integrable_const (k:ℝ)).mono' (measurable_sum_relativeBadMass ℓ A hA).aestronglyMeasurable
  exact ae_of_all _ fun p => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sum_relativeBadMass_bounds ℓ A p.1 p.2).1]
    exact (sum_relativeBadMass_bounds ℓ A p.1 p.2).2

lemma tupleBadMass_mean {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (A : Set (Path d)) (hA : MeasurableSet A)
    (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π] :
    (∫ ω, tupleBadMass ℓ A π ω ∂environmentLaw ν) = (k:ℝ)*(annealedLaw ν).real (A ∩ NoDrop ℓ 0) := by
  change (∫ ω, ∫ x, ∑ j, relativeBadMass ℓ A ω (x j) ∂π ∂environmentLaw ν) = _
  rw [integral_integral_swap (integrable_sum_relativeBadMass ν ℓ A hA π)]
  have he (x : Fin k → Lattice d) :
      (∫ ω, ∑ j, relativeBadMass ℓ A ω (x j) ∂environmentLaw ν) =
        (k:ℝ)*(annealedLaw ν).real (A ∩ NoDrop ℓ 0) := by
    rw [integral_finsetSum]
    · simp only [relativeBadMass_mean ν ℓ A hA]
      simp
    · intro j _
      apply (integrable_const (1:ℝ)).mono'
        ((measurable_relativeBadMass ℓ A hA).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      exact ae_of_all _ fun ω => by
        change ‖relativeBadMass ℓ A ω (x j)‖ ≤ 1
        rw [Real.norm_eq_abs,abs_of_nonneg (relativeBadMass_nonneg _ _ _ _)]
        exact relativeBadMass_le_one _ _ _ _
  simp_rw [he]
  simp

lemma product_noDrop_le_good_bad {d k : ℕ} (ℓ : Vector d) (A : Set (Path d)) (hA : MeasurableSet A)
    (ω : Environment d) (x : Fin k → Lattice d) :
    noDropProduct ℓ x ω ≤ (∏ j, relativeGoodMass ℓ A ω (x j)) +
      ∑ j, relativeBadMass ℓ A ω (x j) := by
  have hh := prod_difference_bound Finset.univ
    (fun j : Fin k => (noDropQuenched ℓ (x j) ω).toReal)
    (fun j => relativeGoodMass ℓ A ω (x j)) le_rfl
    (fun j _ => ⟨measureReal_nonneg,relativeGoodMass_le_noDrop _ _ _ _,
      noDropQuenched_toReal_le_one _ _ _⟩)
  have he (j : Fin k) : (noDropQuenched ℓ (x j) ω).toReal-relativeGoodMass ℓ A ω (x j) =
      relativeBadMass ℓ A ω (x j) := by linarith [good_add_bad_noDrop ℓ A hA ω (x j)]
  simpa only [noDropProduct,one_pow,one_mul,he] using hh

end DirectionalTransience

end

end OAI
