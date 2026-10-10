import Mathlib
import OAI.Probability.JammingConcavity.StableLawScaling

namespace OAI

/-! Cloud Counting Decomposition. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def cloudShift {A : Type*} (n : ℕ) (z : ℝ × A) : ℝ × A := ((n:ℝ)+z.1,z.2)

lemma measurable_cloudShift {A : Type*} [MeasurableSpace A] (n : ℕ) :
    Measurable (@cloudShift A n) := by fun_prop [cloudShift]

def cloudBinMeasure {A : Type*} [MeasurableSpace A] (n : ℕ) (b : PoissonBin (ℝ × A)) :
    Measure (ℝ × A) := (poissonBinMeasure b).map (cloudShift n)

lemma measurable_cloudBinMeasure {A : Type*} [MeasurableSpace A] (n : ℕ) :
    Measurable (@cloudBinMeasure A _ n) :=
  (Measure.measurable_map _ (measurable_cloudShift n)).comp measurable_poissonBinMeasure

lemma poissonBinMeasure_eq_sum {X : Type*} [MeasurableSpace X] (b : PoissonBin X) :
    poissonBinMeasure b = Measure.sum (fun j : ℕ => if j < b.1 then Measure.dirac (b.2 j) else 0) := by
  classical
  ext s hs
  rw [Measure.sum_apply _ hs]
  simp only [poissonBinMeasure, finiteCounting, Measure.finsetSum_apply, Measure.dirac_apply' _ hs]
  have h := tsum_eq_sum (L := .unconditional ℕ) (s := Finset.range b.1)
    (f := fun j : ℕ => (if j < b.1 then Measure.dirac (b.2 j) else 0) s) (by
      intro j hj
      simp only [Finset.mem_range, not_lt] at hj
      simp [not_lt.mpr hj])
  rw [h]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => s.indicator 1 (b.2 j)) b.1]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  simp [hj, Measure.dirac_apply' _ hs]

lemma cloudBinMeasure_eq_sum {A : Type*} [MeasurableSpace A] (n : ℕ) (b : PoissonBin (ℝ × A)) :
    cloudBinMeasure n b = Measure.sum (fun j : ℕ =>
      if j < b.1 then Measure.dirac (cloudShift n (b.2 j)) else 0) := by
  unfold cloudBinMeasure
  rw [poissonBinMeasure_eq_sum, Measure.map_sum (measurable_cloudShift n).aemeasurable]
  congr 1
  funext j
  split_ifs
  · exact Measure.map_dirac' (measurable_cloudShift n) _
  · exact Measure.map_zero _

lemma pointCloudMeasure_bins {A : Type*} [MeasurableSpace A] (ω : PointCloud A) :
    pointCloudMeasure ω = Measure.sum (fun n => cloudBinMeasure n (ω n)) := by
  simp only [cloudBinMeasure_eq_sum]
  rfl

def pointCloudRest {A : Type*} [MeasurableSpace A] (n : ℕ) (ω : PointCloud A) : Measure (ℝ × A) :=
  Measure.sum (fun i : ℕ => if i = n then 0 else cloudBinMeasure i (ω i))

lemma measurable_pointCloudRest {A : Type*} [MeasurableSpace A] (n : ℕ) :
    Measurable (@pointCloudRest A _ n) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [pointCloudRest, Measure.sum_apply _ hs]
  apply Measurable.tsum
  intro i
  by_cases hi : i = n
  · simp only [hi, ite_true]; exact measurable_const
  · simp only [hi, ite_false]
    exact (Measure.measurable_coe hs).comp ((measurable_cloudBinMeasure i).comp (measurable_pi_apply i))

lemma pointCloudMeasure_split {A : Type*} [MeasurableSpace A] (n : ℕ) (ω : PointCloud A) :
    pointCloudMeasure ω = cloudBinMeasure n (ω n) + pointCloudRest n ω := by
  ext s hs
  rw [pointCloudMeasure_bins, Measure.sum_apply _ hs, Measure.add_apply,
    pointCloudRest, Measure.sum_apply _ hs, ENNReal.tsum_eq_add_tsum_ite n]
  congr 1
  apply tsum_congr
  intro i
  split_ifs <;> rfl

lemma pointCloudMeasure_update {A : Type*} [MeasurableSpace A] (n : ℕ)
    (ω : PointCloud A) (b : PoissonBin (ℝ × A)) :
    pointCloudMeasure (Function.update ω n b) = cloudBinMeasure n b + pointCloudRest n ω := by
  rw [pointCloudMeasure_split n, Function.update_self]
  congr 1
  unfold pointCloudRest
  congr 1
  funext i
  by_cases hi : i = n
  · simp [hi]
  · simp [hi]

lemma measurable_cloudBin_functional {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (n : ℕ) {b : B → PoissonBin (ℝ × A)} (hb : Measurable b)
    {F : B × (ℝ × A) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun a => ∫⁻ z, F (a,z) ∂cloudBinMeasure n (b a)) := by
  have he (a : B) : (∫⁻ z, F (a,z) ∂cloudBinMeasure n (b a)) =
      ∫⁻ z, F (a,cloudShift n z) ∂poissonBinMeasure (b a) :=
    lintegral_map (hF.comp (measurable_const.prodMk measurable_id)) (measurable_cloudShift n)
  simp_rw [he]
  exact measurable_bin_functional hb (hF.comp (measurable_fst.prodMk
    ((measurable_cloudShift n).comp measurable_snd)))

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming
lemma measurable_iid_update {B : Type*} [MeasurableSpace B] (p : ℕ) :
    Measurable (fun z : (ℕ → B) × B => Function.update z.1 p z.2) := by
  apply Measurable.of_eval
  intro j
  by_cases hj : j = p
  · subst j; simpa only [Function.update_self] using (measurable_snd : Measurable (Prod.snd : (ℕ → B) × B → B))
  · simpa only [Function.update_of_ne hj, Function.comp_def] using (measurable_pi_apply j).comp (measurable_fst : Measurable (Prod.fst : (ℕ → B) × B → (ℕ → B)))

lemma iid_update_preserving {B : Type*} [MeasurableSpace B] (ν : Measure B)
    [IsProbabilityMeasure ν] (p : ℕ) :
    MeasurePreserving (fun z : (ℕ → B) × B => Function.update z.1 p z.2)
      ((Measure.infinitePi (fun _ : ℕ => ν)).prod ν) (Measure.infinitePi (fun _ : ℕ => ν)) := by
  refine ⟨measurable_iid_update p, ?_⟩
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.map_apply (measurable_iid_update p) (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  classical
  by_cases hp : p ∈ s
  · have he : (fun z : (ℕ → B) × B => Function.update z.1 p z.2) ⁻¹' Set.pi (s : Set ℕ) t =
        (Set.pi ((s.erase p : Finset ℕ) : Set ℕ) t) ×ˢ t p := by
      ext z
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_erase]
      constructor
      · intro h
        exact ⟨fun j hj => by simpa only [Function.update_of_ne hj.1] using h j (by tauto),
          by simpa only [Function.update_self] using h p hp⟩
      · rintro ⟨hc, hv⟩ j hj
        by_cases hjp : j = p
        · subst j; simpa only [Function.update_self] using hv
        · simpa only [Function.update_of_ne hjp] using hc j ⟨hjp, hj⟩
    rw [he, Measure.prod_prod]
    rw [Measure.infinitePi_pi _ (fun i _ => ht i)]
    exact Finset.prod_erase_mul _ _ hp
  · have he : (fun z : (ℕ → B) × B => Function.update z.1 p z.2) ⁻¹' Set.pi (s : Set ℕ) t =
        (Set.pi (s : Set ℕ) t) ×ˢ (Set.univ : Set B) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Set.mem_univ, and_true]
      apply forall_congr'
      intro j
      by_cases hj : j ∈ s
      · have hjp : j ≠ p := by intro h; subst j; exact hp hj
        simp only [Function.update_of_ne hjp]
      · simp only [hj, false_implies]
    rw [he, Measure.prod_prod, measure_univ, mul_one]
    exact Measure.infinitePi_pi _ (fun i _ => ht i)

lemma lintegral_iid_refresh {B : Type*} [MeasurableSpace B] (ν : Measure B)
    [IsProbabilityMeasure ν] {f : (ℕ → B) → ℝ≥0∞} (hf : Measurable f) (p : ℕ) :
    (∫⁻ ω, ∫⁻ b, f (Function.update ω p b) ∂ν ∂Measure.infinitePi (fun _ : ℕ => ν)) =
      ∫⁻ ω, f ω ∂Measure.infinitePi (fun _ : ℕ => ν) := by
  rw [← lintegral_prod (fun z : (ℕ → B) × B => f (Function.update z.1 p z.2))
    (hf.comp (measurable_iid_update p)).aemeasurable]
  exact (iid_update_preserving ν p).lintegral_comp hf

end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma cloud_bin_campbell {A : Type*} [MeasurableSpace A] (ν : Measure A)
    [IsProbabilityMeasure ν] (n : ℕ) (R : Measure (ℝ × A))
    {F : (ℝ × A) × Measure (ℝ × A) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ b, ∫⁻ z, F (z,cloudBinMeasure n b + R) ∂cloudBinMeasure n b
      ∂poissonBinLaw (cloudUniform.prod ν)) =
      ∫⁻ z, ∫⁻ b, F (cloudShift n z, Measure.dirac (cloudShift n z) + cloudBinMeasure n b + R)
        ∂poissonBinLaw (cloudUniform.prod ν) ∂cloudUniform.prod ν := by
  let G : (ℝ × A) × Measure (ℝ × A) → ℝ≥0∞ :=
    fun z => F (cloudShift n z.1,z.2.map (cloudShift n) + R)
  have hG : Measurable G := hF.comp (((measurable_cloudShift n).comp measurable_fst).prodMk
    (((Measure.measurable_map _ (measurable_cloudShift n)).comp measurable_snd).add measurable_const))
  have he (b : PoissonBin (ℝ × A)) :
      (∫⁻ z, F (z,cloudBinMeasure n b + R) ∂cloudBinMeasure n b) =
        ∫⁻ z, G (z,poissonBinMeasure b) ∂poissonBinMeasure b :=
    lintegral_map (hF.comp (measurable_id.prodMk measurable_const)) (measurable_cloudShift n)
  simp_rw [he]
  rw [poisson_bin_campbell _ hG]
  apply lintegral_congr
  intro z
  apply lintegral_congr
  intro b
  dsimp [G, cloudBinMeasure]
  rw [Measure.map_add _ _ (measurable_cloudShift n), Measure.map_dirac' (measurable_cloudShift n)]

lemma cloud_campbell_one_bin {A : Type*} [MeasurableSpace A] (ν : Measure A)
    [IsProbabilityMeasure ν] (n : ℕ)
    {F : (ℝ × A) × Measure (ℝ × A) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ω, ∫⁻ z, F (z,pointCloudMeasure ω) ∂cloudBinMeasure n (ω n) ∂pointCloudLaw ν) =
      ∫⁻ z, ∫⁻ ω, F (cloudShift n z, Measure.dirac (cloudShift n z) + pointCloudMeasure ω)
        ∂pointCloudLaw ν ∂cloudUniform.prod ν := by
  let μ := cloudUniform.prod ν
  let σ := poissonBinLaw μ
  have hL : Measurable (fun ω : PointCloud A => ∫⁻ z, F (z,pointCloudMeasure ω)
      ∂cloudBinMeasure n (ω n)) :=
    measurable_cloudBin_functional n (measurable_pi_apply n)
      (hF.comp (measurable_snd.prodMk (measurable_pointCloudMeasure.comp measurable_fst)))
  have href := lintegral_iid_refresh σ hL n
  change (∫⁻ ω, ∫⁻ b, ∫⁻ z, F (z,pointCloudMeasure (Function.update ω n b))
    ∂cloudBinMeasure n ((Function.update ω n b) n) ∂σ ∂pointCloudLaw ν) =
      (∫⁻ ω, ∫⁻ z, F (z,pointCloudMeasure ω) ∂cloudBinMeasure n (ω n) ∂pointCloudLaw ν) at href
  rw [← href]
  simp_rw [pointCloudMeasure_update, Function.update_self]
  have hb (ω : PointCloud A) :
      (∫⁻ b, ∫⁻ z, F (z,cloudBinMeasure n b + pointCloudRest n ω) ∂cloudBinMeasure n b ∂σ) =
      ∫⁻ z, ∫⁻ b, F (cloudShift n z,
        Measure.dirac (cloudShift n z) + cloudBinMeasure n b + pointCloudRest n ω) ∂σ ∂μ :=
    cloud_bin_campbell ν n _ hF
  simp_rw [hb]
  have hM : Measurable (fun w : PointCloud A × (ℝ × A) =>
      ∫⁻ b, F (cloudShift n w.2,Measure.dirac (cloudShift n w.2) + cloudBinMeasure n b + pointCloudRest n w.1) ∂σ) := by
    have h : Measurable (fun v : (PointCloud A × (ℝ × A)) × PoissonBin (ℝ × A) =>
      F (cloudShift n v.1.2, Measure.dirac (cloudShift n v.1.2) + cloudBinMeasure n v.2 + pointCloudRest n v.1.1)) :=
      hF.comp (((measurable_cloudShift n).comp measurable_fst.snd).prodMk
        (((Measure.measurable_dirac.comp ((measurable_cloudShift n).comp measurable_fst.snd)).add
          ((measurable_cloudBinMeasure n).comp measurable_snd)).add
          ((measurable_pointCloudRest n).comp measurable_fst.fst)))
    exact h.lintegral_prod_right'
  rw [lintegral_lintegral_swap hM.aemeasurable]
  apply lintegral_congr
  intro z
  have hZ : Measurable (fun ω : PointCloud A =>
      F (cloudShift n z,Measure.dirac (cloudShift n z) + pointCloudMeasure ω)) :=
    hF.comp (measurable_const.prodMk (measurable_const.add measurable_pointCloudMeasure))
  have hz := lintegral_iid_refresh σ hZ n
  simp only [pointCloudMeasure_update, ← add_assoc] at hz
  exact hz

theorem pointCloudCampbell : PointCloudCampbellStatement := by
  intro A mA ν hν F hF
  let := hν
  have hL (n : ℕ) : Measurable (fun ω : PointCloud A => ∫⁻ z, F (z,pointCloudMeasure ω)
      ∂cloudBinMeasure n (ω n)) :=
    measurable_cloudBin_functional n (measurable_pi_apply n)
      (hF.comp (measurable_snd.prodMk (measurable_pointCloudMeasure.comp measurable_fst)))
  have he (ω : PointCloud A) : (∫⁻ z, F (z,pointCloudMeasure ω) ∂pointCloudMeasure ω) =
      ∑' n, ∫⁻ z, F (z,pointCloudMeasure ω) ∂cloudBinMeasure n (ω n) := by
    rw [pointCloudMeasure_bins ω]
    exact lintegral_sum_measure _ _
  simp_rw [he]
  rw [lintegral_tsum (fun n => (hL n).aemeasurable)]
  simp_rw [cloud_campbell_one_bin ν _ hF]
  let g : ℝ × A → ℝ≥0∞ := fun z =>
    ∫⁻ ω, F (z,Measure.dirac z + pointCloudMeasure ω) ∂pointCloudLaw ν
  have hg : Measurable g := by
    have h : Measurable (fun w : (ℝ × A) × PointCloud A => F (w.1,
        Measure.dirac w.1 + pointCloudMeasure w.2)) := hF.comp (measurable_fst.prodMk
          ((Measure.measurable_dirac.comp measurable_fst).add
            (measurable_pointCloudMeasure.comp measurable_snd)))
    exact h.lintegral_prod_right'
  change (∑' n, ∫⁻ z, g (cloudShift n z) ∂cloudUniform.prod ν) =
    ∫⁻ z, g z ∂(volume.restrict (Set.Ioi 0)).prod ν
  have hn (n : ℕ) : (∫⁻ z, g (cloudShift n z) ∂cloudUniform.prod ν) =
      ∫⁻ u in Set.Ico (0:ℝ) 1, ∫⁻ a, g ((n:ℝ)+u,a) ∂ν :=
    lintegral_prod _ (hg.comp (measurable_cloudShift n)).aemeasurable
  simp_rw [hn]
  rw [lintegral_prod _ hg.aemeasurable]
  exact tsum_lintegral_unit_shifts hg.lintegral_prod_right'

end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def cloudFiniteWeight {A : Type*} (z : ℝ × A) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-z.1))

lemma measurable_cloudFiniteWeight {A : Type*} [MeasurableSpace A] :
    Measurable (@cloudFiniteWeight A) := by fun_prop [cloudFiniteWeight]

lemma cloudFiniteWeight_ne_zero {A : Type*} (z : ℝ × A) : cloudFiniteWeight z ≠ 0 :=
  (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

lemma cloudFiniteWeight_ne_top {A : Type*} (z : ℝ × A) : cloudFiniteWeight z ≠ ∞ :=
  ENNReal.ofReal_ne_top

lemma cloud_intensity_weight {A : Type*} [MeasurableSpace A] (ν : Measure A)
    [IsProbabilityMeasure ν] :
    (∫⁻ z, cloudFiniteWeight z ∂(volume.restrict (Set.Ioi 0)).prod ν) = 1 := by
  rw [lintegral_prod _ measurable_cloudFiniteWeight.aemeasurable]
  simp only [cloudFiniteWeight, lintegral_const, measure_univ, mul_one]
  rw [← ofReal_integral_eq_lintegral_ofReal (by
    exact (integrableOn_exp_neg_Ioi 0)) (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le),
    integral_exp_neg_Ioi_zero, ENNReal.ofReal_one]

lemma cloud_weightedMass_ae_finite {A : Type} [MeasurableSpace A] (ν : Measure A)
    [IsProbabilityMeasure ν] :
    ∀ᵐ ω ∂pointCloudLaw ν, weightedMass cloudFiniteWeight (pointCloudMeasure ω) ≠ ∞ := by
  have h := pointCloudCampbell A inferInstance ν inferInstance
    (fun z => cloudFiniteWeight z.1) (measurable_cloudFiniteWeight.comp measurable_fst)
  simp only [lintegral_const, measure_univ, mul_one] at h
  rw [cloud_intensity_weight] at h
  have hm : Measurable (fun ω : PointCloud A => weightedMass cloudFiniteWeight (pointCloudMeasure ω)) :=
    (Measure.measurable_lintegral measurable_cloudFiniteWeight).comp measurable_pointCloudMeasure
  exact (ae_lt_top hm (by simpa only [weightedMass, h] using (ENNReal.one_ne_top))).mono fun _ hω => hω.ne

def cloudHull {A : Type*} [MeasurableSpace A] : Kernel (Measure (ℝ × A)) (ℝ × A) :=
  weightedHull cloudFiniteWeight measurable_cloudFiniteWeight

instance cloudHull_sfinite {A : Type*} [MeasurableSpace A] : IsSFiniteKernel (@cloudHull A _) :=
  weightedHull_sfinite _ _ cloudFiniteWeight_ne_zero

lemma cloudHull_eq {A : Type*} [MeasurableSpace A] (μ : Measure (ℝ × A))
    (hμ : weightedMass cloudFiniteWeight μ ≠ ∞) : cloudHull μ = μ :=
  weightedHull_eq measurable_cloudFiniteWeight cloudFiniteWeight_ne_zero cloudFiniteWeight_ne_top μ hμ

lemma cloud_weightedMass_add_dirac_finite {A : Type*} [MeasurableSpace A]
    (μ : Measure (ℝ × A)) (hμ : weightedMass cloudFiniteWeight μ ≠ ∞) (z : ℝ × A) :
    weightedMass cloudFiniteWeight (Measure.dirac z + μ) ≠ ∞ := by
  unfold weightedMass
  rw [lintegral_add_measure, lintegral_dirac' _ measurable_cloudFiniteWeight]
  exact ENNReal.add_ne_top.mpr ⟨cloudFiniteWeight_ne_top _,hμ⟩

end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma measurable_distinct_cloud_hull {A : Type} [MeasurableSpace A] [MeasurableEq (ℝ × A)]
    (fs : List ((ℝ × A) → ℝ≥0∞)) (hfs : ∀ f ∈ fs, Measurable f) (xs : List (ℝ × A)) :
    Measurable (fun μ : Measure (ℝ × A) => distinctCloudIntegral fs (cloudHull μ) xs) := by
  have h := measurable_distinctCloudIntegral fs hfs cloudHull
    (xs.map (fun x => fun _ : Measure (ℝ × A) => x)) (by
      intro f hf
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hf
      exact measurable_const)
  simpa [Function.comp_def] using h

lemma measurable_distinct_cloud_hull_cons {A : Type} [MeasurableSpace A] [MeasurableEq (ℝ × A)]
    (fs : List ((ℝ × A) → ℝ≥0∞)) (hfs : ∀ f ∈ fs, Measurable f) (xs : List (ℝ × A)) :
    Measurable (fun z : (ℝ × A) × Measure (ℝ × A) =>
      distinctCloudIntegral fs (cloudHull z.2) (z.1::xs)) := by
  have h := measurable_distinctCloudIntegral fs hfs (cloudHull.comap Prod.snd measurable_snd)
    (Prod.fst :: xs.map (fun x => fun _ : (ℝ × A) × Measure (ℝ × A) => x)) (by
      intro f hf
      simp only [List.mem_cons, List.mem_map] at hf
      rcases hf with rfl | ⟨x,hx,rfl⟩
      · exact measurable_fst
      · exact measurable_const)
  simpa [Function.comp_def, Kernel.comap_apply] using h

lemma aemeasurable_distinct_cloud {A : Type} [MeasurableSpace A] [MeasurableEq (ℝ × A)]
    (ν : Measure A) [IsProbabilityMeasure ν] (fs : List ((ℝ × A) → ℝ≥0∞))
    (hfs : ∀ f ∈ fs, Measurable f) (xs : List (ℝ × A)) :
    AEMeasurable (fun ω : PointCloud A => distinctCloudIntegral fs (pointCloudMeasure ω) xs)
      (pointCloudLaw ν) := by
  apply ((measurable_distinct_cloud_hull fs hfs xs).comp measurable_pointCloudMeasure).aemeasurable.congr
  filter_upwards [cloud_weightedMass_ae_finite ν] with ω hω
  dsimp only [Function.comp_def]
  rw [cloudHull_eq _ hω]

def cloudLaplaceFactor {X : Type*} [MeasurableSpace X] (g : X → ℝ≥0∞)
    (μ : Measure X) : ℝ≥0∞ := ENNReal.ofReal (expNeg (∫⁻ x, g x ∂μ))

lemma measurable_cloudLaplaceFactor {X : Type*} [MeasurableSpace X]
    {g : X → ℝ≥0∞} (hg : Measurable g) : Measurable (cloudLaplaceFactor g) :=
  (continuous_expNeg.measurable.comp (Measure.measurable_lintegral hg)).ennreal_ofReal

lemma cloudLaplaceFactor_add_dirac {X : Type*} [MeasurableSpace X]
    {g : X → ℝ≥0∞} (hg : Measurable g) (μ : Measure X) (x : X) :
    cloudLaplaceFactor g (Measure.dirac x + μ) =
      ENNReal.ofReal (expNeg (g x)) * cloudLaplaceFactor g μ := by
  unfold cloudLaplaceFactor
  rw [lintegral_add_measure, lintegral_dirac' _ hg, expNeg_add,
    ENNReal.ofReal_mul (expNeg_nonneg _)]

end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def cloudAtomKernel {A : Type*} [MeasurableSpace A] (n j : ℕ) :
    Kernel (PointCloud A) (ℝ × A) := by
  classical
  exact Kernel.piecewise (show MeasurableSet {ω : PointCloud A | j < (ω n).1} by measurability)
    (Kernel.deterministic (fun ω => ((n:ℝ)+((ω n).2 j).1, ((ω n).2 j).2)) (by fun_prop)) 0

instance cloudAtomKernel_finite {A : Type*} [MeasurableSpace A] (n j : ℕ) :
    IsFiniteKernel (cloudAtomKernel (A := A) n j) := by
  unfold cloudAtomKernel
  infer_instance

def cloudKernel {A : Type*} [MeasurableSpace A] : Kernel (PointCloud A) (ℝ × A) :=
  Kernel.sum (fun n : ℕ => Kernel.sum (fun j : ℕ => cloudAtomKernel n j))

instance cloudKernel_sfinite {A : Type*} [MeasurableSpace A] :
    IsSFiniteKernel (cloudKernel (A := A)) := by
  unfold cloudKernel
  infer_instance

lemma cloudKernel_apply {A : Type*} [MeasurableSpace A] (ω : PointCloud A) :
    cloudKernel ω = pointCloudMeasure ω := by
  classical
  simp only [cloudKernel, Kernel.sum_apply, cloudAtomKernel, Kernel.piecewise_apply,
    Kernel.deterministic_apply, zero_apply, pointCloudMeasure, Set.mem_ofPred_eq]

lemma measurable_distinct_actual_cloud {A : Type} [MeasurableSpace A] [MeasurableEq (ℝ × A)]
    (fs : List ((ℝ × A) → ℝ≥0∞)) (hfs : ∀ f ∈ fs, Measurable f) (xs : List (ℝ × A)) :
    Measurable (fun ω : PointCloud A => distinctCloudIntegral fs (pointCloudMeasure ω) xs) := by
  have h := measurable_distinctCloudIntegral fs hfs (cloudKernel (A := A))
    (xs.map (fun x => fun _ : PointCloud A => x)) (by
      intro f hf
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hf
      exact measurable_const)
  simpa [cloudKernel_apply, Function.comp_def] using h
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

lemma stable_positive_moment_value {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) (h0 : ∀ ω, 0 ≤ X ω)
    {c m : ℝ} (hc : 0 ≤ c) (hm : 0 < m) (hm1 : m < 1)
    (hL : ∀ t : ℝ, 0 ≤ t → (∫ ω, Real.exp (-t*X ω) ∂μ) = Real.exp (-c*t^m))
    {a : ℝ} (ha : 0 < a) (ham : a < m) :
    (∫ ω, (X ω)^a ∂μ) = c^(a/m)*Real.Gamma (1-a/m)/Real.Gamma (1-a) := by
  let K : ℝ × Ω → ℝ := fun z => 1-Real.exp (-(z.1^(-1/a))*X z.2)
  have hK : Measurable K := by unfold K; fun_prop
  have hK0 : ∀ x : ℝ, 0 < x → ∀ ω, 0 ≤ K (x,ω) := by
    intro x hx ω
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.rpow_nonneg hx.le _)) (h0 ω)))
  have hKi : ∀ x : ℝ, 0 < x → Integrable (fun ω => K (x,ω)) μ := by
    intro x hx
    exact (integrable_const 1).sub (integrable_exp_neg_mul μ hX h0 (Real.rpow_nonneg hx.le _))
  have hKval : ∀ x : ℝ, 0 < x → (∫ ω, K (x,ω) ∂μ) =
      1-Real.exp (-c*x^(-1/(a/m))) := by
    intro x hx
    unfold K
    rw [integral_sub (integrable_const 1)
      (integrable_exp_neg_mul μ hX h0 (Real.rpow_nonneg hx.le _)), hL _ (Real.rpow_nonneg hx.le _)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [← Real.rpow_mul hx.le]
    congr 3
    field_simp
  have hip : Integrable K ((volume.restrict (Set.Ioi 0)).prod μ) := by
    apply (integrable_prod_iff hK.aestronglyMeasurable).mpr
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hKi x hx
    · apply (stable_integrable (div_pos ha hm) ((div_lt_one hm).mpr ham) hc).congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [← hKval x hx]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => (Real.norm_of_nonneg (hK0 x hx ω)).symm
  have hinner : ∀ ω, (∫ x in Set.Ioi (0:ℝ), K (x,ω)) = Real.Gamma (1-a)*(X ω)^a := by
    intro ω
    have he : (fun x : ℝ => K (x,ω)) =
        (fun x : ℝ => 1-Real.exp (-(X ω)*x^(-1/a))) := by
      funext x; unfold K; congr 2; ring
    rw [he, stable_integral ha (ham.trans hm1) (h0 ω)]
  have he := integral_integral_swap (f := fun x ω => K (x,ω)) hip
  simp_rw [hinner] at he
  rw [integral_const_mul] at he
  have hout : (∫ x in Set.Ioi (0:ℝ), ∫ ω, K (x,ω) ∂μ) =
      Real.Gamma (1-a/m)*c^(a/m) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => hKval x hx)]
    exact stable_integral (div_pos ha hm) ((div_lt_one hm).mpr ham) hc
  rw [hout] at he
  have hγ : Real.Gamma (1-a) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith : 0 < 1-a)).ne'
  apply (eq_div_iff hγ).mpr
  nlinarith [he]

end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma measurable_stableTotal (m c : ℝ) : Measurable (stableTotal m c) := by
  apply measurable_pointCloudFunctional
  unfold stableJump; fun_prop

lemma stableTotal_is_integral (m c : ℝ) (ω : PointCloud Unit) :
    stableTotal m c ω = ∫⁻ z, stableJump m c z ∂pointCloudMeasure ω := by
  symm
  apply lintegral_pointCloudMeasure
  unfold stableJump; fun_prop

lemma stableTotal_properties {m c : ℝ} (hm : 0 < m) (hm1 : m < 1) (hc : 0 < c) :
    (∀ᵐ ω ∂pointCloudLaw (Measure.dirac ()), 0 < stableTotal m c ω ∧ stableTotal m c ω < ∞) ∧
    (∀ t : ℝ, 0 ≤ t →
      (∫ ω, Real.exp (-t*(stableTotal m c ω).toReal) ∂pointCloudLaw (Measure.dirac ())) =
        Real.exp (-(c*Real.Gamma (1-m))*t^m)) := by
  let d : ℝ≥0 := ⟨c^(1/m), (Real.rpow_pos_of_pos hc _).le⟩
  have hd : (d:ℝ)^m = c := by
    change (c^(1/m))^m = c
    rw [← Real.rpow_mul hc.le, one_div_mul_cancel hm.ne', Real.rpow_one]
  have hi : Integrable (fun y : ℝ≥0 => (y:ℝ)^m) (Measure.dirac d) := integrable_dirac (by finiteness)
  have hp : 0 < ∫ y : ℝ≥0, (y:ℝ)^m ∂Measure.dirac d := by simpa [hd] using hc
  have hs := stableCloud m hm hm1 (Measure.dirac d) inferInstance hi hp
  have hmap : MeasurePreserving (mapPointCloud (fun _ : Unit => d))
      (pointCloudLaw (Measure.dirac ())) (markedCloudLaw (Measure.dirac d)) := by
    refine ⟨measurable_mapPointCloud measurable_const, ?_⟩
    change (pointCloudLaw (Measure.dirac ())).map _ = pointCloudLaw (Measure.dirac d)
    rw [pointCloudLaw_map _ measurable_const]
    simp
  have he (ω : PointCloud Unit) : stableCloudSum m (mapPointCloud (fun _ : Unit => d) ω) =
      stableTotal m c ω := by
    rw [stableCloudSum_mapPointCloud]
    change pointCloudFunctional (fun z => ENNReal.ofReal (z.1^(-1/m)*(d:ℝ))) ω =
      pointCloudFunctional (stableJump m c) ω
    congr 1
    funext z
    change ENNReal.ofReal (z.1^(-1/m)*c^(1/m)) = ENNReal.ofReal (c^(1/m)*z.1^(-1/m))
    rw [mul_comm]
  refine ⟨?_, ?_⟩
  · simpa only [he] using hmap.quasiMeasurePreserving.ae hs.1
  · intro t ht
    have hF : Measurable (fun ω : MarkedCloud => Real.exp (-t*(stableCloudSum m ω).toReal)) :=
      (measurable_const.mul (measurable_stableCloudSum m).ennreal_toReal).exp
    have hv := integral_map (μ := pointCloudLaw (Measure.dirac ())) hmap.measurable.aemeasurable hF.aestronglyMeasurable
    rw [hmap.map_eq] at hv
    simp only [he] at hv
    rw [← hv, hs.2.1 t ht, integral_dirac, hd]
    congr 1; ring

lemma stableTotal_moment {m c η : ℝ} (hm : 0 < m) (hm1 : m < 1) (hc : 0 < c)
    (hη : 0 ≤ η) (hηm : η < m) :
    (∫ ω, (stableTotal m c ω).toReal^η ∂pointCloudLaw (Measure.dirac ())) =
      (c*Real.Gamma (1-m))^(η/m)*Real.Gamma (1-η/m)/Real.Gamma (1-η) := by
  rcases hη.eq_or_lt with rfl | hη
  · simp
  · exact stable_positive_moment_value (pointCloudLaw (Measure.dirac ()))
      (measurable_stableTotal m c).ennreal_toReal (fun _ => ENNReal.toReal_nonneg)
      (mul_pos hc (Real.Gamma_pos_of_pos (by linarith))).le hm hm1
      (stableTotal_properties hm hm1 hc).2 hη hηm
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma measurable_expMarkedJump {A : Type*} [MeasurableSpace A] (m : ℝ)
    {X : A → ℝ} (hX : Measurable X) : Measurable (expMarkedJump m X) := by
  unfold expMarkedJump; fun_prop

lemma measurable_expMarkedBlock {A : Type*} [MeasurableSpace A] (m : ℝ)
    {X : A → ℝ} (hX : Measurable X) (n : ℕ) {s : Set A} (hs : MeasurableSet s) :
    Measurable (expMarkedBlock m X n s) := by
  change Measurable ((Prod.snd ⁻¹' s).indicator (fun z => expMarkedJump m X z^n))
  exact ((measurable_expMarkedJump m hX).pow_const n).indicator (hs.preimage measurable_snd)

lemma expMarkedTotal_integral {A : Type*} [MeasurableSpace A] (m : ℝ)
    {X : A → ℝ} (hX : Measurable X) (ω : PointCloud A) :
    expMarkedTotal m X ω = ∫⁻ z, expMarkedJump m X z ∂pointCloudMeasure ω := by
  rw [lintegral_pointCloudMeasure (measurable_expMarkedJump m hX)]
  unfold expMarkedTotal coloredStableSum
  congr 1
  funext z
  exact ENNReal.ofReal_mul' (Real.exp_pos _).le

lemma measurable_expMarkedTotal {A : Type*} [MeasurableSpace A] (m : ℝ)
    {X : A → ℝ} (hX : Measurable X) : Measurable (expMarkedTotal m X) :=
  measurable_coloredStableSum m (by fun_prop)

lemma expMarkedTotal_properties {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] {m : ℝ} (hm : 0 < m) (hm1 : m < 1)
    {X : A → ℝ} (hX : Measurable X) (hi : Integrable (fun a => Real.exp (m*X a)) ν) :
    (∀ᵐ ω ∂pointCloudLaw ν, 0 < expMarkedTotal m X ω ∧ expMarkedTotal m X ω < ∞) ∧
    (∀ t : ℝ, 0 ≤ t → (∫ ω, Real.exp (-t*(expMarkedTotal m X ω).toReal) ∂pointCloudLaw ν) =
      Real.exp (-((∫ a, Real.exp (m*X a) ∂ν)*Real.Gamma (1-m))*t^m)) := by
  let Y : A → ℝ≥0 := fun a => ⟨Real.exp (X a),(Real.exp_pos _).le⟩
  have hY : Measurable Y := by fun_prop
  have he (a : A) : (Y a:ℝ)^m = Real.exp (m*X a) := by
    change (Real.exp (X a))^m = _
    rw [← Real.exp_mul, mul_comm (X a) m]
  have hiY : Integrable (fun a => (Y a:ℝ)^m) ν := by simpa only [he] using hi
  have hpY : 0 < ∫ a, (Y a:ℝ)^m ∂ν := by
    simp_rw [he]; exact integral_exp_pos hi
  refine ⟨(coloredStable_properties ν hm hm1 hY hiY hpY).1, ?_⟩
  intro t ht
  have hl := coloredStable_laplace ν hm hm1 hY hiY hpY ht
  simpa only [he, expMarkedTotal, Y, mul_comm (Real.Gamma (1-m))] using hl

lemma expMarkedTotal_moment_eq {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] {m η : ℝ} (hm : 0 < m) (hm1 : m < 1)
    {X : A → ℝ} (hX : Measurable X) (hi : Integrable (fun a => Real.exp (m*X a)) ν)
    (hη : 0 ≤ η) (hηm : η < m) :
    (∫ ω, (expMarkedTotal m X ω).toReal^η ∂pointCloudLaw ν) =
      ∫ ω, (stableTotal m (∫ a, Real.exp (m*X a) ∂ν) ω).toReal^η ∂pointCloudLaw (Measure.dirac ()) := by
  have hc := integral_exp_pos hi
  rw [stableTotal_moment hm hm1 hc hη hηm]
  rcases hη.eq_or_lt with rfl | hη
  · simp
  · exact stable_positive_moment_value (pointCloudLaw ν)
      (measurable_expMarkedTotal m hX).ennreal_toReal (fun _ => ENNReal.toReal_nonneg)
      (mul_pos hc (Real.Gamma_pos_of_pos (by linarith))).le hm hm1
      (expMarkedTotal_properties ν hm hm1 hX hi).2 hη hηm
end MicroscopicJamming

end

end OAI
