import OAI.Probability.DirectionalWalk.WordPosterior

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def freshPathKernel {d : ℕ} (x : Site d) : Kernel (Environment d) (Path d) :=
  (quenchedKernel d).comap (fun ω => (ω,x)) (measurable_id.prodMk measurable_const)

instance {d : ℕ} (x : Site d) : IsMarkovKernel (freshPathKernel x) := by
  unfold freshPathKernel
  infer_instance

noncomputable def freshJoint {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) : Measure (Environment d × Path d) :=
  environmentLaw μ ⊗ₘ freshPathKernel x

instance {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] (x : Site d) :
    IsProbabilityMeasure (freshJoint μ x) := by
  unfold freshJoint
  infer_instance

lemma freshJoint_apply {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] (x : Site d)
    {A : Set (Environment d × Path d)} (hA : MeasurableSet A) :
    freshJoint μ x A = ∫⁻ ω, quenchedKernel d (ω,x) (Prod.mk ω ⁻¹' A) ∂environmentLaw μ := by
  rw [freshJoint,Measure.compProd_apply hA]
  rfl

lemma freshJoint_path_marginal {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] (x : Site d) :
    MeasurePreserving Prod.snd (freshJoint μ x) (annealed μ x) := by
  refine ⟨measurable_snd,?_⟩
  ext A hA
  rw [Measure.map_apply measurable_snd hA,freshJoint_apply μ x (hA.preimage measurable_snd),annealed_apply μ x hA]
  rfl

lemma freshJoint_lintegral {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] (x : Site d)
    (f : Environment d × Path d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ξ, f ξ ∂freshJoint μ x) =
      ∫⁻ ω, ∫⁻ X, f (ω,X) ∂quenchedKernel d (ω,x) ∂environmentLaw μ := by
  rw [freshJoint,Measure.lintegral_compProd hf]
  rfl

lemma measurable_random_visitAfter {d : ℕ} (R K : Set (Site d)) (A : Environment d → Set (Site d))
    (hA : ∀ y, MeasurableSet {ω | y ∈ A ω}) :
    MeasurableSet {ξ : Environment d × Path d | ξ.2 ∈ visitAfter R (A ξ.1) K} := by
  have he : {ξ : Environment d × Path d | ξ.2 ∈ visitAfter R (A ξ.1) K} =
      ⋃ y : Site d, {ξ | y ∈ A ξ.1} ∩ {ξ | ξ.2 ∈ visitAfter R {y} K} := by
    ext ⟨ω,X⟩
    simp only [Set.mem_iUnion,Set.mem_inter_iff,Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n,hAn,hR,hK⟩
      exact ⟨X n,hAn,n,rfl,hR,hK⟩
    · rintro ⟨y,hy,n,hAn,hR,hK⟩
      exact ⟨n,hAn ▸ hy,hR,hK⟩
  rw [he]
  exact MeasurableSet.iUnion (fun y => ((hA y).preimage measurable_fst).inter
    ((measurableSet_visitAfter R {y} K).preimage measurable_snd))

noncomputable def quenchedReturn {d : ℕ} (e : Step d) (k N : ℤ)
    (ω : Environment d) (y : Site d) : ℝ≥0∞ :=
  quenchedKernel d (ω,y) (hitBefore (axisLower e k) (axisUpper e N))

lemma measurable_quenchedReturn {d : ℕ} (e : Step d) (k N : ℤ) (y : Site d) :
    Measurable (fun ω => quenchedReturn e k N ω y) :=
  ((quenchedKernel d).measurable_coe (measurableSet_hitBefore _ _)).comp
    (measurable_id.prodMk measurable_const)

def returnAtLeast {d : ℕ} (e : Step d) (k N : ℤ) (a : ℝ≥0∞)
    (ω : Environment d) : Set (Site d) :=
  {y | k ≤ axisHeight e y ∧ axisHeight e y < N ∧ a ≤ quenchedReturn e k N ω y}

def returnBin {d : ℕ} (e : Step d) (k N : ℤ) (a : ℝ≥0∞)
    (ω : Environment d) : Set (Site d) :=
  {y | y ∈ returnAtLeast e k N a ω ∧ quenchedReturn e k N ω y < 2*a}

lemma measurableSet_returnAtLeast {d : ℕ} (e : Step d) (k N : ℤ) (a : ℝ≥0∞) (y : Site d) :
    MeasurableSet {ω | y ∈ returnAtLeast e k N a ω} :=
  (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    (measurableSet_le measurable_const (measurable_quenchedReturn e k N y)))

lemma measurableSet_returnBin {d : ℕ} (e : Step d) (k N : ℤ) (a : ℝ≥0∞) (y : Site d) :
    MeasurableSet {ω | y ∈ returnBin e k N a ω} :=
  (measurableSet_returnAtLeast e k N a y).inter
    (measurableSet_lt (measurable_quenchedReturn e k N y) measurable_const)

lemma freshJoint_return_visit_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) {r N : ℕ} (hrN : r ≤ N) (a : ℝ≥0∞) :
    a * freshJoint μ 0 {ξ | ξ.2 ∈ visitAfter (axisUpper e r) (returnAtLeast e 0 N a ξ.1)
      (axisLower e 0 ∪ axisUpper e N)} ≤ axisReachProb μ e r - axisReachProb μ e N := by
  rw [freshJoint_apply μ 0 (measurable_random_visitAfter _ _ _ (measurableSet_returnAtLeast e 0 N a))]
  exact annealed_axis_visitAfter_bound μ hell e hrN a _ (by
    filter_upwards [] with ω
    exact fun y hy => hy.2.2)

lemma weighted_disjoint_measure_bound_ae {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) (s : ι → Set Ω) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (w : ι → ℝ≥0∞) (F : Ω → ℝ≥0∞)
    (E : Set Ω) (hsub : ∀ i, s i ⊆ E) (hbound : ∀ i, ∀ᵐ ω ∂μ, ω ∈ s i → w i ≤ F ω) :
    ∑' i, w i * μ (s i) ≤ ∫⁻ ω in E, F ω ∂μ := by
  calc
    ∑' i, w i * μ (s i) ≤ ∑' i, ∫⁻ ω in s i, F ω ∂μ := by
      apply ENNReal.tsum_le_tsum
      intro i
      rw [← setLIntegral_const]
      exact lintegral_mono_ae ((ae_restrict_iff' (hs i)).mpr (hbound i))
    _ = ∫⁻ ω in ⋃ i, s i, F ω ∂μ := (lintegral_iUnion hs hd F).symm
    _ ≤ _ := lintegral_mono_set (Set.iUnion_subset hsub)

lemma weighted_contact_bin_bound_ae {d : ℕ} (P Q : Measure (Path d)) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (A : Set (Word d)) (D V : Set (Path d)) (K : Set (Site d))
    (hD : MeasurableSet D) (w : Word d → ℝ≥0∞) (M : Path d → ℝ≥0∞)
    (hM : Measurable M) (hA : ∀ a ∈ A, wordEnd a ∈ K)
    (hAV : ∀ a ∈ A, wordCylinder a ⊆ V)
    (hw : ∀ a ∈ A, ∀ᵐ X ∂P, X ∈ wordCylinder a → w a ≤ M X) (c : ℝ≥0∞)
    (hc : Q (D ∩ {B | ∃ n, B n ∈ K}) ≤ c) :
    ∑' a : A, w a * (P (wordCylinder a) * Q (D ∩ contactAvoid a)) ≤
      c * ∫⁻ X in V, M X ∂P := by
  let R : Set (Path d) := D ∩ {B | ∃ n, B n ∈ K}
  have hR : MeasurableSet R := hD.inter (by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion (fun n => (Set.to_countable K).measurableSet.preimage (measurable_pi_apply n)))
  have hs (a : A) : MeasurableSet (wordCylinder a.val ×ˢ (D ∩ contactAvoid a.val)) :=
    (measurableSet_pathCylinder _ _).prod (hD.inter (measurableSet_contactAvoid _))
  have hd : Pairwise (fun a b : A => Disjoint
      (wordCylinder a.val ×ˢ (D ∩ contactAvoid a.val))
      (wordCylinder b.val ×ˢ (D ∩ contactAvoid b.val))) := by
    intro a b hab
    apply (contactRectangles_disjoint (i := a.val) (j := b.val) (fun h => hab (Subtype.ext h))).mono
    · exact fun _ h => ⟨h.1,h.2.2⟩
    · exact fun _ h => ⟨h.1,h.2.2⟩
  have hsub (a : A) : wordCylinder a.val ×ˢ (D ∩ contactAvoid a.val) ⊆ V ×ˢ R := by
    rintro ⟨X,B⟩ ⟨hX,hB⟩
    obtain ⟨n,hn⟩ := hB.2.1
    exact ⟨hAV _ a.property hX,hB.1,n,hn ▸ hA _ a.property⟩
  have hb (a : A) : ∀ᵐ p ∂P.prod Q, p ∈ wordCylinder a.val ×ˢ (D ∩ contactAvoid a.val) → w a.val ≤ M p.1 := by
    have hfst : ∀ᵐ p ∂P.prod Q, p.1 ∈ wordCylinder a.val → w a.val ≤ M p.1 :=
      (measurePreserving_fst (μ := P) (ν := Q)).quasiMeasurePreserving.ae (hw a a.property)
    filter_upwards [hfst] with p hp
    exact fun h => hp h.1
  have h := weighted_disjoint_measure_bound_ae (P.prod Q)
    (fun a : A => wordCylinder a.val ×ˢ (D ∩ contactAvoid a.val)) hs hd
    (fun a => w a) (fun p => M p.1) (V ×ˢ R) hsub hb
  simp only [Measure.prod_prod] at h
  apply h.trans
  rw [setLIntegral_prod (fun p : Path d × Path d => M p.1) (hM.comp measurable_fst).aemeasurable.restrict]
  simp only [setLIntegral_const]
  rw [lintegral_mul_const _ hM,mul_comm]
  exact mul_le_mul_left hc _

end DirectionalZeroOne

end OAI
