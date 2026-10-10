import Mathlib
import OAI.Probability.Ballisticity.Walk.PathCompact

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma gaussian_block_count_limit {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun i => ((⌊b*n i⌋₊-⌊a*n i⌋₊:ℕ):ℝ)/n i) atTop (𝓝 (b-a)) := by
  have he : (fun i => ((⌊b*n i⌋₊-⌊a*n i⌋₊:ℕ):ℝ)/n i) =ᶠ[atTop]
      fun i => (⌊b*n i⌋₊:ℝ)/n i-(⌊a*n i⌋₊:ℝ)/n i := by
    filter_upwards [hn.eventually (eventually_ge_atTop (0:ℝ))] with i hi
    rw [Nat.cast_sub (Nat.floor_mono (mul_le_mul_of_nonneg_right hab hi)),sub_div]
  apply Tendsto.congr' he.symm
  exact ((tendsto_nat_floor_mul_div_atTop (ha.trans hab)).comp hn).sub
    ((tendsto_nat_floor_mul_div_atTop ha).comp hn)

lemma tendstoInMeasure_sub_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F G : ℕ → Ω → ℝ)
    (hF : TendstoInMeasure μ F atTop 0) (hG : TendstoInMeasure μ G atTop 0) :
    TendstoInMeasure μ (F-G) atTop 0 := by
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  have hf := (tendstoInMeasure_iff_measureReal_norm.1 hF) (ε/2) (by positivity)
  have hg := (tendstoInMeasure_iff_measureReal_norm.1 hG) (ε/2) (by positivity)
  simp only [Pi.zero_apply,sub_zero,Real.norm_eq_abs] at hf hg ⊢
  have hs n : {ω | ε ≤ |(F-G) n ω|} ⊆
      {ω | ε/2 ≤ |F n ω|} ∪ {ω | ε/2 ≤ |G n ω|} := by
    intro ω hω
    by_contra! hc
    simp only [Set.mem_union,Set.mem_ofPred_eq,not_or,not_le] at hc
    have ht := abs_sub (F n ω) (G n ω)
    change ε ≤ |F n ω-G n ω| at hω
    exact (not_lt_of_ge hω) (ht.trans_lt (by linarith))
  have hb n := (measureReal_mono (μ := μ) (hs n) (measure_ne_top _ _)).trans (measureReal_union_le (μ := μ) _ _)
  exact squeeze_zero (fun _ => measureReal_nonneg) hb (by simpa using hf.add hg)

lemma fluctuationScale_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (r : ℝ) : 0 ≤ fluctuationScale μ S r := by
  apply div_nonneg (sq_nonneg _)
  exact integral_nonneg (fun x => le_min (sq_nonneg _) (sq_nonneg _))

lemma disjoint_blocks_injective {ι : Type*} (a b : ι → ℕ)
    (hdisj : ∀ j k, j ≠ k → b j ≤ a k ∨ b k ≤ a j) :
    Function.Injective (fun p : (j : ι) × Fin (b j-a j) => a p.1+p.2.1) := by
  rintro ⟨j,l⟩ ⟨k,m⟩ he
  have hj : l.1 < b j-a j := l.2
  have hk : m.1 < b k-a k := m.2
  by_cases hjk : j = k
  · subst k
    have hlm : l = m := Fin.ext (by simpa using he)
    subst m
    rfl
  · rcases hdisj j k hjk with h|h <;> simp only at he <;> omega

lemma realPartialSum_sub_eq_block (x : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    realPartialSum x b-realPartialSum x a = ∑ l : Fin (b-a), x (a+l) := by
  have h := realPartialSum_add x a (b-a)
  rw [Nat.add_sub_of_le hab] at h
  rw [Fin.sum_univ_eq_sum_range (f := fun l => x (a+l))]
  change _ = realPartialSum (fun l => x (a+l)) (b-a)
  linarith

theorem gaussian_polygon_increment_limit {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {x | X 0 x ≠ 0})
    (hsym : IdentDistrib (X 0) (fun x => -X 0 x) μ μ)
    (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T : ℝ} (hT : 0 ≤ T) (a b : ι → unitInterval)
    (hab : ∀ j, a j ≤ b j)
    (hdisj : ∀ j k, j ≠ k → b j ≤ a k ∨ b k ≤ a j) :
    TendstoInDistribution (fun i ω (j : ι) =>
      scaledPolygon (fun k => X k ω) (r i) (fluctuationScale μ (X 0) (r i)) T (b j)-
      scaledPolygon (fun k => X k ω) (r i) (fluctuationScale μ (X 0) (r i)) T (a j))
      atTop id (fun _ => μ) (Measure.pi (fun j : ι => gaussianReal 0
        (Real.toNNReal (T*((b j : ℝ)-a j))))) := by
  let n := fun i => fluctuationScale μ (X 0) (r i)
  have hn := (fluctuationScale_tendsto μ (X 0) (hX 0) hI hne).comp hr.1
  have hn0 i : 0 ≤ n i := fluctuationScale_nonneg _ _ _
  let A := fun i j => ⌊(T*a j)*n i⌋₊
  let B := fun i j => ⌊(T*b j)*n i⌋₊
  have hAB i j : A i j ≤ B i j := Nat.floor_mono
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hab j) hT) (hn0 i))
  have hd i j k (hjk : j ≠ k) : B i j ≤ A i k ∨ B i k ≤ A i j := by
    rcases hdisj j k hjk with h|h
    · exact Or.inl (Nat.floor_mono (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hT) (hn0 i)))
    · exact Or.inr (Nat.floor_mono (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hT) (hn0 i)))
  let τ : ι → ℝ≥0 := fun j => Real.toNNReal (T*((b j : ℝ)-a j))
  have hc j : Tendsto (fun i => ((B i j-A i j:ℕ):ℝ)/n i) atTop (𝓝 (τ j : ℝ)) := by
    have h := gaussian_block_count_limit (mul_nonneg hT (a j).2.1)
      (mul_le_mul_of_nonneg_left (hab j) hT) n hn
    dsimp only [τ]
    rw [Real.coe_toNNReal _ (mul_nonneg hT (sub_nonneg.mpr (hab j)))]
    simpa only [A,B,mul_sub] using h
  have hb := gaussian_iid_finite_block_limit μ X hX hind hident hI hne hsym r hr
    (fun i j => B i j-A i j) (fun i j l => A i j+l)
    (fun i => disjoint_blocks_injective (A i) (B i) (hd i)) τ hc
  have hb' := hb.continuous_comp (g := (WithLp.ofLp : EuclideanSpace ℝ ι → (ι → ℝ))) (by fun_prop)
  let Z := fun i ω j => (∑ l : Fin (B i j-A i j), X (A i j+l) ω)/r i
  have hZ : TendstoInDistribution Z atTop id (fun _ => μ)
      (Measure.pi (fun j => gaussianReal 0 (τ j))) := by
    convert hb' using 1 <;> rfl
  let Y := fun i ω j => scaledPolygon (fun k => X k ω) (r i) (n i) T (b j)-
    scaledPolygon (fun k => X k ω) (r i) (n i) T (a j)
  apply tendstoInDistribution_of_tendstoInMeasure_sub Y id hZ
  · apply tendstoInMeasure_pi
    intro j
    have ha := polygon_eval_error_tendstoInMeasure μ X (hX 0) hident r n hr.1
      (Eventually.of_forall hn0) hT (a j)
    have hb := polygon_eval_error_tendstoInMeasure μ X (hX 0) hident r n hr.1
      (Eventually.of_forall hn0) hT (b j)
    have he := tendstoInMeasure_sub_zero μ _ _ hb ha
    convert he using 1
    ext i ω
    change Y i ω j-Z i ω j = _
    dsimp [Y,Z]
    rw [← realPartialSum_sub_eq_block (fun k => X k ω) (hAB i j)]
    dsimp [A,B]
    ring
  · intro i
    apply Measurable.aemeasurable
    apply Measurable.of_eval
    intro j
    exact ((continuous_eval_const _).measurable.comp (measurable_scaledPolygon X hX _ _ _)).sub
      ((continuous_eval_const _).measurable.comp (measurable_scaledPolygon X hX _ _ _))

noncomputable def orderedTimes (I : Finset unitInterval) (i : Fin (I.card+1)) : unitInterval :=
  if h : i = 0 then 0 else I.orderEmbOfFin rfl (i.pred h)

lemma orderedTimes_monotone (I : Finset unitInterval) : Monotone (orderedTimes I) := by
  intro i j hij
  obtain rfl | hi := eq_or_ne i 0
  · simp [orderedTimes]
  have hj : j ≠ 0 := by intro hj; subst j; exact hi (le_antisymm hij (Fin.zero_le _))
  rw [orderedTimes,dite_eq_right hi,orderedTimes,dite_eq_right hj]
  exact OrderEmbedding.monotone _ (by simpa)

lemma orderedTimes_succ (I : Finset unitInterval) (i : Fin I.card) :
    orderedTimes I i.succ = I.orderEmbOfFin rfl i := by simp [orderedTimes]

noncomputable def incrementCumsum (I : Finset unitInterval) : (Fin I.card → ℝ) →L[ℝ] (I → ℝ) :=
  { toFun x i := ∑ j ≤ (I.orderIsoOfFin rfl).symm i, x j
    map_add' x y := by ext; simp [Finset.sum_add_distrib]
    map_smul' m x := by ext; simp [Finset.mul_sum]
    cont := by fun_prop }

lemma incrementCumsum_eval (I : Finset unitInterval) (f : unitInterval → ℝ) (hf : f 0 = 0) :
    I.restrict f = incrementCumsum I (fun j => f (orderedTimes I j.succ)-f (orderedTimes I j.castSucc)) := by
  ext t
  simp only [Finset.restrict,incrementCumsum,ContinuousLinearMap.coe_mk',LinearMap.coe_mk,AddHom.coe_mk]
  rw [Fin.sum_Iic_sub _ (fun j => f (orderedTimes I j))]
  simp [orderedTimes,hf,Finset.orderEmbOfFin]

noncomputable def gaussianPathFiniteLaw (T : ℝ) (I : Finset unitInterval) : Measure (I → ℝ) :=
  (Measure.pi (fun j : Fin I.card => gaussianReal 0
    (Real.toNNReal (T*((orderedTimes I j.succ : ℝ)-orderedTimes I j.castSucc))))).map
    (incrementCumsum I)

instance gaussianPathFiniteLaw_probability (T : ℝ) (I : Finset unitInterval) :
    IsProbabilityMeasure (gaussianPathFiniteLaw T I) := by
  unfold gaussianPathFiniteLaw
  infer_instance

lemma ordered_adjacent_disjoint {m : ℕ} (t : Fin (m+1) → unitInterval) (ht : Monotone t) :
    ∀ j k : Fin m, j ≠ k → t j.succ ≤ t k.castSucc ∨ t k.succ ≤ t j.castSucc := by
  intro j k hjk
  rcases lt_or_gt_of_ne hjk with h|h
  · exact Or.inl (ht (by exact_mod_cast h))
  · exact Or.inr (ht (by exact_mod_cast h))

theorem gaussian_polygon_finite_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {x | X 0 x ≠ 0})
    (hsym : IdentDistrib (X 0) (fun x => -X 0 x) μ μ)
    (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T : ℝ} (hT : 0 ≤ T) (I : Finset unitInterval) :
    TendstoInDistribution (fun i ω => I.restrict
      (scaledPolygon (fun k => X k ω) (r i) (fluctuationScale μ (X 0) (r i)) T))
      atTop id (fun _ => μ) (gaussianPathFiniteLaw T I) := by
  let Y := fun i ω => scaledPolygon (fun k => X k ω) (r i)
    (fluctuationScale μ (X 0) (r i)) T
  let t := orderedTimes I
  have ht : Monotone t := orderedTimes_monotone I
  have hi := gaussian_polygon_increment_limit μ X hX hind hident hI hne hsym r hr hT
    (fun j : Fin I.card => t j.castSucc) (fun j => t j.succ)
    (fun j => ht (Fin.castSucc_le_succ j)) (ordered_adjacent_disjoint t ht)
  have hc := hi.continuous_comp (incrementCumsum I).continuous
  have hl i : (fun ω => I.restrict ((Y i ω) ·)) =ᵐ[μ]
      (incrementCumsum I) ∘ (fun ω j => Y i ω (t j.succ)-Y i ω (t j.castSucc)) := by
    filter_upwards [] with ω
    exact incrementCumsum_eval I (Y i ω) (scaledPolygon_zero _ _ _ _)
  have hc' := hc.congr (fun i => (hl i).symm) Filter.EventuallyEq.rfl
  refine ⟨hc'.forall_aemeasurable,measurable_id.aemeasurable,?_⟩
  convert hc'.tendsto using 1
  simp only [gaussianPathFiniteLaw,Function.comp_def,id_eq,Measure.map_id]
  rfl

lemma continuous_path_restrict (I : Finset unitInterval) :
    Continuous (fun f : C(unitInterval,ℝ) => I.restrict f) := by
  apply continuous_pi
  intro j
  exact continuous_eval_const _

lemma continuous_path_measure_ext (μ ν : Measure C(unitInterval,ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ I : Finset unitInterval, μ.map (fun f : C(unitInterval,ℝ) => I.restrict f) =
      ν.map (fun f : C(unitInterval,ℝ) => I.restrict f)) : μ = ν := by
  classical
  let e := TopologicalSpace.denseSeq unitInterval
  let E := fun f : C(unitInterval,ℝ) => fun n => f (e n)
  have hE : Continuous E := continuous_pi (fun n => continuous_eval_const _)
  have hEinj : Function.Injective E := by
    intro f g hfg
    apply ContinuousMap.coe_injective
    exact TopologicalSpace.denseRange_denseSeq unitInterval |>.equalizer
      f.continuous g.continuous hfg
  apply hE.measurableEmbedding hEinj |>.map_injective
  let P := fun J : Finset ℕ => (μ.map E).map J.restrict
  have : ∀ J, IsFiniteMeasure (P J) := fun _ => inferInstance
  apply IsProjectiveLimit.unique (P := P) (fun _ => rfl)
  intro J
  let I := J.image e
  let g := fun f : I → ℝ => fun j : J => f ⟨e j,Finset.mem_image_of_mem e j.2⟩
  have hg : Measurable g := by fun_prop
  have hm : Measurable (J.restrict : (ℕ → ℝ) → (J → ℝ)) := by fun_prop
  change (ν.map E).map J.restrict = (μ.map E).map J.restrict
  rw [Measure.map_map hm hE.measurable,Measure.map_map hm hE.measurable]
  have he : J.restrict ∘ E = g ∘ (fun f : C(unitInterval,ℝ) => I.restrict f) := rfl
  rw [he,← Measure.map_map hg (continuous_path_restrict I).measurable,
    ← Measure.map_map hg (continuous_path_restrict I).measurable,h I]

theorem exists_path_limit_of_tight_finite_limit
    (μ : ℕ → ProbabilityMeasure C(unitInterval,ℝ))
    (P : (I : Finset unitInterval) → ProbabilityMeasure (I → ℝ))
    (ht : IsTightMeasureSet (Set.range (fun n => (μ n : Measure C(unitInterval,ℝ)))))
    (hf : ∀ I, Tendsto (fun n => (μ n).map (fun path : C(unitInterval,ℝ) => I.restrict path))
      atTop (𝓝 (P I))) :
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ), Tendsto μ atTop (𝓝 W) ∧
      ∀ I, W.map (fun path : C(unitInterval,ℝ) => I.restrict path) = P I := by
  have hc : IsCompact (closure (Set.range μ)) :=
    isCompact_closure_of_isTightMeasureSet (by
      convert ht using 1
      ext x
      simp)
  have hmem n : μ n ∈ closure (Set.range μ) := subset_closure (Set.mem_range_self n)
  obtain ⟨W,_,s,hs,hw⟩ := hc.tendsto_subseq hmem
  have hid : ∀ (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
      (V : ProbabilityMeasure C(unitInterval,ℝ)),
      Tendsto (μ ∘ n) atTop (𝓝 V) →
      ∀ I, V.map (fun path : C(unitInterval,ℝ) => I.restrict path) = P I := by
    intro n hn V hv I
    exact tendsto_nhds_unique
      ((ProbabilityMeasure.continuous_map (continuous_path_restrict I)).tendsto V |>.comp hv)
      ((hf I).comp hn)
  have hW := hid s hs.tendsto_atTop W hw
  refine ⟨W,?_,hW⟩
  apply Filter.tendsto_of_subseq_tendsto
  intro n hn
  obtain ⟨V,_,s,hs,hv⟩ := hc.tendsto_subseq (fun j => hmem (n j))
  have hV := hid (n ∘ s) (hn.comp hs.tendsto_atTop) V hv
  have he : V = W := by
    have : IsProbabilityMeasure (V : Measure C(unitInterval,ℝ)) := V.prop
    have : IsProbabilityMeasure (W : Measure C(unitInterval,ℝ)) := W.prop
    apply Subtype.ext
    apply continuous_path_measure_ext (V : Measure C(unitInterval,ℝ))
      (W : Measure C(unitInterval,ℝ))
    intro I
    exact congrArg (fun Q : ProbabilityMeasure (I → ℝ) => (Q : Measure (I → ℝ)))
      ((hV I).trans (hW I).symm)
  subst V
  exact ⟨s,hv⟩

theorem gaussian_iid_path_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
    (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      TendstoInDistribution (fun i ω => scaledPolygon (fun k => X k ω)
        (r i) (fluctuationScale μ (X 0) (r i)) T) atTop id (fun _ => μ) W ∧
      ∀ I : Finset unitInterval,
        (W : Measure C(unitInterval,ℝ)).map (fun f : C(unitInterval,ℝ) => I.restrict f) =
          gaussianPathFiniteLaw T I := by
  let Y := fun i ω => scaledPolygon (fun k => X k ω) (r i)
    (fluctuationScale μ (X 0) (r i)) T
  have hY : ∀ i, Measurable (Y i) := fun _ => measurable_scaledPolygon X hX _ _ _
  let M : ℕ → ProbabilityMeasure C(unitInterval,ℝ) := fun i =>
    ⟨μ.map (Y i),inferInstance⟩
  let P : (I : Finset unitInterval) → ProbabilityMeasure (I → ℝ) := fun I =>
    ⟨gaussianPathFiniteLaw T I,inferInstance⟩
  have ht : IsTightMeasureSet (Set.range (fun i => (M i : Measure C(unitInterval,ℝ)))) :=
    gaussian_iid_path_tight μ X hX hind hident hsym hI hne r hr hT
  have hf : ∀ I, Tendsto (fun i => (M i).map (fun path : C(unitInterval,ℝ) => I.restrict path))
      atTop (𝓝 (P I)) := by
    intro I
    have h := (gaussian_polygon_finite_limit μ X hX hind hident hI hne hsym r hr hT I).tendsto
    have he : (fun i => (M i).map (fun path : C(unitInterval,ℝ) => I.restrict path)) =
        (fun i => (⟨μ.map (fun ω => I.restrict (Y i ω)),
          inferInstance⟩ :
          ProbabilityMeasure (I → ℝ))) := by
      funext i
      apply Subtype.ext
      exact Measure.map_map (continuous_path_restrict I).measurable (hY i)
    rw [he]
    simpa only [Measure.map_id] using h
  obtain ⟨W,hw,hf⟩ := exists_path_limit_of_tight_finite_limit M P ht hf
  refine ⟨W,⟨fun i => (hY i).aemeasurable,measurable_id.aemeasurable,?_⟩,?_⟩
  · convert hw using 1
    apply congrArg
    apply Subtype.ext
    exact Measure.map_id
  · intro I
    exact congrArg (fun Q : ProbabilityMeasure (I → ℝ) => (Q : Measure (I → ℝ))) (hf I)

theorem transverse_common_gaussian_path_limit {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) {T : ℝ} (hT : 0 ≤ T) :
    letI : IsProbabilityMeasure (independentConditionedPairLaw ν (realPosition (step e))) :=
      independentConditionedPairLaw_probability ν _
        (ne_of_gt (noDrop_positive_of_directionallyTransient ν _ htrans))
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      TendstoInDistribution (fun i P => scaledPolygon
        (fun k => commonIncrementProcess (realPosition (step e)) f k P) (r i)
        (fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) (r i)) T)
        atTop id (fun _ => independentConditionedPairLaw ν (realPosition (step e))) W ∧
      ∀ I : Finset unitInterval,
        (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) =
          gaussianPathFiniteLaw T I := by
  let ℓ := realPosition (step e)
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) :=
    independentConditionedPairLaw_probability ν ℓ
      (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  exact gaussian_iid_path_limit _ _ (measurable_commonIncrementProcess ℓ f)
    (commonIncrements_independent ν ℓ htrans (signedHeight e)
      (signedHeight_projection e) (signedHeight_step_le e) f)
    (commonIncrements_identDistrib ν ℓ htrans (signedHeight e)
      (signedHeight_projection e) (signedHeight_step_le e) f)
    (independent_commonWordIncrement_symmetric ν ℓ htrans f)
    (independent_commonWordIncrement_integrable ν hue ℓ (signed_direction_unit e)
      htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f)
    (independent_commonWordIncrement_nonzero ν hue e f hef htrans) r hr hT

noncomputable def renewalSum (L : ℕ → ℕ) (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, L k

lemma renewalSum_zero (L : ℕ → ℕ) : renewalSum L 0 = 0 := by simp [renewalSum]
lemma renewalSum_succ (L : ℕ → ℕ) (n : ℕ) : renewalSum L (n+1) = renewalSum L n+L n := by
  simp [renewalSum,Finset.sum_range_succ]
lemma renewalSum_ge (L : ℕ → ℕ) (hL : ∀ k, 0 < L k) (n : ℕ) : n ≤ renewalSum L n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => rw [renewalSum_succ]; have := hL n; omega
lemma renewalSum_strictMono (L : ℕ → ℕ) (hL : ∀ k, 0 < L k) : StrictMono (renewalSum L) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [renewalSum_succ]
  exact Nat.lt_add_of_pos_right (hL n)

open scoped Classical in
noncomputable def renewalCount (L : ℕ → ℕ) (h : ℕ) : ℕ :=
  Nat.findGreatest (fun k => renewalSum L k ≤ h) h
lemma renewalCount_le (L : ℕ → ℕ) (h : ℕ) : renewalCount L h ≤ h := Nat.findGreatest_le _
lemma renewalCount_lower (L : ℕ → ℕ) (h : ℕ) : renewalSum L (renewalCount L h) ≤ h := by
  classical
  exact Nat.findGreatest_spec (P := fun k => renewalSum L k ≤ h) (Nat.zero_le h)
    (by rw [renewalSum_zero]; exact Nat.zero_le _)
lemma renewalCount_upper (L : ℕ → ℕ) (hL : ∀ k, 0 < L k) (h : ℕ) :
    h < renewalSum L (renewalCount L h+1) := by
  classical
  by_cases hk : renewalCount L h+1 ≤ h
  · exact Nat.lt_of_not_ge (Nat.findGreatest_is_greatest
      (P := fun k => renewalSum L k ≤ h) (Nat.lt_succ_self _) hk)
  · exact (Nat.lt_of_not_ge hk).trans_le (renewalSum_ge L hL _)
lemma renewalCount_zero (L : ℕ → ℕ) : renewalCount L 0 = 0 := by simp [renewalCount]
lemma renewalCount_monotone (L : ℕ → ℕ) : Monotone (renewalCount L) := by
  intro a b hab
  exact Nat.findGreatest_mono (fun _ h => h.trans hab) hab

lemma linear_error_uniform (f : ℕ → ℝ) (c : ℝ)
    (hf : Tendsto (fun k : ℕ => f k/k) atTop (𝓝 c))
    {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ k : ℕ, (k : ℝ) ≤ T*a → |f k-c*k| ≤ ε*a := by
  have hδ : 0 < ε/(T+1) := div_pos hε (by linarith)
  obtain ⟨K,hK⟩ := (Metric.tendsto_atTop.1 hf) (ε/(T+1)) hδ
  let C := ∑ k ∈ Finset.range (K+1), |f k-c*k|
  filter_upwards [eventually_ge_atTop (max 0 (C/ε))] with a ha k hk
  have ha0 : 0 ≤ a := (le_max_left _ _).trans ha
  by_cases hkK : k ≤ K
  · have h1 : |f k-c*k| ≤ C := Finset.single_le_sum (fun j _ => abs_nonneg (f j-c*j))
      (Finset.mem_range.2 (Nat.lt_succ_of_le hkK))
    exact h1.trans (by simpa [mul_comm] using (div_le_iff₀ hε).1 ((le_max_right _ _).trans ha))
  · have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have he : f k/(k : ℝ)-c = (f k-c*k)/k := by field_simp
    have hbound := hK k (by omega)
    rw [Real.dist_eq,he,abs_div,abs_of_pos hkpos] at hbound
    have hh := (div_lt_iff₀ hkpos).1 hbound
    have h2 : (ε/(T+1))*(k : ℝ) ≤ ε*a := by
      calc
        _ ≤ (ε/(T+1))*(T*a) := mul_le_mul_of_nonneg_left hk hδ.le
        _ ≤ ε*a := by
          have hd : T/(T+1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
          calc
            _ = (ε*a)*(T/(T+1)) := by ring
            _ ≤ ε*a := mul_le_of_le_one_right (mul_nonneg hε.le ha0) hd
    exact hh.le.trans h2

end DirectionalTransience
end
end

end OAI
