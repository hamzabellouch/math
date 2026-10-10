import OAI.Dynamics.MultipleMixing.WeakLimits

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [TopologicalSpace A] [BorelSpace A]

def fullShift : (ℤ → A) ≃ₜ (ℤ → A) where
  toFun x q := x (q+1)
  invFun x q := x (q-1)
  left_inv x := by funext q; simp
  right_inv x := by funext q; simp
  continuous_toFun := continuous_pi fun _ => continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_apply _

omit [MeasurableSpace A] [BorelSpace A] in
lemma fullShift_iterate (n : ℕ) (x : ℤ → A) (q : ℤ) :
    (fullShift^[n]) x q = x (q+n) := by
  induction n generalizing q with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (fullShift^[n]) x (q+1) = _
    rw [ih]
    congr 1
    push_cast
    ring

def symbolicCode (T : Ω ≃ᵐ Ω) (a : Ω → A) : Ω → (ℤ → A) :=
  fun x q => a (timeMap T q x)

omit [TopologicalSpace A] [BorelSpace A] in
lemma symbolicCode_measurable (T : Ω ≃ᵐ Ω) (a : Ω → A) (ha : Measurable a) :
    Measurable (symbolicCode T a) := Measurable.of_eval fun q => ha.comp (timeMap_measurable T q)

omit [MeasurableSpace A] [BorelSpace A] in
lemma symbolicCode_time (T : Ω ≃ᵐ Ω) (a : Ω → A) (n : ℕ) (x : Ω) :
    symbolicCode T a (timeMap T n x) = (fullShift^[n]) (symbolicCode T a x) := by
  funext q
  rw [fullShift_iterate]
  exact congrArg a (congrFun (timeMap_add T q n).symm x)

variable [SecondCountableTopology A]
lemma symbolicShift_preserving (μ : Measure Ω) (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (a : Ω → A) (ha : Measurable a) :
    MeasurePreserving fullShift (μ.map (symbolicCode T a)) (μ.map (symbolicCode T a)) := by
  refine ⟨fullShift.continuous.measurable,?_⟩
  rw [Measure.map_map fullShift.continuous.measurable (symbolicCode_measurable T a ha)]
  have he : fullShift ∘ symbolicCode T a = symbolicCode T a ∘ T := by
    funext x
    simpa only [Function.comp_apply,timeMap_nat,Function.iterate_one] using (symbolicCode_time T a 1 x).symm
  rw [he,←Measure.map_map (symbolicCode_measurable T a ha) T.measurable,hT.map_eq]

omit [SecondCountableTopology A] [TopologicalSpace A] [BorelSpace A] in
lemma symbolicCode_preserving (μ : Measure Ω) (T : Ω ≃ᵐ Ω) (a : Ω → A) (ha : Measurable a) :
    MeasurePreserving (symbolicCode T a) μ (μ.map (symbolicCode T a)) :=
  ⟨symbolicCode_measurable T a ha,rfl⟩

lemma symbolicShift_mixing (μ : Measure Ω) (T : Ω ≃ᵐ Ω)
    (hmix : ∀ s t : Set Ω, MeasurableSet s → MeasurableSet t →
      Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t)))
    (a : Ω → A) (ha : Measurable a) :
    ∀ s t : Set (ℤ → A), MeasurableSet s → MeasurableSet t →
      Tendsto (fun n : ℕ => μ.map (symbolicCode T a) (s ∩ (fullShift^[n]) ⁻¹' t)) atTop
        (𝓝 (μ.map (symbolicCode T a) s * μ.map (symbolicCode T a) t)) := by
  intro s t hs ht
  have hc := symbolicCode_measurable T a ha
  have h := hmix (symbolicCode T a ⁻¹' s) (symbolicCode T a ⁻¹' t) (hc hs) (hc ht)
  rw [Measure.map_apply hc hs,Measure.map_apply hc ht]
  convert h using 1
  funext n
  rw [Measure.map_apply hc (hs.inter ((fullShift.continuous.iterate n).measurable ht))]
  congr 1
  ext x
  simp only [Set.mem_preimage,Set.mem_inter_iff]
  rw [←symbolicCode_time,timeMap_nat]

lemma symbolicCode_rectangles {I : Type*} [Fintype I]
    (μ : Measure Ω) (T : Ω ≃ᵐ Ω) (a : Ω → A) (ha : Measurable a)
    (d : I → ℕ) (s : I → Set (ℤ → A)) (hs : ∀ i, MeasurableSet (s i)) :
    μ.map (symbolicCode T a) (⋂ i, (fullShift^[d i]) ⁻¹' s i) =
      μ (⋂ i, (T^[d i]) ⁻¹' (symbolicCode T a ⁻¹' s i)) := by
  rw [Measure.map_apply (symbolicCode_measurable T a ha)
    (MeasurableSet.iInter fun i => (fullShift.continuous.iterate (d i)).measurable (hs i))]
  congr 1
  ext x
  simp only [Set.mem_preimage,Set.mem_iInter]
  simp_rw [←symbolicCode_time,timeMap_nat]

omit [SecondCountableTopology A] [TopologicalSpace A] [BorelSpace A] in
lemma symbolicCode_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (T : Ω ≃ᵐ Ω) (a : Ω → A) (ha : Measurable a)
    (f : (ℤ → A) → E) (hf : AEStronglyMeasurable f (μ.map (symbolicCode T a))) :
    (∫ x, f x ∂μ.map (symbolicCode T a)) = ∫ x, f (symbolicCode T a x) ∂μ :=
  integral_map (symbolicCode_measurable T a ha).aemeasurable hf

variable [Fintype A] [MeasurableSingletonClass A]
lemma symbolicCode_entropy {B : Type*} [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω ≃ᵐ Ω) (a : Ω → A) (ha : Measurable a)
    (b : A → B) (n : ℕ) :
    randomEntropy (μ.map (symbolicCode T a)) (fun x : ℤ → A => fun i : Fin n => b ((fullShift^[i.val]) x 0)) =
      randomEntropy μ (fun x => fun i : Fin n => b (a (timeMap T i.val x))) := by
  let : IsProbabilityMeasure (μ.map (symbolicCode T a)) := (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) (symbolicCode_measurable T a ha).aemeasurable
  have hb : Measurable (fun x : ℤ → A => fun i : Fin n => b ((fullShift^[i.val]) x 0)) :=
    Measurable.of_eval fun i => (measurable_of_finite b).comp
      ((measurable_pi_apply 0).comp (fullShift.continuous.iterate i.val).measurable)
  have h := randomEntropy_measurePreserving μ (μ.map (symbolicCode T a))
    (symbolicCode_preserving μ T a ha) _ hb
  simpa [Function.comp_def,fullShift_iterate,symbolicCode] using h.symm
end

section
open MeasureTheory Filter TopologicalSpace
open scoped Topology BigOperators
variable {Ω : Type*} {I : Type} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]

theorem finite_alphabet_no_witness (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hmix : ∀ s t : Set Ω, MeasurableSet s → MeasurableSet t →
      Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t)))
    (hk : 3 ≤ Fintype.card I) (d : ℕ → I → ℕ)
    (hrect : ∀ J : Finset I, J ≠ Finset.univ → ∀ s : J → Set Ω,
      (∀ j, MeasurableSet (s j)) → Tendsto
        (fun r => μ (⋂ j : J, (T^[d r j]) ⁻¹' s j)) atTop
        (𝓝 (∏ j : J, μ (s j))))
    {A B : Type} [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
    [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (a : Ω → A) (ha : Measurable a) (b : A → B)
    (v : B → ℝ) (hcenter : ∫ x, v (b (a x)) ∂μ = 0)
    (hH : Tendsto (fun n : ℕ => randomEntropy μ
        (fun x => fun i : Fin n => b (a ((T^[i.val]) x))) / n) atTop (𝓝 0))
    (i : I) (f : I → A → ℝ) (hb : ∀ j z, |f j z| ≤ 1)
    (hi : ∀ z, f i z = v (b z)) (δ : ℝ) (hδ : 0 < δ)
    (hc : ∀ r, δ ≤ ∫ x, ∏ j, f j (a ((T^[d r j]) x)) ∂μ) : False := by
  let X : ArrayObjects.StandardSpace := ⟨ℤ → A,inferInstance,inferInstance,inferInstance⟩
  let C : Ω → X := symbolicCode T a
  have hC : Measurable C := symbolicCode_measurable T a ha
  let : IsProbabilityMeasure (μ.map C) := (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) hC.aemeasurable
  let ν : ProbabilityMeasure X := ⟨μ.map C,inferInstance⟩
  let S : X ≃ₜ X := fullShift
  let F : I → C(X,ℝ) := fun j => ⟨fun x => f j (x 0),
    (continuous_of_discreteTopology (f := f j)).comp (continuous_apply 0)⟩
  have hp : MeasurePreserving S ν ν := symbolicShift_preserving μ T hT a ha
  have hr : ∀ J : Finset I, J ≠ Finset.univ → ∀ s : J → Set X,
      (∀ j, MeasurableSet (s j)) → Tendsto
        (fun r => (ν : Measure X) (⋂ j : J, (S^[d r j]) ⁻¹' s j)) atTop
        (𝓝 (∏ j : J, (ν : Measure X) (s j))) := by
    intro J hJ s hs
    have hh := hrect J hJ (fun j => C ⁻¹' s j) (fun j => hC (hs j))
    convert hh using 1
    · funext r
      exact symbolicCode_rectangles μ T a ha _ s hs
    · congr 1
      apply Finset.prod_congr rfl
      intro j _
      exact Measure.map_apply hC (hs j)
  have hctr : ∫ x : X, v (b (x 0)) ∂(ν : Measure X) = 0 := by
    change (∫ x : ℤ → A, v (b (x 0)) ∂μ.map C) = 0
    have hm : AEStronglyMeasurable (fun x : ℤ → A => v (b (x 0))) (μ.map C) :=
      (((measurable_of_finite v).comp ((measurable_of_finite b).comp (measurable_pi_apply 0))).aestronglyMeasurable)
    rw [integral_map hC.aemeasurable hm]
    change (∫ x, v (b (a (timeMap T 0 x))) ∂μ) = 0
    simpa only [timeMap_zero,id_eq] using hcenter
  have hent : Tendsto (fun n : ℕ => wordEntropy (η := (ν : Measure X))
      (fun m x => b ((S^[m]) x 0)) n / n) atTop (𝓝 0) := by
    convert hH using 1
    funext n
    congr 1
    change randomEntropy (μ.map C) (fun x => fun j : Fin n => b ((S^[j.val]) x 0)) = _
    simpa only [timeMap_nat] using symbolicCode_entropy μ T a ha b n
  apply ArrayObjects.compact_zero_entropy_no_witness S d ν hp hr hk
    (symbolicShift_mixing μ T hmix a ha) (fun x => b (x 0))
    ((measurable_of_finite b).comp (measurable_pi_apply 0)) v hctr hent i F
    (fun j x => hb j (x 0)) (fun x => hi (x 0)) δ hδ
  intro r
  change δ ≤ ∫ x : X, ∏ j, f j ((S^[d r j]) x 0) ∂μ.map C
  have hm : AEStronglyMeasurable (fun x : X => ∏ j, f j ((S^[d r j]) x 0)) (μ.map C) := by
    apply Continuous.aestronglyMeasurable
    exact continuous_finsetProd Finset.univ fun j _ =>
      (continuous_of_discreteTopology (f := f j)).comp
        ((continuous_apply 0).comp (S.continuous.iterate (d r j)))
  rw [integral_map hC.aemeasurable hm]
  convert hc r using 1
  apply integral_congr_ae
  filter_upwards with x
  apply Finset.prod_congr rfl
  intro j _
  change f j ((fullShift^[d r j]) (symbolicCode T a x) 0) = _
  rw [fullShift_iterate,zero_add]
  change f j (a (timeMap T (d r j) x)) = _
  rw [timeMap_nat]
end

section
open Filter
open scoped Topology
lemma exists_signed_subsequence {x : ℕ → ℝ} (hx : ¬Tendsto x atTop (𝓝 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ σ : ℝ, |σ| = 1 ∧ ∃ u : ℕ → ℕ,
      StrictMono u ∧ ∀ n, ε ≤ σ*x (u n) := by
  have hh : ¬∀ ε > (0:ℝ), ∀ᶠ n in atTop, |x n| < ε := by
    intro h
    apply hx
    exact Metric.tendsto_nhds.mpr (by simpa only [Real.dist_eq,sub_zero] using h)
  push Not at hh
  obtain ⟨ε,hε,he⟩ := hh
  have hf : ∃ᶠ n in atTop, ε ≤ x n ∨ x n ≤ -ε := by
    simpa only [not_lt,le_abs,le_neg] using he
  rcases frequently_or_distrib.mp hf with hp | hn
  · obtain ⟨u,hu,hp⟩ := extraction_of_frequently_atTop hp
    exact ⟨ε,hε,1,by norm_num,u,hu,fun n => by simpa using hp n⟩
  · obtain ⟨u,hu,hn⟩ := extraction_of_frequently_atTop hn
    exact ⟨ε,hε,-1,by norm_num,u,hu,fun n => by have := hn n; linarith⟩
end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω : Type*} {I : Type} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]

lemma prod_sign_one (i : I) (σ : ℝ) (z : I → ℝ) :
    (∏ j, (if j=i then σ else 1)*z j) = σ*∏ j, z j := by
  rw [Finset.prod_mul_distrib]
  simp

theorem finite_alphabet_correlation_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hmix : ∀ s t : Set Ω, MeasurableSet s → MeasurableSet t →
      Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t)))
    (hk : 3 ≤ Fintype.card I) (d : ℕ → I → ℕ)
    (hrect : ∀ J : Finset I, J ≠ Finset.univ → ∀ s : J → Set Ω,
      (∀ j, MeasurableSet (s j)) → Tendsto
        (fun r => μ (⋂ j : J, (T^[d r j]) ⁻¹' s j)) atTop
        (𝓝 (∏ j : J, μ (s j))))
    {A B : Type} [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
    [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (a : Ω → A) (ha : Measurable a) (b : A → B)
    (v : B → ℝ) (hcenter : ∫ x, v (b (a x)) ∂μ = 0)
    (hH : Tendsto (fun n : ℕ => randomEntropy μ
        (fun x => fun i : Fin n => b (a ((T^[i.val]) x))) / n) atTop (𝓝 0))
    (i : I) (f : I → A → ℝ) (hb : ∀ j z, |f j z| ≤ 1) (hi : ∀ z, f i z = v (b z)) :
    Tendsto (fun r => ∫ x, ∏ j, f j (a ((T^[d r j]) x)) ∂μ) atTop (𝓝 0) := by
  by_contra hn
  obtain ⟨δ,hδ,σ,hσ,u,hu,hpos⟩ := exists_signed_subsequence hn
  let F : I → A → ℝ := fun j z => (if j=i then σ else 1)*f j z
  apply finite_alphabet_no_witness μ T hT hmix hk (fun r => d (u r))
    (fun J hJ s hs => (hrect J hJ s hs).comp hu.tendsto_atTop) a ha b
    (fun z => σ*v z) ?_ hH i F ?_ ?_ δ hδ ?_
  · rw [integral_const_mul,hcenter,mul_zero]
  · intro j z
    dsimp [F]
    rw [abs_mul]
    split_ifs <;> simpa only [hσ,abs_one,one_mul] using hb j z
  · intro z
    simp [F,hi]
  · intro r
    change δ ≤ ∫ x, ∏ j, (if j=i then σ else 1)*f j (a ((T^[d (u r) j]) x)) ∂μ
    simp_rw [prod_sign_one]
    rw [integral_const_mul]
    exact hpos r
end

section
open MeasureTheory Filter
open scoped Topology
variable {Ω A B : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]

abbrev observableProcess (T : Ω ≃ᵐ Ω) (a : Ω → A) : ℤ → Ω → A :=
  fun q x => a (timeMap T q x)

abbrev observableTail (T : Ω ≃ᵐ Ω) (a : Ω → A) : MeasurableSpace Ω :=
  processTail μ (observableProcess T a)

omit [Fintype A] [Nonempty A] [MeasurableSingletonClass A] [MeasurableSpace A] [IsProbabilityMeasure μ] in
lemma observableProcess_translate (T : Ω ≃ᵐ Ω) (a : Ω → A) (s t : ℤ) (x : Ω) :
    observableProcess T a (s+t) x = observableProcess T a s (timeMap T t x) := by
  exact congrArg a (congrFun (timeMap_add T s t) x)

omit [Fintype A] [Nonempty A] [MeasurableSingletonClass A] [IsProbabilityMeasure μ] in
lemma observableProcess_measurable (T : Ω ≃ᵐ Ω) (a : Ω → A) (ha : Measurable a) (q : ℤ) :
    Measurable (observableProcess T a q) := ha.comp (timeMap_measurable T q)

theorem finite_tail_entropy_zero (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (a : Ω → A) (ha : Measurable a) (b : Ω → B) (hb : Measurable[observableTail μ T a] b) :
    Tendsto (fun n : ℕ => randomEntropy μ (fun x => fun i : Fin n => b ((T^[i.val]) x)) / n)
      atTop (𝓝 0) := by
  have hbm : Measurable b := hb.mono (processTail_le μ _) le_rfl
  have hh := tail_process_entropy_zero μ (timeMap T) (timeMap_preserving μ T hT)
    (observableProcess T a) (observableProcess_measurable T a ha) (observableProcess_translate T a)
    (observableProcess T b) (observableProcess_measurable T b hbm) (observableProcess_translate T b)
    (fun t s => measurable_tail_translate μ (timeMap T) (timeMap_preserving μ T hT)
      (observableProcess T a) (observableProcess_translate T a) b hb s t)
  change Tendsto (fun n : ℕ => randomEntropy μ (fun x => fun i : Fin n => b (timeMap T (0+(i.val:ℤ)) x)) / n) atTop (𝓝 0) at hh
  simpa only [zero_add,timeMap_nat] using hh
end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω : Type*} {I A B : Type} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
    [Fintype B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]
    [TopologicalSpace B] [DiscreteTopology B] [BorelSpace B]

theorem tail_finite_correlation_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hmix : ∀ s t : Set Ω, MeasurableSet s → MeasurableSet t →
      Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t)))
    (hk : 3 ≤ Fintype.card I) (d : ℕ → I → ℕ)
    (hrect : ∀ J : Finset I, J ≠ Finset.univ → ∀ s : J → Set Ω,
      (∀ j, MeasurableSet (s j)) → Tendsto
        (fun r => μ (⋂ j : J, (T^[d r j]) ⁻¹' s j)) atTop
        (𝓝 (∏ j : J, μ (s j))))
    (a : Ω → A) (ha : Measurable a) (b : Ω → B)
    (hb : Measurable[observableTail μ T a] b) (v : B → ℝ)
    (hc : ∫ x, v (b x) ∂μ = 0) (hv : ∀ z, |v z| ≤ 1)
    (i : I) (f : I → A → ℝ) (hf : ∀ j z, |f j z| ≤ 1) :
    Tendsto (fun r => ∫ x, ∏ j, if j=i then v (b ((T^[d r j]) x))
      else f j (a ((T^[d r j]) x)) ∂μ) atTop (𝓝 0) := by
  have hbm : Measurable b := hb.mono (processTail_le μ _) le_rfl
  exact finite_alphabet_correlation_zero μ T hT hmix hk d hrect
    (fun x => (a x,b x)) (ha.prodMk hbm) Prod.snd v hc
    (finite_tail_entropy_zero μ T hT a ha b hb) i
    (fun j z => if j=i then v z.2 else f j z.1)
    (fun j z => by split_ifs; exact hv _; exact hf _ _) (fun _ => ite_eq_left rfl)
end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω : Type*} {I A : Type} [m₀ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]

lemma prod_replace_one (i : I) (v : ℝ) (f : I → ℝ) :
    (∏ j, if j=i then v else f j) = v * ∏ j ∈ Finset.univ.erase i, f j := by
  rw [←Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  rw [ite_eq_left rfl]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [ite_eq_right (Finset.ne_of_mem_erase hj)]

lemma prod_replace_dep (i : I) (v f : I → ℝ) :
    (∏ j, if j=i then v j else f j) = v i * ∏ j ∈ Finset.univ.erase i, f j := by
  rw [←Finset.mul_prod_erase _ _ (Finset.mem_univ i),ite_eq_left rfl]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [ite_eq_right (Finset.ne_of_mem_erase hj)]

lemma integral_comp_preserving (μ : Measure Ω) (U : Ω → Ω) (hU : MeasurePreserving U μ μ)
    (f : Ω → ℝ) (hf : Measurable f) : (∫ x, f (U x) ∂μ) = ∫ x, f x ∂μ := by
  have h := integral_map (μ := μ) hU.measurable.aemeasurable
    (hf.aestronglyMeasurable (μ := Measure.map U μ))
  simpa only [hU.map_eq] using h.symm

lemma integral_mean_interval (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hb : ∀ x, g x ∈ Set.Icc (0:ℝ) 1) :
    (∫ x, g x ∂μ) ∈ Set.Icc (0:ℝ) 1 := by
  have hi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hb x).1]; exact (hb x).2)
  exact ⟨integral_nonneg fun x => (hb x).1, by
    simpa using integral_mono hi (integrable_const (1:ℝ)) (fun x => (hb x).2)⟩

lemma centered_pairing_distance (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → Ω) (hU : MeasurePreserving U μ μ)
    (g s w : Ω → ℝ) (hg : Measurable g) (hs : Measurable s) (hw : Measurable w)
    (hgb : ∀ x, g x ∈ Set.Icc (0:ℝ) 1) (hsb : ∀ x, s x ∈ Set.Icc (0:ℝ) 1)
    (hwb : ∀ x, |w x| ≤ 1) :
    |(∫ x, (g (U x)-∫ y, g y ∂μ)*w x ∂μ) -
      (∫ x, (s (U x)-∫ y, s y ∂μ)*w x ∂μ)| ≤ 2*∫ x, |s x-g x| ∂μ := by
  have bound {v : Ω → ℝ} (hv : Measurable v) (hb : ∀ x, |v x| ≤ 1) : Integrable v μ :=
    Integrable.of_bound hv.aestronglyMeasurable 1 (Eventually.of_forall fun x => by simpa using hb x)
  have hg1 x : |g x| ≤ 1 := by rw [abs_of_nonneg (hgb x).1]; exact (hgb x).2
  have hs1 x : |s x| ≤ 1 := by rw [abs_of_nonneg (hsb x).1]; exact (hsb x).2
  have hgi := bound hg hg1
  have hsi := bound hs hs1
  have hgm := integral_mean_interval μ g hg hgb
  have hsm := integral_mean_interval μ s hs hsb
  have cg x : |g (U x)-∫ y, g y ∂μ| ≤ 1 := abs_le.mpr ⟨by have := (hgb (U x)).1; linarith [hgm.2],by have := (hgb (U x)).2; linarith [hgm.1]⟩
  have cs x : |s (U x)-∫ y, s y ∂μ| ≤ 1 := abs_le.mpr ⟨by have := (hsb (U x)).1; linarith [hsm.2],by have := (hsb (U x)).2; linarith [hsm.1]⟩
  have hgp : Integrable (fun x => (g (U x)-∫ y, g y ∂μ)*w x) μ := bound (((hg.comp hU.measurable).sub measurable_const).mul hw)
    (fun x => by rw [abs_mul]; exact (fun leftBound rightNonneg rightBound => (mul_le_of_le_one_left rightNonneg leftBound).trans rightBound) (cg x) (abs_nonneg _) (hwb x))
  have hsp : Integrable (fun x => (s (U x)-∫ y, s y ∂μ)*w x) μ := bound (((hs.comp hU.measurable).sub measurable_const).mul hw)
    (fun x => by rw [abs_mul]; exact (fun leftBound rightNonneg rightBound => (mul_le_of_le_one_left rightNonneg leftBound).trans rightBound) (cs x) (abs_nonneg _) (hwb x))
  rw [←integral_sub hgp hsp]
  have hiabs : Integrable (fun x => |s x-g x|) μ := (hsi.sub hgi).abs
  have hiU : Integrable (fun x => |s (U x)-g (U x)|) μ := hU.integrable_comp_of_integrable hiabs
  have hmean : |(∫ y, s y ∂μ)-(∫ y, g y ∂μ)| ≤ ∫ y, |s y-g y| ∂μ := by
    rw [←integral_sub hsi hgi]
    exact abs_integral_le_integral_abs
  calc
    _ ≤ ∫ x, |(g (U x)-∫ y, g y ∂μ)*w x-(s (U x)-∫ y, s y ∂μ)*w x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (|s (U x)-g (U x)|+|(∫ y, s y ∂μ)-(∫ y, g y ∂μ)|) ∂μ := by
      apply integral_mono (hgp.sub hsp).abs (hiU.add (integrable_const _))
      intro x
      calc
        _ = |(g (U x)-s (U x))+((∫ y, s y ∂μ)-(∫ y, g y ∂μ))| * |w x| := by simp only [Pi.sub_apply]; rw [←abs_mul]; congr 1; ring
        _ ≤ |(g (U x)-s (U x))+((∫ y, s y ∂μ)-(∫ y, g y ∂μ))| := mul_le_of_le_one_right (abs_nonneg _) (hwb x)
        _ ≤ _ := by simpa only [Pi.add_apply,Pi.sub_apply,Function.comp_apply,abs_sub_comm] using abs_add_le (g (U x)-s (U x)) ((∫ y, s y ∂μ)-(∫ y, g y ∂μ))
    _ = (∫ x, |s x-g x| ∂μ)+|(∫ y, s y ∂μ)-(∫ y, g y ∂μ)| := by
      rw [integral_add hiU (integrable_const _),integral_comp_preserving μ U hU (fun x => |s x-g x|) (hs.sub hg).abs]
      simp
    _ ≤ _ := by linarith

variable [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]

theorem tail_correlation_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hmix : ∀ s t : Set Ω, MeasurableSet s → MeasurableSet t →
      Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t)))
    (hk : 3 ≤ Fintype.card I) (d : ℕ → I → ℕ)
    (hrect : ∀ J : Finset I, J ≠ Finset.univ → ∀ s : J → Set Ω,
      (∀ j, MeasurableSet (s j)) → Tendsto
        (fun r => μ (⋂ j : J, (T^[d r j]) ⁻¹' s j)) atTop
        (𝓝 (∏ j : J, μ (s j))))
    (a : Ω → A) (ha : Measurable a) (g : Ω → ℝ)
    (hg : Measurable[observableTail μ T a] g) (hgb : ∀ x, g x ∈ Set.Icc (0:ℝ) 1)
    (i : I) (f : I → A → ℝ) (hf : ∀ j z, |f j z| ≤ 1) :
    Tendsto (fun r => ∫ x, (g ((T^[d r i]) x)-∫ y, g y ∂μ) *
      ∏ j ∈ Finset.univ.erase i, f j (a ((T^[d r j]) x)) ∂μ) atTop (𝓝 0) := by
  let m := observableTail μ T a
  have hm : m ≤ m₀ := processTail_le (m₀ := m₀) μ _
  let : MeasurableSpace Ω := m₀
  have hgm : Measurable g := hg.mono hm le_rfl
  let w r x := ∏ j ∈ Finset.univ.erase i, f j (a ((T^[d r j]) x))
  have hwm r : Measurable (w r) := Finset.measurable_prod _ (fun j _ =>
    (measurable_of_finite (f j)).comp (ha.comp (T.measurable.iterate _)))
  have hwb r x : |w r x| ≤ 1 := by
    dsimp [w]
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun j _ => hf j _)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨s,hs,hsapprox⟩ := exists_simple_interval_approx μ m hm g hg hgb (ε/4) (by positivity)
  let : MeasurableSpace Ω := m
  let B := ↥s.range
  let b : Ω → B := fun x => ⟨s x,s.mem_range_self x⟩
  have hbm : Measurable[m] b := s.measurable.subtype_mk
  have hsm : Measurable[m₀] (fun x => s x) := s.measurable.mono hm le_rfl
  have hsrange : ∀ z ∈ s.range, z ∈ Set.Icc (0:ℝ) 1 := SimpleFunc.forall_mem_range.mpr hs
  let : MeasurableSpace Ω := m₀
  let : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  let : Nonempty B := ⟨b (Classical.arbitrary Ω)⟩
  let v : B → ℝ := fun z => z.val-∫ x, s x ∂μ
  have hmean := integral_mean_interval μ s hsm hs
  have hv z : |v z| ≤ 1 := by
    have hz := hsrange z.val z.property
    dsimp [v]
    exact abs_le.mpr ⟨by linarith [hmean.2,hz.1],by linarith [hmean.1,hz.2]⟩
  have hc : ∫ x, v (b x) ∂μ = 0 := by
    change (∫ x, s x-(∫ y, s y ∂μ) ∂μ) = 0
    have hi : Integrable (fun x => s x) μ := Integrable.of_bound hsm.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hs x).1]; exact (hs x).2)
    rw [integral_sub hi (integrable_const _)]
    simp
  have ht := tail_finite_correlation_zero μ T hT hmix hk d hrect a ha b hbm v hc hv i f hf
  have ht' : Tendsto (fun r => ∫ x, (s ((T^[d r i]) x)-∫ y, s y ∂μ)*w r x ∂μ) atTop (𝓝 0) := by
    simpa only [prod_replace_dep,b,v,w] using ht
  have he := ht'.eventually (Metric.ball_mem_nhds (0:ℝ) (by positivity : 0 < ε/2))
  filter_upwards [he] with r hr
  change dist (∫ x, (g ((T^[d r i]) x)-∫ y, g y ∂μ)*w r x ∂μ) 0 < ε
  rw [Real.dist_eq,sub_zero]
  have hd := centered_pairing_distance μ (T^[d r i]) (hT.iterate _) g s (w r) hgm hsm (hwm r) hgb hs (hwb r)
  have hr' : |∫ x, (s ((T^[d r i]) x)-∫ y, s y ∂μ)*w r x ∂μ| < ε/2 := by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hr
  have htri := abs_add_le
    ((∫ x, (g ((T^[d r i]) x)-∫ y, g y ∂μ)*w r x ∂μ) -
      (∫ x, (s ((T^[d r i]) x)-∫ y, s y ∂μ)*w r x ∂μ))
    (∫ x, (s ((T^[d r i]) x)-∫ y, s y ∂μ)*w r x ∂μ)
  rw [sub_add_cancel] at htri
  linarith
end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω : Type*} {I A : Type} [m₀ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    [retained19 : Fintype A] [retained20 : Nonempty A] [MeasurableSpace A] [retained21 : MeasurableSingletonClass A]
    [retained22 : TopologicalSpace A] [retained23 : DiscreteTopology A] [retained24 : BorelSpace A]

include m₀ retained19 retained20 retained21 retained22 retained23 retained24 in
lemma processPast_coord (F : ℤ → Ω → A) {q t : ℤ} (h : q < t) :
    Measurable[processPast F t] (F q) := by
  let _ := m₀
  let _ := retained19
  let _ := retained20
  let _ := retained21
  let _ := retained22
  let _ := retained23
  let _ := retained24
  apply measurable_iff_comap_le.mpr
  rw [processPast_eq_generators]
  exact le_iSup_of_le ⟨q,h⟩ le_rfl

lemma real_integrable_bound (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)

theorem remote_last_replacement (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (d : ℕ → I → ℕ) (i : I) (hremote : ∀ r j, j ≠ i → d r j+r < d r i)
    (a : Ω → A) (ha : Measurable a) (f : I → A → ℝ)
    (hf : ∀ j z, f j z ∈ Set.Icc (0:ℝ) 1) :
    Tendsto (fun r => ∫ x,
      (f i (a ((T^[d r i]) x)) - clippedConditional μ (observableTail μ T a) (fun y => f i (a y)) ((T^[d r i]) x)) *
      ∏ j ∈ Finset.univ.erase i, f j (a ((T^[d r j]) x)) ∂μ) atTop (𝓝 0) := by
  let F := observableProcess T a
  let m (n : ℕ) := processPast F (-(n:ℤ))
  have hm n : m n ≤ m₀ := processPast_le F (observableProcess_measurable T a ha) _
  have hanti : Antitone m := fun n l h => processPast_mono F (by omega)
  let w r x := ∏ j ∈ Finset.univ.erase i, f j (F ((d r j:ℤ)-(d r i:ℤ)) x)
  have hw r : Measurable[m r] (w r) := by
    apply Finset.measurable_prod
    intro j hj
    apply (measurable_of_finite (f j)).comp
    apply processPast_coord
    have hh := hremote r j (Finset.ne_of_mem_erase hj)
    omega
  have hwb r x : |w r x| ≤ 1 := by
    dsimp [w]
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun j _ => by
      rw [abs_of_nonneg (hf j _).1]; exact (hf j _).2)
  have hfm : Measurable (fun x => f i (a x)) := (measurable_of_finite _).comp ha
  have hfb x : |f i (a x)| ≤ 1 := by rw [abs_of_nonneg (hf i _).1]; exact (hf i _).2
  have hflp : MemLp (fun x => f i (a x)) 2 μ := MemLp.of_bound hfm.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hfb x)
  have hrep := integral_tail_replacement μ m hm hanti id tendsto_id _ hflp w hw hwb
  let g := clippedConditional μ (observableTail μ T a) (fun x => f i (a x))
  have hgm : Measurable g := (clippedConditional_measurable μ _ _).mono (processTail_le μ _) le_rfl
  have hgae : g =ᵐ[μ] μ[(fun x => f i (a x)) | observableTail μ T a] :=
    clippedConditional_ae μ _ _ (Eventually.of_forall fun x => hf i (a x))
  have he r : (∫ x, (f i (a x)-g x)*w r x ∂μ) =
      ∫ x, (f i (a x)-μ[(fun x => f i (a x)) | observableTail μ T a] x)*w r x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hgae] with x hx
    rw [hx]
  have ht : Tendsto (fun r => ∫ x, (f i (a x)-g x)*w r x ∂μ) atTop (𝓝 0) := by
    simpa only [he] using hrep
  convert ht using 1
  funext r
  have hwm : Measurable (w r) := (hw r).mono (hm r) le_rfl
  have hi := integral_comp_preserving μ (T^[d r i]) (hT.iterate (d r i)) (fun x => (f i (a x)-g x)*w r x) ((hfm.sub hgm).mul hwm)
  rw [←hi]
  apply integral_congr_ae
  filter_upwards with x
  change (_-g ((T^[d r i]) x))*_ = (_-g ((T^[d r i]) x))*_
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  dsimp [w,F,observableProcess]
  rw [←timeMap_nat T (d r i)]
  symm
  change f j (a ((timeMap T ((d r j:ℤ)-(d r i:ℤ)) ∘ timeMap T (d r i)) x)) = _
  rw [←timeMap_add,sub_add_cancel,timeMap_nat]
end

open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω : Type*} {I A : Type} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]

theorem last_centered_correlation_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hmix : ∀ s t : Set Ω, MeasurableSet s → MeasurableSet t →
      Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t)))
    (hk : 3 ≤ Fintype.card I) (d : ℕ → I → ℕ)
    (hrect : ∀ J : Finset I, J ≠ Finset.univ → ∀ s : J → Set Ω,
      (∀ j, MeasurableSet (s j)) → Tendsto
        (fun r => μ (⋂ j : J, (T^[d r j]) ⁻¹' s j)) atTop
        (𝓝 (∏ j : J, μ (s j))))
    (i : I) (hremote : ∀ r j, j ≠ i → d r j+r < d r i)
    (a : Ω → A) (ha : Measurable a) (f : I → A → ℝ)
    (hf : ∀ j z, f j z ∈ Set.Icc (0:ℝ) 1) :
    Tendsto (fun r => ∫ x, (f i (a ((T^[d r i]) x))-∫ y, f i (a y) ∂μ) *
      ∏ j ∈ Finset.univ.erase i, f j (a ((T^[d r j]) x)) ∂μ) atTop (𝓝 0) := by
  let g := clippedConditional μ (observableTail μ T a) (fun y => f i (a y))
  have hg : Measurable[observableTail μ T a] g := clippedConditional_measurable μ _ _
  have hgb x : g x ∈ Set.Icc (0:ℝ) 1 := clippedConditional_bounds μ _ _ x
  have hgm : Measurable g := hg.mono (processTail_le μ _) le_rfl
  have hf1 j z : |f j z| ≤ 1 := by rw [abs_of_nonneg (hf j z).1]; exact (hf j z).2
  have hc : (∫ x, g x ∂μ) = ∫ x, f i (a x) ∂μ :=
    clippedConditional_mean μ _ (processTail_le μ _) _ (Eventually.of_forall fun x => hf i (a x))
  have htail := tail_correlation_zero μ T hT hmix hk d hrect a ha g hg hgb i f hf1
  have hrep := remote_last_replacement μ T hT d i hremote a ha f hf
  have ht := hrep.add htail
  rw [add_zero] at ht
  convert ht using 1
  funext r
  let w x := ∏ j ∈ Finset.univ.erase i, f j (a ((T^[d r j]) x))
  have hwm : Measurable w := Finset.measurable_prod _ fun j _ =>
    (measurable_of_finite _).comp (ha.comp (T.measurable.iterate _))
  have hw x : |w x| ≤ 1 := by
    dsimp [w]
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun j _ => hf1 j _)
  have hfm : Measurable (fun x => f i (a ((T^[d r i]) x))) :=
    (measurable_of_finite _).comp (ha.comp (T.measurable.iterate _))
  have hi1 : Integrable (fun x => (f i (a ((T^[d r i]) x))-g ((T^[d r i]) x))*w x) μ := by
    apply real_integrable_bound μ ((hfm.sub (hgm.comp (T.measurable.iterate _))).mul hwm) 1
    intro x
    simp only [Pi.mul_apply,Pi.sub_apply,Function.comp_apply]
    rw [abs_mul]
    apply (fun leftBound rightNonneg rightBound => (mul_le_of_le_one_left rightNonneg leftBound).trans rightBound) _ (abs_nonneg _) (hw x)
    exact abs_le.mpr ⟨by linarith [(hf i (a ((T^[d r i]) x))).1,(hgb ((T^[d r i]) x)).2],
      by linarith [(hf i (a ((T^[d r i]) x))).2,(hgb ((T^[d r i]) x)).1]⟩
  have hmean := integral_mean_interval μ g hgm hgb
  have hi2 : Integrable (fun x => (g ((T^[d r i]) x)-∫ y, g y ∂μ)*w x) μ := by
    apply real_integrable_bound μ (((hgm.comp (T.measurable.iterate _)).sub measurable_const).mul hwm) 1
    intro x
    simp only [Pi.mul_apply,Pi.sub_apply,Function.comp_apply]
    rw [abs_mul]
    apply (fun leftBound rightNonneg rightBound => (mul_le_of_le_one_left rightNonneg leftBound).trans rightBound) _ (abs_nonneg _) (hw x)
    exact abs_le.mpr ⟨by linarith [(hgb ((T^[d r i]) x)).1,hmean.2],
      by linarith [(hgb ((T^[d r i]) x)).2,hmean.1]⟩
  change (∫ x, (_-_)*w x ∂μ) = (∫ x, _*w x ∂μ)+(∫ x, _*w x ∂μ)
  rw [←integral_add hi1 hi2]
  apply integral_congr_ae
  filter_upwards with x
  simp only [hc]
  ring

end Rokhlin

end

end OAI
