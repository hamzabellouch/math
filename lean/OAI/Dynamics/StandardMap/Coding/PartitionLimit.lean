import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Bernoulli.IntegerDynamics

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X]

theorem exists_partition_limit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (μ : Measure X) (q : ℕ → X → A) (hq : ∀ n,Measurable (q n))
    (hs : (∑' n : ℕ,μ {x | q (n+1) x≠q n x})≠⊤) :
    ∃ p : X → A,Measurable p ∧ ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x := by
  obtain ⟨p,hp,hlim⟩ := exists_eventual_decoder q hq
  have hh := ae_eventually_notMem hs
  refine ⟨p,hp,?_⟩
  filter_upwards [hh] with x hx
  obtain ⟨N,hN⟩ := eventually_atTop.mp hx
  have hconst : ∀ n,N≤n → q n x=q N x := by
    intro n hn
    induction n,hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => exact (not_ne_iff.mp (hN n hn)).trans ih
  have hc : ∀ᶠ n : ℕ in atTop,q n x=q N x := eventually_atTop.mpr ⟨N,hconst⟩
  rwa [hlim x (q N x) hc]

lemma measureReal_tendsto_zero_of_ae_eventually_notMem (μ : Measure X) [IsFiniteMeasure μ]
    (D : ℕ → Set X) (hD : ∀ n,MeasurableSet (D n))
    (ha : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,x∉D n) :
    Tendsto (fun n => μ.real (D n)) atTop (𝓝 0) := by
  let U (n : ℕ) : Set X := ⋃ j : ℕ,⋃ (_ : n≤j),D j
  have hU (n : ℕ) : MeasurableSet (U n) :=
    MeasurableSet.iUnion (fun j => MeasurableSet.iUnion (fun _ => hD j))
  have hanti : Antitone U := by
    intro n m hnm x hx
    obtain ⟨j,hx⟩ := mem_iUnion.mp hx
    obtain ⟨hj,hx⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hnm.trans hj,hx⟩⟩
  have hi : μ (⋂ n,U n)=0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [ha] with x hx hmem
    obtain ⟨N,hN⟩ := eventually_atTop.mp hx
    obtain ⟨j,hmem⟩ := mem_iUnion.mp (mem_iInter.mp hmem N)
    obtain ⟨hj,hmem⟩ := mem_iUnion.mp hmem
    exact hN j hj hmem
  have ht := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hU n).nullMeasurableSet)
    hanti ⟨0,measure_ne_top μ _⟩
  rw [hi] at ht
  have htr := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞)≠⊤)).comp ht
  simp only [Function.comp_def,ENNReal.toReal_zero] at htr
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_) htr
  exact measureReal_mono (μ := μ) (fun x hx => mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨le_rfl,hx⟩⟩) (measure_ne_top μ _)

lemma partition_limit_integer_names [MeasurableSpace A] {μ : Measure X} (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {q : ℕ → X → A} {p : X → A}
    (hlim : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x) :
    ∀ᵐ x ∂μ,∀ s : Finset ℤ,∀ᶠ n : ℕ in atTop,∀ i∈s,
      orbitName e (q n) x i=orbitName e p x i := by
  have hh : ∀ i : ℤ,∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,
      q n (integerIterate e i x)=p (integerIterate e i x) :=
    fun i => (integerIterate_measurePreserving e he i).quasiMeasurePreserving.ae hlim
  filter_upwards [ae_all_iff.mpr hh] with x hx s
  have hall : ∀ᶠ n : ℕ in atTop,∀ i : s,
      q n (integerIterate e i x)=p (integerIterate e i x) :=
    Filter.eventually_all.2 (fun i => hx i)
  exact hall.mono (fun n hn i hi => hn ⟨i,hi⟩)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] [Fintype A]

lemma finite_code_error_tendsto_zero {μ : Measure X} [IsFiniteMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    [MeasurableEq A] {q : ℕ → X → A} {p : X → A}
    (hq : ∀ n,Measurable (q n)) (hp : Measurable p)
    (hlim : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x) (s : Finset ℤ) :
    Tendsto (fun n => μ.real {x | s.restrict (orbitName e (q n) x)≠s.restrict (orbitName e p x)})
      atTop (𝓝 0) := by
  apply measureReal_tendsto_zero_of_ae_eventually_notMem μ
  · intro n
    exact (measurableSet_eq_fun ((measurable_restrict (s : Set ℤ)).comp (measurable_orbitName e (hq n)))
      ((measurable_restrict (s : Set ℤ)).comp (measurable_orbitName e hp))).compl
  · filter_upwards [partition_limit_integer_names e he hlim] with x hx
    filter_upwards [hx s] with n hn
    simp only [not_ne_iff]
    funext i
    exact hn i i.property

lemma finite_box_law_tendsto {μ : Measure X} [IsFiniteMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    [MeasurableEq A] {q : ℕ → X → A} {p : X → A}
    (hq : ∀ n,Measurable (q n)) (hp : Measurable p)
    (hlim : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x)
    (s : Finset ℤ) (t : ℤ → Set A) (ht : ∀ i,MeasurableSet (t i)) :
    Tendsto (fun n => (μ.map (orbitName e (q n))).real (Set.pi s t)) atTop
      (𝓝 ((μ.map (orbitName e p)).real (Set.pi s t))) := by
  let D : Set (s → A) := Set.pi Set.univ (fun i => t i)
  have hD : MeasurableSet D := MeasurableSet.univ_pi (fun i => ht i)
  have hpre : (s.restrict : (ℤ → A) → (s → A)) ⁻¹' D=Set.pi s t := by
    ext w
    simp only [D,mem_preimage,Set.mem_pi,mem_univ,true_implies,Finset.mem_coe,Finset.restrict]
    exact ⟨fun h i hi => h ⟨i,hi⟩,fun h i => h i i.property⟩
  have hdist (n : ℕ) :
      |(μ.map (orbitName e (q n))).real (Set.pi s t)-
       (μ.map (orbitName e p)).real (Set.pi s t)|≤
        μ.real {x | s.restrict (orbitName e (q n) x)≠s.restrict (orbitName e p x)} := by
    have hd := law_distance_le_disagreement μ
      ((measurable_restrict (s : Set ℤ)).comp (measurable_orbitName e (hq n)))
      ((measurable_restrict (s : Set ℤ)).comp (measurable_orbitName e hp)) hD
    have hr : Measurable (s.restrict : (ℤ → A) → (s → A)) := measurable_restrict (s : Set ℤ)
    have hmap (u : X → A) (hu : Measurable u) :
        (μ.map (s.restrict ∘ orbitName e u)).real D=
          (μ.map (orbitName e u)).real (Set.pi s t) := by
      simp only [Measure.real]
      rw [←Measure.map_map hr (measurable_orbitName e hu),Measure.map_apply hr hD,hpre]
    change |(μ.map (s.restrict ∘ orbitName e (q n))).real D-
      (μ.map (s.restrict ∘ orbitName e p)).real D|≤_ at hd
    rw [hmap (q n) (hq n),hmap p hp] at hd
    exact hd
  have hz := squeeze_zero (fun n => abs_nonneg _ ) hdist
    (finite_code_error_tendsto_zero e he hq hp hlim s)
  exact tendsto_iff_dist_tendsto_zero.mpr (by simpa only [Real.dist_eq] using hz)

theorem iid_law_of_partition_limit {μ : Measure X} [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    [MeasurableEq A] {q : ℕ → X → A} {p : X → A}
    (hq : ∀ n,Measurable (q n)) (hp : Measurable p)
    (hlim : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x)
    (β : Measure A) [IsProbabilityMeasure β]
    (hblock : ∀ (s : Finset ℤ) (t : ℤ → Set A),(∀ i,MeasurableSet (t i)) →
      Tendsto (fun n => (μ.map (orbitName e (q n))).real (Set.pi s t)) atTop
        (𝓝 ((∏ i∈s,β (t i)).toReal))) :
    MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => β)) := by
  refine ⟨measurable_orbitName e hp,Measure.eq_infinitePi _ ?_⟩
  intro s t ht
  have h := tendsto_nhds_unique (finite_box_law_tendsto e he hq hp hlim s t ht) (hblock s t ht)
  have hf : (∏ i∈s,β (t i))≠⊤ := by
    rw [←Measure.infinitePi_pi (fun _ : ℤ => β) (fun i _ => ht i)]
    exact measure_ne_top _ _
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) hf).mp h

end HyperbolicCoding

end
section
open MeasureTheory Set Filter

namespace HyperbolicCoding
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountablySeparated Y] [MeasurableEq Y]

theorem measurable_decoder_of_ae_point_separation [StandardBorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → Y) (hf : Measurable f)
    (hsep : ∀ᵐ x ∂μ,∀ y,f y=f x → y=x) :
    ∃ d : Y → X,MeasurePreserving d (μ.map f) μ ∧
      (∀ᵐ x ∂μ,d (f x)=x) ∧ (∀ᵐ y ∂μ.map f,f (d y)=y) := by
  obtain ⟨S,hSae,hSm,hS⟩ := IsMeasurablyGenerated.exists_measurable_subset hsep
  let _ : StandardBorelSpace S := hSm.standardBorel
  have hAE : ∀ᵐ x ∂μ,x∈S := hSae
  let _ : Nonempty S := by obtain ⟨x,hx⟩ := hAE.exists; exact ⟨⟨x,hx⟩⟩
  let r : S → Y := fun x => f x
  have hr : MeasurableEmbedding r := (hf.comp measurable_subtype_coe).measurableEmbedding (by
    intro x y h
    exact Subtype.ext ((hS y.property) x h))
  let d : Y → X := fun y => (hr.invFun y).val
  have hd : Measurable d := measurable_subtype_coe.comp hr.measurable_invFun
  have hl : ∀ᵐ x ∂μ,d (f x)=x := by
    filter_upwards [hSae] with x hx
    exact congrArg Subtype.val (hr.leftInverse_invFun ⟨x,hx⟩)
  have hmp : MeasurePreserving d (μ.map f) μ := by
    refine ⟨hd,?_⟩
    rw [Measure.map_map hd hf]
    have hm : d ∘ f =ᵐ[μ] id := hl
    exact (Measure.map_congr hm).trans (Measure.map_id)
  refine ⟨d,hmp,hl,?_⟩
  apply (ae_map_iff hf.aemeasurable (measurableSet_eq_fun (hf.comp hd) measurable_id)).mpr
  filter_upwards [hl] with x hx
  exact congrArg f hx

theorem orbitName_shift_preserving [StandardBorelSpace X] {A : Type*} [MeasurableSpace A]
    (e : X ≃ᵐ X) {μ : Measure X} (he : MeasurePreserving e μ μ)
    (α : X → A) (hα : Measurable α) :
    MeasurePreserving (fun w : ℤ → A => fun i => w (i+1)) (μ.map (orbitName e α)) (μ.map (orbitName e α)) := by
  have hcode := measurable_orbitName e hα
  have hshift : Measurable (fun w : ℤ → A => fun i => w (i+1)) :=
    Measurable.of_eval (fun i => measurable_pi_apply (i+1))
  refine ⟨hshift,?_⟩
  rw [Measure.map_map hshift hcode]
  have heq : (fun w : ℤ → A => fun i => w (i+1)) ∘ orbitName e α=(orbitName e α) ∘ e :=
    funext (fun x => (orbitName_shift e α x).symm)
  rw [heq,←Measure.map_map hcode e.measurable,he.map_eq]

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter
open scoped ENNReal Topology
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [MeasurableSpace.CountablySeparated Y] [MeasurableEq Y]

theorem measurable_decoder_of_conull_injective (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → Y) (hf : Measurable f) {S : Set X} (hS : MeasurableSet S)
    (hSae : ∀ᵐ x ∂μ,x∈S) (hinj : Set.InjOn f S) :
    ∃ d : Y → X,MeasurePreserving d (μ.map f) μ ∧
      (∀ᵐ x ∂μ,d (f x)=x) ∧ (∀ᵐ y ∂μ.map f,f (d y)=y) := by
  let _ : StandardBorelSpace S := hS.standardBorel
  let _ : Nonempty S := by obtain ⟨x,hx⟩ := hSae.exists; exact ⟨⟨x,hx⟩⟩
  let r : S → Y := fun x => f x
  have hr : MeasurableEmbedding r := (hf.comp measurable_subtype_coe).measurableEmbedding (by
    intro x y h
    exact Subtype.ext (hinj x.property y.property h))
  let d : Y → X := fun y => (hr.invFun y).val
  have hd : Measurable d := measurable_subtype_coe.comp hr.measurable_invFun
  have hl : ∀ᵐ x ∂μ,d (f x)=x := by
    filter_upwards [hSae] with x hx
    exact congrArg Subtype.val (hr.leftInverse_invFun ⟨x,hx⟩)
  have hmp : MeasurePreserving d (μ.map f) μ := by
    refine ⟨hd,?_⟩
    rw [Measure.map_map hd hf]
    have hm : d ∘ f =ᵐ[μ] id := hl
    exact (Measure.map_congr hm).trans (Measure.map_id)
  refine ⟨d,hmp,hl,?_⟩
  apply (ae_map_iff hf.aemeasurable (measurableSet_eq_fun (hf.comp hd) measurable_id)).mpr
  filter_upwards [hl] with x hx
  exact congrArg f hx

theorem measurable_decoder_of_countable_factors {I C : Type*} [Countable I]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → Y) (hf : Measurable f)
    (α : I → X → C) (hsep : Function.Injective (fun x => fun i => α i x))
    (hfac : ∀ i,∃ g : Y → C,∀ᵐ x ∂μ,α i x=g (f x)) :
    ∃ d : Y → X,MeasurePreserving d (μ.map f) μ ∧
      (∀ᵐ x ∂μ,d (f x)=x) ∧ (∀ᵐ y ∂μ.map f,f (d y)=y) := by
  choose g hg using hfac
  have hAE : ∀ᵐ x ∂μ,∀ i,α i x=g i (f x) := ae_all_iff.mpr hg
  obtain ⟨S,hSae,hSm,hS⟩ := IsMeasurablyGenerated.exists_measurable_subset hAE
  apply measurable_decoder_of_conull_injective μ f hf hSm hSae
  intro x hx y hy hxy
  apply hsep
  funext i
  exact (hS hx i).trans ((congrArg (g i) hxy).trans (hS hy i).symm)

theorem measurable_decoder_of_generating_approximations {I C : Type*} [Countable I]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C] [Nonempty C]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → Y) (hf : Measurable f)
    (α : I → X → C) (hsep : Function.Injective (fun x => fun i => α i x))
    (happ : ∀ i,∀ ε : ℝ,0<ε → ∃ g : Y → C,Measurable g ∧
      μ {x | g (f x)≠α i x}<ENNReal.ofReal ε) :
    ∃ d : Y → X,MeasurePreserving d (μ.map f) μ ∧
      (∀ᵐ x ∂μ,d (f x)=x) ∧ (∀ᵐ y ∂μ.map f,f (d y)=y) := by
  apply measurable_decoder_of_countable_factors μ f hf α hsep
  intro i
  obtain ⟨g,_hgm,hg⟩ := exists_factor_of_approx μ f (α i) (happ i)
  exact ⟨g,hg⟩

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology symmDiff
variable {X A C : Type*} [MeasurableSpace X] [MeasurableSpace A] [Fintype A]
    [MeasurableEq A] [MeasurableSpace C] [MeasurableEq C]

lemma decoder_error_tendsto {μ : Measure X} [IsFiniteMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {q : ℕ → X → A} {p : X → A}
    (hq : ∀ n,Measurable (q n)) (hp : Measurable p)
    (hlim : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x)
    (s : Finset ℤ) (G : (s → A) → C) (hG : Measurable G)
    (α : X → C) (hα : Measurable α) :
    Tendsto (fun n => μ.real {x | G (s.restrict (orbitName e (q n) x))≠α x}) atTop
      (𝓝 (μ.real {x | G (s.restrict (orbitName e p x))≠α x})) := by
  have hm (u : X → A) (hu : Measurable u) :
      MeasurableSet {x | G (s.restrict (orbitName e u x))≠α x} :=
    (measurableSet_eq_fun (hG.comp ((measurable_restrict (s : Set ℤ)).comp (measurable_orbitName e hu))) hα).compl
  have hd (n : ℕ) :
      |μ.real {x | G (s.restrict (orbitName e (q n) x))≠α x}-
        μ.real {x | G (s.restrict (orbitName e p x))≠α x}|≤
          μ.real {x | s.restrict (orbitName e (q n) x)≠s.restrict (orbitName e p x)} := by
    apply (abs_measureReal_sub_le_measureReal_symmDiff
      (hm _ (hq n)).nullMeasurableSet (hm _ hp).nullMeasurableSet).trans
    apply ENNReal.toReal_mono (measure_ne_top μ _)
    apply measure_mono
    intro x hx hEq
    simp only [Set.mem_symmDiff,mem_ofPred_eq,hEq,and_not_self,or_self] at hx
  have hz := squeeze_zero (fun n => abs_nonneg _) hd (finite_code_error_tendsto_zero e he hq hp hlim s)
  exact tendsto_iff_dist_tendsto_zero.mpr (by simpa only [Real.dist_eq] using hz)

theorem approximate_decoders_pass_to_limit {μ : Measure X} [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {q : ℕ → X → A} {p : X → A}
    (hq : ∀ n,Measurable (q n)) (hp : Measurable p)
    (hlim : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x)
    (α : X → C) (hα : Measurable α)
    (happ : ∀ ε : ℝ,0<ε → ∃ (s : Finset ℤ) (G : (s → A) → C),Measurable G ∧
      ∀ᶠ n : ℕ in atTop,μ.real {x | G (s.restrict (orbitName e (q n) x))≠α x}<ε) :
    ∀ ε : ℝ,0<ε → ∃ g : (ℤ → A) → C,Measurable g ∧
      μ {x | g (orbitName e p x)≠α x}<ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨s,G,hG,happ⟩ := happ (ε/2) (by positivity)
  refine ⟨G ∘ s.restrict,hG.comp (measurable_restrict (s : Set ℤ)),?_⟩
  have hle : μ.real {x | G (s.restrict (orbitName e p x))≠α x}≤ε/2 :=
    le_of_tendsto (decoder_error_tendsto e he hq hp hlim s G hG α hα) (happ.mono (fun n hn => hn.le))
  have hh : μ.real {x | G (s.restrict (orbitName e p x))≠α x}<ε := lt_of_le_of_lt hle (by linarith)
  change μ {x | G (s.restrict (orbitName e p x))≠α x}<ENNReal.ofReal ε
  rw [←ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_lt_ofReal_iff hε |>.mpr hh

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology

theorem bernoulli_model_of_coherent_coding
    {X A I C : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [StandardBorelSpace A] [Fintype A] [Nonempty A]
    [Countable I] [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C] [Nonempty C]
    (μ : Measure X) [IsProbabilityMeasure μ] (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (α : I → X → C) (hα : ∀ i,Measurable (α i))
    (hsep : Function.Injective (fun x => fun i => α i x))
    (β : Measure A) [IsProbabilityMeasure β]
    (q : ℕ → X → A) (hq : ∀ n,Measurable (q n))
    (hs : (∑' n : ℕ,μ {x | q (n+1) x≠q n x})≠⊤)
    (hblock : ∀ (s : Finset ℤ) (t : ℤ → Set A),(∀ i,MeasurableSet (t i)) →
      Tendsto (fun n => (μ.map (orbitName e (q n))).real (Set.pi s t)) atTop
        (𝓝 ((∏ i∈s,β (t i)).toReal)))
    (hdecode : ∀ i,∀ ε : ℝ,0<ε → ∃ (s : Finset ℤ) (G : (s → A) → C),Measurable G ∧
      ∀ᶠ n : ℕ in atTop,μ.real {x | G (s.restrict (orbitName e (q n) x))≠α i x}<ε) :
    ∃ βR : Measure ℝ,IsProbabilityMeasure βR ∧
      ∃ (encode : X → (ℤ → ℝ)) (decode : (ℤ → ℝ) → X),
        MeasurePreserving encode μ (Measure.infinitePi (fun _ : ℤ => βR)) ∧
        MeasurePreserving decode (Measure.infinitePi (fun _ : ℤ => βR)) μ ∧
        (∀ᵐ x ∂μ,decode (encode x)=x) ∧
        (∀ᵐ w ∂Measure.infinitePi (fun _ : ℤ => βR),encode (decode w)=w) ∧
        (∀ᵐ x ∂μ,encode (e x)=fun i : ℤ => encode x (i+1)) := by
  obtain ⟨p,hp,hlim⟩ := exists_partition_limit μ q hq hs
  have hcode := iid_law_of_partition_limit e he hq hp hlim β hblock
  obtain ⟨d,hd,hl,_hr⟩ := measurable_decoder_of_generating_approximations μ (orbitName e p)
    (measurable_orbitName e hp) α hsep (fun i =>
      approximate_decoders_pass_to_limit e he hq hp hlim (α i) (hα i) (hdecode i))
  rw [hcode.map_eq] at hd
  let b : A → ℝ := embeddingReal A
  have hb : MeasurableEmbedding b := measurableEmbedding_embeddingReal A
  let βR := β.map b
  have : IsProbabilityMeasure βR := inferInstance
  let F : (ℤ → A) → (ℤ → ℝ) := fun w i => b (w i)
  let G : (ℤ → ℝ) → (ℤ → A) := fun w i => hb.invFun (w i)
  have hF : Measurable F := Measurable.of_eval (fun i => hb.measurable.comp (measurable_pi_apply i))
  have hG : Measurable G := Measurable.of_eval (fun i => hb.measurable_invFun.comp (measurable_pi_apply i))
  have hGF (w : ℤ → A) : G (F w)=w := funext (fun i => hb.leftInverse_invFun (w i))
  have hmpF : MeasurePreserving F (Measure.infinitePi (fun _ : ℤ => β))
      (Measure.infinitePi (fun _ : ℤ => βR)) :=
    ⟨hF,Measure.infinitePi_map_pi _ (fun _ => hb.measurable)⟩
  have hmpG : MeasurePreserving G (Measure.infinitePi (fun _ : ℤ => βR))
      (Measure.infinitePi (fun _ : ℤ => β)) := by
    refine ⟨hG,?_⟩
    rw [←hmpF.map_eq,Measure.map_map hG hF,show G ∘ F=id from funext hGF,Measure.map_id]
  let encode : X → (ℤ → ℝ) := F ∘ orbitName e p
  let decode : (ℤ → ℝ) → X := d ∘ G
  have hE : MeasurePreserving encode μ (Measure.infinitePi (fun _ : ℤ => βR)) := hmpF.comp hcode
  have hD : MeasurePreserving decode (Measure.infinitePi (fun _ : ℤ => βR)) μ := hd.comp hmpG
  have hleft : ∀ᵐ x ∂μ,decode (encode x)=x := by
    filter_upwards [hl] with x hx
    exact (congrArg d (hGF (orbitName e p x))).trans hx
  refine ⟨βR,inferInstance,encode,decode,hE,hD,hleft,?_,?_⟩
  · rw [←hE.map_eq]
    apply (ae_map_iff hE.measurable.aemeasurable
      (measurableSet_eq_fun (hE.measurable.comp hD.measurable) measurable_id)).mpr
    filter_upwards [hleft] with x hx
    exact congrArg encode hx
  · exact ae_of_all _ (fun x => funext (fun i => congrArg b (congrFun (orbitName_shift e p x) i)))

end HyperbolicCoding

end
end

end OAI
