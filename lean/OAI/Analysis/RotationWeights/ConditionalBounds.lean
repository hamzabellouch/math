import OAI.Analysis.RotationWeights.EndpointMoments

namespace OAI

noncomputable section

universe uD uΩ uι uT uX uY

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace CircleCoupling

lemma measure_le_of_singletons {D : Type uD} [MeasurableSpace D] [Countable D]
    [MeasurableSingletonClass D] {μ ν : Measure D}
    (h : ∀ d, μ {d} ≤ ν {d}) : μ ≤ ν := by
  rw [← Measure.sum_smul_dirac μ, ← Measure.sum_smul_dirac ν]
  apply Measure.le_iff.mpr
  intro s hs
  simp only [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.tsum_le_tsum (fun d => mul_le_mul' (h d) le_rfl)

lemma map_restrict_le_of_fibers {Ω : Type uΩ} {D : Type uD} [MeasurableSpace Ω]
    [MeasurableSpace D] [Countable D] [MeasurableSingletonClass D]
    (μ : Measure Ω) (f : Ω → D) (hf : Measurable f) (H : Set Ω)
    (δ : ℝ≥0∞)
    (h : ∀ d, μ ((f ⁻¹' {d}) ∩ H) ≤ δ * μ (f ⁻¹' {d})) :
    Measure.map f (μ.restrict H) ≤ δ • Measure.map f μ := by
  apply measure_le_of_singletons
  intro d
  simpa only [Measure.map_apply hf (measurableSet_singleton d),
    Measure.restrict_apply (hf (measurableSet_singleton d)),
    Measure.smul_apply, smul_eq_mul] using h d

lemma independent_fiber_failures {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type uΩ} {D : ι → Type uD} [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSpace (D i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, Ω i → D i) (d : ∀ i, D i) (H : ∀ i, Set (Ω i))
    (A : Finset ι) (c : ι → ℝ≥0∞)
    (h : ∀ i ∈ A, μ i ((f i ⁻¹' {d i}) ∩ H i) ≤ c i * μ i (f i ⁻¹' {d i})) :
    (Measure.pi μ) {ω | (∀ i, f i (ω i) = d i) ∧ ∀ i ∈ A, ω i ∈ H i} ≤
      (∏ i ∈ A, c i) * (Measure.pi μ) {ω | ∀ i, f i (ω i) = d i} := by
  classical
  have hset : {ω | (∀ i, f i (ω i) = d i) ∧ ∀ i ∈ A, ω i ∈ H i} =
      univ.pi (fun i => (f i ⁻¹' {d i}) ∩ if i ∈ A then H i else univ) := by
    ext ω
    simp only [mem_ofPred_eq, Set.mem_pi, mem_univ, forall_const, mem_inter_iff,
      mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hf,hH⟩ i
      exact ⟨hf i, by split_ifs with hi; exact hH i hi; trivial⟩
    · intro hp
      exact ⟨fun i => (hp i).1, fun i hi => by simpa [hi] using (hp i).2⟩
  have hset' : {ω | ∀ i, f i (ω i) = d i} = univ.pi (fun i => f i ⁻¹' {d i}) := by
    ext ω
    simp
  rw [hset,hset',Measure.pi_pi,Measure.pi_pi]
  calc
    _ ≤ ∏ i, (if i ∈ A then c i else 1) * μ i (f i ⁻¹' {d i}) := by
      apply Finset.prod_le_prod
      intro i _
      by_cases hi : i ∈ A
      · simpa [hi] using h i hi
      · simp [hi]
    _ = _ := by rw [Finset.prod_mul_distrib]; congr 1; simp

lemma independent_selected_failures {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type uΩ} {D : ι → Type uD} [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSpace (D i)]
    [∀ i, Countable (D i)] [∀ i, MeasurableSingletonClass (D i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, Ω i → D i) (hf : ∀ i, Measurable (f i))
    (H : Set (∀ i, Ω i)) (bad : ∀ i, Set (Ω i))
    (A : (∀ i, D i) → Finset ι) (c : ι → ℝ≥0∞) (δ : ℝ≥0∞)
    (hlocal : ∀ d i, i ∈ A d →
      μ i ((f i ⁻¹' {d i}) ∩ bad i) ≤ c i * μ i (f i ⁻¹' {d i}))
    (hprod : ∀ d, (∃ ω ∈ H, (fun i => f i (ω i)) = d) → (∏ i∈A d, c i) ≤ δ)
    (hbad : ∀ ω ∈ H, ∀ i ∈ A (fun i => f i (ω i)), ω i ∈ bad i) :
    Measure.map (fun ω i => f i (ω i)) ((Measure.pi μ).restrict H) ≤
      δ • Measure.map (fun ω i => f i (ω i)) (Measure.pi μ) := by
  apply map_restrict_le_of_fibers _ _ (Measurable.of_eval (fun i => (hf i).comp (measurable_pi_apply i)))
  intro d
  change (Measure.pi μ) (((fun ω : ∀ i, Ω i => fun i => f i (ω i)) ⁻¹' {d}) ∩ H) ≤
    δ * (Measure.pi μ) ((fun ω : ∀ i, Ω i => fun i => f i (ω i)) ⁻¹' {d})
  by_cases hex : ∃ ω ∈ H, (fun i => f i (ω i)) = d
  swap
  · have hempty : ((fun ω i => f i (ω i)) ⁻¹' {d}) ∩ H = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨he,hω⟩
      exact hex ⟨ω,hω,he⟩
    rw [hempty,measure_empty]
    exact bot_le
  have hs : ((fun ω i => f i (ω i)) ⁻¹' {d}) ∩ H ⊆
      {ω | (∀ i, f i (ω i) = d i) ∧ ∀ i ∈ A d, ω i ∈ bad i} := by
    rintro ω ⟨hd,hω⟩
    have he : (fun i => f i (ω i)) = d := hd
    exact ⟨fun i => congrFun he i, by simpa only [← he] using hbad ω hω⟩
  apply (measure_mono hs).trans
  apply (independent_fiber_failures μ f d bad (A d) c (hlocal d)).trans
  have hset : {ω : ∀ i, Ω i | ∀ i, f i (ω i) = d i} = (fun ω i => f i (ω i)) ⁻¹' {d} := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff, funext_iff]
  rw [hset]
  exact mul_le_mul' (hprod d hex) le_rfl

lemma full_tail_domination {T : Type uT} {Ω : Type uΩ} {D : Type uD} [MeasurableSpace T]
    [MeasurableSpace Ω] [MeasurableSpace D]
    (ν : Measure T) (μ : Measure Ω) [SFinite μ]
    (f : Ω → D) (hf : Measurable f) (H : Set (T × Ω)) (hH : MeasurableSet H)
    (δ : ℝ≥0∞)
    (hsection : ∀ t, Measure.map f (μ.restrict {ω | (t,ω) ∈ H}) ≤
      δ • Measure.map f μ) :
    Measure.map (fun z : T × Ω => (z.1,f z.2)) ((ν.prod μ).restrict H) ≤
      δ • Measure.map (fun z : T × Ω => (z.1,f z.2)) (ν.prod μ) := by
  have hF : Measurable (fun z : T × Ω => (z.1,f z.2)) :=
    measurable_fst.prodMk (hf.comp measurable_snd)
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.map_apply hF hs,Measure.restrict_apply (hF hs),Measure.smul_apply,
    Measure.map_apply hF hs,Measure.prod_apply ((hF hs).inter hH),
    Measure.prod_apply (hF hs)]
  simp only [smul_eq_mul]
  calc
    _ ≤ ∫⁻ t, δ * μ ((fun ω => (t,f ω)) ⁻¹' s) ∂ν := by
      apply lintegral_mono
      intro t
      have hst : MeasurableSet (Prod.mk t ⁻¹' s) :=
        (measurable_const.prodMk measurable_id) hs
      have hh := hsection t (Prod.mk t ⁻¹' s)
      rw [Measure.map_apply hf hst,Measure.restrict_apply (hf hst),
        Measure.smul_apply,Measure.map_apply hf hst] at hh
      exact hh
    _ = _ := by
      exact lintegral_const_mul δ (show Measurable (fun t => μ ((fun ω => (t,f ω)) ⁻¹' s)) from
        measurable_measure_prodMk_left (ν := μ) (hF hs))


lemma map_domination {X : Type uX} {Y : Type uY} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (hf : Measurable f) {μ ν : Measure X} (δ : ℝ≥0∞)
    (h : μ ≤ δ • ν) : Measure.map f μ ≤ δ • Measure.map f ν := by
  rw [← Measure.map_smul _ hf.aemeasurable]
  exact Measure.map_mono h hf

lemma selected_failures_endpoint {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type uΩ} {D : ι → Type uD} [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSpace (D i)]
    [∀ i, Countable (D i)] [∀ i, MeasurableSingletonClass (D i)]
    {T : Type uT} {Y : Type uY} [MeasurableSpace T] [MeasurableSpace Y]
    (ν : Measure T) (μ : ∀ i, Measure (Ω i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, Ω i → D i) (hf : ∀ i, Measurable (f i))
    (E : T × (∀ i, D i) → Y) (hE : Measurable E)
    (H : Set (T × (∀ i, Ω i))) (hH : MeasurableSet H) (bad : ∀ i, Set (Ω i))
    (A : T → (∀ i, D i) → Finset ι) (c : ι → ℝ≥0∞) (δ : ℝ≥0∞)
    (hlocal : ∀ t d i, i ∈ A t d →
      μ i ((f i ⁻¹' {d i}) ∩ bad i) ≤ c i * μ i (f i ⁻¹' {d i}))
    (hprod : ∀ t d, (∃ ω, (t,ω) ∈ H ∧ (fun i => f i (ω i)) = d) →
      (∏ i ∈ A t d, c i) ≤ δ)
    (hbad : ∀ t ω, (t,ω) ∈ H → ∀ i ∈ A t (fun i => f i (ω i)), ω i ∈ bad i) :
    Measure.map (fun z : T × (∀ i, Ω i) => E (z.1,fun i => f i (z.2 i)))
      ((ν.prod (Measure.pi μ)).restrict H) ≤
      δ • Measure.map (fun z : T × (∀ i, Ω i) => E (z.1,fun i => f i (z.2 i)))
        (ν.prod (Measure.pi μ)) := by
  have hf' : Measurable (fun ω : ∀ i, Ω i => fun i => f i (ω i)) :=
    Measurable.of_eval (fun i => (hf i).comp (measurable_pi_apply i))
  have hsection (t : T) := independent_selected_failures μ f hf {ω | (t,ω) ∈ H}
    bad (A t) c δ (hlocal t) (hprod t) (hbad t)
  have hdom := full_tail_domination ν (Measure.pi μ) _ hf' H hH δ hsection
  have hh := map_domination E hE δ hdom
  have hG : Measurable (fun z : T × (∀ i, Ω i) => (z.1,fun i => f i (z.2 i))) :=
    measurable_fst.prodMk (hf'.comp measurable_snd)
  rw [Measure.map_map hE hG,Measure.map_map hE hG] at hh
  exact hh

lemma failure_power_exponential (ρ m : ℝ) (n : ℕ)
    (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) (hcard : m/40 ≤ (n : ℝ)) :
    (ENNReal.ofReal (1-ρ/10)) ^ n ≤ ENNReal.ofReal (Real.exp (-m*ρ/400)) := by
  rw [← ENNReal.ofReal_pow (by linarith : 0 ≤ 1-ρ/10)]
  apply ENNReal.ofReal_le_ofReal
  calc
    (1-ρ/10)^n ≤ (Real.exp (-ρ/10))^n := by
      apply pow_le_pow_left₀ (by linarith)
      have h := Real.add_one_le_exp (-ρ/10)
      linarith
    _ = Real.exp ((n : ℝ)*(-ρ/10)) := (Real.exp_nat_mul _ n).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

end CircleCoupling
open MeasureTheory Set
open scoped ENNReal
namespace CircleCoupling
lemma infinitePi_split {ι : Type uι} {Ω : ι → Type uΩ}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i))
    [∀ i, IsProbabilityMeasure (μ i)] (p : ι → Prop) [DecidablePred p] :
    Measure.map (MeasurableEquiv.piEquivPiSubtypeProd Ω p).symm
      ((Measure.infinitePi fun i : {i // p i} => μ i).prod
        (Measure.infinitePi fun i : {i // ¬p i} => μ i)) = Measure.infinitePi μ := by
  classical
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.map_apply (by fun_prop) (.pi (Finset.countable_toSet _) fun i _ => ht i)]
  have hset : (MeasurableEquiv.piEquivPiSubtypeProd Ω p).symm ⁻¹' Set.pi (s : Set ι) t =
      (Set.pi ((s.subtype p) : Set {i // p i}) (fun i => t i)) ×ˢ
      (Set.pi ((s.subtype (fun i => ¬p i)) : Set {i // ¬p i}) (fun i => t i)) := by
    ext z
    simp only [mem_preimage, Set.mem_pi, mem_prod, Finset.mem_coe, Finset.mem_subtype]
    constructor
    · intro hz
      constructor
      · rintro ⟨i,hi⟩ his
        simpa [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hi]
          using hz i his
      · rintro ⟨i,hi⟩ his
        simpa [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hi]
          using hz i his
    · rintro ⟨hx,hy⟩ i his
      by_cases hi : p i
      · simpa [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hi]
          using hx ⟨i,hi⟩ his
      · simpa [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hi]
          using hy ⟨i,hi⟩ his
  rw [hset, Measure.prod_prod, Measure.infinitePi_pi, Measure.infinitePi_pi]
  · rw [Finset.prod_subtype_eq_prod_filter (fun i : ι => μ i (t i)),
      Finset.prod_subtype_eq_prod_filter (fun i : ι => μ i (t i))]
    exact Finset.prod_filter_mul_prod_filter_not s p (fun i => μ i (t i))
  · intro i hi; exact ht i
  · intro i hi; exact ht i

def glue {ι : Type uι} (Ω : ι → Type uΩ) (I : Finset ι) [DecidablePred (· ∈ I)]
    (z : (∀ i : {i // i ∉ I}, Ω i) × (∀ i : I, Ω i)) : ∀ i, Ω i :=
  fun i => if hi : i ∈ I then z.2 ⟨i,hi⟩ else z.1 ⟨i,hi⟩

lemma measurable_glue {ι : Type uι} (Ω : ι → Type uΩ) [∀ i, MeasurableSpace (Ω i)]
    (I : Finset ι) [DecidablePred (· ∈ I)] : Measurable (glue Ω I) := by
  apply Measurable.of_eval
  intro i
  dsimp [glue]
  split_ifs <;> fun_prop

lemma map_glue {ι : Type uι} {Ω : ι → Type uΩ} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (I : Finset ι) [DecidablePred (· ∈ I)] :
    Measure.map (glue Ω I)
      ((Measure.infinitePi (fun i : {i // i ∉ I} => μ i)).prod (Measure.pi (fun i : I => μ i))) =
      Measure.infinitePi μ := by
  classical
  let e := MeasurableEquiv.piEquivPiSubtypeProd Ω (· ∈ I)
  have he : glue Ω I = e.symm ∘ Prod.swap := by
    funext z i
    simp [glue,e,MeasurableEquiv.piEquivPiSubtypeProd,Equiv.piEquivPiSubtypeProd]
  rw [he,← Measure.map_map e.symm.measurable measurable_swap,Measure.prod_swap]
  rw [← Measure.infinitePi_eq_pi (fun i : I => μ i)]
  exact infinitePi_split μ (· ∈ I)

lemma observe_glue {ι : Type uι} {Ω : ι → Type uΩ} {D : ι → Type uD} (I : Finset ι)
    [DecidablePred (· ∈ I)] (f : ∀ i, Ω i → D i)
    (z : (∀ i : {i // i ∉ I}, Ω i) × (∀ i : I, Ω i)) :
    (fun i => f i (glue Ω I z i)) =
      glue D I (fun i : {i // i ∉ I} => f i (z.1 i),fun i : I => f i (z.2 i)) := by
  funext i
  dsimp [glue]
  split_ifs <;> rfl

lemma infinite_selected_failures {ι : Type uι} {Ω : ι → Type uΩ} {D : ι → Type uD}
    [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSpace (D i)]
    [∀ i, Countable (D i)] [∀ i, MeasurableSingletonClass (D i)]
    {Y : Type uY} [MeasurableSpace Y]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (I : Finset ι) (f : ∀ i, Ω i → D i) (hf : ∀ i, Measurable (f i))
    (E : (∀ i, D i) → Y) (hE : Measurable E)
    (H : Set (∀ i, Ω i)) (hH : MeasurableSet H) (bad : ∀ i : I, Set (Ω i))
    (A : (∀ i, D i) → Finset I) (c : I → ℝ≥0∞) (δ : ℝ≥0∞)
    (hlocal : ∀ d i, i ∈ A d →
      μ i ((f i ⁻¹' {d i}) ∩ bad i) ≤ c i * μ i (f i ⁻¹' {d i}))
    (hprod : ∀ ω, ω ∈ H → (∏ i ∈ A (fun i => f i (ω i)), c i) ≤ δ)
    (hbad : ∀ ω, ω ∈ H → ∀ i ∈ A (fun i => f i (ω i)), ω i ∈ bad i) :
    Measure.map (fun ω => E (fun i => f i (ω i))) ((Measure.infinitePi μ).restrict H) ≤
      δ • Measure.map (fun ω => E (fun i => f i (ω i))) (Measure.infinitePi μ) := by
  classical
  let T := ∀ i : {i // i ∉ I}, Ω i
  let ν : Measure T := Measure.infinitePi (fun i : {i // i ∉ I} => μ i)
  let o : (∀ i, Ω i) → (∀ i, D i) := fun ω i => f i (ω i)
  have ho : Measurable o := Measurable.of_eval (fun i => (hf i).comp (measurable_pi_apply i))
  let g : T × (∀ i : I, D i) → (∀ i, D i) :=
    fun z => glue D I (fun i : {i // i ∉ I} => f i (z.1 i),z.2)
  have hg : Measurable g := (measurable_glue D I).comp
    ((Measurable.of_eval (fun i : {i // i ∉ I} => (hf i).comp ((measurable_pi_apply i).comp measurable_fst))).prodMk measurable_snd)
  have hh := selected_failures_endpoint ν (fun i : I => μ i) (fun i : I => f i)
    (fun i => hf i) (E ∘ g) (hE.comp hg) ((glue Ω I) ⁻¹' H)
    ((measurable_glue Ω I) hH) bad (fun t d => A (g (t,d))) c δ
    (by
      intro t d i hi
      have hh := hlocal (g (t,d)) i hi
      simpa [g,glue,i.property] using hh)
    (by
      intro t d hd
      obtain ⟨ω,hω,hfd⟩ := hd
      have hh := hprod (glue Ω I (t,ω)) hω
      rw [observe_glue,hfd] at hh
      exact hh)
    (by
      intro t ω hω i hi
      have hh := hbad (glue Ω I (t,ω)) hω i
      rw [observe_glue] at hh
      simpa [glue,i.property] using hh hi)
  have hid : (fun z : T × (∀ i : I, Ω i) => (E ∘ g) (z.1, fun i => f i (z.2 i))) =
      (E ∘ o) ∘ glue Ω I := by
    funext z
    dsimp [Function.comp_def,o,g]
    rw [observe_glue]
  rw [hid,← Measure.map_map (hE.comp ho) (measurable_glue Ω I),
    ← Measure.restrict_map (measurable_glue Ω I) hH,
    show Measure.map (glue Ω I) (ν.prod (Measure.pi (fun i : I => μ i))) = Measure.infinitePi μ from map_glue μ I,
    ← Measure.map_map (hE.comp ho) (measurable_glue Ω I),
    show Measure.map (glue Ω I) (ν.prod (Measure.pi (fun i : I => μ i))) = Measure.infinitePi μ from map_glue μ I] at hh
  exact hh

end CircleCoupling
namespace CircleDigits
lemma digit_interval_weak {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i) (d : Digits b) (n : ℕ) :
    (d n : ℝ)/(b n : ℝ) ≤ scaledTail b d n ∧
    scaledTail b d n ≤ ((d n : ℝ)+1)/(b n : ℝ) := by
  have hpos : (0:ℝ)<b n := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0<2) (hb n)
  rw [div_le_iff₀ hpos,le_div_iff₀ hpos,mul_comm (scaledTail b d n),scaledTail_recurrence]
  exact ⟨le_add_of_nonneg_right (scaledTail_bounds hb d (n+1)).1,
    add_le_add_right (scaledTail_bounds hb d (n+1)).2 _⟩
lemma measurable_prefixNumeral (b : ℕ → ℕ) (n : ℕ) : Measurable (fun d : Digits b => prefixNumeral b d n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    simp only [prefixNumeral]
    exact (measurable_const.mul ih).add ((measurable_of_countable (fun x : Fin (b n) => x.val)).comp (measurable_pi_apply n))
lemma measurable_scaledTail (b : ℕ → ℕ) (n : ℕ) : Measurable (fun d : Digits b => scaledTail b d n) :=
  (measurable_const.mul (measurable_expansion b)).sub ((measurable_of_countable (fun x : ℕ => (x:ℝ))).comp (measurable_prefixNumeral b n))
end CircleDigits

end

end OAI
