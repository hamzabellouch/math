import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Bernoulli.ErgodicAverages

namespace OAI

section
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology

namespace HyperbolicCoding

def tailName {X A : Type*} (T : X → X) (α : X → A) (m : ℕ) (x : X) : ℕ → A :=
  fun n => α (T^[n+m] x)

lemma measurable_tailName {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    {T : X → X} (hT : Measurable T) {α : X → A} (hα : Measurable α) (m : ℕ) :
    Measurable (tailName T α m) :=
  Measurable.of_eval (fun n => hα.comp (hT.iterate (n+m)))

def TailEvent {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (μ : Measure X) (T : X → X) (α : X → A) (E : Set X) : Prop :=
  ∀ m : ℕ,∃ D : Set (ℕ → A),MeasurableSet D ∧ E=ᵐ[μ](tailName T α m) ⁻¹' D

theorem tailEvent_saturation {X A : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [MeasurableSpace A] (μ : Measure X) {T : X → X} {α : X → A}
    (hnames : ∀ᵐ x ∂μ,∀ y,ExponentiallyAsymptotic T x y →
      ∀ᶠ n : ℕ in atTop,α (T^[n] x)=α (T^[n] y)) {E : Set X}
    (hE : TailEvent μ T α E) :
    ∃ Q : Set X,(∀ᵐ x ∂μ,x∈Q) ∧ ∀ x∈Q,∀ y∈Q,
      ExponentiallyAsymptotic T x y → (x∈E ↔ y∈E) := by
  choose D hDm hDE using hE
  let Q : Set X := {x | (∀ m,x∈E ↔ tailName T α m x∈D m) ∧
    ∀ y,ExponentiallyAsymptotic T x y → ∀ᶠ n : ℕ in atTop,α (T^[n] x)=α (T^[n] y)}
  have hQ : ∀ᵐ x ∂μ,x∈Q := by
    filter_upwards [ae_all_iff.mpr hDE,hnames] with x hx hn
    exact ⟨fun m => Iff.of_eq (hx m),hn⟩
  refine ⟨Q,hQ,?_⟩
  intro x hx y hy hxy
  obtain ⟨m,hm⟩ := eventually_atTop.mp (hx.2 y hxy)
  have hname : tailName T α m x=tailName T α m y := by
    funext n
    exact hm (n+m) (by omega)
  have hmem : tailName T α m x∈D m ↔ tailName T α m y∈D m := by rw [hname]
  exact (hx.1 m).trans (hmem.trans (hy.1 m).symm)

lemma ExponentiallyAsymptotic.iterate {X : Type*} [PseudoMetricSpace X]
    {T : X → X} {x y : X} (h : ExponentiallyAsymptotic T x y) {N : ℕ} (hN : 0<N) :
    ExponentiallyAsymptotic (T^[N]) x y := by
  obtain ⟨ρ,hρ0,hρ1,C,hC⟩ := h
  have hseq : Tendsto (fun n : ℕ => N*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by change n≤N*n; nlinarith) tendsto_id
  refine ⟨ρ^N,pow_nonneg hρ0 N,pow_lt_one₀ hρ0 hρ1 hN.ne',C,?_⟩
  filter_upwards [hseq.eventually hC] with n hn
  simpa only [Function.iterate_mul,pow_mul] using hn

end HyperbolicCoding

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal NNReal
open HyperbolicCoding
attribute [local instance] Measure.Subtype.measureSpace

lemma fineStableCurve_exponentiallyAsymptotic (k χ ε δ : ℝ) (hδ : 0<δ)
    (hq : Real.exp (-χ+ε)+δ<1) (w : ℂ)
    (hw : ∀ n : ℕ,FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1) :
    ExponentiallyAsymptotic (standardMap k)
      (complexProjection (fineStableCurve k χ ε δ hδ hq w hw s))
      (complexProjection (fineStableCurve k χ ε δ hδ hq w hw t)) := by
  refine ⟨Real.exp (-χ+ε)+δ,by positivity,hq,(2*fineScale k ε δ)*|s-t|,Filter.Eventually.of_forall ?_⟩
  intro n
  have h := (complexProjection_dist_le _ _).trans (fineStableCurve_contraction k χ ε δ hδ hq w hw hs ht n)
  rw [complexProjection_iterate,complexProjection_iterate] at h
  exact h.trans_eq (by ring)

lemma fineUnstableCurve_exponentiallyAsymptotic (k χ ε δ : ℝ) (hδ : 0<δ)
    (hq : Real.exp (-χ+ε)+δ<1) (w : ℂ)
    (hw : ∀ n : ℕ,FineRegular k χ ε (complexProjection ((standardLift k)^[n] (tangentReversal w))))
    {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1) :
    ExponentiallyAsymptotic (inverseMap k)
      (complexProjection (fineUnstableCurve k χ ε δ hδ hq w hw s))
      (complexProjection (fineUnstableCurve k χ ε δ hδ hq w hw t)) := by
  refine ⟨Real.exp (-χ+ε)+δ,by positivity,hq,(6*fineScale k ε δ)*|s-t|,Filter.Eventually.of_forall ?_⟩
  intro n
  have h := (complexProjection_dist_le _ _).trans (fineUnstableCurve_contraction k χ ε δ hδ hq w hw hs ht n)
  rw [complexProjection_inverse_iterate,complexProjection_inverse_iterate] at h
  exact h.trans_eq (by ring)

namespace ReversibleGraphRectangle
variable {k χ : ℝ} {B : ReversibleRectangleBlock k χ} {F : ReversibleGraphFamilies B}
    (R : ReversibleGraphRectangle F)

lemma row_exponential (a b b' : B.coordinateCarrier) :
    ExponentiallyAsymptotic (standardMap k) (R.torusPoint (a,b)) (R.torusPoint (a,b')) := by
  have h := fineStableCurve_exponentiallyAsymptotic k χ B.ε B.δ B.δ_pos B.contraction (B.label a)
    (B.regular (B.label a) (B.label a).property)
    ((F.stable_bound (B.label a) (R.point (a,b)).1).trans (by linarith [B.r_small]))
    ((F.stable_bound (B.label a) (R.point (a,b')).1).trans (by linarith [B.r_small]))
  simpa only [torusPoint,R.stable_representation] using h

lemma column_exponential (a a' b : B.coordinateCarrier) :
    ExponentiallyAsymptotic (inverseMap k) (R.torusPoint (a,b)) (R.torusPoint (a',b)) := by
  have h := fineUnstableCurve_exponentiallyAsymptotic k χ B.ε B.δ B.δ_pos B.contraction (B.label b)
    (B.reversed (B.label b) (B.label b).property)
    ((F.unstable_bound (B.label b) (R.point (a,b)).2).trans (by linarith [B.r'_small]))
    ((F.unstable_bound (B.label b) (R.point (a',b)).2).trans (by linarith [B.r'_small]))
  simpa only [torusPoint,R.unstable_representation] using h

theorem exists_partitions_doubleTail_constant {N : ℕ} (hN : 0<N)
    (μ : Measure Torus) [IsProbabilityMeasure μ]
    (hπ : QuasiMeasurePreserving R.torusPoint (B.carrierProbability.prod B.carrierProbability) μ) :
    ∃ α : ℕ → ℕ → Torus → Bool,
      (∀ i j,Measurable (α i j)) ∧
      Function.Injective (fun z => fun i j => α i j z) ∧
      ∀ M : ℕ,∀ E : Set Torus,
        TailEvent μ ((standardMap k)^[N]) (joinedBinary α M) E →
        TailEvent μ ((inverseMap k)^[N]) (joinedBinary α M) E →
        ∃ c : Prop,∀ᵐ p ∂B.carrierProbability.prod B.carrierProbability,
          (R.torusPoint p∈E ↔ c) := by
  obtain ⟨α,hm,hi,hf,hb⟩ := exists_good_binary_partitions μ
    ((measurePreserving_standardMap k).measurable.iterate N)
    ((measurePreserving_inverseMap k).measurable.iterate N)
  refine ⟨α,hm,hi,?_⟩
  intro M E hEf hEb
  obtain ⟨Qf,hQf,hSatf⟩ := tailEvent_saturation μ
    (hf.mono (fun x hx y hxy => hx y hxy M)) hEf
  obtain ⟨Qb,hQb,hSatb⟩ := tailEvent_saturation μ
    (hb.mono (fun x hx y hxy => hx y hxy M)) hEb
  have hQ := hπ.ae (hQf.and hQb)
  have hrow (a b b' : B.coordinateCarrier)
      (hx : R.torusPoint (a,b)∈Qf ∧ R.torusPoint (a,b)∈Qb)
      (hy : R.torusPoint (a,b')∈Qf ∧ R.torusPoint (a,b')∈Qb) :
      (R.torusPoint (a,b)∈E)=(R.torusPoint (a,b')∈E) :=
    propext (hSatf _ hx.1 _ hy.1 ((R.row_exponential a b b').iterate hN))
  have hcol (a a' b : B.coordinateCarrier)
      (hx : R.torusPoint (a,b)∈Qf ∧ R.torusPoint (a,b)∈Qb)
      (hy : R.torusPoint (a',b)∈Qf ∧ R.torusPoint (a',b)∈Qb) :
      (R.torusPoint (a,b)∈E)=(R.torusPoint (a',b)∈E) :=
    propext (hSatb _ hx.2 _ hy.2 ((R.column_exponential a a' b).iterate hN))
  obtain ⟨c,hc⟩ := ae_constant_of_product_rows_columns
    (F := fun p => R.torusPoint p∈E) hQ hrow hcol
  exact ⟨c,hc.mono (fun p hp => Iff.of_eq hp)⟩

end ReversibleGraphRectangle
end StandardMapEntropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal symmDiff
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] [Nonempty β]

omit [Fintype α] [MeasurableSingletonClass α] in
lemma exists_prefix_approx {Z : Ω → (ℕ → α)} (hZ : Measurable Z)
    {G : (ℕ → α) → β} (hG : Measurable G) (ε : ℝ) (hε : 0<ε) :
    ∃ (N : ℕ) (g : (Fin N → α) → β),
      μ {x | g (fun i => Z x i.val)≠G (Z x)}<ENNReal.ofReal ε := by
  classical
  let η := ε/((Fintype.card β : ℝ)+1)
  have hη : 0<η := div_pos hε (by positivity)
  let ν := μ.map Z
  have : IsProbabilityMeasure ν := inferInstance
  have happ (b : β) : ∃ C ∈ measurableCylinders (fun _ : ℕ => α),
      ν (C ∆ (G ⁻¹' {b}))<ENNReal.ofReal η := by
    apply exists_measure_symmDiff_lt_of_generateFrom_isSetRing isSetRing_measurableCylinders
      (μ := ν) ?_ generateFrom_measurableCylinders.symm (hG (measurableSet_singleton b))
      (ENNReal.ofReal_pos.mpr hη)
    refine ⟨{univ},countable_singleton _,?_,by simp⟩
    simpa only [singleton_subset_iff] using (univ_mem_measurableCylinders (fun _ : ℕ => α))
  choose C hC hsmall using happ
  have hcyl (b : β) : ∃ (s : Finset ℕ) (S : Set (∀ i : s,α)),MeasurableSet S ∧ C b=cylinder s S := by
    simpa only [mem_measurableCylinders] using hC b
  choose s S hS hSC using hcyl
  let N : ℕ := 1+∑ b : β,(s b).sup id
  have hindex (b : β) (i : s b) : i.val<N := by
    have hl := Finset.le_sup (f := id) i.property
    have hs := Finset.single_le_sum (f := fun b : β => (s b).sup id)
      (fun b _ => Nat.zero_le _) (Finset.mem_univ b)
    dsimp only [id_eq] at hl
    dsimp [N]
    omega
  let P (b : β) (v : Fin N → α) : Prop := (fun i : s b => v ⟨i.val,hindex b i⟩)∈S b
  let g (v : Fin N → α) : β := if h : ∃ b,P b v then h.choose else Classical.choice inferInstance
  have hPred (b : β) (v : ℕ → α) : P b (fun i : Fin N => v i.val) ↔ v∈C b := by
    rw [hSC b]
    rfl
  have herr : {x | g (fun i => Z x i.val)≠G (Z x)}⊆
      Z ⁻¹' ⋃ b : β,C b ∆ (G ⁻¹' {b}) := by
    intro x hx
    by_contra hn
    have hall (b : β) : (Z x∈C b) ↔ G (Z x)=b := by
      have hb : Z x∉C b ∆ (G ⁻¹' {b}) := fun hb => hn (mem_iUnion_of_mem b hb)
      simp only [mem_symmDiff,mem_preimage,mem_singleton_iff] at hb
      tauto
    have hex : ∃ b,P b (fun i => Z x i.val) :=
      ⟨G (Z x),(hPred _ _).mpr ((hall _).mpr rfl)⟩
    have hg : g (fun i => Z x i.val)=hex.choose := dite_eq_left hex
    exact hx (hg.trans ((hall _).mp ((hPred _ _).mp hex.choose_spec)).symm)
  refine ⟨N,g,?_⟩
  have hCm (b : β) : MeasurableSet (C b) := by rw [hSC b]; exact (hS b).cylinder
  have hU : MeasurableSet (⋃ b : β,C b ∆ (G ⁻¹' {b})) :=
    MeasurableSet.iUnion (fun b => (hCm b).symmDiff (hG (measurableSet_singleton b)))
  calc
    μ {x | g (fun i => Z x i.val)≠G (Z x)}≤μ (Z ⁻¹' ⋃ b : β,C b ∆ (G ⁻¹' {b})) := measure_mono herr
    _=ν (⋃ b : β,C b ∆ (G ⁻¹' {b})) := (Measure.map_apply hZ hU).symm
    _≤∑ b : β,ν (C b ∆ (G ⁻¹' {b})) := measure_iUnion_fintype_le _ _
    _≤∑ _b : β,ENNReal.ofReal η := Finset.sum_le_sum (fun b _ => (hsmall b).le)
    _=ENNReal.ofReal ((Fintype.card β : ℝ)*η) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
    _<ENNReal.ofReal ε := ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr (by
      have hc : (0 : ℝ)≤Fintype.card β := Nat.cast_nonneg _
      dsimp [η]
      rw [←mul_div_assoc]
      apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith)

lemma exists_cond_prefix_lt {Z : Ω → (ℕ → α)} (hZ : Measurable Z)
    {q : Ω → β} (hq : Measurable q)
    (hfactor : ∃ G : (ℕ → α) → β,Measurable G ∧ q=ᵐ[μ]G ∘ Z)
    (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ,cond μ q (fun x => fun i : Fin N => Z x i.val)<ε := by
  classical
  obtain ⟨η,hη,hs⟩ := cond_small_of_error (α := β) μ ε hε
  obtain ⟨G,hG,hqG⟩ := hfactor
  obtain ⟨N,g,hg⟩ := exists_prefix_approx μ hZ hG η hη
  let p : Ω → (Fin N → α) := fun x i => Z x i.val
  have hp : Measurable p := Measurable.of_eval (fun i => (measurable_pi_apply i.val).comp hZ)
  have hm : mass μ (errorObs q (g ∘ p)) true<η := by
    have he : (errorObs q (g ∘ p)) ⁻¹' {true}=ᵐ[μ]{x | g (p x)≠G (Z x)} := by
      filter_upwards [hqG] with x hx
      change (errorObs q (g ∘ p) x=true)=(g (p x)≠G (Z x))
      apply propext
      simp only [errorObs,Function.comp_def,decide_eq_true_eq,hx,ne_comm]
    rw [mass,measure_congr he]
    exact (ENNReal.toReal_lt_of_lt_ofReal hg)
  exact ⟨N,lt_of_le_of_lt (cond_factor_right μ q p g hq hp)
    (hs q (g ∘ p) hq ((measurable_of_countable g).comp hp) hm)⟩

end StandardMapEntropy.Entropy

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter

def TailObservable {X A B : Type*} [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure X) (T : X → X) (α : X → A) (q : X → B) : Prop :=
  ∀ m : ℕ,∃ G : (ℕ → A) → B,Measurable G ∧ q=ᵐ[μ]G ∘ tailName T α m

lemma TailObservable.word {X A B : Type*} [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure X} {T : X → X} (hT : MeasurePreserving T μ μ)
    {α : X → A} {q : X → B} (hq : TailObservable μ T α q) (n : ℕ) :
    TailObservable μ T α (StandardMapEntropy.Entropy.word T q n) := by
  intro m
  obtain ⟨G,hG,he⟩ := hq m
  let H (v : ℕ → A) (i : Fin n) := G (fun j => v (j+i.val))
  have hH : Measurable H := Measurable.of_eval (fun i => hG.comp
    (Measurable.of_eval (fun j => measurable_pi_apply (j+i.val))))
  refine ⟨H,hH,?_⟩
  have hall := ae_all_iff.mpr (fun i : Fin n => (hT.iterate i.val).quasiMeasurePreserving.ae he)
  filter_upwards [hall] with x hx
  funext i
  have hi := hx i
  change q (T^[i.val] x)=G (fun j => α (T^[j+i.val+m] x))
  rw [hi]
  change G (tailName T α m (T^[i.val] x))=G (fun j => α (T^[j+i.val+m] x))
  congr 1
  funext j
  simp only [tailName,←Function.iterate_add_apply]
  congr 2
  omega

lemma tailEvent_bool {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    {μ : Measure X} {T : X → X} {α : X → A} {E : Set X}
    (hE : TailEvent μ T α E) :
    TailObservable μ T α (fun x => by classical exact decide (x∈E)) := by
  classical
  intro m
  obtain ⟨D,hD,he⟩ := hE m
  refine ⟨fun v => decide (v∈D),?_,?_⟩
  · have hF : Measurable (fun v : ℕ → A => if v∈D then (true : Bool) else false) :=
      Measurable.ite hD measurable_const measurable_const
    convert hF using 1
    funext v
    by_cases h : v∈D <;> simp [h]
  · filter_upwards [he] with x hx
    change decide (x∈E)=decide (tailName T α m x∈D)
    exact congrArg (fun P : Prop => decide P) hx
end HyperbolicCoding
end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

omit [IsProbabilityMeasure μ] in
lemma cond_word_future_eq (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (n m : ℕ) :
    cond μ (word f p n) (fun x => word f p m (f^[n] x))=
      obs μ (word f p (n+m))-obs μ (word f p m) := by
  unfold cond
  rw [←obs_word_split μ f p n m]
  exact congrArg (fun t => obs μ (word f p (n+m))-t)
    (obs_comp_preserving μ (f^[n]) (hf.iterate n) (word f p m) (word_measurable f hf.measurable p hp m))

omit [IsProbabilityMeasure μ] in
lemma entropy_increment_eq (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (m : ℕ) :
    obs μ (word f p (m+1))-obs μ (word f p m)=
      cond μ p (fun x => word f p m (f x)) := by
  have h := cond_word_future_eq μ f hf p hp 1 m
  rw [Nat.add_comm 1 m] at h
  have he : (Equiv.funUnique (Fin 1) α) ∘ word f p 1=p := by
    funext x; rfl
  rw [←cond_equiv_left μ (word f p 1) (fun x => word f p m (f^[1] x))
    (Equiv.funUnique (Fin 1) α),he] at h
  simpa only [Function.iterate_one] using h.symm

lemma entropy_increment_antitone (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) :
    Antitone (fun m : ℕ => obs μ (word f p (m+1))-obs μ (word f p m)) := by
  apply antitone_nat_of_succ_le
  intro m
  rw [entropy_increment_eq μ f hf p hp,entropy_increment_eq μ f hf p hp]
  exact cond_factor_right μ p (fun x => word f p (m+1) (f x))
    (fun v : Fin (m+1) → α => fun i : Fin m => v i.castSucc) hp
    ((word_measurable f hf.measurable p hp (m+1)).comp hf.measurable)

lemma entropy_increment_nonneg (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (m : ℕ) :
    0≤obs μ (word f p (m+1))-obs μ (word f p m) := by
  rw [entropy_increment_eq μ f hf p hp]
  exact cond_nonneg μ p _ hp ((word_measurable f hf.measurable p hp m).comp hf.measurable)

lemma entropy_increment_tendsto (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) :
    Tendsto (fun m : ℕ => obs μ (word f p (m+1))-obs μ (word f p m)) atTop (𝓝 (rate μ f p)) := by
  let d := fun m : ℕ => obs μ (word f p (m+1))-obs μ (word f p m)
  have hbd : BddBelow (Set.range d) := ⟨0,by rintro _ ⟨m,rfl⟩; exact entropy_increment_nonneg μ f hf p hp m⟩
  have hd := tendsto_atTop_ciInf (entropy_increment_antitone μ f hf p hp) hbd
  have hs (n : ℕ) : ∑ j ∈ Finset.range n,d j=obs μ (word f p n) := by
    induction n with
    | zero => simp only [Finset.range_zero,Finset.sum_empty,obs_word_zero]
    | succ n ih => rw [Finset.sum_range_succ,ih]; dsimp [d]; ring
  change Tendsto d atTop (𝓝 (⨅ i,d i)) at hd
  have hh := hd.cesaro
  simp only [hs,←div_eq_inv_mul] at hh
  have he := tendsto_nhds_unique hh (rate_tendsto μ f hf p hp)
  rwa [he] at hd

lemma rate_le_entropy_increment (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (m : ℕ) :
    rate μ f p≤obs μ (word f p (m+1))-obs μ (word f p m) := by
  apply le_of_tendsto (entropy_increment_tendsto μ f hf p hp)
  filter_upwards [eventually_ge_atTop m] with n hn
  exact entropy_increment_antitone μ f hf p hp hn

lemma rate_mul_le_cond_future (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (n m : ℕ) :
    (n : ℝ)*rate μ f p≤cond μ (word f p n) (fun x => word f p m (f^[n] x)) := by
  rw [cond_word_future_eq μ f hf p hp]
  induction n with
  | zero =>
    simp only [Nat.cast_zero,zero_mul]
    have he (a b : ℕ) (h : a=b) : obs μ (word f p a)=obs μ (word f p b) := by subst b; rfl
    exact sub_nonneg.mpr (le_of_eq (he (0+m) m (Nat.zero_add m)).symm)
  | succ n ih =>
    have hh := rate_le_entropy_increment μ f hf p hp (n+m)
    rw [Nat.cast_add,Nat.cast_one]
    rw [show n+1+m=n+m+1 from by omega]
    nlinarith

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open HyperbolicCoding MeasureTheory Set Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]

lemma cond_triangle (p : Ω → α) (q : Ω → β) (r : Ω → γ)
    (hp : Measurable p) (hq : Measurable q) (hr : Measurable r) :
    cond μ p r≤cond μ p q+cond μ q r := by
  have h1 := cond_chain μ p r q
  have h2 := cond_chain μ q r p
  have hz := cond_nonneg μ q (fun x => (p x,r x)) hq (hp.prodMk hr)
  have hb := cond_pair_right μ p q r hp hq hr
  have he : cond μ (fun x => (p x,q x)) r=cond μ (fun x => (q x,p x)) r := by
    exact (cond_equiv_left μ (fun x => (p x,q x)) r (Equiv.prodComm α β)).symm
  linarith

lemma cond_word_window_bound (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (q : Ω → β) (hq : Measurable q) (n M : ℕ) :
    cond μ (word f q n) (word f p (n+M))≤(n : ℝ)*cond μ q (word f p M) := by
  let g (v : Fin (n+M) → α) (i : Fin n) (j : Fin M) := v ⟨j.val+i.val,by omega⟩
  have he : g ∘ word f p (n+M)=word f (word f p M) n := by
    funext x i j
    simp only [Function.comp_def,g,word,←Function.iterate_add_apply]
  have hb := cond_factor_right μ (word f q n) (word f p (n+M)) g
    (word_measurable f hf.measurable q hq n) (word_measurable f hf.measurable p hp _)
  rw [he] at hb
  exact hb.trans (cond_word_bound μ f hf q (word f p M) hq
    (word_measurable f hf.measurable p hp M) n)

lemma rate_mul_le_cond_tail [Nonempty β] (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (q : Ω → β) (hq : Measurable q)
    (ht : TailObservable μ f p q) (n : ℕ) :
    (n : ℝ)*rate μ f p≤cond μ (word f p n) q := by
  by_contra hn
  have hε : 0<(n : ℝ)*rate μ f p-cond μ (word f p n) q := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨M,hM⟩ := exists_cond_prefix_lt μ (measurable_tailName hf.measurable hp n) hq
    (ht n) _ hε
  have he : (fun x => fun i : Fin M => tailName f p n x i.val)=
      (fun x => word f p M (f^[n] x)) := by
    funext x i
    simp only [tailName,word,←Function.iterate_add_apply]
  rw [he] at hM
  have hb := rate_mul_le_cond_future μ f hf p hp n M
  have hc := cond_triangle μ (word f p n) q (fun x => word f p M (f^[n] x))
    (word_measurable f hf.measurable p hp n) hq
    ((word_measurable f hf.measurable p hp M).comp (hf.measurable.iterate n))
  linarith

theorem tailObservable_rate_zero [Nonempty β] (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (q : Ω → β) (hq : Measurable q)
    (ht : TailObservable μ f p q) : rate μ f q=0 := by
  apply le_antisymm ?_ (rate_nonneg μ f hf q hq)
  by_contra hn
  have hε : 0<rate μ f q/2 := half_pos (lt_of_not_ge hn)
  obtain ⟨M,hM⟩ := exists_cond_prefix_lt μ (measurable_tailName hf.measurable hp 0) hq
    (ht 0) _ hε
  change cond μ q (word f p M)<rate μ f q/2 at hM
  have hb (n : ℕ) : obs μ (word f q n)≤obs μ (word f p n)-(n : ℝ)*rate μ f p+
      obs μ (word f p M)+(n : ℝ)*(rate μ f q/2) := by
    have hl := rate_mul_le_cond_tail μ f hf p hp (word f q n)
      (word_measurable f hf.measurable q hq n) (ht.word hf n) (n+M)
    have hu := cond_word_window_bound μ f hf p hp q hq n M
    have hs := obs_word_subadd μ f hf p hp n M
    have he := obs_pair_swap μ (word f q n) (word f p (n+M))
    have hz := mul_nonneg (Nat.cast_nonneg M) (rate_nonneg μ f hf p hp)
    have hc := mul_le_mul_of_nonneg_left hM.le (Nat.cast_nonneg n)
    unfold cond at hl hu hc
    rw [Nat.cast_add] at hl
    nlinarith
  have hlim : Tendsto (fun n : ℕ => (obs μ (word f p n)/(n : ℝ)-rate μ f p)+
      obs μ (word f p M)/(n : ℝ)+rate μ f q/2) atTop (𝓝 (rate μ f q/2)) := by
    have hh := ((rate_tendsto μ f hf p hp).sub_const (rate μ f p)).add
      (tendsto_const_div_atTop_nhds_zero_nat (obs μ (word f p M)))
    simpa only [sub_self,zero_add] using hh.add_const (rate μ f q/2)
  have hh := le_of_tendsto_of_tendsto (rate_tendsto μ f hf q hq) hlim (show
      ∀ᶠ n : ℕ in atTop,obs μ (word f q n)/(n : ℝ)≤
        (obs μ (word f p n)/(n : ℝ)-rate μ f p)+
          obs μ (word f p M)/(n : ℝ)+rate μ f q/2 from by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ)<n := by exact_mod_cast hn
    apply (div_le_iff₀ hn0).mpr
    have h1 := div_mul_cancel₀ (obs μ (word f p n)) hn0.ne'
    have h2 := div_mul_cancel₀ (obs μ (word f p M)) hn0.ne'
    nlinarith [hb n])
  linarith

end StandardMapEntropy.Entropy

end
end

end OAI
