import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Coding.PartitionLimit
import OAI.Dynamics.StandardMap.Coding.SanitizedTowerLaw

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]

def FiniteRateSupremum (μ : Measure X) (f : X → X) (h : ℝ) : Prop :=
  (∀ r : ℕ,∀ p : X → Fin (r+1),Measurable p → rate μ f p≤h) ∧
  (∀ ε : ℝ,0 < ε → ∃ r : ℕ,∃ p : X → Fin (r+1),Measurable p ∧ h-ε < rate μ f p)

omit [StandardBorelSpace X] [TopologicalSpace X] [SecondCountableTopology X]
  [OpensMeasurableSpace X] in
lemma FiniteRateSupremum.upper {μ : Measure X} [IsProbabilityMeasure μ] {f : X → X} {h : ℝ}
    (H : FiniteRateSupremum μ f h)
    {C : Type*} [Fintype C] [Nonempty C] [MeasurableSpace C] [MeasurableSingletonClass C]
    (p : X → C) (hp : Measurable p) : rate μ f p≤h := by
  have hc : Fintype.card C-1+1=Fintype.card C := Nat.sub_add_cancel Fintype.card_pos
  let e : C ≃ Fin (Fintype.card C-1+1) := (Fintype.equivFin C).trans (finCongr hc.symm)
  have he := H.1 (Fintype.card C-1) (e ∘ p) ((measurable_of_finite e).comp hp)
  rwa [rate_equiv] at he

omit [StandardBorelSpace X] [TopologicalSpace X] [SecondCountableTopology X]
  [OpensMeasurableSpace X] [DecidableEq A] [Nonempty A] in
lemma iid_lawClose_prefix (μ : Measure X) (e : X ≃ᵐ X) (p : X → A) (hp : Measurable p)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    {m n : ℕ} (hmn : m≤n) {δ : ℝ}
    (h : LawClose (μ.map (word e p n))
      (Measure.pi (fun _ : Fin n => finiteWeightLaw β)) δ) :
    LawClose (μ.map (word e p m))
      (Measure.pi (fun _ : Fin m => finiteWeightLaw β)) δ := by
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  let ν := Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)
  have h' : LawClose (μ.map (word e p n))
      (ν.map (word iidShift (fun w : ℤ → A => w 0) n)) δ := by
    simpa only [ν,iid_word_law] using h
  have hh := lawClose_prefix μ ν e iidShift e.measurable iidShift.measurable p
    (fun w : ℤ → A => w 0) hp (measurable_pi_apply 0) hmn h'
  simpa only [ν,iid_word_law] using hh

def GoodIIDStage (μ : Measure X) (e : X ≃ᵐ X) (β : A → ℝ)
    {η : ℝ} (T : IIDCopyTest μ e β η) (n : ℕ) (q : X → A) : Prop :=
  Measurable q ∧
  LawClose (μ.map (word e q (max T.length n)))
    (Measure.pi (fun _ : Fin (max T.length n) => finiteWeightLaw β))
    (min T.tolerance (1/(n+1 : ℝ))) ∧
  weightEntropy β-T.tolerance≤rate μ e q

lemma goodIIDStage_initial (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (e^[m]) μ)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0 < weightEntropy β) (H : FiniteRateSupremum μ e (weightEntropy β))
    (zero one : A) (h01 : zero≠one) {η : ℝ} (T : IIDCopyTest μ e β η) (n : ℕ) :
    ∃ q : X → A,GoodIIDStage μ e β T n q := by
  obtain ⟨r,p,hp,hpnear⟩ := H.2 (T.tolerance/2) (half_pos T.tolerance_pos)
  have hε : 0 < min T.tolerance (1/(n+1 : ℝ)) := lt_min T.tolerance_pos (by positivity)
  obtain ⟨q,hq,hl,hr⟩ := initial_rate_controlled_copy μ e he htotal p hp β hβ hβsum
    hβentropy (H.1 r p hp) zero one h01 (max T.length n) hε (half_pos T.tolerance_pos)
  exact ⟨q,hq,hl,by linarith⟩

lemma goodIIDStage_next (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (e^[m]) μ)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0 < weightEntropy β) (H : FiniteRateSupremum μ e (weightEntropy β))
    (zero one : A) (h01 : zero≠one) {η ξ : ℝ} (hη : 0 < η)
    (T : IIDCopyTest μ e β (η/2)) (U : IIDCopyTest μ e β ξ)
    {n : ℕ} {q : X → A} (hq : GoodIIDStage μ e β T n q) :
    ∃ q' : X → A,GoodIIDStage μ e β U (n+1) q' ∧ μ.real {x | q x≠q' x}<η := by
  obtain ⟨r,p,hp,hpnear⟩ := H.2 (U.tolerance/2) (half_pos U.tolerance_pos)
  let P : X → A × Fin (r+1) := fun x => (q x,p x)
  have hP : Measurable P := hq.1.prodMk hp
  have hrateP : rate μ e p≤rate μ e P := rate_factor μ e he.toMeasurePreserving P hP Prod.snd
  have htest : LawClose (μ.map (word e (Prod.fst ∘ P) T.length))
      (Measure.pi (fun _ : Fin T.length => finiteWeightLaw β)) T.tolerance :=
    (iid_lawClose_prefix μ e q hq.1 β hβ hβsum (le_max_left _ _) hq.2.1).mono (min_le_left _ _)
  have hε : 0 < min U.tolerance (1/((n+1)+1 : ℝ)) := lt_min U.tolerance_pos (by positivity)
  obtain ⟨q',s,M,G,hq',hc,hl,_hd,hr⟩ := T.copy μ e he htotal β hβ hβsum hβentropy
    zero one h01 hη P hP Prod.fst htest hq.2.2 (H.upper P hP)
    (max U.length (n+1)) hε (half_pos U.tolerance_pos)
  refine ⟨q',⟨hq',?_,by linarith⟩,hc⟩
  simpa only [Nat.cast_add,Nat.cast_one] using hl

theorem full_entropy_copy_sequence (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (e^[m]) μ)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0 < weightEntropy β) (H : FiniteRateSupremum μ e (weightEntropy β))
    (zero one : A) (h01 : zero≠one) (η : ℕ → ℝ) (hη : ∀ n,0 < η n) :
    ∃ q : ℕ → X → A,(∀ n,Measurable (q n)) ∧
      (∀ n,μ.real {x | q (n+1) x≠q n x}<η n) ∧
      (∀ n,LawClose (μ.map (word e (q n) n))
        (Measure.pi (fun _ : Fin n => finiteWeightLaw β)) (1/(n+1 : ℝ))) := by
  have hT (n : ℕ) : Nonempty (IIDCopyTest μ e β (η n/2)) :=
    exists_iidCopyTest μ e he.toMeasurePreserving β hβ hβsum hβentropy (half_pos (hη n))
  let T (n : ℕ) : IIDCopyTest μ e β (η n/2) := Classical.choice (hT n)
  obtain ⟨q₀,hq₀⟩ := goodIIDStage_initial μ e he htotal β hβ hβsum hβentropy H zero one h01 (T 0) 0
  have hnext (n : ℕ) (q : {q : X → A // GoodIIDStage μ e β (T n) n q}) :
      ∃ q' : X → A,GoodIIDStage μ e β (T (n+1)) (n+1) q' ∧
        μ.real {x | q.val x≠q' x}<η n :=
    goodIIDStage_next μ e he htotal β hβ hβsum hβentropy H zero one h01 (hη n)
      (T n) (T (n+1)) q.property
  let next (n : ℕ) (q : {q : X → A // GoodIIDStage μ e β (T n) n q}) :
      {q' : X → A // GoodIIDStage μ e β (T (n+1)) (n+1) q'} :=
    ⟨Classical.choose (hnext n q),(Classical.choose_spec (hnext n q)).1⟩
  let z : (n : ℕ) → {q : X → A // GoodIIDStage μ e β (T n) n q} :=
    fun n => Nat.rec (motive:=fun j => {q : X → A // GoodIIDStage μ e β (T j) j q})
      ⟨q₀,hq₀⟩ next n
  refine ⟨fun n => (z n).val,fun n => (z n).property.1,?_,?_⟩
  · intro n
    have h := (Classical.choose_spec (hnext n (z n))).2
    have h' : μ.real {x | (z n).val x≠(z (n+1)).val x}<η n := h
    have hs : {x | (z (n+1)).val x≠(z n).val x}=
        {x | (z n).val x≠(z (n+1)).val x} := Set.ext (fun _ => ne_comm)
    rw [hs]
    exact h'
  · intro n
    exact (iid_lawClose_prefix μ e (z n).val (z n).property.1 β hβ hβsum
      (le_max_right _ _) (z n).property.2.1).mono (min_le_right _ _)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iidShift_integerIterate (n : ℤ) (w : ℤ → A) (i : ℤ) :
    integerIterate iidShift n w i=w (i+n) := by
  cases n with
  | ofNat m => rw [Int.ofNat_eq_natCast,integerIterate_nat,iidShift_iterate]
  | negSucc m =>
    have hn : Int.negSucc m= -((m+1 : ℕ) : ℤ) := by omega
    rw [hn,integerIterate_neg_nat,iidShift_symm_iterate,sub_eq_add_neg]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iid_orbitName (w : ℤ → A) : orbitName iidShift (fun z : ℤ → A => z 0) w=w := by
  funext i
  exact (iidShift_integerIterate i w 0).trans (by rw [zero_add])

lemma finite_integer_window (s : Finset ℤ) :
    ∃ a : ℤ,∃ N : ℕ,∀ i∈s,0≤ i-a ∧ i-a < (N : ℤ) := by
  let b := s.sup Int.natAbs
  refine ⟨-(b : ℤ),2*b+1,?_⟩
  intro i hi
  have hb : i.natAbs≤b := Finset.le_sup (f:=Int.natAbs) hi
  have hb' : (i.natAbs : ℤ)≤b := by exact_mod_cast hb
  have h1 : -i≤(i.natAbs : ℤ) := by simpa only [Int.natAbs_neg] using (Int.le_natAbs (a:=-i))
  have h2 := (Int.le_natAbs (a:=i))
  constructor <;> omega

lemma orbit_restrict_map_eq_window (μ : Measure X) (e : X ≃ᵐ X)
    (he : MeasurePreserving e μ μ) (p : X → A) (hp : Measurable p)
    (s : Finset ℤ) (a : ℤ) (N : ℕ) (hb : ∀ i∈s,0≤ i-a ∧ i-a < (N : ℤ)) :
    μ.map (s.restrict ∘ orbitName e p)=
      (μ.map (word e p N)).map (fun w : Fin N → A => fun i : s =>
        w ⟨(i.val-a).toNat,by have h := hb i.val i.property; omega⟩) := by
  let W : (Fin N → A) → (s → A) := fun w i =>
    w ⟨(i.val-a).toNat,by have h := hb i.val i.property; omega⟩
  have hW : Measurable W := measurable_of_finite W
  have hpN := word_measurable e e.measurable p hp N
  have hfun : s.restrict ∘ orbitName e p=(W ∘ word e p N) ∘ integerIterate e a := by
    funext x i
    change p (integerIterate e i.val x) = p (e^[((i.val-a).toNat)] (integerIterate e a x))
    rw [←integerIterate_nat,←integerIterate_add]
    have h := hb i.val i.property
    congr 2
    omega
  change μ.map (s.restrict ∘ orbitName e p)=(μ.map (word e p N)).map W
  rw [hfun,←Measure.map_map (hW.comp hpN) (integerIterate_measurable e a),
    (integerIterate_measurePreserving e he a).map_eq,Measure.map_map hW hpN]

lemma lawClose_orbit_restrict_of_word
    (μ : Measure X) (ν : Measure Y) (e : X ≃ᵐ X) (d : Y ≃ᵐ Y)
    (he : MeasurePreserving e μ μ) (hd : MeasurePreserving d ν ν)
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q)
    (s : Finset ℤ) (a : ℤ) (N : ℕ) (hb : ∀ i∈s,0≤ i-a ∧ i-a < (N : ℤ))
    {δ : ℝ} (hl : LawClose (μ.map (word e p N)) (ν.map (word d q N)) δ) :
    LawClose (μ.map (s.restrict ∘ orbitName e p))
      (ν.map (s.restrict ∘ orbitName d q)) δ := by
  rw [orbit_restrict_map_eq_window μ e he p hp s a N hb,
    orbit_restrict_map_eq_window ν d hd q hq s a N hb]
  exact hl.map (measurable_of_finite _)

omit [Fintype A] [MeasurableSingletonClass A] in
lemma restricted_box_lawClose (μ : Measure X) (ν : Measure Y)
    (e : X ≃ᵐ X) (d : Y ≃ᵐ Y) (p : X → A) (q : Y → A)
    (hp : Measurable p) (hq : Measurable q) (s : Finset ℤ)
    (t : ℤ → Set A) (ht : ∀ i,MeasurableSet (t i)) {δ : ℝ}
    (h : LawClose (μ.map (s.restrict ∘ orbitName e p))
      (ν.map (s.restrict ∘ orbitName d q)) δ) :
    |(μ.map (orbitName e p)).real (Set.pi s t)-
      (ν.map (orbitName d q)).real (Set.pi s t)|≤δ := by
  let D : Set (s → A) := Set.pi Set.univ (fun i => t i.val)
  have hD : MeasurableSet D := MeasurableSet.pi Set.countable_univ (fun i _ => ht i.val)
  have hpre : (s.restrict : (ℤ → A) → (s → A)) ⁻¹' D=Set.pi s t := by
    ext w
    simp only [D,mem_preimage,Set.mem_pi,mem_univ,true_implies,Finset.mem_coe,Finset.restrict]
    exact ⟨fun h i hi => h ⟨i,hi⟩,fun h i => h i i.property⟩
  have hr : Measurable (s.restrict : (ℤ → A) → (s → A)) := measurable_restrict (s : Set ℤ)
  have h1 : (μ.map (s.restrict ∘ orbitName e p)).real D=
      (μ.map (orbitName e p)).real (Set.pi s t) := by
    simp only [Measure.real]
    rw [←Measure.map_map hr (measurable_orbitName e hp),Measure.map_apply hr hD,hpre]
  have h2 : (ν.map (s.restrict ∘ orbitName d q)).real D=
      (ν.map (orbitName d q)).real (Set.pi s t) := by
    simp only [Measure.real]
    rw [←Measure.map_map hr (measurable_orbitName d hq),Measure.map_apply hr hD,hpre]
  simpa only [h1,h2] using h D hD

theorem iid_law_of_growing_forward_words [Nonempty A]
    (μ : Measure X) [IsProbabilityMeasure μ] (e : X ≃ᵐ X)
    (he : MeasurePreserving e μ μ) (q : ℕ → X → A) (hq : ∀ n,Measurable (q n))
    (p : X → A) (hp : Measurable p)
    (hlim : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x)
    (β : Measure A) [IsProbabilityMeasure β] (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hlaw : ∀ n,LawClose (μ.map (word e (q n) n))
      (Measure.pi (fun _ : Fin n => β)) (ε n)) :
    MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => β)) := by
  apply iid_law_of_partition_limit e he hq hp hlim β
  intro s t ht
  let ν := Measure.infinitePi (fun _ : ℤ => β)
  obtain ⟨a,N,hN⟩ := finite_integer_window s
  have htarget : (ν.map (orbitName iidShift (fun w : ℤ → A => w 0))).real (Set.pi s t)=
      (∏ i∈s,β (t i)).toReal := by
    rw [show orbitName iidShift (fun w : ℤ → A => w 0)=id from funext iid_orbitName,
      Measure.map_id]
    exact congrArg ENNReal.toReal (Measure.infinitePi_pi (fun _ : ℤ => β) (fun i _ => ht i))
  have hbound : ∀ᶠ n : ℕ in atTop,
      |(μ.map (orbitName e (q n))).real (Set.pi s t)-(∏ i∈s,β (t i)).toReal|≤ε n := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hb : ∀ i∈s,0≤ i-a ∧ i-a < (n : ℤ) := by
      intro i hi
      have h := hN i hi
      exact ⟨h.1,lt_of_lt_of_le h.2 (by exact_mod_cast hn)⟩
    have hl : LawClose (μ.map (word e (q n) n))
        (ν.map (word iidShift (fun w : ℤ → A => w 0) n)) (ε n) := by
      simpa only [ν,iid_word_law] using hlaw n
    have hr := lawClose_orbit_restrict_of_word μ ν e iidShift he (iidShift_preserving β)
      (q n) (fun w : ℤ → A => w 0) (hq n) (measurable_pi_apply 0) s a n hb hl
    have hh := restricted_box_lawClose μ ν e iidShift (q n) (fun w : ℤ → A => w 0)
      (hq n) (measurable_pi_apply 0) s t ht hr
    rwa [htarget] at hh
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  exact squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hbound hε

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal NNReal Topology
variable {X A : Type*} [MeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma word_law_of_iid_factor (μ : Measure X) (e : X ≃ᵐ X) (p : X → A)
    (_hp : Measurable p) (β : Measure A) [IsProbabilityMeasure β]
    (hcode : MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => β)))
    (n : ℕ) : μ.map (word e p n)=Measure.pi (fun _ : Fin n => β) := by
  have heq : word iidShift (fun w : ℤ → A => w 0) n ∘ orbitName e p=word e p n := by
    funext x i
    rw [Function.comp_apply,iid_word_eq]
    exact congrArg p (integerIterate_nat e i.val x)
  have hm := congrArg (fun ν => ν.map (word iidShift (fun w : ℤ → A => w 0) n)) hcode.map_eq
  rw [Measure.map_map (word_measurable iidShift iidShift.measurable _ (measurable_pi_apply 0) n)
    hcode.measurable,heq,iid_word_law] at hm
  exact hm

lemma rate_of_iid_factor [DecidableEq A] (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (p : X → A) (hp : Measurable p)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hcode : MeasurePreserving (orbitName e p) μ
      (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β))) :
    rate μ e p=weightEntropy β := by
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  have hword (n : ℕ) : obs μ (word e p n)=(n : ℝ)*weightEntropy β := by
    have hmass : mass μ (word e p n)=productWordWeight β n := by
      funext w
      change μ.real ((word e p n) ⁻¹' {w})=_
      rw [←map_measureReal_apply (word_measurable e e.measurable p hp n) (measurableSet_singleton w),
        word_law_of_iid_factor μ e p hp (finiteWeightLaw β) hcode,
        Measure.real,Measure.pi_singleton]
      simp only [finiteWeightLaw_singleton,ENNReal.toReal_prod,ENNReal.toReal_ofReal (hβ _),
        productWordWeight]
    rw [obs,hmass]
    exact shannon_productWordWeight β hβsum n
  apply tendsto_nhds_unique (rate_tendsto μ e he p hp)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [hword,mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn.ne')]

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] in
lemma geometric_repainting_summable (μ : Measure X) [IsFiniteMeasure μ]
    (q : ℕ → X → A)
    (h : ∀ n,μ.real {x | q (n+1) x≠q n x}<((1/2 : ℝ≥0)^n : ℝ)) :
    (∑' n : ℕ,μ {x | q (n+1) x≠q n x})≠⊤ := by
  have hs : (∑' n : ℕ,(((1/2 : ℝ≥0)^n) : ℝ≥0∞))≠⊤ := by
    apply ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr
    simpa only [NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] using
      (summable_geometric_of_lt_one (show (0 : ℝ)≤1/2 by norm_num) (by norm_num : (1/2 : ℝ) < 1))
  apply ne_top_of_le_ne_top hs
  apply ENNReal.tsum_le_tsum
  intro n
  apply (ENNReal.toReal_le_toReal (measure_ne_top μ _) (by simp)).mp
  simpa only [Measure.real,ENNReal.toReal_pow,ENNReal.coe_toReal,NNReal.coe_pow] using (h n).le

variable [StandardBorelSpace X] [TopologicalSpace X] [SecondCountableTopology X]
  [OpensMeasurableSpace X] [DecidableEq A] [Nonempty A]

theorem full_entropy_iid_factor (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (e^[m]) μ)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0 < weightEntropy β) (H : FiniteRateSupremum μ e (weightEntropy β))
    (zero one : A) (h01 : zero≠one) :
    ∃ p : X → A,Measurable p ∧
      MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)) ∧
      rate μ e p=weightEntropy β ∧
      (∀ x,orbitName e p (e x)=fun i => orbitName e p x (i+1)) ∧
      (∀ r : ℕ,∀ α : X → Fin (r+1),Measurable α →
        rate μ e (fun x => (p x,α x))=weightEntropy β) := by
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  obtain ⟨q,hq,hpaint,hlaw⟩ := full_entropy_copy_sequence μ e he htotal β hβ hβsum hβentropy
    H zero one h01 (fun n => ((1/2 : ℝ≥0)^n : ℝ)) (fun _ => by positivity)
  obtain ⟨p,hp,hlim⟩ := exists_partition_limit μ q hq (geometric_repainting_summable μ q hpaint)
  have hcode := iid_law_of_growing_forward_words μ e he.toMeasurePreserving q hq p hp hlim
    (finiteWeightLaw β) (fun n => 1/(n+1 : ℝ)) tendsto_one_div_add_atTop_nhds_zero_nat hlaw
  have hrate := rate_of_iid_factor μ e he.toMeasurePreserving p hp β hβ hβsum hcode
  refine ⟨p,hp,hcode,hrate,fun x => orbitName_shift e p x,?_⟩
  intro r α hα
  apply le_antisymm (H.upper (fun x => (p x,α x)) (hp.prodMk hα))
  rw [←hrate]
  exact rate_pair_ge_left μ e he.toMeasurePreserving p α hp hα

end HyperbolicCoding

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

lemma shannon_weighted_le {A : Type*} [Fintype A]
    (p q : A → ℝ) (hp : ∀ a,0 ≤ p a) (hq : ∀ a,0 ≤ q a)
    (hps : ∑ a,p a=1) (hqs : ∑ a,q a=1)
    {c : ℝ} (hc : 0 < c) (hdom : ∀ a,c*p a ≤ q a) :
    c*shannon p ≤ shannon q := by
  have hs (a : A) (ha : p a≠0) : q a≠0 := by
    have hp' : 0 < p a := lt_of_le_of_ne (hp a) (Ne.symm ha)
    exact ne_of_gt ((mul_pos hc hp').trans_le (hdom a))
  have hh := mul_le_mul_of_nonneg_left
    (shannon_le_cross p q hp hq hs (by rw [hps,hqs])) hc.le
  apply hh.trans
  rw [shannon,←Finset.sum_neg_distrib,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have hq1 : q a ≤ 1 := (Finset.single_le_sum (fun b _ => hq b) (Finset.mem_univ a)).trans_eq hqs
  have hl : Real.log (q a) ≤ 0 := Real.log_nonpos (hq a) hq1
  have hh := mul_le_mul_of_nonpos_right (hdom a) hl
  rw [Real.negMulLog]
  nlinarith

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
  [Fintype A] [MeasurableSingletonClass A]
lemma obs_weighted_le (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {c : ℝ} (hc : 0 < c) (hdom : ∀ E : Set X,c*ν.real E ≤ μ.real E)
    (p : X → A) (hp : Measurable p) : c*obs ν p ≤ obs μ p :=
  shannon_weighted_le (mass ν p) (mass μ p) (mass_nonneg _ _) (mass_nonneg _ _)
    (by simpa only [measure_univ,ENNReal.toReal_one] using mass_sum ν p hp)
    (by simpa only [measure_univ,ENNReal.toReal_one] using mass_sum μ p hp) hc (fun a => hdom _)

lemma rate_weighted_le (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {c : ℝ} (hc : 0 < c) (hdom : ∀ E : Set X,c*ν.real E ≤ μ.real E)
    (f : X → X) (hμ : MeasurePreserving f μ μ) (hν : MeasurePreserving f ν ν)
    (p : X → A) (hp : Measurable p) : c*rate ν f p ≤ rate μ f p := by
  apply le_of_tendsto_of_tendsto
    ((rate_tendsto ν f hν p hp).const_mul c) (rate_tendsto μ f hμ p hp)
  apply Filter.Eventually.of_forall
  intro n
  have hh := div_le_div_of_nonneg_right
    (obs_weighted_le μ ν hc hdom (word f p n) (word_measurable f hμ.measurable p hp n))
    (Nat.cast_nonneg n)
  simpa only [mul_div_assoc] using hh
end StandardMapEntropy.Entropy

namespace StandardMapEntropy
open MeasureTheory Set Filter HyperbolicCoding
open scoped BigOperators ENNReal Topology
lemma area_weight_normalized (E : Set Torus) (hE : 0 < area E) (B : Set Torus) :
    area.real E*(normalizedArea E).real B ≤ area.real B := by
  have hc : area.real E≠0 := (ENNReal.toReal_pos hE.ne' (measure_ne_top area E)).ne'
  have he : area.real E*(normalizedArea E).real B=(area.restrict E).real B := by
    simp only [normalizedArea,Measure.real,Measure.smul_apply,smul_eq_mul,
      ENNReal.toReal_mul,ENNReal.toReal_inv]
    change area.real E*((area.real E)⁻¹*(area.restrict E).real B)=_
    rw [←mul_assoc,mul_inv_cancel₀ hc,one_mul]
    rfl
  rw [he]
  exact ENNReal.toReal_mono (measure_ne_top area B) (Measure.restrict_le_self B)

lemma restricted_finite_rate_upper {A : Type*} [MeasurableSpace A]
    [Fintype A] [MeasurableSingletonClass A]
    (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (E : Set Torus) (hE : 0 < area E)
    (hinv : MeasurePreserving ((standardMap k)^[n]) (normalizedArea E) (normalizedArea E))
    (p : Torus → A) (hp : Measurable p) :
    Entropy.rate (normalizedArea E) ((standardMap k)^[n]) p ≤
      (Real.log 1000+(∫ z,Real.log ‖standardDerivativeProduct k z n‖ ∂area))/(area.real E) := by
  let := normalizedArea_probability hE
  have hc : 0 < area.real E := ENNReal.toReal_pos hE.ne' (measure_ne_top area E)
  have hweighted := Entropy.rate_weighted_le area (normalizedArea E) hc
    (area_weight_normalized E hE) _ ((measurePreserving_standardMap k).iterate n) hinv p hp
  have hu := (finite_rate_le_metricEntropy area _ ((measurePreserving_standardMap k).iterate n) p hp).trans
    (metricEntropy_iterate_derivative_upper k hk n)
  have hnonneg : 0 ≤ Real.log 1000+(∫ z,Real.log ‖standardDerivativeProduct k z n‖ ∂area) := by
    apply add_nonneg (Real.log_nonneg (by norm_num))
    apply integral_nonneg
    intro z
    exact Real.log_nonneg (standardDerivativeProduct_norm_ge_one k z n)
  have hh := (ENNReal.ofReal_le_ofReal_iff hnonneg).mp hu
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_comm] using hweighted.trans hh
end StandardMapEntropy

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X : Type*} [MeasurableSpace X]

theorem exists_finiteRateSupremum (μ : Measure X) (f : X → X)
    (b : ℝ) (hb : ∀ r : ℕ,∀ p : X → Fin (r+1),Measurable p → rate μ f p ≤ b) :
    ∃ h : ℝ,FiniteRateSupremum μ f h ∧ h ≤ b := by
  let S : Set ℝ := {v | ∃ r : ℕ,∃ p : X → Fin (r+1),Measurable p ∧ v=rate μ f p}
  have hne : S.Nonempty := ⟨rate μ f (fun _ => (0 : Fin 1)),0,fun _ => 0,measurable_const,rfl⟩
  have hbd : BddAbove S := ⟨b,by rintro v ⟨r,p,hp,rfl⟩; exact hb r p hp⟩
  refine ⟨sSup S,⟨?_,?_⟩,csSup_le hne (by rintro v ⟨r,p,hp,rfl⟩; exact hb r p hp)⟩
  · intro r p hp
    exact le_csSup hbd ⟨r,p,hp,rfl⟩
  · intro ε hε
    obtain ⟨v,hv,hlt⟩ := exists_lt_of_lt_csSup hne (show sSup S-ε < sSup S by linarith)
    obtain ⟨r,p,hp,rfl⟩ := hv
    exact ⟨r,p,hp,hlt⟩
end HyperbolicCoding
end

end OAI
