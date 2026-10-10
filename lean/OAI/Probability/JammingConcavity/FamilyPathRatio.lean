import Mathlib
import OAI.Probability.JammingConcavity.RowReplicaMixtureFamilyReplicaNumeratorAe

namespace OAI

/-! Family Path Ratio. -/

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
open scoped ENNReal NNReal BigOperators Classical
open Classical
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
open scoped NNReal BigOperators
open MeasureTheory Metric Set
open Metric
open scoped RealInnerProductSpace
open Filter
open Finset Set
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open scoped BigOperators Classical
open scoped ENNReal NNReal Topology BigOperators Matrix MatrixOrder
open scoped BigOperators RealInnerProductSpace
open scoped NNReal Topology BigOperators
open scoped NNReal BigOperators RealInnerProductSpace
open scoped ENNReal NNReal BigOperators MatrixOrder
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

theorem familyReplica : FamilyReplicaStatement := by
  intro E _ _ _ _ ms
  induction ms with
  | nil =>
    intro hms h01 ν hν u hu hi b hb η hη hηm x
    let := familyCascadeLaw_probability 0 ν hν
    have hp : 0 < (ENNReal.ofReal (Real.exp (u x))).toReal^η :=
      Real.rpow_pos_of_pos (by rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]; exact Real.exp_pos _) _
    simp only [familyLeafTotal,familyReplicaWeight,familyReplicaMean,
      rpcPatternProduct,integral_const,lintegral_const,measure_univ,
      probReal_univ,one_smul,mul_one,ENNReal.ofReal_one,one_mul]
    rw [mul_comm, ENNReal.mul_div_cancel_right (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top]
  | cons m ms ih =>
    intro hms h01 ν hν u hu hi bs hbs η hη hηm x
    have hm := h01 m (by simp)
    have hs := List.pairwise_cons.mp hms
    have h01t : ∀ a ∈ ms, 0 < a ∧ a < 1 := fun a ha => h01 a (by simp [ha])
    change List (MarkedReplicaPattern E ms.length) at bs
    change bs ≠ (List.nil : List (MarkedReplicaPattern E ms.length)) ∧
      (∀ b, List.Mem b bs → ValidMarkedReplicaPattern ms.length b) at hbs
    let τ := familyCascadeLaw ms.length (fun j => ν (j+1))
    let := hν 0
    let := familyCascadeLaw_probability ms.length (fun j => ν (j+1)) (fun j => hν (j+1))
    have hτ : IsProbabilityMeasure τ := inferInstance
    let := hτ
    let F : E × FamilyCascadeTree E ms.length → ℝ≥0∞ :=
      fun z => familyLeafTotal ms u (x+z.1) z.2
    let r : E → ℝ := fun a => familyRecursion ms (fun j => ν (j+1)) u (x+a)
    let X : E × FamilyCascadeTree E ms.length → ℝ := fun z => Real.log (F z).toReal
    have hpmap : Measurable (fun z : E × FamilyCascadeTree E ms.length => (x+z.1,z.2)) := by fun_prop
    have hF : Measurable F := (measurable_familyLeafTotal ms hu).comp hpmap
    have hX : Measurable X := hF.ennreal_toReal.log
    have hS := familyUnmarkedTotal_properties ms hs.2 h01t (fun j => ν (j+1)) (fun j => hν (j+1))
    have hdis (a : E) : IdentDistrib (fun t => F (a,t)) (fun t => ENNReal.ofReal (Real.exp (r a))*
        familyUnmarkedTotal ms t) τ τ :=
      familyLeafTotal_identDistrib ms hs.2 h01t (fun j => ν (j+1)) (fun j => hν (j+1)) hu hi.2 (x+a)
    have hiS : Integrable (fun t => (familyUnmarkedTotal ms t).toReal^m) τ := hS.2.1 m hm.1 hs.1
    have hir : Integrable (fun a => Real.exp (m*r a)) (ν 0) := hi.1 x
    have hpF : ∀ᵐ z ∂(ν 0).prod τ, 0 < F z ∧ F z < ∞ :=
      familyChildTotal_positive_ae ms hs.2 h01t ν hν hu hi.2 x
    have hip := (scaled_family_rpow (ν 0) τ hF hdis hiS hir).1
    have hexp : (fun z => Real.exp (m*X z)) =ᵐ[(ν 0).prod τ] (fun z => (F z).toReal^m) := by
      filter_upwards [hpF] with z hz
      rw [Real.rpow_def_of_pos (ENNReal.toReal_pos hz.1.ne' hz.2.ne)]
      exact congrArg Real.exp (mul_comm _ _)
    have hiX : Integrable (fun z => Real.exp (m*X z)) ((ν 0).prod τ) := hip.congr hexp.symm
    let G (b : MarkedReplicaPattern E ms.length) (a : E) :=
      familyReplicaMean ms b (fun j => ν (j+1)) u (x+a)
    let C (b : MarkedReplicaPattern E ms.length) :=
      ENNReal.ofReal (rpcPatternProduct ms m (markedReplicaShape ms.length b))
    have hG (b : MarkedReplicaPattern E ms.length) (hb : List.Mem b bs) : Measurable (G b) :=
      (measurable_familyReplicaMean ms (fun j => ν (j+1)) (fun j => hν (j+1)) hu b
        (hbs.2 b hb)).comp (measurable_const.add measurable_id)
    have hw (b : MarkedReplicaPattern E ms.length) (hb : List.Mem b bs) :
        Measurable (fun z : E × FamilyCascadeTree E ms.length => familyReplicaWeight ms b u (x+z.1) z.2) :=
      (measurable_familyReplicaWeight ms hu b (hbs.2 b hb)).comp hpmap
    have hmean (b : MarkedReplicaPattern E ms.length) (hb : List.Mem b bs) :
        weightedChildMean ((ν 0).prod τ) m X
          (fun z => familyReplicaWeight ms b u (x+z.1) z.2) =
        C b * ∫⁻ a, familyReplicaMean ms b (fun j => ν (j+1)) u (x+a)
          ∂decoratedTransition m ms ν u x := by
      have hh (a : E) : (∫⁻ t, ENNReal.ofReal ((F (a,t)).toReal^m) *
          familyReplicaWeight ms b u (x+a) t ∂τ) / ENNReal.ofReal (∫ t, (F (a,t)).toReal^m ∂τ) =
          C b * G b a :=
        ih hs.2 h01t (fun j => ν (j+1)) (fun j => hν (j+1)) u hu hi.2 b (hbs.2 b hb)
          m hm.1.le hs.1 (x+a)
      have hcan := scaledFamilyWeightedMean (ν 0) τ hF (hw b hb)
        (measurable_const.mul (hG b hb)) hdis hS.1 hiS hir hh
      rw [hcan,decoratedTransition_lintegral_ratio m hm.1.ne' ms ν hν hu hi (hG b hb) x]
      simp only [Pi.mul_apply,mul_assoc]
      change (∫⁻ a, C b * (G b a * ENNReal.ofReal (Real.exp (m*r a))) ∂ν 0) /
        ENNReal.ofReal (∫ a, Real.exp (m*r a) ∂ν 0) =
        C b * ((∫⁻ a, G b a * ENNReal.ofReal (Real.exp (m*r a)) ∂ν 0) /
          ENNReal.ofReal (∫ a, Real.exp (m*r a) ∂ν 0))
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      simp only [div_eq_mul_inv,mul_assoc,C]
    have hblocks : ∀ b ∈ familyWeightedBlocks ms bs u x, 0 < b.1 ∧ Measurable b.2 := by
      intro b hb
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
      exact ⟨replicaPatternSize_pos _ _ (validMarked_shape _ a (hbs.2 a ha)),hw a ha⟩
    have hfin : ∀ b ∈ familyWeightedBlocks ms bs u x,
        weightedChildMean ((ν 0).prod τ) m X b.2 ≠ ∞ := by
      intro b hb
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
      rw [hmean a ha]
      apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      apply ne_of_lt
      calc
        _ ≤ ∫⁻ _ : E, 1 ∂decoratedTransition m ms ν u x := lintegral_mono fun y =>
          familyReplicaMean_le_one ms (fun z hz => (h01t z hz).1) (fun j => ν (j+1))
            (fun j => hν (j+1)) u hi.2 a (hbs.2 a ha) (x+y)
        _ = 1 := by
          let := decoratedTransition_probability m hm.1.ne' ms ν hν u hi x
          simp
        _ < ∞ := ENNReal.one_lt_top
    have hne : familyWeightedBlocks ms bs u x ≠ [] := by
      intro he
      exact hbs.1 (List.map_eq_nil_iff.mp he)
    have hwE := weightedEPPF ((ν 0).prod τ) m η hm.1 hm.2 hη (hηm m (by simp)) X hX hiX
      (familyWeightedBlocks ms bs u x) hne hblocks hfin
    have he := familyTotal_expMarked_ae ms hs.2 h01t ν hν hu hi.2 m x
    have hden : (∫ ω, (familyLeafTotal (m::ms) u x ω).toReal^η ∂familyCascadeLaw (m::ms).length ν) =
        ∫ ω, (expMarkedTotal m X ω).toReal^η ∂pointCloudLaw ((ν 0).prod τ) :=
      integral_congr_ae (he.mono fun _ h => congrArg (fun y : ℝ≥0∞ => y.toReal^η) h)
    rw [lintegral_congr_ae (familyReplica_numerator_ae ms m η hms h01 ν hν hu hi bs x),hden]
    change (∫⁻ ω, weightedMarkedPartitionNumerator m η X (familyWeightedBlocks ms bs u x) ω
      ∂pointCloudLaw ((ν 0).prod τ)) / _ = _
    rw [hwE]
    have hmeans : ((familyWeightedBlocks ms bs u x).map
        (fun b => weightedChildMean ((ν 0).prod τ) m X b.2)) =
        bs.map (fun b => C b * ∫⁻ a, familyReplicaMean ms b (fun j => ν (j+1)) u (x+a)
          ∂decoratedTransition m ms ν u x) :=
      (List.map_map (l := bs)).trans (List.map_congr_left hmean)
    have hsizes : (familyWeightedBlocks ms bs u x).map Prod.fst =
        bs.map (fun b => replicaPatternSize ms.length (markedReplicaShape ms.length b)) := List.map_map (l := bs)
    rw [hmeans,hsizes,List.prod_map_mul]
    have hprod : (bs.map C).prod =
        ENNReal.ofReal ((bs.map (fun b => rpcPatternProduct ms m (markedReplicaShape ms.length b))).prod) := by
      rw [ofReal_list_prod (by
        intro y hy
        obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
        exact rpcPatternProduct_nonneg ms hs.2 h01t m hs.1 _)]
      simp only [List.map_map,Function.comp_def,C]
    rw [hprod,←mul_assoc,←ENNReal.ofReal_mul
      (partitionProduct_nonneg hm.1.le hm.2 (hηm m (by simp)) _)]
    simp only [List.length_cons,markedReplicaShape,rpcPatternProduct,List.map_map,Function.comp_def,familyReplicaMean]
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

lemma lintegral_pi_prod_countable {I : Type*} [Fintype I]
    {P : I → Type*} [∀ i, Countable (P i)] [∀ i, MeasurableSpace (P i)]
    [∀ i, MeasurableSingletonClass (P i)]
    (μ : ∀ i, Measure (P i)) [∀ i, IsProbabilityMeasure (μ i)] (f : ∀ i, P i → ℝ≥0∞) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ a, f i a ∂μ i := by
  have hi := iIndepFun_pi (μ := μ) (X := f) (fun i => (measurable_of_countable _).aemeasurable)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hi
    (fun i => (measurable_of_countable (f i)).comp (measurable_pi_apply i))]
  apply Finset.prod_congr rfl
  intro i _
  exact (measurePreserving_eval μ i).lintegral_comp (measurable_of_countable _)

lemma lintegral_pi_fixed_root {I P L A : Type*} [Fintype I] [Countable P] [Countable A]
    [MeasurableSpace P] [MeasurableSingletonClass P]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (e : P ≃ L × A) (μ : Measure P) (ν : Measure A)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (c : ℝ≥0∞) (l : L)
    (hd : ∀ a, μ {e.symm (l,a)} = c * ν {a}) (f : (I → A) → ℝ≥0∞) :
    (∫⁻ x, if ∀ i, (e (x i)).1 = l then f (fun i => (e (x i)).2) else 0
      ∂Measure.pi (fun _ : I => μ)) = c ^ Fintype.card I *
        ∫⁻ y, f y ∂Measure.pi (fun _ : I => ν) := by
  let T : (I → P) → (I → A) := fun x i => (e (x i)).2
  let R : Set (I → P) := {x | ∀ i, (e (x i)).1 = l}
  have hm : ((Measure.pi (fun _ : I => μ)).restrict R).map T =
      c ^ Fintype.card I • Measure.pi (fun _ : I => ν) := by
    ext B hB
    rw [Measure.map_apply (measurable_of_countable _) hB,
      Measure.restrict_apply ((measurable_of_countable T) hB), Measure.smul_apply, smul_eq_mul]
    have he : T ⁻¹' B ∩ R = {x | (∀ i, (e (x i)).1 = l) ∧ T x ∈ B} := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_preimage, R, Set.mem_ofPred_eq]; exact and_comm
    rw [he]
    exact pi_fixed_root e μ ν c l hd B
  have he : (fun x : I → P => if ∀ i, (e (x i)).1 = l then f (T x) else 0) =
      R.indicator (f ∘ T) := by
    funext x; simp [R,Set.indicator]
  rw [he,lintegral_indicator (Set.to_countable R |>.measurableSet)]
  change (∫⁻ a, f (T a) ∂(Measure.pi (fun _ : I => μ)).restrict R) = _
  rw [← lintegral_map (measurable_of_countable _) (measurable_of_countable T),hm,
    lintegral_smul_measure,smul_eq_mul]

lemma familySampleLeafLaw_apply_good {E : Type} [MeasurableSpace E] [Add E]
    (ms : List ℝ) (u : E → ℝ) (x : E) (ω : FamilyCascadeTree E ms.length)
    (hω : 0 < familyLeafTotal ms u x ω ∧ familyLeafTotal ms u x ω < ∞)
    (A : Set (CascadePath ms.length)) :
    familySampleLeafLaw ms u x ω A = ∑' ℓ, if ℓ ∈ A then
      familyLeafMass ms u x ω ℓ / familyLeafTotal ms u x ω else 0 := by
  simp only [familySampleLeafLaw, ite_eq_left hω, Measure.sum_apply _ (show MeasurableSet A from trivial),
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (show MeasurableSet A from trivial)]
  apply tsum_congr
  intro ℓ
  by_cases hℓ : ℓ ∈ A <;> simp [hℓ,familyLeafMass]

lemma familySampleLeafLaw_probability {E : Type} [MeasurableSpace E] [Add E] [MeasurableAdd₂ E]
    (ms : List ℝ) (u : E → ℝ) (x : E) (ω : FamilyCascadeTree E ms.length) :
    IsProbabilityMeasure (familySampleLeafLaw ms u x ω) := by
  by_cases hω : 0 < familyLeafTotal ms u x ω ∧ familyLeafTotal ms u x ω < ∞
  · constructor
    simp only [familySampleLeafLaw_apply_good ms u x ω hω,mem_univ,ite_true]
    simp_rw [div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right,tsum_familyLeafMass, ENNReal.mul_inv_cancel hω.1.ne' hω.2.ne]
  · simp only [familySampleLeafLaw,ite_eq_right hω]
    infer_instance

lemma familySampleLeafLaw_singleton {E : Type} [MeasurableSpace E] [Add E]
    (ms : List ℝ) (u : E → ℝ) (x : E) (ω : FamilyCascadeTree E ms.length)
    (hω : 0 < familyLeafTotal ms u x ω ∧ familyLeafTotal ms u x ω < ∞)
    (ℓ : CascadePath ms.length) :
    familySampleLeafLaw ms u x ω {ℓ} = familyLeafMass ms u x ω ℓ / familyLeafTotal ms u x ω := by
  simp [familySampleLeafLaw_apply_good ms u x ω hω]

lemma markedPatternIndex_card {E : Type} (k : ℕ) (b : MarkedReplicaPattern E k) :
    Fintype.card (MarkedPatternIndex k b) = replicaPatternSize k (markedReplicaShape k b) := by
  induction k with
  | zero => exact Fintype.card_fin _
  | succ k ih =>
    change List (MarkedReplicaPattern E k) at b
    change Fintype.card ((i : Fin b.length) × MarkedPatternIndex k (b.get i)) = _
    rw [Fintype.card_sigma]
    simp only [ih,markedReplicaShape,replicaPatternSize,List.map_map,Function.comp_def]
    exact (Fin.sum_ofFn (fun i : Fin b.length => replicaPatternSize k (markedReplicaShape k (b.get i)))).symm.trans
      (congrArg List.sum (List.ofFn_getElem_eq_map b
        (fun x => replicaPatternSize k (markedReplicaShape k x))))

end MicroscopicJamming

namespace MicroscopicJamming
lemma measurable_familyLeafMass {E : Type} [MeasurableSpace E] [Add E] [MeasurableAdd₂ E]
    (ms : List ℝ) {u : E → ℝ} (hu : Measurable u) (ℓ : CascadePath ms.length) :
    Measurable (fun z : E × FamilyCascadeTree E ms.length => familyLeafMass ms u z.1 z.2 ℓ) :=
  ((measurable_familyPathWeight ms ℓ).comp measurable_snd).mul
    ((hu.comp (measurable_familyPathMark ms.length ℓ)).exp.ennreal_ofReal)

lemma measurable_familySampleLeafLaw_singleton {E : Type} [MeasurableSpace E]
    [Add E] [MeasurableAdd₂ E] (ms : List ℝ) {u : E → ℝ} (hu : Measurable u)
    (ℓ : CascadePath ms.length) :
    Measurable (fun z : E × FamilyCascadeTree E ms.length => familySampleLeafLaw ms u z.1 z.2 {ℓ}) := by
  have hF := measurable_familyLeafTotal ms hu
  have hg : MeasurableSet {z : E × FamilyCascadeTree E ms.length |
      0 < familyLeafTotal ms u z.1 z.2 ∧ familyLeafTotal ms u z.1 z.2 < ∞} :=
    (measurableSet_lt measurable_const hF).inter (measurableSet_lt hF measurable_const)
  have he : (fun z : E × FamilyCascadeTree E ms.length => familySampleLeafLaw ms u z.1 z.2 {ℓ}) =
      (fun z => if 0 < familyLeafTotal ms u z.1 z.2 ∧ familyLeafTotal ms u z.1 z.2 < ∞ then
        familyLeafMass ms u z.1 z.2 ℓ / familyLeafTotal ms u z.1 z.2
        else Measure.dirac (cascadeZeroPath ms.length) {ℓ}) := by
    funext z
    split_ifs with hz
    · exact familySampleLeafLaw_singleton ms u z.1 z.2 hz ℓ
    · simp [familySampleLeafLaw,hz]
  rw [he]
  exact ((measurable_familyLeafMass ms hu ℓ).div hF).ite hg measurable_const

lemma measurable_familySampleObservable {E : Type} [MeasurableSpace E]
    [Add E] [MeasurableAdd₂ E] (ms : List ℝ) (b : MarkedReplicaPattern E ms.length)
    (hb : ValidMarkedReplicaPattern ms.length b)
    (ℓ : MarkedPatternIndex ms.length b → CascadePath ms.length) :
    Measurable (fun z : E × FamilyCascadeTree E ms.length => familySampleObservable ms b z.1 z.2 ℓ) := by
  induction ms with
  | nil => exact hb.2.1.comp measurable_fst
  | cons m ms ih =>
    change List (MarkedReplicaPattern E ms.length) at b
    change b ≠ [] ∧ ∀ b' ∈ b, ValidMarkedReplicaPattern ms.length b' at hb
    change Measurable (fun z : E × FamilyCascadeTree E (m::ms).length =>
      ∑' a : {a : Fin b.length → CloudLabel // Function.Injective a}, ∏ i : Fin b.length,
        if ∀ j : MarkedPatternIndex ms.length (b.get i), (ℓ ⟨i,j⟩).1 = a.1 i then
          familySampleObservable ms (b.get i) (z.1+(cloudLabelPoint z.2 (a.1 i)).2.1)
            (cloudLabelPoint z.2 (a.1 i)).2.2 (fun j => (ℓ ⟨i,j⟩).2) else 0)
    apply Measurable.tsum
    intro a
    apply Finset.measurable_prod
    intro i _
    by_cases ha : ∀ j : MarkedPatternIndex ms.length (b.get i), (ℓ ⟨i,j⟩).1 = a.1 i
    · simp only [ite_eq_left ha]
      exact (ih (b.get i) (hb.2 _ (b.get_mem i)) (fun j => (ℓ ⟨i,j⟩).2)).comp
        (show Measurable (fun z : E × FamilyCascadeTree E (m::ms).length =>
          (z.1+(cloudLabelPoint z.2 (a.1 i)).2.1,(cloudLabelPoint z.2 (a.1 i)).2.2)) by
            dsimp only [cloudLabelPoint]; fun_prop)
    · simp only [ite_eq_right ha]; exact measurable_const

lemma measurable_familySampleMean {E : Type} [MeasurableSpace E]
    [Add E] [MeasurableAdd₂ E] (ms : List ℝ) {u : E → ℝ} (hu : Measurable u)
    (b : MarkedReplicaPattern E ms.length) (hb : ValidMarkedReplicaPattern ms.length b) :
    Measurable (fun z : E × FamilyCascadeTree E ms.length => familySampleMean ms b u z.1 z.2) := by
  have he : (fun z : E × FamilyCascadeTree E ms.length => familySampleMean ms b u z.1 z.2) =
      fun z => ∑' ℓ : MarkedPatternIndex ms.length b → CascadePath ms.length,
        familySampleObservable ms b z.1 z.2 ℓ * ∏ i, familySampleLeafLaw ms u z.1 z.2 {ℓ i} := by
    funext z
    let := familySampleLeafLaw_probability ms u z.1 z.2
    simp only [familySampleMean,lintegral_countable',Measure.pi_singleton]
  rw [he]
  apply Measurable.tsum
  intro ℓ
  exact (measurable_familySampleObservable ms b hb ℓ).mul
    (Finset.measurable_prod _ (fun i _ => measurable_familySampleLeafLaw_singleton ms hu (ℓ i)))

lemma familySampleLeafLaw_child_density {E : Type} [MeasurableSpace E] [Add E]
    (ms : List ℝ) (m : ℝ) (u : E → ℝ) (x : E)
    (ω : FamilyCascadeTree E (m::ms).length) (i : CloudLabel)
    (hω : 0 < familyLeafTotal (m::ms) u x ω ∧ familyLeafTotal (m::ms) u x ω < ∞)
    (hc : 0 < familyLeafTotal ms u (x+(cloudLabelPoint ω i).2.1) (cloudLabelPoint ω i).2.2 ∧
      familyLeafTotal ms u (x+(cloudLabelPoint ω i).2.1) (cloudLabelPoint ω i).2.2 < ∞)
    (ℓ : CascadePath ms.length) :
    familySampleLeafLaw (m::ms) u x ω {(i,ℓ)} =
      (if i.2 < (ω i.1).1 then ENNReal.ofReal ((cloudLabelPoint ω i).1^(-1/m)) *
        familyLeafTotal ms u (x+(cloudLabelPoint ω i).2.1) (cloudLabelPoint ω i).2.2 /
        familyLeafTotal (m::ms) u x ω else 0) *
      familySampleLeafLaw ms u (x+(cloudLabelPoint ω i).2.1) (cloudLabelPoint ω i).2.2 {ℓ} := by
  erw [familySampleLeafLaw_singleton _ _ _ _ hω,familySampleLeafLaw_singleton _ _ _ _ hc,
    familyLeafMass_cons]
  by_cases hi : i.2 < (ω i.1).1
  · simp only [hi,ite_true,div_eq_mul_inv]
    have hAlg (A B C T : ℝ≥0∞) (hT : T ≠ 0) (hT' : T ≠ ∞) :
        A*B*C = (A*T*C)*(B*T⁻¹) := by
      rw [show (A*T*C)*(B*T⁻¹) = (A*B*C)*(T*T⁻¹) by ac_rfl,
        ENNReal.mul_inv_cancel hT hT',mul_one]
    exact hAlg _ _ _ _ hc.1.ne' hc.2.ne
  · simp [hi]
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

lemma familySampleMean_cons {E : Type} [MeasurableSpace E] [MeasurableEq E]
    [Add E] [MeasurableAdd₂ E] (ms : List ℝ) (m : ℝ)
    (u : E → ℝ) (x : E)
    (bs : List (MarkedReplicaPattern E ms.length)) (hb : ValidMarkedReplicaPattern (m::ms).length bs)
    (ω : FamilyCascadeTree E (m::ms).length)
    (hω : 0 < familyLeafTotal (m::ms) u x ω ∧ familyLeafTotal (m::ms) u x ω < ∞)
    (hc : ∀ i : CloudLabel,
      0 < familyLeafTotal ms u (x+(cloudLabelPoint ω i).2.1) (cloudLabelPoint ω i).2.2 ∧
      familyLeafTotal ms u (x+(cloudLabelPoint ω i).2.1) (cloudLabelPoint ω i).2.2 < ∞)
    (hinj : Function.Injective (cloudLabelPoint ω))
    (hp : ∀ (i : CloudLabel) (b : MarkedReplicaPattern E ms.length), b ∈ bs →
      familySampleMean ms b u (x+(cloudLabelPoint ω i).2.1) (cloudLabelPoint ω i).2.2 =
        familyReplicaWeight ms b u (x+(cloudLabelPoint ω i).2.1) (cloudLabelPoint ω i).2.2) :
    familySampleMean (m::ms) bs u x ω = familyReplicaWeight (m::ms) bs u x ω := by
  change List (MarkedReplicaPattern E ms.length) at bs
  change bs ≠ [] ∧ ∀ b ∈ bs, ValidMarkedReplicaPattern ms.length b at hb
  let J (i : Fin bs.length) := MarkedPatternIndex ms.length (bs.get i)
  let μ := familySampleLeafLaw (m::ms) u x ω
  let : IsProbabilityMeasure μ := familySampleLeafLaw_probability _ _ _ _
  have hgroup := pi_grouping J μ
  have hi (a : {a : Fin bs.length → CloudLabel // Function.Injective a}) :
      (∫⁻ ℓ : ((i : Fin bs.length) × J i) → CascadePath (m::ms).length,
        ∏ i : Fin bs.length, if ∀ j : J i, (ℓ ⟨i,j⟩).1 = a.1 i then
          familySampleObservable ms (bs.get i) (x+(cloudLabelPoint ω (a.1 i)).2.1)
            (cloudLabelPoint ω (a.1 i)).2.2 (fun j => (ℓ ⟨i,j⟩).2) else 0 ∂Measure.pi (fun _ => μ)) =
        ∏ i : Fin bs.length, ∫⁻ ℓ : J i → CascadePath (m::ms).length,
          if ∀ j : J i, (ℓ j).1 = a.1 i then
            familySampleObservable ms (bs.get i) (x+(cloudLabelPoint ω (a.1 i)).2.1)
              (cloudLabelPoint ω (a.1 i)).2.2 (fun j => (ℓ j).2) else 0 ∂Measure.pi (fun _ => μ) := by
    let F (i : Fin bs.length) (ℓ : J i → CascadePath (m::ms).length) : ℝ≥0∞ :=
      if ∀ j : J i, (ℓ j).1 = a.1 i then
        familySampleObservable ms (bs.get i) (x+(cloudLabelPoint ω (a.1 i)).2.1)
          (cloudLabelPoint ω (a.1 i)).2.2 (fun j => (ℓ j).2) else 0
    change (∫⁻ ℓ : ((i : Fin bs.length) × J i) → CascadePath (m::ms).length, (fun ys => ∏ i, F i (ys i)) (fun i j => ℓ ⟨i,j⟩) ∂Measure.pi (fun _ => μ)) = _
    rw [←lintegral_map
      (f := fun ys : (i : Fin bs.length) → J i → CascadePath (m::ms).length => ∏ i, F i (ys i))
      (g := fun ℓ : ((i : Fin bs.length) × J i) → CascadePath (m::ms).length => fun i j => ℓ ⟨i,j⟩)
      (measurable_of_countable _) (measurable_of_countable _),hgroup]
    exact lintegral_pi_prod_countable _ F
  have hsplit : familySampleMean (m::ms) bs u x ω =
      ∑' a : {a : Fin bs.length → CloudLabel // Function.Injective a},
        ∏ i : Fin bs.length, ∫⁻ ℓ : J i → CascadePath (m::ms).length,
          if ∀ j : J i, (ℓ j).1 = a.1 i then
            familySampleObservable ms (bs.get i) (x+(cloudLabelPoint ω (a.1 i)).2.1)
              (cloudLabelPoint ω (a.1 i)).2.2 (fun j => (ℓ j).2) else 0 ∂Measure.pi (fun _ => μ) := by
    change (∫⁻ ℓ : ((i : Fin bs.length) × J i) → CascadePath (m::ms).length,
      ∑' a : {a : Fin bs.length → CloudLabel // Function.Injective a},
        ∏ i : Fin bs.length, if ∀ j : J i, (ℓ ⟨i,j⟩).1 = a.1 i then
          familySampleObservable ms (bs.get i) (x+(cloudLabelPoint ω (a.1 i)).2.1)
            (cloudLabelPoint ω (a.1 i)).2.2 (fun j => (ℓ ⟨i,j⟩).2) else 0 ∂Measure.pi (fun _ => μ)) = _
    rw [lintegral_tsum (fun _ => (measurable_of_countable _).aemeasurable)]
    exact tsum_congr hi
  rw [hsplit]
  have hblock (a : CloudLabel) (i : Fin bs.length) :
      (∫⁻ ℓ : J i → CascadePath (m::ms).length,
        if ∀ j : J i, (ℓ j).1 = a then
          familySampleObservable ms (bs.get i) (x+(cloudLabelPoint ω a).2.1)
            (cloudLabelPoint ω a).2.2 (fun j => (ℓ j).2) else 0 ∂Measure.pi (fun _ => μ)) =
      (familyLeafTotal (m::ms) u x ω)⁻¹ ^ replicaPatternSize ms.length (markedReplicaShape ms.length (bs.get i)) *
        (if a.2 < (ω a.1).1 then
          (ENNReal.ofReal ((cloudLabelPoint ω a).1^(-1/m)) *
            familyLeafTotal ms u (x+(cloudLabelPoint ω a).2.1) (cloudLabelPoint ω a).2.2)^
              replicaPatternSize ms.length (markedReplicaShape ms.length (bs.get i)) *
            familyReplicaWeight ms (bs.get i) u (x+(cloudLabelPoint ω a).2.1) (cloudLabelPoint ω a).2.2
        else 0) := by
    let ν := familySampleLeafLaw ms u (x+(cloudLabelPoint ω a).2.1) (cloudLabelPoint ω a).2.2
    let : IsProbabilityMeasure ν := familySampleLeafLaw_probability _ _ _ _
    have H := lintegral_pi_fixed_root (I := J i) (P := CascadePath (m::ms).length)
      (show CascadePath (m::ms).length ≃ CloudLabel × CascadePath ms.length from Equiv.refl _) μ ν
      (if a.2 < (ω a.1).1 then ENNReal.ofReal ((cloudLabelPoint ω a).1^(-1/m)) *
        familyLeafTotal ms u (x+(cloudLabelPoint ω a).2.1) (cloudLabelPoint ω a).2.2 /
        familyLeafTotal (m::ms) u x ω else 0) a
      (familySampleLeafLaw_child_density ms m u x ω a hω (hc a))
      (familySampleObservable ms (bs.get i) (x+(cloudLabelPoint ω a).2.1) (cloudLabelPoint ω a).2.2)
    change _ = _ * familySampleMean ms (bs.get i) u (x+(cloudLabelPoint ω a).2.1) (cloudLabelPoint ω a).2.2 at H
    simp only at H
    refine H.trans ?_
    rw [hp a _ (bs.get_mem i)]
    have hcard : Fintype.card (J i) = replicaPatternSize ms.length (markedReplicaShape ms.length (bs.get i)) :=
      markedPatternIndex_card _ _
    rw [hcard]
    by_cases ha : a.2 < (ω a.1).1
    · simp only [ite_eq_left ha, div_eq_mul_inv, mul_pow]
      exact (_root_.mul_assoc _ _ _).trans (_root_.mul_left_comm _ _ _)
    · simp only [ite_eq_right ha, zero_pow (ne_of_gt (replicaPatternSize_pos _ _
        (validMarked_shape _ _ (hb.2 _ (bs.get_mem i))))),zero_mul,mul_zero]
  refine Eq.trans (tsum_congr (fun a => Finset.prod_congr rfl (fun i _ => hblock (a.1 i) i))) ?_
  simp_rw [Finset.prod_mul_distrib]
  have hsum : (∑ i : Fin bs.length, replicaPatternSize ms.length (markedReplicaShape ms.length (bs.get i))) =
      replicaPatternSize (ms.length+1) (markedReplicaShape (ms.length+1) bs) := by
    simp only [markedReplicaShape,replicaPatternSize,List.map_map,Function.comp_def]
    exact (Fin.sum_ofFn (fun i : Fin bs.length => replicaPatternSize ms.length (markedReplicaShape ms.length (bs.get i)))).symm.trans
      (congrArg List.sum (List.ofFn_getElem_eq_map bs
        (fun x => replicaPatternSize ms.length (markedReplicaShape ms.length x))))
  rw [Finset.prod_pow_eq_pow_sum, hsum, ENNReal.tsum_mul_left]
  let fs := bs.map (fun b (z : ℝ × (E × FamilyCascadeTree E ms.length)) =>
    (ENNReal.ofReal (z.1^(-1/m))*familyLeafTotal ms u (x+z.2.1) z.2.2)^
      replicaPatternSize ms.length (markedReplicaShape ms.length b) *
      familyReplicaWeight ms b u (x+z.2.1) z.2.2)
  have he := labelCloudIntegral_points ω hinj fs []
  simp only [List.map_nil] at he
  have he' := labelCloudIntegral_map ω bs (fun b a =>
    (ENNReal.ofReal ((cloudLabelPoint ω a).1^(-1/m))*
      familyLeafTotal ms u (x+(cloudLabelPoint ω a).2.1) (cloudLabelPoint ω a).2.2)^
        replicaPatternSize ms.length (markedReplicaShape ms.length b) *
      familyReplicaWeight ms b u (x+(cloudLabelPoint ω a).2.1) (cloudLabelPoint ω a).2.2)
  change _ = ENNReal.ofReal ((familyLeafTotal (m::ms) u x ω).toReal ^
      (-(replicaPatternSize (ms.length+1) (markedReplicaShape (ms.length+1) bs) : ℝ))) *
    distinctCloudIntegral fs (pointCloudMeasure ω) []
  rw [ofReal_toReal_neg_nat _ hω,←he]
  congr 1
  simpa only [fs,List.map_map,Function.comp_def] using he'.symm
end MicroscopicJamming

namespace MicroscopicJamming
lemma familySampleMean_eq_ae {E : Type} [MeasurableSpace E] [MeasurableEq E]
    [Add E] [MeasurableAdd₂ E]
    (ms : List ℝ) (hms : ms.Pairwise (· < ·)) (h01 : ∀ m ∈ ms, 0 < m ∧ m < 1)
    (ν : ℕ → Measure E) (hν : ∀ j, IsProbabilityMeasure (ν j))
    {u : E → ℝ} (hu : Measurable u) (hi : FamilyMomentsFinite ms ν u)
    (b : MarkedReplicaPattern E ms.length) (hb : ValidMarkedReplicaPattern ms.length b) (x : E) :
    familySampleMean ms b u x =ᵐ[familyCascadeLaw ms.length ν] familyReplicaWeight ms b u x := by
  induction ms generalizing ν x with
  | nil =>
    exact Eventually.of_forall fun ω => by
      let := familySampleLeafLaw_probability [] u x ω
      simp [familySampleMean,familySampleObservable,familyReplicaWeight]
  | cons m ms ih =>
    have hs := List.pairwise_cons.mp hms
    have h01t : ∀ a ∈ ms, 0 < a ∧ a < 1 := fun a ha => h01 a (by simp [ha])
    change List (MarkedReplicaPattern E ms.length) at b
    change b ≠ [] ∧ ∀ b' ∈ b, ValidMarkedReplicaPattern ms.length b' at hb
    let τ := familyCascadeLaw ms.length (fun j => ν (j+1))
    let := hν 0
    let : IsProbabilityMeasure τ := familyCascadeLaw_probability ms.length (fun j => ν (j+1)) (fun j => hν (j+1))
    have hp (c : MarkedReplicaPattern E ms.length) (hc : c ∈ b) :
        ∀ᵐ z ∂(ν 0).prod τ,
          familySampleMean ms c u (x+z.1) z.2 = familyReplicaWeight ms c u (x+z.1) z.2 := by
      have hhmap : Measurable (fun z : E × FamilyCascadeTree E ms.length => (x+z.1,z.2)) := by fun_prop
      apply (Measure.ae_prod_iff_ae_ae
        (measurableSet_eq_fun ((measurable_familySampleMean ms hu c (hb.2 c hc)).comp hhmap)
          ((measurable_familyReplicaWeight ms hu c (hb.2 c hc)).comp hhmap))).mpr
      exact Eventually.of_forall fun a => ih hs.2 h01t (fun j => ν (j+1)) (fun j => hν (j+1)) hi.2 c (hb.2 c hc) (x+a)
    have hpa : ∀ᵐ ω ∂pointCloudLaw ((ν 0).prod τ), ∀ c ∈ b, ∀ i : CloudLabel,
        familySampleMean ms c u (x+(cloudLabelPoint ω i).2.1) (cloudLabelPoint ω i).2.2 =
          familyReplicaWeight ms c u (x+(cloudLabelPoint ω i).2.1) (cloudLabelPoint ω i).2.2 := by
      apply (ae_ball_iff (show Set.Countable {c | c ∈ b} from by simpa using b.toFinset.finite_toSet.countable)).mpr
      intro c hc
      exact (ae_pointCloud_marks ((ν 0).prod τ) (hp c hc)).mono fun ω hω i => hω i.1 i.2
    have hct := ae_pointCloud_marks ((ν 0).prod τ)
      (familyChildTotal_positive_ae ms hs.2 h01t ν hν hu hi.2 x)
    filter_upwards [familyLeafTotal_positive_ae (m::ms) hms h01 ν hν hu hi x,
      hct,cloudLabelPoint_injective_ae ((ν 0).prod τ),hpa] with ω hω hc hinj hp
    exact familySampleMean_cons ms m u x b hb ω hω (fun i => hc i.1 i.2) hinj
      (fun i c hc => hp c hc i)

theorem familySample : FamilySampleStatement := by
  intro E _ _ _ _ ms hms h01 ν hν u hu hi
  refine ⟨fun x ω => familySampleLeafLaw_probability _ _ _ _, ?_⟩
  intro b hb η hη hηms x
  have he := familySampleMean_eq_ae ms hms h01 ν hν hu hi b hb x
  rw [lintegral_congr_ae (he.mono (fun ω hω => congrArg
    (fun z => ENNReal.ofReal ((familyLeafTotal ms u x ω).toReal^η)*z) hω))]
  exact familyReplica E inferInstance inferInstance inferInstance inferInstance
    ms hms h01 ν hν u hu hi b hb η hη hηms x
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace MicroscopicJamming

 

def RowExpGrowth (v : ℝ → ℝ) : Prop :=
  ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧ ∀ x, |v x| ≤ K*Real.exp (L*|x|)

lemma gaussian_exp_abs_integrable (L : ℝ) :
    Integrable (fun x : ℝ => Real.exp (L*|x|)) (gaussianReal 0 1) := by
  apply ((integrable_exp_mul_gaussianReal L).add (integrable_exp_mul_gaussianReal (-L))).mono'
    (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_neg (lt_of_not_ge hx)]
    have he : L*(-x)=(-L)*x := by ring
    rw [he]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

lemma RowExpGrowth.integrable_affine {v : ℝ → ℝ} (hg : RowExpGrowth v)
    (hv : Measurable v) (a b : ℝ) :
    Integrable (fun z => v (a+b*z)) (gaussianReal 0 1) := by
  obtain ⟨K,L,hK,hL,hg⟩ := hg
  apply ((gaussian_exp_abs_integrable (L*|b|)).const_mul (K*Real.exp (L*|a|))).mono'
    (hv.comp (by fun_prop)).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs]
  calc
    _ ≤ K*Real.exp (L*|a+b*z|) := hg _
    _ ≤ K*Real.exp (L*(|a|+|b| * |z|)) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK
      exact mul_le_mul_of_nonneg_left (by simpa only [abs_mul] using abs_add_le a (b*z)) hL
    _ = _ := by rw [mul_add,Real.exp_add]; ring_nf

lemma RowExpGrowth.bounded {v : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hv : ∀ x, |v x| ≤ K) :
    RowExpGrowth v := ⟨K,0,hK,le_rfl,by simpa using hv⟩

lemma RowExpGrowth.mul_bounded {v h : ℝ → ℝ} (hv : RowExpGrowth v)
    {B : ℝ} (hB : 0 ≤ B) (hh : ∀ x, |h x| ≤ B) : RowExpGrowth (fun x => h x*v x) := by
  obtain ⟨K,L,hK,hL,hv⟩ := hv
  refine ⟨B*K,L,mul_nonneg hB hK,hL,fun x => ?_⟩
  rw [abs_mul]
  calc
    _ ≤ B*(K*Real.exp (L*|x|)) := mul_le_mul (hh x) (hv x) (abs_nonneg _) hB
    _ = _ := by ring

lemma bounded_deriv_linear {u : ℝ → ℝ} (hu : Differentiable ℝ u)
    {L : ℝ} (hL : ∀ x, |deriv u x| ≤ L) (x : ℝ) : |u x| ≤ |u 0|+L*|x| := by
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le (f := u) (s := univ)
    (fun y _ => hu y) (fun y _ => by simpa using hL y) convex_univ
    (x := 0) (y := x) (mem_univ _) (mem_univ _)
  simp only [Real.norm_eq_abs,sub_zero] at hh
  have ht := abs_add_le (u x-u 0) (u 0)
  rw [sub_add_cancel] at ht
  linarith

lemma RowExpGrowth.of_bounded_deriv {u : ℝ → ℝ} (hu : Differentiable ℝ u)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ x, |deriv u x| ≤ L) : RowExpGrowth u := by
  refine ⟨|u 0|+L,1,by positivity,by norm_num,fun x => ?_⟩
  have he := Real.add_one_le_exp |x|
  have he1 : 1 ≤ Real.exp |x| := Real.one_le_exp (abs_nonneg x)
  have hu0 := mul_le_mul_of_nonneg_left he1 (abs_nonneg (u 0))
  have hx := mul_le_mul_of_nonneg_left (show |x| ≤ Real.exp |x| by linarith) hL0
  have hb := bounded_deriv_linear hu hL x
  simp only [one_mul]
  nlinarith

lemma RowExpGrowth.exp_bounded_deriv {u : ℝ → ℝ} (hu : Differentiable ℝ u)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ x, |deriv u x| ≤ L) (a : ℝ) :
    RowExpGrowth (fun x => Real.exp (a*u x)) := by
  refine ⟨Real.exp (|a| * |u 0|),|a| * L,(Real.exp_pos _).le,mul_nonneg (abs_nonneg _) hL0,fun x => ?_⟩
  rw [abs_of_pos (Real.exp_pos _),← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have ha : a*u x ≤ |a| * |u x| := by simpa only [abs_mul] using le_abs_self (a*u x)
  have hb := mul_le_mul_of_nonneg_left (bounded_deriv_linear hu hL x) (abs_nonneg a)
  nlinarith only [ha,hb]

lemma rowExpHeat_space_derivative {v v' : ℝ → ℝ}
    (hv : Measurable v) (hv' : Measurable v') (hg : RowExpGrowth v) (hg' : RowExpGrowth v')
    (hdv : ∀ x, HasDerivAt v (v' x) x) (T x : ℝ) :
    HasDerivAt (gaussianHeat v T) (gaussianHeat v' T x) x := by
  obtain ⟨K,L,hK,hL,hg'⟩ := hg'
  let B := K*Real.exp (L*(|x|+1))
  have hs : {y : ℝ | |y| < |x|+1} ∈ 𝓝 x :=
    (continuous_abs.tendsto x).eventually (eventually_lt_nhds (by linarith : |x| < |x|+1))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (s := {y : ℝ | |y| < |x|+1})
    (F := fun y z => v (y+Real.sqrt T*z)) (F' := fun y z => v' (y+Real.sqrt T*z))
    (bound := fun z => B*Real.exp ((L*|Real.sqrt T|)*|z|)) hs
    (Eventually.of_forall fun _ => (hv.comp (by fun_prop)).aestronglyMeasurable)
    (hg.integrable_affine hv x (Real.sqrt T))
    (hv'.comp (by fun_prop)).aestronglyMeasurable ?_
    ((gaussian_exp_abs_integrable _).const_mul B) ?_).2
  · filter_upwards [] with z
    intro y hy
    change |v' (y+Real.sqrt T*z)| ≤ _
    calc
      _ ≤ K*Real.exp (L*|y+Real.sqrt T*z|) := hg' _
      _ ≤ K*Real.exp (L*(|x|+1+|Real.sqrt T| * |z|)) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK
        apply mul_le_mul_of_nonneg_left _ hL
        have htt := abs_add_le y (Real.sqrt T*z)
        rw [abs_mul] at htt
        linarith [hy]
      _ = _ := by dsimp [B]; rw [mul_add,Real.exp_add]; ring_nf
  · filter_upwards [] with z
    intro y hy
    convert (hdv (y+Real.sqrt T*z)).comp y ((hasDerivAt_id y).add_const (Real.sqrt T*z)) using 1
    <;> first | rfl | simp only [mul_one]
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace MicroscopicJamming

lemma measurable_rowTiltStep {f h : ℝ → ℝ} (hf : Measurable f) (hh : Measurable h) (a T : ℝ) :
    Measurable (fun x => rowTiltStep a T f x h) := by
  have ha : Measurable (fun p : ℝ × ℝ => p.1+Real.sqrt T*p.2) := by fun_prop
  exact ((hh.comp ha).mul ((hf.comp ha).const_mul a).exp).stronglyMeasurable.integral_prod_right'.measurable.div
    (((hf.comp ha).const_mul a).exp.stronglyMeasurable.integral_prod_right'.measurable)

lemma rowTiltStep_weight_integrable {f : ℝ → ℝ} {a : ℝ}
    (hf : Measurable f) (hg : RowExpGrowth (fun x => Real.exp (a*f x))) (T x : ℝ) :
    Integrable (fun z => Real.exp (a*f (x+Real.sqrt T*z))) (gaussianReal 0 1) :=
  hg.integrable_affine (hf.const_mul a).exp x (Real.sqrt T)

lemma rowTiltStep_product_integrable {f h : ℝ → ℝ} {a : ℝ}
    (hf : Measurable f) (hg : RowExpGrowth (fun x => Real.exp (a*f x)))
    (hh : Measurable h) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |h x| ≤ B) (T x : ℝ) :
    Integrable (fun z => h (x+Real.sqrt T*z)*Real.exp (a*f (x+Real.sqrt T*z))) (gaussianReal 0 1) :=
  (hg.mul_bounded hB hb).integrable_affine (hh.mul (hf.const_mul a).exp) x (Real.sqrt T)

lemma rowTiltStep_abs_bound {f h : ℝ → ℝ} {a : ℝ}
    (hf : Measurable f) (hg : RowExpGrowth (fun x => Real.exp (a*f x)))
    (hh : Measurable h) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |h x| ≤ B) (T x : ℝ) :
    |rowTiltStep a T f x h| ≤ B := by
  have hw := rowTiltStep_weight_integrable hf hg T x
  have hi := rowTiltStep_product_integrable hf hg hh hB hb T x
  have hZ := integral_exp_pos hw
  rw [rowTiltStep,abs_div,abs_of_pos hZ]
  apply (div_le_iff₀ hZ).mpr
  calc
    _ ≤ ∫ z, |h (x+Real.sqrt T*z)*Real.exp (a*f (x+Real.sqrt T*z))| ∂gaussianReal 0 1 := abs_integral_le_integral_abs
    _ ≤ ∫ z, B*Real.exp (a*f (x+Real.sqrt T*z)) ∂gaussianReal 0 1 := by
      apply integral_mono hi.abs (hw.const_mul B)
      intro z
      dsimp only
      rw [abs_mul,abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (hb _) (Real.exp_pos _).le
    _ = _ := integral_const_mul _ _

lemma rowTiltStep_nonneg {f h : ℝ → ℝ} {a T x : ℝ} (hh : ∀ y, 0 ≤ h y) :
    0 ≤ rowTiltStep a T f x h := by
  apply div_nonneg (integral_nonneg (fun z => mul_nonneg (hh _) (Real.exp_pos _).le))
    (integral_nonneg (fun z => (Real.exp_pos _).le))

lemma rowTiltStep_mono {f h k : ℝ → ℝ} {a : ℝ}
    (hf : Measurable f) (hg : RowExpGrowth (fun x => Real.exp (a*f x)))
    (hh : Measurable h) (hk : Measurable k) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ x, |h x| ≤ B) (hc : ∀ x, |k x| ≤ C) (hle : ∀ x, h x ≤ k x) (T x : ℝ) :
    rowTiltStep a T f x h ≤ rowTiltStep a T f x k := by
  apply div_le_div_of_nonneg_right _ (integral_nonneg (fun z => (Real.exp_pos _).le))
  apply integral_mono (rowTiltStep_product_integrable hf hg hh hB hb T x)
    (rowTiltStep_product_integrable hf hg hk hC hc T x)
  intro z
  exact mul_le_mul_of_nonneg_right (hle _) (Real.exp_pos _).le

lemma rowTiltStep_square_ge {f h : ℝ → ℝ} {a : ℝ}
    (hf : Measurable f) (hg : RowExpGrowth (fun x => Real.exp (a*f x)))
    (hh : Measurable h) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |h x| ≤ B) (T x : ℝ) :
    (rowTiltStep a T f x h)^2 ≤ rowTiltStep a T f x (fun y => (h y)^2) := by
  have hs (y : ℝ) : |(h y)^2| ≤ B^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hb y,sq_abs (h y),abs_nonneg (h y)]
  have hw := rowTiltStep_weight_integrable hf hg T x
  have hZ := integral_exp_pos hw
  have hv := weighted_variance_nonneg (fun z => (Real.exp_pos (a*f (x+Real.sqrt T*z))).le)
    hw (rowTiltStep_product_integrable hf hg hh hB hb T x)
    (rowTiltStep_product_integrable hf hg (hh.pow_const 2) (sq_nonneg B) hs T x) hZ
  unfold rowTiltStep
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos hZ 2)).mpr
  have he : ((∫ z, (h (x+Real.sqrt T*z))^2*Real.exp (a*f (x+Real.sqrt T*z)) ∂gaussianReal 0 1) /
      (∫ z, Real.exp (a*f (x+Real.sqrt T*z)) ∂gaussianReal 0 1)) *
      (∫ z, Real.exp (a*f (x+Real.sqrt T*z)) ∂gaussianReal 0 1)^2 =
      (∫ z, Real.exp (a*f (x+Real.sqrt T*z)) ∂gaussianReal 0 1)*
      (∫ z, (h (x+Real.sqrt T*z))^2*Real.exp (a*f (x+Real.sqrt T*z)) ∂gaussianReal 0 1) := by
    field_simp [hZ.ne']
  rw [he]
  exact hv

lemma rowTiltStep_zero (a : ℝ) (f h : ℝ → ℝ) (x : ℝ) : rowTiltStep a 0 f x h=h x := by
  simp [rowTiltStep,Real.exp_ne_zero]
end MicroscopicJamming

end

end OAI
