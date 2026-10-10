import Mathlib
import OAI.Probability.Ballisticity.Estimates.OrderedTimes
import OAI.Probability.Ballisticity.Estimates.MartingaleExponentialSubmartingale

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

lemma gaussian_independent_sum_range_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ n, Measurable (X n)) (hind : iIndepFun X μ)
    (v : ℕ → ℝ≥0) (hLaw : ∀ n, μ.map (X n) = gaussianReal 0 (v n)) (n : ℕ) :
    μ.map (fun ω => ∑ j ∈ Finset.range n, X j ω) =
      gaussianReal 0 (∑ j ∈ Finset.range n, v j) := by
  induction n with
  | zero => simp [gaussianReal_zero_var]
  | succ n ih =>
    have he : (∑ j ∈ Finset.range n, X j) = (fun ω => ∑ j ∈ Finset.range n, X j ω) := by
      funext ω
      simp
    have hi' : μ.map (∑ j ∈ Finset.range n, X j) =
        gaussianReal 0 (∑ j ∈ Finset.range n, v j) := by rw [he]; exact ih
    have hh := gaussianReal_add_gaussianReal_of_indepFun
      (hind.indepFun_finsetSum_of_notMem hXm (Finset.notMem_range_self (n := n)))
      ⟨by rw [he]; fun_prop, hi'⟩ ⟨(hXm n).aemeasurable, hLaw n⟩
    rw [he] at hh
    convert hh using 1
    · congr 1
      funext ω
      simp [Finset.sum_range_succ]
    · simp only [zero_add, Finset.sum_range_succ]

lemma gaussian_martingale_maximal_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ ‹MeasurableSpace Ω›)
    (X : ℕ → Ω → ℝ) (hX : Martingale X F μ) (v : ℕ → ℝ≥0)
    (hLaw : ∀ n, μ.map (X n) = gaussianReal 0 (v n))
    (n : ℕ) (V : ℝ) (hV : 0 < V) (hv : (v n : ℝ) ≤ V) (a : ℝ) (ha : 0 < a) :
    μ.real {ω | ∃ k ≤ n, a ≤ X k ω} ≤ Real.exp (-a^2/(2*V)) := by
  let c := a/V
  have hc : 0 < c := div_pos ha hV
  have hXm (j : ℕ) : Measurable (X j) := (hX.stronglyMeasurable j).measurable.mono (F.le j) le_rfl
  have hi (j : ℕ) : Integrable (fun ω => Real.exp (c*X j ω)) μ := by
    have hh : Integrable (fun z : ℝ => Real.exp (c*z)) (μ.map (X j)) := by
      rw [hLaw j]
      exact integrable_exp_mul_gaussianReal c
    exact (integrable_map_measure (by fun_prop) (hXm j).aemeasurable).mp hh
  have hh := martingale_exponential_maximal μ F (c • X) (hX.smul c) hi n (c*a)
  have hs : {ω | ∃ k ≤ n, c*a ≤ (c • X) k ω} = {ω | ∃ k ≤ n, a ≤ X k ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, mul_le_mul_iff_right₀ hc]
  rw [hs] at hh
  have he : (∫ ω, Real.exp ((c • X) n ω) ∂μ) = Real.exp ((v n:ℝ)*c^2/2) := by
    simpa only [mgf, Pi.smul_apply, smul_eq_mul, zero_mul, zero_add] using
      mgf_gaussianReal ⟨(hXm n).aemeasurable, hLaw n⟩ c
  rw [he, ← Real.exp_add] at hh
  refine hh.trans (Real.exp_le_exp.mpr ?_)
  calc
    -(c*a) + (v n:ℝ)*c^2/2 ≤ -(c*a) + V*c^2/2 := by gcongr
    _ = -a^2/(2*V) := by dsimp [c]; field_simp; ring

lemma gaussian_martingale_abs_maximal_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℕ ‹MeasurableSpace Ω›)
    (X : ℕ → Ω → ℝ) (hX : Martingale X F μ) (v : ℕ → ℝ≥0)
    (hLaw : ∀ n, μ.map (X n) = gaussianReal 0 (v n))
    (n : ℕ) (V : ℝ) (hV : 0 < V) (hv : (v n : ℝ) ≤ V) (a : ℝ) (ha : 0 < a) :
    μ.real {ω | ∃ k ≤ n, a ≤ |X k ω|} ≤ 2*Real.exp (-a^2/(2*V)) := by
  have hneg (j : ℕ) : μ.map ((-X) j) = gaussianReal 0 (v j) := by
    have hm : AEMeasurable (X j) μ :=
      ((hX.stronglyMeasurable j).measurable.mono (F.le j) le_rfl).aemeasurable
    simpa only [neg_zero, Pi.neg_apply] using
      (gaussianReal_neg (show HasLaw (X j) (gaussianReal 0 (v j)) μ from ⟨hm,hLaw j⟩)).map_eq
  have hp := gaussian_martingale_maximal_le μ F X hX v hLaw n V hV hv a ha
  have hn := gaussian_martingale_maximal_le μ F (-X) hX.neg v hneg n V hV hv a ha
  have hs : {ω | ∃ k ≤ n, a ≤ |X k ω|} =
      {ω | ∃ k ≤ n, a ≤ X k ω} ∪ {ω | ∃ k ≤ n, a ≤ (-X) k ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs, Pi.neg_apply]
    aesop
  rw [hs]
  exact (measureReal_union_le _ _).trans (by simpa only [two_mul] using add_le_add hp hn)

lemma fin_sum_Iic_eq_range {M : Type*} [AddCommMonoid M] {n : ℕ}
    (x : ℕ → M) (k : Fin n) :
    (∑ j ≤ k, x j) = ∑ j ∈ Finset.range (k+1), x j := by
  apply Finset.sum_bij (fun j _ => j.val)
  · intro j hj
    simp only [Finset.mem_Iic] at hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  · intro j hj j' hj' he
    exact Fin.ext he
  · intro j hj
    have hjk : j ≤ k.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact ⟨⟨j, hjk.trans_lt k.isLt⟩, Finset.mem_Iic.mpr hjk, rfl⟩
  · intros; rfl

lemma gaussian_pi_prefix_maximal {n : ℕ} (v : Fin n → ℝ≥0)
    (V : ℝ) (hV : 0 < V) (hv : (∑ j, (v j : ℝ)) ≤ V) (a : ℝ) (ha : 0 < a) :
    (Measure.pi (fun j => gaussianReal 0 (v j))).real
      {x | ∃ k : Fin n, a ≤ |∑ j ≤ k, x j|} ≤ 2*Real.exp (-a^2/(2*V)) := by
  let w : ℕ → ℝ≥0 := fun j => if hj : j < n then v ⟨j,hj⟩ else 0
  let μ := Measure.infinitePi (fun j => gaussianReal 0 (w j))
  let X : ℕ → (ℕ → ℝ) → ℝ := fun j x => x j
  have hXm (j : ℕ) : Measurable (X j) := measurable_pi_apply j
  have hLaw (j : ℕ) : μ.map (X j) = gaussianReal 0 (w j) :=
    Measure.infinitePi_map_eval _ j
  have hHasLaw (j : ℕ) : HasLaw (X j) (gaussianReal 0 (w j)) μ :=
    ⟨(hXm j).aemeasurable, hLaw j⟩
  have hi (j : ℕ) : Integrable (X j) μ := (hHasLaw j).hasGaussianLaw.integrable
  have hmean (j : ℕ) : ∫ x, X j x ∂μ = 0 := by
    rw [(hHasLaw j).integral_eq]
    exact integral_id_gaussianReal
  have hind : iIndepFun X μ := iIndepFun_infinitePi (X := fun _ x => x) (by fun_prop)
  have hM := independent_centered_sum_martingale μ X hXm hi hind hmean
  have hsum (j : ℕ) := gaussian_independent_sum_range_law μ X hXm hind w hLaw (j+1)
  have htotal : ((∑ j ∈ Finset.range (n+1), w j : ℝ≥0) : ℝ) ≤ V := by
    rw [Finset.sum_range_succ]
    have hw : w n = 0 := by simp [w]
    rw [hw, add_zero]
    have hs : ∑ j ∈ Finset.range n, w j = ∑ j, v j := by
      symm
      exact Finset.sum_fin_eq_sum_range _
    rw [hs]
    simpa only [NNReal.coe_sum] using hv
  have hh := gaussian_martingale_abs_maximal_le μ _ _ hM
    (fun j => ∑ k ∈ Finset.range (j+1), w k) hsum n V hV htotal a ha
  let π : (ℕ → ℝ) → (Fin n → ℝ) := fun x j => x j
  have hm : μ.map π = Measure.pi (fun j => gaussianReal 0 (v j)) := by
    have hh := Measure.map_infinitePi_infinitePi_of_inj
      (P := fun j => gaussianReal 0 (w j)) (f := fun j : Fin n => j.val) Fin.val_injective
    rw [Measure.infinitePi_eq_pi (fun j : Fin n => gaussianReal 0 (w j))] at hh
    simpa only [w, dite_eq_left (Fin.isLt _)] using hh
  rw [← hm, measureReal_def, Measure.map_apply (by fun_prop)
    (by measurability)]
  apply le_trans (measureReal_mono (show π ⁻¹' {x | ∃ k : Fin n, a ≤ |∑ j ≤ k, x j|} ⊆
    {x | ∃ k ≤ n, a ≤ |∑ j ∈ Finset.range (k+1), X j x|} from ?_)) hh
  rintro x ⟨k,hk⟩
  refine ⟨k,k.isLt.le,?_⟩
  simpa only [π, X, fin_sum_Iic_eq_range] using hk

lemma gaussianPathFiniteLaw_abs_maximal (V : ℝ) (hV : 0 < V)
    (I : Finset unitInterval) (a : ℝ) (ha : 0 < a) :
    (gaussianPathFiniteLaw V I).real {x | ∃ i : I, a ≤ |x i|} ≤
      2*Real.exp (-a^2/(2*V)) := by
  let v : Fin I.card → ℝ≥0 := fun j =>
    Real.toNNReal (V*((orderedTimes I j.succ : ℝ)-orderedTimes I j.castSucc))
  have hv : (∑ j, (v j : ℝ)) ≤ V := by
    have hn (j : Fin I.card) : 0 ≤ V*((orderedTimes I j.succ : ℝ)-orderedTimes I j.castSucc) :=
      mul_nonneg hV.le (sub_nonneg.mpr (orderedTimes_monotone I (Fin.castSucc_le_succ j)))
    simp only [v, Real.coe_toNNReal _ (hn _)]
    by_cases hI : I.card = 0
    · have he : I = ∅ := Finset.card_eq_zero.mp hI
      subst I
      have : IsEmpty (Fin ((∅ : Finset unitInterval).card)) := by
        change IsEmpty (Fin 0)
        infer_instance
      rw [Finset.univ_eq_empty, Finset.sum_empty]
      exact hV.le
    · let k : Fin I.card := ⟨I.card-1, by omega⟩
      have hk : Finset.Iic k = Finset.univ := by
        ext j
        simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
        change j.val ≤ I.card-1
        have := j.isLt
        omega
      rw [← Finset.mul_sum, ← hk, Fin.sum_Iic_sub k (fun j => (orderedTimes I j : ℝ))]
      have hz : (orderedTimes I 0 : ℝ) = 0 := by simp [orderedTimes]
      rw [hz, sub_zero]
      exact (mul_le_mul_of_nonneg_left (orderedTimes I k.succ).2.2 hV.le).trans_eq (mul_one V)
  have hh := gaussian_pi_prefix_maximal v V hV hv a ha
  unfold gaussianPathFiniteLaw
  rw [measureReal_def, Measure.map_apply (by fun_prop)
    (show MeasurableSet {x : I → ℝ | ∃ i : I, a ≤ |x i|} from by
      simp only [Set.ofPred_exists]
      exact MeasurableSet.iUnion fun i => measurableSet_le measurable_const (measurable_pi_apply i).abs)]
  apply le_trans (measureReal_mono (show (incrementCumsum I) ⁻¹' {x | ∃ i : I, a ≤ |x i|} ⊆
      {x | ∃ k : Fin I.card, a ≤ |∑ j ≤ k, x j|} from ?_)) hh
  rintro x ⟨i,hi⟩
  exact ⟨(I.orderIsoOfFin rfl).symm i, hi⟩

lemma wiener_path_finite_abs_maximal (W : ProbabilityMeasure C(unitInterval,ℝ))
    (V : ℝ) (hV : 0 < V)
    (hW : ∀ I : Finset unitInterval,
      (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) =
        gaussianPathFiniteLaw V I)
    (I : Finset unitInterval) (a : ℝ) (ha : 0 < a) :
    (W : Measure C(unitInterval,ℝ)).real {g | ∃ t ∈ I, a ≤ |g t|} ≤
      2*Real.exp (-a^2/(2*V)) := by
  have hh := gaussianPathFiniteLaw_abs_maximal V hV I a ha
  rw [← hW I, measureReal_def, Measure.map_apply (continuous_path_restrict I).measurable
    (show MeasurableSet {x : I → ℝ | ∃ i : I, a ≤ |x i|} from by
      simp only [Set.ofPred_exists]
      exact MeasurableSet.iUnion fun i => measurableSet_le measurable_const (measurable_pi_apply i).abs)] at hh
  have hs : (fun g : C(unitInterval,ℝ) => I.restrict g) ⁻¹' {x | ∃ i : I, a ≤ |x i|} =
      {g | ∃ t ∈ I, a ≤ |g t|} := by
    ext g
    constructor
    · rintro ⟨⟨t,ht⟩,hg⟩
      exact ⟨t,ht,hg⟩
    · rintro ⟨t,ht,hg⟩
      exact ⟨⟨t,ht⟩,hg⟩
  rw [hs] at hh
  exact hh

lemma wiener_path_countable_abs_maximal (W : ProbabilityMeasure C(unitInterval,ℝ))
    (V : ℝ) (hV : 0 < V)
    (hW : ∀ I : Finset unitInterval,
      (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) =
        gaussianPathFiniteLaw V I)
    (t : ℕ → unitInterval) (a : ℝ) (ha : 0 < a) :
    (W : Measure C(unitInterval,ℝ)).real {g | ∃ k, a ≤ |g (t k)|} ≤
      2*Real.exp (-a^2/(2*V)) := by
  let E := fun n => {g : C(unitInterval,ℝ) | ∃ k ∈ Finset.range n, a ≤ |g (t k)|}
  have hm : Monotone E := by
    intro i j hij g
    rintro ⟨k,hk,hka⟩
    exact ⟨k,Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans_le hij),hka⟩
  have hu : {g : C(unitInterval,ℝ) | ∃ k, a ≤ |g (t k)|} = ⋃ n, E n := by
    ext g
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion,E]
    constructor
    · rintro ⟨k,hk⟩; exact ⟨k+1,k,Finset.mem_range.mpr (Nat.lt_succ_self k),hk⟩
    · rintro ⟨n,k,_,hk⟩; exact ⟨k,hk⟩
  have hb n : (W : Measure C(unitInterval,ℝ)) (E n) ≤
      ENNReal.ofReal (2*Real.exp (-a^2/(2*V))) := by
    have hh := wiener_path_finite_abs_maximal W V hV hW ((Finset.range n).image t) a ha
    have he : {g : C(unitInterval,ℝ) | ∃ z ∈ (Finset.range n).image t, a ≤ |g z|} = E n := by
      ext g
      simp only [Set.mem_ofPred_eq,Finset.mem_image,E]
      aesop
    rw [he] at hh
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal hh
  have hbound : (W : Measure C(unitInterval,ℝ)) {g | ∃ k, a ≤ |g (t k)|} ≤
      ENNReal.ofReal (2*Real.exp (-a^2/(2*V))) := by
    rw [hu,hm.measure_iUnion]
    exact iSup_le hb
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  simpa only [measureReal_def,ENNReal.toReal_ofReal
    (by positivity : 0 ≤ 2*Real.exp (-a^2/(2*V)))] using hh

lemma wiener_path_abs_gt_maximal (W : ProbabilityMeasure C(unitInterval,ℝ))
    (V : ℝ) (hV : 0 < V)
    (hW : ∀ I : Finset unitInterval,
      (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) =
        gaussianPathFiniteLaw V I)
    (a : ℝ) (ha : 0 < a) :
    (W : Measure C(unitInterval,ℝ)).real {g | ∃ t, a < |g t|} ≤
      2*Real.exp (-a^2/(2*V)) := by
  let u := TopologicalSpace.denseSeq unitInterval
  have hu : DenseRange u := TopologicalSpace.denseRange_denseSeq _
  have hh := wiener_path_countable_abs_maximal W V hV hW u a ha
  refine (measureReal_mono (show {g : C(unitInterval,ℝ) | ∃ t, a < |g t|} ⊆
      {g | ∃ k, a ≤ |g (u k)|} from ?_)).trans hh
  rintro g ⟨t,hat⟩
  obtain ⟨k,hk⟩ := hu.exists_mem_open (isOpen_lt continuous_const g.continuous.abs) ⟨t,hat⟩
  exact ⟨k,hk.le⟩

lemma wiener_path_abs_maximal (W : ProbabilityMeasure C(unitInterval,ℝ))
    (V : ℝ) (hV : 0 < V)
    (hW : ∀ I : Finset unitInterval,
      (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) =
        gaussianPathFiniteLaw V I)
    (a : ℝ) (ha : 0 < a) :
    (W : Measure C(unitInterval,ℝ)).real {g | ∃ t, a ≤ |g t|} ≤
      2*Real.exp (-a^2/(2*V)) := by
  let b : ℕ → ℝ := fun n => a-a/((n:ℝ)+2)
  have hbpos n : 0 < b n := by
    have hd : a/((n:ℝ)+2) < a := (div_lt_iff₀ (by positivity)).2 (by nlinarith [Nat.cast_nonneg (α:=ℝ) n])
    dsimp [b]; linarith
  have hblt n : b n < a := by dsimp [b]; exact sub_lt_self a (div_pos ha (by positivity))
  have hb : Tendsto b atTop (𝓝 a) := by
    have hd := (tendsto_const_div_atTop_nhds_zero_nat a).comp (tendsto_add_atTop_nat 2)
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_ofNat,sub_zero] using tendsto_const_nhds.sub hd
  have hlim : Tendsto (fun n => 2*Real.exp (-(b n)^2/(2*V))) atTop
      (𝓝 (2*Real.exp (-a^2/(2*V)))) := by
    exact tendsto_const_nhds.mul (Real.continuous_exp.tendsto _ |>.comp ((hb.pow 2).neg.div_const (2*V)))
  apply ge_of_tendsto hlim
  filter_upwards [] with n
  have hh := wiener_path_abs_gt_maximal W V hV hW (b n) (hbpos n)
  refine (measureReal_mono (show {g : C(unitInterval,ℝ) | ∃ t, a ≤ |g t|} ⊆
    {g | ∃ t, b n < |g t|} from ?_)).trans hh
  rintro g ⟨t,hat⟩
  exact ⟨t,(hblt n).trans_le hat⟩

lemma wiener_path_norm_maximal (W : ProbabilityMeasure C(unitInterval,ℝ))
    (V : ℝ) (hV : 0 < V)
    (hW : ∀ I : Finset unitInterval,
      (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) =
        gaussianPathFiniteLaw V I)
    (a : ℝ) (ha : 0 < a) :
    (W : Measure C(unitInterval,ℝ)).real {g | a ≤ ‖g‖} ≤
      2*Real.exp (-a^2/(2*V)) := by
  have hs : {g : C(unitInterval,ℝ) | a ≤ ‖g‖} = {g | ∃ t, a ≤ |g t|} := by
    ext g
    simp only [Set.mem_ofPred_eq, ← not_lt, g.norm_lt_iff ha, Real.norm_eq_abs, not_forall]
  rw [hs]
  exact wiener_path_abs_maximal W V hV hW a ha

lemma distribution_path_norm_limsup {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (F : ℕ → Ω → C(unitInterval,ℝ)) (hF : ∀ i, Measurable (F i))
    (W : ProbabilityMeasure C(unitInterval,ℝ))
    (hlim : TendstoInDistribution F atTop id μ W)
    (V : ℝ) (hV : 0 < V)
    (hW : ∀ I : Finset unitInterval,
      (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) =
        gaussianPathFiniteLaw V I)
    (a : ℝ) (ha : 0 < a) :
    limsup (fun i => (μ i).real {ω | a ≤ ‖F i ω‖}) atTop ≤
      2*Real.exp (-a^2/(2*V)) := by
  let P : ℕ → ProbabilityMeasure C(unitInterval,ℝ) := fun i =>
    ⟨(μ i).map (F i),inferInstance⟩
  have hp : Tendsto P atTop (𝓝 (⟨(W : Measure C(unitInterval,ℝ)),inferInstance⟩ : ProbabilityMeasure C(unitInterval,ℝ))) := by
    simpa only [Measure.map_id] using hlim.tendsto
  have hA : IsClosed {g : C(unitInterval,ℝ) | a ≤ ‖g‖} :=
    isClosed_le continuous_const continuous_norm
  have hh := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hp hA
  change limsup (fun i => ((μ i).map (F i)) {g | a ≤ ‖g‖}) atTop ≤
    (W : Measure C(unitInterval,ℝ)) {g | a ≤ ‖g‖} at hh
  simp only [Measure.map_apply (hF _) hA.measurableSet] at hh
  have he : limsup (fun i => (μ i).real {ω | a ≤ ‖F i ω‖}) atTop =
      (limsup (fun i => μ i {ω | a ≤ ‖F i ω‖}) atTop).toReal := by
    exact ENNReal.limsup_toReal_eq (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
      (Eventually.of_forall fun i => prob_le_one)
  rw [he]
  exact (ENNReal.toReal_mono (measure_ne_top _ _) hh).trans
    (wiener_path_norm_maximal W V hV hW a ha)

end DirectionalTransience

end

end

end OAI
