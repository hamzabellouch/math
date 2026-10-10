import OAI.Probability.DirectionalWalk.FreshPaths

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def wordEndpointCoordinate {d ι : ℕ} (P : Measure (Path d))
    (E : Fin ι → Set (Path d)) (q : Fin ι) (a : Word d) : ℝ :=
  runningMax (endpointPosterior P E q) a.1 (wordPath a)

lemma sum_wordEndpointCoordinate {d ι : ℕ} (P : Measure (Path d))
    (E : Fin ι → Set (Path d)) (a : Word d) :
    ∑ q, wordEndpointCoordinate P E q a = wordEndpointMax P E a := rfl

lemma wordPosterior_le_stoppedCoordinate {d ι : ℕ} (P : Measure (Path d))
    (E : Fin ι → Set (Path d)) (q : Fin ι) (K : Set (Site d)) (a : Word d)
    (ha : ∀ j < a.1, wordPath a j ∉ K) (X : Path d) (hX : X ∈ wordCylinder a)
    (hex : ∃ n, X n ∈ K) :
    wordPosterior P E q a ≤ wordEndpointCoordinate P E q (firstVisitWord K X) := by
  classical
  have hle : a.1 ≤ firstVisitIndex K X := by
    by_contra h
    have hj : firstVisitIndex K X < a.1 := by omega
    apply ha _ hj
    rw [← hX _ hj.le,firstVisitIndex_eq K X hex]
    exact Nat.find_spec hex
  have hc : X ∈ wordCylinder (firstVisitWord K X) := (firstVisitWord_spec K X hex).2
  have he : endpointPosterior P E q a.1 X = wordPosterior P E q a := by
    unfold endpointPosterior
    rw [(prefixWord_eq_iff a.1 X a).mpr ⟨rfl,hX⟩]
  rw [← he,endpointPosterior_prefix P E q (firstVisitWord K X) X hc hle]
  exact Finset.le_sup' (fun i => endpointPosterior P E q i (wordPath (firstVisitWord K X)))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))

def upperContactWord {d : ℕ} (z : Site d) (R K : Set (Site d)) (a : Word d) : Prop :=
  wordPath a 0 = z ∧ (∃ j ≤ a.1, wordPath a j ∈ R) ∧ ∀ j ≤ a.1, wordPath a j ∉ K

def contactBinWords {d : ℕ} (e : Step d) (z : Site d) (r N : ℕ) (a : ℝ≥0∞)
    (ω : Environment d) : Set (Word d) :=
  {b | upperContactWord z (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b ∧
    wordEnd b ∈ returnBin e 0 N a ω}

lemma upperContactWord_visit {d : ℕ} (z : Site d) (R K A : Set (Site d)) (b : Word d)
    (hb : upperContactWord z R K b) (hA : wordEnd b ∈ A) :
    wordCylinder b ⊆ visitAfter R A K := by
  intro X hX
  refine ⟨b.1,?_,?_,?_⟩
  · rw [hX _ le_rfl];exact hA
  · obtain ⟨j,hj,hR⟩ := hb.2.1
    exact ⟨j,hj,by rw [hX _ hj];exact hR⟩
  · intro j hj
    rw [hX _ hj]
    exact hb.2.2 j hj

lemma posterior_contact_bin_quenched {d ι : ℕ} (P : Measure (Path d)) [IsProbabilityMeasure P]
    (E : Fin ι → Set (Path d)) (hE : ∀ q, MeasurableSet (E q))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j))) (e : Step d)
    (ω : Environment d) (z : Site d) (start : Fin ι → Site d) (r N : ℕ) (a : ℝ≥0∞)
    (hex : ∀ᵐ X ∂quenchedKernel d (ω,z), ∃ n, X n ∈ axisLower e 0 ∪ axisUpper e N)
    (hneg : ∀ x : Site d, quenchedKernel d (ω,x)
      (avoids (axisUpper e N) ∩ {B | ∃ n, B n ∈ returnBin e 0 N a ω}) ≤ 2*a) :
    (∑ q, ∑' b : contactBinWords e z r N a ω,
      ENNReal.ofReal (wordPosterior P E q b) *
        (quenchedKernel d (ω,z) (wordCylinder b) *
          quenchedKernel d (ω,start q) (avoids (axisUpper e N) ∩ contactAvoid b))) ≤
      (2*a) * ∫⁻ X in visitAfter (axisUpper e r) (returnAtLeast e 0 N a ω)
        (axisLower e 0 ∪ axisUpper e N),
        ENNReal.ofReal (wordEndpointMax P E (firstVisitWord (axisLower e 0 ∪ axisUpper e N) X))
        ∂quenchedKernel d (ω,z) := by
  classical
  let K := axisLower e 0 ∪ axisUpper e N
  let V := visitAfter (axisUpper e r) (returnAtLeast e 0 N a ω) K
  let M := fun q X => ENNReal.ofReal (wordEndpointCoordinate P E q (firstVisitWord K X))
  have hM (q : Fin ι) : Measurable (M q) :=
    ((measurable_of_countable (wordEndpointCoordinate P E q)).comp (measurable_firstVisitWord K)).ennreal_ofReal
  have hq (q : Fin ι) : (∑' b : contactBinWords e z r N a ω,
      ENNReal.ofReal (wordPosterior P E q b) *
        (quenchedKernel d (ω,z) (wordCylinder b) *
          quenchedKernel d (ω,start q) (avoids (axisUpper e N) ∩ contactAvoid b))) ≤
        (2*a) * ∫⁻ X in V, M q X ∂quenchedKernel d (ω,z) := by
    apply weighted_contact_bin_bound_ae _ _ (contactBinWords e z r N a ω)
      (avoids (axisUpper e N)) V (returnBin e 0 N a ω) (measurableSet_avoids _)
      (fun b => ENNReal.ofReal (wordPosterior P E q b)) (M q) (hM q)
      (fun _ hb => hb.2)
    · intro b hb
      exact upperContactWord_visit z _ _ _ b hb.1 hb.2.1
    · intro b hb
      filter_upwards [hex] with X hx
      exact fun hX => ENNReal.ofReal_le_ofReal (wordPosterior_le_stoppedCoordinate P E q K b
        (fun j hj => hb.1.2.2 j hj.le) X hX hx)
    · exact hneg _
  calc
    _ ≤ ∑ q, (2*a) * ∫⁻ X in V, M q X ∂quenchedKernel d (ω,z) := Finset.sum_le_sum (fun q _ => hq q)
    _ = (2*a) * ∫⁻ X in V, (∑ q, M q X) ∂quenchedKernel d (ω,z) := by
      rw [lintegral_finsetSum _ (fun q _ => hM q),Finset.mul_sum]
    _ = _ := by
      congr 1
      apply lintegral_congr
      intro X
      change (∑ q, ENNReal.ofReal (wordEndpointCoordinate P E q (firstVisitWord K X))) = _
      rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ => show 0 ≤ wordEndpointCoordinate P E q (firstVisitWord K X) from
        runningMax_nonneg _ ((endpointPosterior_bounds P E hE hdis).1 q) _ _),sum_wordEndpointCoordinate]

lemma posterior_contact_bin_joint {d ι : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (P : Measure (Path d)) [IsProbabilityMeasure P]
    (E : Fin ι → Set (Path d)) (hE : ∀ q, MeasurableSet (E q))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j))) (e : Step d)
    (z : Site d) (start : Fin ι → Site d) (r N : ℕ) (a : ℝ≥0∞) (ha : a ≠ ∞) :
    (∫⁻ ω, ∑ q, ∑' b : contactBinWords e z r N a ω,
      ENNReal.ofReal (wordPosterior P E q b) *
        (quenchedKernel d (ω,z) (wordCylinder b) *
          quenchedKernel d (ω,start q) (avoids (axisUpper e N) ∩ contactAvoid b)) ∂environmentLaw μ) ≤
    (2*a) * ∫⁻ ξ in {ξ | ξ.2 ∈ visitAfter (axisUpper e r) (returnAtLeast e 0 N a ξ.1)
      (axisLower e 0 ∪ axisUpper e N)},
      ENNReal.ofReal (wordEndpointMax P E (firstVisitWord (axisLower e 0 ∪ axisUpper e N) ξ.2))
      ∂freshJoint μ z := by
  let K := axisLower e 0 ∪ axisUpper e N
  let V : Set (Environment d × Path d) := {ξ | ξ.2 ∈ visitAfter (axisUpper e r) (returnAtLeast e 0 N a ξ.1) K}
  let f : Environment d × Path d → ℝ≥0∞ := fun ξ => ENNReal.ofReal (wordEndpointMax P E (firstVisitWord K ξ.2))
  have hf : Measurable f := ((measurable_of_countable (wordEndpointMax P E)).comp
    ((measurable_firstVisitWord K).comp measurable_snd)).ennreal_ofReal
  have hV : MeasurableSet V := measurable_random_visitAfter _ _ _ (measurableSet_returnAtLeast e 0 N a)
  have hex : ∀ᵐ ω ∂environmentLaw μ, ∀ᵐ X ∂quenchedKernel d (ω,z), ∃ n, X n ∈ K := by
    apply annealed_ae_quenched μ z
    · have hh : (fun X : Path d => ∃ n, X n ∈ K) = ⋃ n : ℕ, {X : Path d | X n ∈ K} := by
        funext X
        apply propext
        change (∃ n, X n ∈ K) ↔ X ∈ ⋃ n : ℕ, {X : Path d | X n ∈ K}
        constructor
        · rintro ⟨n, hn⟩
          exact Set.mem_iUnion.mpr ⟨n, hn⟩
        · intro h
          exact Set.mem_iUnion.mp h
      rw [hh]
      exact MeasurableSet.iUnion (fun n => (Set.to_countable K).measurableSet.preimage (measurable_pi_apply n))
    · exact annealed_axis_exit μ hell e z 0 N
  have hinner : (∫⁻ ξ in V, f ξ ∂freshJoint μ z) =
      ∫⁻ ω, ∫⁻ X in visitAfter (axisUpper e r) (returnAtLeast e 0 N a ω) K,
        ENNReal.ofReal (wordEndpointMax P E (firstVisitWord K X)) ∂quenchedKernel d (ω,z) ∂environmentLaw μ := by
    rw [← lintegral_indicator hV,freshJoint_lintegral μ z _ (hf.indicator hV)]
    apply lintegral_congr
    intro ω
    rw [← lintegral_indicator (measurableSet_visitAfter _ _ _)]
    rfl
  change _ ≤ (2*a) * ∫⁻ ξ in V, f ξ ∂freshJoint μ z
  rw [hinner,← lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num) ha)]
  apply lintegral_mono_ae
  filter_upwards [hex,quenched_negative_bins μ hell e] with ω hω hn
  apply posterior_contact_bin_quenched P E hE hdis e ω z start r N a hω
  intro x
  exact hn x 0 N (returnBin e 0 N a ω) (2*a) (fun y hy => hy.2.le)

lemma axisHeight_axialRay {d : ℕ} (e f : Step d) (x : Site d) (n : ℕ) :
    axisHeight e (axialRay x f n) = axisHeight e x + n * axisHeight e (stepVector f) := by
  induction n with
  | zero => simp [axialRay_zero]
  | succ n ih => rw [axialRay_succ,axisHeight_add,ih,Nat.cast_add,Nat.cast_one];ring

lemma axisHeight_step_opposite {d : ℕ} (e : Step d) :
    axisHeight e (stepVector (oppositeStep e)) = -1 := by
  have h := axisHeight_step_self (oppositeStep e)
  rw [axisHeight_opposite] at h
  omega

lemma quenchedReturn_pos_lt_one {d : ℕ} (e : Step d) (k N : ℤ)
    (ω : Environment d) (hω : ∀ x f, 0 < (ω x).val f) (y : Site d)
    (hy : k ≤ axisHeight e y ∧ axisHeight e y < N) :
    0 < quenchedReturn e k N ω y ∧ quenchedReturn e k N ω y < 1 := by
  let down := (axisHeight e y-k+1).toNat
  let up := (N-axisHeight e y).toNat
  have hd : (down : ℤ) = axisHeight e y-k+1 := Int.toNat_of_nonneg (by omega)
  have hu : (up : ℤ) = N-axisHeight e y := Int.toNat_of_nonneg (by omega)
  have hdown : pathCylinder down (axialRay y (oppositeStep e)) ⊆ hitBefore (axisLower e k) (axisUpper e N) := by
    intro X hX
    refine ⟨down,?_,?_⟩
    · rw [hX _ le_rfl]
      change axisHeight e (axialRay y (oppositeStep e) down) < k
      rw [axisHeight_axialRay,axisHeight_step_opposite,hd]
      omega
    · intro i hi
      rw [hX _ hi]
      change ¬N ≤ axisHeight e (axialRay y (oppositeStep e) i)
      rw [axisHeight_axialRay,axisHeight_step_opposite]
      omega
  have hup : pathCylinder up (axialRay y e) ⊆ hitBefore (axisUpper e N) (axisLower e k) := by
    intro X hX
    refine ⟨up,?_,?_⟩
    · rw [hX _ le_rfl]
      change N ≤ axisHeight e (axialRay y e up)
      rw [axisHeight_axialRay,axisHeight_step_self,hu]
      omega
    · intro i hi
      rw [hX _ hi]
      change ¬axisHeight e (axialRay y e i) < k
      rw [axisHeight_axialRay,axisHeight_step_self]
      omega
  have hdp : 0 < quenchedReturn e k N ω y :=
    (quenched_axialRay_pos ω hω y (oppositeStep e) down).trans_le (measure_mono hdown)
  have hup' : 0 < quenchedKernel d (ω,y) (hitBefore (axisUpper e N) (axisLower e k)) :=
    (quenched_axialRay_pos ω hω y e up).trans_le (measure_mono hup)
  refine ⟨hdp,lt_of_le_of_ne prob_le_one ?_⟩
  intro he
  have hb : quenchedReturn e k N ω y + quenchedKernel d (ω,y) (hitBefore (axisUpper e N) (axisLower e k)) ≤ 1 := by
    rw [quenchedReturn,← measure_union (hitBefore_disjoint _ _) (measurableSet_hitBefore _ _)]
    exact prob_le_one
  rw [he] at hb
  have hz : quenchedKernel d (ω,y) (hitBefore (axisUpper e N) (axisLower e k)) ≤ 0 := by
    apply (ENNReal.add_le_add_iff_left (by norm_num : (1 : ℝ≥0∞) ≠ ∞)).mp
    simpa using hb
  exact (not_le_of_gt hup') hz

end DirectionalZeroOne

end OAI
