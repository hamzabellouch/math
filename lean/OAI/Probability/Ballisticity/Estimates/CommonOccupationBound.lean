import Mathlib
import OAI.Probability.Ballisticity.Estimates.OccupationParameters
import OAI.Probability.Ballisticity.Estimates.OccupationAlgebra
import OAI.Probability.Ballisticity.Estimates.ObserverAlmostSure

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

def PhysicalGapExit {d : ℕ} (e f : Direction d) (R : ℝ) (H : ℕ)
    (i : Lattice d × Lattice d) : Set (Path d × Path d) :=
  {P | ∃ j < H, R ≤ |physicalFirstHitGap (realPosition (step e)) f i.1 i.2 j P|}

lemma measurableSet_physicalGapExit {d : ℕ} (e f : Direction d) (R : ℝ) (H : ℕ)
    (i : Lattice d × Lattice d) : MeasurableSet (PhysicalGapExit e f R H i) := by
  unfold PhysicalGapExit
  simp only [Set.ofPred_exists,Set.ofPred_and]
  exact MeasurableSet.iUnion fun j => (MeasurableSet.const _).inter
    (measurableSet_le measurable_const ((measurable_physicalFirstHitGap _ _ _ _ j).abs))

lemma smallCommonCount_expectation_eq_sum {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (s : ℝ) (H : ℕ) (i : Lattice d × Lattice d) :
    (∫⁻ P, (smallCommonCount e f s H P : ℝ≥0∞)
      ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2) =
    ∑ j ∈ Finset.range H, sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2
      (SmallCommonLayer e f s (signedHeight e i.1+j)) := by
  let μ := sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2
  have he : (fun P => (smallCommonCount e f s H P : ℝ≥0∞)) =ᵐ[μ]
      (fun P => ∑ j ∈ Finset.range H,
        (SmallCommonLayer e f s (signedHeight e i.1+j)).indicator (fun _ => (1:ℝ≥0∞)) P) := by
    filter_upwards [pairOrigin_ae ν (realPosition (step e)) htrans i.1 i.2] with P hP
    have hx : P.1 0=i.1 := congrArg Prod.fst hP
    simp only [smallCommonCount,hx,Nat.cast_sum,Set.indicator_apply]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  rw [lintegral_congr_ae he,lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    simpa using lintegral_indicator_const
      (measurableSet_smallCommonLayer e f s (signedHeight e i.1+j)) (1:ℝ≥0∞) (μ := μ)
  · intro j hj
    exact ((measurable_const : Measurable (fun _ : Path d × Path d => (1:ℝ≥0∞))).indicator
      (measurableSet_smallCommonLayer e f s (signedHeight e i.1+j)))

theorem smallCommonCount_expectation_le {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    {b R s c q L : ℝ} (hb : 0 ≤ b) (hR : b ≤ R) (hc : 0 ≤ c) (hq : 0 ≤ q)
    (hbs : b ≤ 2*s) (K : ℕ) (hK : 0 < K) (k : ℝ → ℕ)
    (hk : ∀ i : Lattice d × Lattice d, signedHeight e i.1=signedHeight e i.2 →
      b < pairGap f i → pairGap f i < R → 0 < k (pairGap f i))
    (hdrift : ∀ i : Lattice d × Lattice d, signedHeight e i.1=signedHeight e i.2 →
      observedStateGain f b R c q i+observedStatePotential f b R i ≤
      ∫ P, observedStatePotential f b R
        (pairOrigin (commonCutObserver (realPosition (step e)) (fun j => pairGap f j < R)
          (observedAdvanceRule e f b K k) P))
        ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2)
    (hmean : ∀ i : Lattice d × Lattice d, signedHeight e i.1=signedHeight e i.2 →
      (∫⁻ P, observedCharge e f b R s K k P
        ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2) ≤
      ENNReal.ofReal L*ENNReal.ofReal (observedStateGain f b R c q i))
    (H : ℕ) (i : Lattice d × Lattice d) (hi : signedHeight e i.1=signedHeight e i.2) :
    (∫⁻ P, (smallCommonCount e f s H P : ℝ≥0∞)
      ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2) ≤
      ENNReal.ofReal L*ENNReal.ofReal ((2*R)^((3:ℝ)/2)-observedStatePotential f b R i)+
      H*sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2 (PhysicalGapExit e f R H i) := by
  let ℓ := realPosition (step e)
  let μ := sharedConditionedPairLaw ν ℓ i.1 i.2
  let next := commonCutObserver ℓ (fun j => pairGap f j < R) (observedAdvanceRule e f b K k)
  let reward := observedCharge e f b R s K k
  let total := fun P => ⨆ N, observerRewardSum next reward N P
  let E := PhysicalGapExit e f R H i
  have hE : MeasurableSet E := measurableSet_physicalGapExit e f R H i
  have hK' : ∀ j : Lattice d × Lattice d, signedHeight e j.1=signedHeight e j.2 →
      pairGap f j < R → 0 < observedAdvanceBound f b K k j := by
    intro j hj ha
    unfold observedAdvanceBound
    split_ifs with hu
    · exact hK
    · exact hk j hj (lt_of_not_ge hu) ha
  have htotal : Measurable total := Measurable.iSup fun N =>
    measurable_observerRewardSum next reward (measurable_commonCutObserver ℓ _ _)
      (measurable_observedCharge e f b R s K k) N
  have hcount : ∀ᵐ P ∂μ, (smallCommonCount e f s H P : ℝ≥0∞) ≤
      total P+E.indicator (fun _ => (H:ℝ≥0∞)) P := by
    filter_upwards [validObservation_iterates_ae ν hue e f htrans b R K k hK' i hi,
      pairOrigin_ae ν ℓ htrans i.1 i.2] with P hv ho
    by_cases hex : P ∈ E
    · rw [Set.indicator_of_mem hex]
      exact (show (smallCommonCount e f s H P : ℝ≥0∞) ≤ H by
        exact_mod_cast smallCommonCount_le e f s H P).trans (le_add_left le_rfl)
    · rw [Set.indicator_of_notMem hex,add_zero]
      have hv0 := hv 0
      simp only [Function.iterate_zero,Function.id_def] at hv0
      obtain ⟨hxy,hD,hF,hnn,hmm,_⟩ := hv0
      have hbound : BoundedCommonGaps e f R H P := by
        apply boundedCommonGaps_of_physical e f R H P hxy hD hF hnn hmm
        intro j hj
        have hx : P.1 0=i.1 := congrArg Prod.fst ho
        have hy : P.2 0=i.2 := congrArg Prod.snd ho
        rw [hx,hy]
        exact lt_of_not_ge fun h => hex ⟨j,hj,h⟩
      exact (smallCommonCount_le_observer e f hbs K k hK' H P hv hbound).trans (le_iSup (fun N => observerRewardSum next reward N P) H)
  calc
    _ ≤ ∫⁻ P, total P+E.indicator (fun _ => (H:ℝ≥0∞)) P ∂μ := lintegral_mono_ae hcount
    _ = (∫⁻ P, total P ∂μ)+(H:ℝ≥0∞)*μ E := by
      rw [lintegral_add_left htotal,lintegral_indicator_const hE]
    _ ≤ _ := add_le_add_left
      (observedAdvance_total_charge ν hue e f htrans hb hR hc hq K hK k hk hdrift hmean i hi) _

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

theorem occupation_finite_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    {t : ℝ} (ht : 0 < t) (D : OccupationData ν e f t)
    {b r ρ A : ℝ} (hb : D.u₀ ≤ b) (hbr : b ≤ r) (hρ : 0 ≤ ρ) (hA : 1 ≤ A)
    (hbs : b ≤ 2*(ρ*r))
    (hg : ∀ u, b ≤ u → u ≤ A*r → fluctuationScale
      (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) u*
      (independentConditionedPairLaw ν (realPosition (step e))).real
        {P | D.l*u < |commonIncrementProcess (realPosition (step e)) f 0 P|} ≤ D.ε)
    (K : ℕ) (hK : 0 < K)
    (hKn : (K:ℝ) ≤ D.C*fluctuationScale
      (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) b)
    (hKprob : ∀ x y : Lattice d, signedHeight e x=signedHeight e y →
      D.q ≤ (sharedConditionedPairLaw ν (realPosition (step e)) x y).real
        (layerPairTruthEvent (realPosition (step e)) (signedHeight e) x y
          (signedHeight e x+K) {uv | 2*b ≤ |signedCoordinate f uv.1-signedCoordinate f uv.2|}))
    (H : ℕ) (i : Lattice d × Lattice d) (hi : signedHeight e i.1=signedHeight e i.2) :
    let ℓ := realPosition (step e)
    let n := fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0)
    let M := 128*commonMeanWidth ν ℓ
    let δ := 8*Real.exp (-commonMeanWidth ν ℓ/(16*t))
    let J := max ((2:ℝ)^((7:ℝ)/4)) (A^2)*n r/r^((3:ℝ)/2)
    (∫⁻ P, (smallCommonCount e f (ρ*r) H P : ℝ≥0∞) ∂sharedConditionedPairLaw ν ℓ i.1 i.2) ≤
      ENNReal.ofReal (occupationCoefficient J D.C D.q M b r ρ A δ*(2*(A*r))^((3:ℝ)/2))+
        H*sharedConditionedPairLaw ν ℓ i.1 i.2 (PhysicalGapExit e f (A*r) H i) := by
  dsimp only
  let ℓ := realPosition (step e)
  let μ := independentConditionedPairLaw ν ℓ
  let S := commonIncrementProcess ℓ f 0
  let n := fluctuationScale μ S
  let M := 128*commonMeanWidth ν ℓ
  let δ := 8*Real.exp (-commonMeanWidth ν ℓ/(16*t))
  let C₀ := max ((2:ℝ)^((7:ℝ)/4)) (A^2)
  let J := C₀*n r/r^((3:ℝ)/2)
  let L := occupationCoefficient J D.C D.q M b r ρ A δ
  let k := fun u => ⌊t*n u⌋₊
  have hbp : 0 < b := D.u₀_pos.trans_le hb
  have hr : 0 < r := hbp.trans_le hbr
  have hAr : r ≤ A*r := le_mul_of_one_le_left hr.le hA
  have hR : b ≤ A*r := hbr.trans hAr
  have hM : 0 < M := by
    have hm := commonMeanWidth_ge_one ν ℓ htrans (signedHeight e)
      (signedHeight_projection e) (signedHeight_step_le e)
    dsimp [M]
    linarith
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hC₀ : 0 ≤ C₀ := (sq_nonneg A).trans (le_max_right _ _)
  have hn (u : ℝ) : 0 ≤ n u := fluctuationScale_nonneg μ S u
  have hJ : 0 ≤ J := by exact div_nonneg (mul_nonneg hC₀ (hn r)) (Real.rpow_nonneg hr.le _)
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hL : 0 ≤ L := occupationCoefficient_nonneg hJ D.C_pos.le D.q_pos hM.le hbp.le hr.le hρ hA0 hδ
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  have hne := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  have hnr : 0 < n r := div_pos (sq_pos_of_pos hr)
    (truncatedVariance_pos μ S (measurable_commonIncrementProcess ℓ f 0) hne hr)
  have hcomp : ∀ u, b ≤ u → u ≤ A*r → n u ≤ C₀*n r*(u/r)^((7:ℝ)/4) := by
    have hh := good_scale_comparison μ S (measurable_commonIncrementProcess ℓ f 0) hne
      hbp hbr hA D.ε_pos.le (by norm_num : (0:ℝ) ≤ 7/4) D.doubling
      (fun v hbv hvr => ?_)
    · intro u hbu huA
      have he := (div_le_iff₀ hnr).mp (hh u hbu huA)
      simpa only [C₀,mul_comm,mul_left_comm,mul_assoc] using he
    · have htail : μ.real {P | v < |S P|} ≤ μ.real {P | D.l*v < |S P|} := by
        apply measureReal_mono _ (measure_ne_top μ _)
        intro P hP
        have hv : 0 ≤ v := hbp.le.trans hbv
        exact lt_of_le_of_lt (mul_le_of_le_one_left hv D.l_le_one) hP
      exact (mul_le_mul_of_nonneg_left htail (hn v)).trans (hg v hbv (hvr.trans hAr))
  have hscale (u a : ℝ) (hbu : b ≤ u) (huA : u ≤ A*r) (hua : u ≤ a*r) :
      n u ≤ J*a^((1:ℝ)/4)*u^((3:ℝ)/2) :=
    occupation_scale_factor (hbp.trans_le hbu) hr hC₀ (hn r) hua (hcomp u hbu huA)
  have hkfloor (u : ℝ) : (k u:ℝ) ≤ t*n u := Nat.floor_le (mul_nonneg ht.le (hn u))
  have hk (j : Lattice d × Lattice d) (hj : signedHeight e j.1=signedHeight e j.2)
      (hbj : b < pairGap f j) (hRj : pairGap f j < A*r) : 0 < k (pairGap f j) := by
    exact (D.upper _ (hb.trans hbj.le) (hg _ hbj.le hRj.le) j.1 j.2 hj rfl b (A*r) hbj.le hRj.le).1
  have hupper (j : Lattice d × Lattice d) (hj : signedHeight e j.1=signedHeight e j.2)
      (hbj : b < pairGap f j) (hRj : pairGap f j < A*r) :
      (pairGap f j)^((3:ℝ)/2)+t/M*(pairGap f j)^((3:ℝ)/2) ≤
      ∫ P, observedStatePotential f b (A*r)
        (boundaryData ℓ ((signedHeight e j.1+k (pairGap f j):ℤ):ℝ) P).endpoints
        ∂sharedConditionedPairLaw ν ℓ j.1 j.2 := by
    exact (D.upper _ (hb.trans hbj.le) (hg _ hbj.le hRj.le) j.1 j.2 hj rfl b (A*r) hbj.le hRj.le).2
  have hdrift := observedAdvance_drift ν hue e f htrans hbp.le hR K hK k hupper
    (fun j hj _ => hKprob j.1 j.2 hj)
  have hmean (j : Lattice d × Lattice d) (hj : signedHeight e j.1=signedHeight e j.2) :
      (∫⁻ P, observedCharge e f b (A*r) (ρ*r) K k P ∂sharedConditionedPairLaw ν ℓ j.1 j.2) ≤
      ENNReal.ofReal L*ENNReal.ofReal (observedStateGain f b (A*r) (t/M) D.q j) := by
    apply observedCharge_mean_le ν hue e f htrans hL hbs K k j (δ := δ)
    · apply occupationCoefficient_lower hJ D.C_pos.le D.q_pos hM.le hbp.le hr.le hρ hA0 hδ
      have hh := mul_le_mul_of_nonneg_left (hscale b (b/r) le_rfl hR (by rw [div_mul_cancel₀ _ hr.ne'])) D.C_pos.le
      exact hKn.trans (by simpa only [mul_assoc,pairGap] using hh)
    · intro hbj hsj hRj
      apply occupationCoefficient_upper hJ D.C_pos.le D.q_pos hM hbp.le hr.le hρ hA0 hδ ht.le (abs_nonneg _)
      have hs : pairGap f j ≤ (2*ρ)*r := by nlinarith
      have hh := mul_le_mul_of_nonneg_left (hscale _ (2*ρ) hbj.le hRj.le hs) ht.le
      exact (hkfloor _).trans (by simpa only [mul_assoc,pairGap] using hh)
    · intro hsj hRj
      apply occupationCoefficient_far hJ D.C_pos.le D.q_pos hM hbp.le hr.le hρ hA0 hδ ht.le (abs_nonneg _)
      have hbj : b ≤ pairGap f j := hbs.trans hsj.le
      have hh := mul_le_mul_of_nonneg_left (hscale _ A hbj hRj.le hRj.le) ht.le
      exact mul_le_mul_of_nonneg_right ((hkfloor _).trans (by simpa only [mul_assoc,pairGap] using hh)) hδ
    · intro hsj hRj
      have hbj : b ≤ pairGap f j := hbs.trans hsj.le
      exact D.shrink _ (hb.trans hbj) (hg _ hbj hRj.le) j.1 j.2 hj rfl
  have hcount := smallCommonCount_expectation_le ν hue e f htrans hbp.le hR
    (div_nonneg ht.le hM.le) D.q_pos.le hbs K hK k hk hdrift hmean H i hi
  apply hcount.trans
  apply add_le_add_left
  rw [← ENNReal.ofReal_mul hL]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ hL
  have hp : 0 ≤ observedStatePotential f b (A*r) i :=
    (Real.rpow_nonneg hbp.le _).trans (observedPotential_above_floor hbp.le hR)
  exact sub_le_self _ hp

end DirectionalTransience

end

end

end OAI
