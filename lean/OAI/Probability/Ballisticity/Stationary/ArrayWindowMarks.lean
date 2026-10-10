import Mathlib
import OAI.Probability.Ballisticity.Estimates.GlobalContinuation
import OAI.Probability.Ballisticity.Walk.KernelTranslation

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal Classical BigOperators
namespace DirectionalTransience

noncomputable def arrayWindowHeight {d : ℕ} (e : Direction d) (i : ℤ) (m : ℕ)
    (Y : ActualEpisodeArray e) : ℕ∞ := ∑ r∈Finset.range m, (Y.1 (i+r)).1
noncomputable def arrayWindowCost {d : ℕ} (e : Direction d) (i : ℤ) (m : ℕ)
    (Y : ActualEpisodeArray e) : ℝ≥0∞ := ∑ r∈Finset.range m, (Y.1 (i+r)).2.2

lemma arrayWindowHeight_continuous {d : ℕ} (e : Direction d) (i : ℤ) (m : ℕ) :
    Continuous (arrayWindowHeight e i m) := by unfold arrayWindowHeight; fun_prop
lemma arrayWindowCost_continuous {d : ℕ} (e : Direction d) (i : ℤ) (m : ℕ) :
    Continuous (arrayWindowCost e i m) := by unfold arrayWindowCost; fun_prop

noncomputable def expNeg (C : ℝ≥0∞) : ℝ≥0∞ := EReal.exp (-(C:EReal))
lemma expNeg_le_one (C : ℝ≥0∞) : expNeg C≤1 := by
  rw [←EReal.exp_zero]
  change EReal.exp (-(C:EReal)) ≤ EReal.exp 0
  simpa only [EReal.expOrderIso_apply] using
    EReal.expOrderIso.monotone (show -(C:EReal) ≤ 0 from (EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg C)))
lemma expNeg_ne_top (C : ℝ≥0∞) : expNeg C≠⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (expNeg_le_one C)
lemma expNeg_continuous : Continuous expNeg :=
  ENNReal.continuous_exp.comp (continuous_coe_ennreal_ereal.neg)
lemma expNeg_toReal_continuous : Continuous (fun C => (expNeg C).toReal) := by
  apply continuous_iff_continuousAt.mpr
  intro C
  exact (ENNReal.continuousAt_toReal (expNeg_ne_top C)).comp expNeg_continuous.continuousAt

lemma arrayWindowHeight_actual {d : ℕ} (e : Direction d) (t J : Environment d → ℤ → ℕ)
    (X : EpisodeInput e) (hmono : Monotone (t X.1.1)) (i : ℤ) (m : ℕ) :
    arrayWindowHeight e i m (actualArrayMap e t J X)=(t X.1.1 (i+m)-t X.1.1 i:ℕ) := by
  have hs : (∑ r∈Finset.range m, (t X.1.1 (i+r+1)-t X.1.1 (i+r)))=
      t X.1.1 (i+m)-t X.1.1 i := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ,ih]
      have h₁ := hmono (show i ≤ i+(m:ℤ) by omega)
      have h₂ := hmono (show i+(m:ℤ) ≤ i+m+1 by omega)
      have hx : i+(m+1:ℕ)=i+(m:ℤ)+1 := by omega
      rw [hx]
      omega
  simpa only [arrayWindowHeight,actualArrayMap,Nat.cast_sum] using congrArg (fun n : ℕ => (n:ℕ∞)) hs

lemma episodeCost_nonneg_real {d : ℕ} (e : Direction d) (t : Environment d → ℤ → ℕ)
    (ω : Environment d) (hmono : Monotone (t ω))
    (hpos : ∀ k : ℕ, crossingQuenched (realPosition (step e)) 0 k ω≠0) (i : ℤ) :
    0≤Real.log (crossingQuenched (realPosition (step e)) 0 (t ω i) ω).toReal-
      Real.log (crossingQuenched (realPosition (step e)) 0 (t ω (i+1)) ω).toReal := by
  apply sub_nonneg.mpr
  apply Real.log_le_log (ENNReal.toReal_pos (hpos _) (crossingQuenched_ne_top _ _ _ _))
  apply ENNReal.toReal_mono (crossingQuenched_ne_top _ _ _ _)
  exact crossingQuenched_antitone _ _ _ (by exact_mod_cast hmono (show i ≤ i+1 by omega))

lemma arrayWindowCost_actual {d : ℕ} (e : Direction d) (t J : Environment d → ℤ → ℕ)
    (X : EpisodeInput e) (hmono : Monotone (t X.1.1))
    (hpos : ∀ k : ℕ, crossingQuenched (realPosition (step e)) 0 k X.1.1≠0) (i : ℤ) (m : ℕ) :
    arrayWindowCost e i m (actualArrayMap e t J X)=ENNReal.ofReal
      (Real.log (crossingQuenched (realPosition (step e)) 0 (t X.1.1 i) X.1.1).toReal-
      Real.log (crossingQuenched (realPosition (step e)) 0 (t X.1.1 (i+m)) X.1.1).toReal) := by
  unfold arrayWindowCost
  simp only [actualArrayMap,episodeCost]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun (r : ℕ) _ => episodeCost_nonneg_real e t X.1.1 hmono hpos (i+(r:ℤ)))]
  congr 1
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ,ih]
    have hx : i+(m+1:ℕ)=i+(m:ℤ)+1 := by omega
    rw [hx]
    ring

lemma expNeg_log_ratio (a b : ℝ≥0∞) (ha : a≠0) (hat : a≠⊤)
    (hb : b≠0) (hbt : b≠⊤) (hba : b≤a) :
    expNeg (ENNReal.ofReal (Real.log a.toReal-Real.log b.toReal))=b/a := by
  have hnonneg : 0≤Real.log a.toReal-Real.log b.toReal := sub_nonneg.mpr
    (Real.log_le_log (ENNReal.toReal_pos hb hbt) (ENNReal.toReal_mono hat hba))
  unfold expNeg
  rw [EReal.coe_ennreal_ofReal, max_eq_left hnonneg]
  simp only [←EReal.coe_neg,EReal.exp_coe]
  rw [neg_sub,Real.exp_sub,Real.exp_log (ENNReal.toReal_pos hb hbt),Real.exp_log (ENNReal.toReal_pos ha hat)]
  rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos ha hat),ENNReal.ofReal_toReal hbt,ENNReal.ofReal_toReal hat]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def arrayProfileMass {d : ℕ} (e : Direction d) (j : ℤ)
    (p : StationaryCompact.Label) (z : HorizontalSpace e) (Y : ActualEpisodeArray e) : ℝ≥0∞ :=
  ENNReal.ofReal (Y.2.2.1 (j,p,z):ℝ)

lemma arrayProfileMass_continuous {d : ℕ} (e : Direction d) (j : ℤ)
    (p : StationaryCompact.Label) (z : HorizontalSpace e) : Continuous (arrayProfileMass e j p z) := by
  exact ENNReal.continuous_ofReal.comp (by fun_prop)

noncomputable def arrayUpperRows {d : ℕ} (e : Direction d) (i : ℤ) (m a : ℕ)
    (Y : ActualEpisodeArray e) : UpperRows e := fun p => Y.2.2.2 (i,m,a,p.1,p.2)
lemma arrayUpperRows_continuous {d : ℕ} (e : Direction d) (i : ℤ) (m a : ℕ) :
    Continuous (arrayUpperRows e i m a) := by unfold arrayUpperRows; fun_prop

noncomputable def arrayKernelImage {d : ℕ} (e : Direction d) (i : ℤ) (m a H : ℕ)
    (A : Set (HorizontalSpace e)) (Y : ActualEpisodeArray e) : ℝ≥0∞ :=
  ∑' z, arrayProfileMass e i (i,a) z Y * upperHorizontalKernel e H (arrayUpperRows e i m a Y) z A

lemma arrayKernelImage_lowerSemicontinuous {d : ℕ} (e : Direction d) (i : ℤ) (m a H : ℕ)
    (A : Set (HorizontalSpace e)) : LowerSemicontinuous (arrayKernelImage e i m a H A) := by
  unfold arrayKernelImage
  apply lowerSemicontinuous_tsum
  intro z
  simp_rw [upperHorizontalKernel_apply, hitKernel_eq_tsum_words _ _ _ _ (disjoint_strip_upper _ _ _) _,
    ←ENNReal.tsum_mul_left]
  apply lowerSemicontinuous_tsum
  intro w
  have hp : Continuous (fun Y : ActualEpisodeArray e => (Y.2.2.1 (i,(i,a),z):ℝ)) := by fun_prop
  have hw : Continuous (fun Y : ActualEpisodeArray e =>
      wordWeight (upperEnvironment e (arrayUpperRows e i m a Y)) (horizontalLift e 0 z) w.val.val) :=
    (continuous_wordWeight _ _).comp ((upperEnvironment_continuous e).comp (arrayUpperRows_continuous e i m a))
  have he : (fun Y : ActualEpisodeArray e => arrayProfileMass e i (i,a) z Y *
      ENNReal.ofReal (wordWeight (upperEnvironment e (arrayUpperRows e i m a Y))
        (horizontalLift e 0 z) w.val.val)) =
      (fun Y => ENNReal.ofReal ((Y.2.2.1 (i,(i,a),z):ℝ)*
        wordWeight (upperEnvironment e (arrayUpperRows e i m a Y)) (horizontalLift e 0 z) w.val.val)) := by
    funext Y
    exact (ENNReal.ofReal_mul (Y.2.2.1 (i,(i,a),z)).property.1).symm
  rw [he]
  exact (ENNReal.continuous_ofReal.comp (hp.mul hw)).lowerSemicontinuous

noncomputable def arrayDiscountedProfile {d : ℕ} (e : Direction d) (i : ℤ) (m a : ℕ)
    (z : HorizontalSpace e) (Y : ActualEpisodeArray e) : ℝ≥0∞ :=
  expNeg (arrayWindowCost e i m Y)*arrayProfileMass e (i+m) (i,a) z Y

lemma arrayDiscountedProfile_continuous {d : ℕ} (e : Direction d) (i : ℤ) (m a : ℕ)
    (z : HorizontalSpace e) : Continuous (arrayDiscountedProfile e i m a z) := by
  have he : arrayDiscountedProfile e i m a z = fun Y => ENNReal.ofReal
      ((expNeg (arrayWindowCost e i m Y)).toReal*(Y.2.2.1 (i+m,(i,a),z):ℝ)) := by
    funext Y
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal (expNeg_ne_top _)]
    rfl
  rw [he]
  exact ENNReal.continuous_ofReal.comp ((expNeg_toReal_continuous.comp
    (arrayWindowCost_continuous e i m)).mul (by fun_prop))

def ArrayContinuation {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e) : Prop :=
  ∀ (i : ℤ) (m a H : ℕ) (z : HorizontalSpace e), arrayWindowHeight e i m Y=H →
    arrayKernelImage e i m a H {z} Y ≤ arrayDiscountedProfile e i m a z Y

lemma arrayContinuation_closed {d : ℕ} (e : Direction d) :
    IsClosed {Y : ActualEpisodeArray e | ArrayContinuation e Y} := by
  simp only [ArrayContinuation,Set.ofPred_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun m => isClosed_iInter fun a =>
    isClosed_iInter fun H => isClosed_iInter fun z => ?_
  have hg : IsClosed {Y : ActualEpisodeArray e | arrayKernelImage e i m a H {z} Y ≤
      arrayDiscountedProfile e i m a z Y} :=
    (arrayKernelImage_lowerSemicontinuous e i m a H {z}).isClosed_epigraph.preimage
      (continuous_id.prodMk (arrayDiscountedProfile_continuous e i m a z))
  have ho : IsOpen {Y : ActualEpisodeArray e | arrayWindowHeight e i m Y=(H:ℕ∞)} :=
    (ENat.isOpen_singleton (by simp)).preimage (arrayWindowHeight_continuous e i m)
  convert ho.isClosed_compl.union hg using 1
  ext Y
  simp [imp_iff_not_or]

lemma actual_arrayProfileMass {d : ℕ} (e : Direction d) (t J : Environment d → ℤ → ℕ)
    (X : EpisodeInput e) (j : ℤ) (p : StationaryCompact.Label) (z : HorizontalSpace e) :
    arrayProfileMass e j p z (actualArrayMap e t J X)=
      globalHorizontalProfile e (t X.1.1 j) X.1.1 {X.1.2 p+z} := by
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

lemma actual_arrayKernelImage {d : ℕ} (e : Direction d) (t J : Environment d → ℤ → ℕ)
    (X : EpisodeInput e) (i : ℤ) (m a : ℕ) (A : Set (HorizontalSpace e)) :
    arrayKernelImage e i m a (t X.1.1 (i+m)-t X.1.1 i) A (actualArrayMap e t J X)=
      ∫⁻ z, variableHitKernel (realPosition (step e)) (t X.1.1 (i+m)-t X.1.1 i)
        (X.1.1,horizontalLift e (t X.1.1 i) z)
        {y | horizontalProjection e y-X.1.2 (i,a)∈A}
        ∂globalHorizontalProfile e (t X.1.1 i) X.1.1 := by
  unfold arrayKernelImage
  simp_rw [actual_arrayProfileMass]
  have he : arrayUpperRows e i m a (actualArrayMap e t J X)=
      fun p => episodeSplicedRow e t X i m a p.1 p.2 := rfl
  simp_rw [he,episodeSpliced_kernel]
  rw [lintegral_countable']
  simp_rw [mul_comm]
  exact (Equiv.addLeft (X.1.2 (i,a))).tsum_eq (fun z : HorizontalSpace e =>
    globalHorizontalProfile e (t X.1.1 i) X.1.1 {z} *
    variableHitKernel (realPosition (step e)) (t X.1.1 (i+m)-t X.1.1 i)
      (X.1.1,horizontalLift e (t X.1.1 i) z)
      {y | horizontalProjection e y-X.1.2 (i,a)∈A})

lemma actual_arrayContinuation {d : ℕ} (e : Direction d) (t J : Environment d → ℤ → ℕ)
    (X : EpisodeInput e) (hmono : Monotone (t X.1.1))
    (hpos : ∀ k : ℕ, crossingQuenched (realPosition (step e)) 0 k X.1.1≠0) :
    ArrayContinuation e (actualArrayMap e t J X) := by
  intro i m a H z hH
  rw [arrayWindowHeight_actual e t J X hmono] at hH
  have hH' : t X.1.1 (i+m)-t X.1.1 i=H := by exact_mod_cast hH
  subst H
  rw [actual_arrayKernelImage]
  have hik : t X.1.1 i ≤ t X.1.1 (i+m) := hmono (by omega)
  have hadd : t X.1.1 i+(t X.1.1 (i+m)-t X.1.1 i)=t X.1.1 (i+m) := Nat.add_sub_of_le hik
  have hh := globalHorizontalProfile_continuation e (t X.1.1 i)
    (t X.1.1 (i+m)-t X.1.1 i) X.1.1 (hpos _) {w | w-X.1.2 (i,a)∈({z}:Set (HorizontalSpace e))}
  simp only [←Nat.cast_add,hadd] at hh
  have hs : {w : HorizontalSpace e | w-X.1.2 (i,a)∈({z}:Set (HorizontalSpace e))}={X.1.2 (i,a)+z} := by
    ext w
    simp only [Set.mem_ofPred,Set.mem_singleton_iff]
    rw [sub_eq_iff_eq_add,add_comm z]
  convert hh using 1
  · rfl
  · unfold arrayDiscountedProfile
    rw [arrayWindowCost_actual e t J X hmono hpos,expNeg_log_ratio _ _ (hpos _)
    (crossingQuenched_ne_top _ _ _ _) (hpos _) (crossingQuenched_ne_top _ _ _ _)
    (crossingQuenched_antitone _ _ _ (by exact_mod_cast hik)),actual_arrayProfileMass,hs]

end DirectionalTransience

end

end OAI
