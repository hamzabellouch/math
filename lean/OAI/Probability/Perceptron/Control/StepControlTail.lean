import Mathlib
import OAI.Probability.Perceptron.Control.StepControl

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def linearStepIntervals : (n : ℕ) → (Fin (n+1)→ℝ) → (Fin (n+1)→ℝ) →
    (Fin n→ℝ≥0) → List HeatIntervalParam
  | 0,_,_,_ => []
  | n+1,q,r,d =>
    { duration := fun t => (1-t)*(q 1-q 0)+t*(r 1-r 0)
      rate := (r 1-q 1)-(r 0-q 0)
      coefficient := d 0 } ::
      linearStepIntervals n (fun i => q i.succ) (fun i => r i.succ) (fun i => d i.succ)

def stepBoundaryWeights : (n : ℕ) → (Fin (n+1)→ℝ) → (Fin n→ℝ≥0) → List ℝ
  | 0,_,_ => []
  | 1,_,_ => []
  | n+2,v,d => ((d 1:ℝ)-(d 0:ℝ))*v 1 ::
      stepBoundaryWeights (n+1) (fun i => v i.succ) (fun i => d i.succ)

lemma linearStepIntervals_start (g : Jet3) (n : ℕ)
    (q r : Fin (n+1)→Time) (d : Fin n→ℝ≥0) :
    parametricHeatJet g (linearStepIntervals n (fun i => q i) (fun i => r i) d) 0=
      finiteStepControlJet g n q d := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [linearStepIntervals,parametricHeatJet,finiteStepControlJet,
      sub_zero,one_mul,zero_mul,add_zero,timeSpan]
    rw [ih]

lemma linearStepIntervals_end (g : Jet3) (n : ℕ)
    (q r : Fin (n+1)→Time) (d : Fin n→ℝ≥0) :
    parametricHeatJet g (linearStepIntervals n (fun i => q i) (fun i => r i) d) 1=
      finiteStepControlJet g n r d := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [linearStepIntervals,parametricHeatJet,finiteStepControlJet,
      sub_self,zero_mul,one_mul,zero_add,timeSpan]
    rw [ih]

lemma linearStepIntervals_boundary (g : Jet3) (θ : ℝ) (n : ℕ)
    (q r : Fin (n+1)→ℝ) (d : Fin n→ℝ≥0) :
    (heatBoundaryTerms g θ (linearStepIntervals n q r d) (r 0-q 0)).map Prod.fst=
      stepBoundaryWeights n (fun i => r i-q i) d := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [linearStepIntervals,heatBoundaryTerms,List.map_cons,List.map_map,
        Function.comp_def,stepBoundaryWeights]
      have he : r 0-q 0+((r 1-q 1)-(r 0-q 0))=r 1-q 1 := by ring
      rw [he]
      congr 1
      exact ih (fun i => q i.succ) (fun i => r i.succ) (fun i => d i.succ)

lemma linearStepIntervals_rate (n : ℕ) (q r : Fin (n+1)→ℝ) (d : Fin n→ℝ≥0) :
    ((linearStepIntervals n q r d).map HeatIntervalParam.rate).sum=
      (r (Fin.last n)-q (Fin.last n))-(r 0-q 0) := by
  induction n with
  | zero => simp [linearStepIntervals]
  | succ n ih =>
    simp only [linearStepIntervals,List.map_cons,List.sum_cons]
    rw [ih]
    simp only [Fin.succ_last,Fin.succ_zero_eq_one]
    ring

lemma linearStepIntervals_continuous (n : ℕ) (q r : Fin (n+1)→ℝ) (d : Fin n→ℝ≥0) :
    ∀ p∈linearStepIntervals n q r d, Continuous p.duration := by
  induction n with
  | zero => simp [linearStepIntervals]
  | succ n ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ((continuous_const.sub continuous_id).mul continuous_const).add
        (continuous_id.mul continuous_const)
    · exact ih _ _ _ p hp

lemma linearStepIntervals_deriv (n : ℕ) (q r : Fin (n+1)→ℝ) (d : Fin n→ℝ≥0)
    (hq : StrictMono q) (hr : StrictMono r) (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    ∀ p∈linearStepIntervals n q r d, HasDerivAt p.duration p.rate θ ∧ 0<p.duration θ := by
  induction n with
  | zero => simp [linearStepIntervals]
  | succ n ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · constructor
      · convert! (((hasDerivAt_const θ 1).sub (hasDerivAt_id θ)).mul_const (q 1-q 0)).add
          ((hasDerivAt_id θ).mul_const (r 1-r 0)) using 1
        dsimp
        ring
      · exact add_pos (mul_pos (sub_pos.mpr hθ.2) (sub_pos.mpr (hq (by simp))))
          (mul_pos hθ.1 (sub_pos.mpr (hr (by simp))))
    · exact ih _ _ _ (hq.comp Fin.strictMono_succ) (hr.comp Fin.strictMono_succ) p hp

lemma finiteStepControlJet_tail_order_strict (g : Jet3) (n : ℕ)
    (q r : Fin (n+1)→Time) (d : Fin n→ℝ≥0) (hq : StrictMono q) (hr : StrictMono r)
    (h0 : q 0=r 0) (h1 : q (Fin.last n)=r (Fin.last n))
    (ht : ∀ zs : List ℝ, zs.IsSuffix (stepBoundaryWeights n (fun i => (r i:ℝ)-q i) d) →
      0≤zs.sum) (x : ℝ) :
    (finiteStepControlJet g n r d).f x≤(finiteStepControlJet g n q d).f x := by
  rw [← linearStepIntervals_start g n q r d,← linearStepIntervals_end g n q r d]
  apply parametricHeatJet_tail_order
  · exact linearStepIntervals_continuous n _ _ d
  · intro θ hθ
    exact linearStepIntervals_deriv n _ _ d ((Subtype.strictMono_coe _).comp hq)
      ((Subtype.strictMono_coe _).comp hr) θ hθ
  · rw [linearStepIntervals_rate,h0,h1]
    ring
  · intro θ _ zs hz
    apply ht
    have hb := linearStepIntervals_boundary g θ n (fun i => (q i:ℝ)) (fun i => (r i:ℝ)) d
    rw [h0,sub_self] at hb
    rw [← hb]
    exact hz.map _

def uniformControlNodes (n : ℕ) (i : Fin (n+1)) : Time :=
  ⟨(i:ℝ)/(n+1),div_nonneg (Nat.cast_nonneg _) (by positivity),
    (div_le_one (by positivity : (0:ℝ)<n+1)).mpr (by exact_mod_cast i.isLt.le)⟩

lemma uniformControlNodes_strict (n : ℕ) : StrictMono (uniformControlNodes n) := by
  intro i j hij
  change (i:ℝ)/(n+1)<(j:ℝ)/(n+1)
  exact div_lt_div_of_pos_right (by exact_mod_cast hij) (by positivity)

def blendControlNodes {n : ℕ} (q e : Fin (n+1)→Time) (t : Time) (i : Fin (n+1)) : Time :=
  ⟨(1-(t:ℝ))*(q i:ℝ)+(t:ℝ)*(e i:ℝ),
    add_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) (q i).2.1) (mul_nonneg t.2.1 (e i).2.1),by
    nlinarith [mul_nonneg (sub_nonneg.mpr t.2.2) (sub_nonneg.mpr (q i).2.2),
      mul_nonneg t.2.1 (sub_nonneg.mpr (e i).2.2)]⟩

lemma blendControlNodes_strict {n : ℕ} (q e : Fin (n+1)→Time) (t : Time)
    (hq : Monotone q) (he : StrictMono e) (ht : 0<(t:ℝ)) : StrictMono (blendControlNodes q e t) := by
  intro i j hij
  change (1-(t:ℝ))*(q i:ℝ)+(t:ℝ)*(e i:ℝ)<(1-(t:ℝ))*(q j:ℝ)+(t:ℝ)*(e j:ℝ)
  exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left (hq hij.le) (sub_nonneg.mpr t.2.2))
    (mul_lt_mul_of_pos_left (he hij) ht)

lemma linearStepIntervals_eval (g : Jet3) (n : ℕ) (q e : Fin (n+1)→Time)
    (d : Fin n→ℝ≥0) (t : Time) :
    parametricHeatJet g (linearStepIntervals n (fun i => q i) (fun i => e i) d) t=
      finiteStepControlJet g n (blendControlNodes q e t) d := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [linearStepIntervals,parametricHeatJet,finiteStepControlJet]
    rw [ih]
    congr 1
    unfold timeSpan blendControlNodes
    congr 1
    ring

lemma stepBoundaryWeights_scale (n : ℕ) (v : Fin (n+1)→ℝ) (d : Fin n→ℝ≥0) (c : ℝ) :
    stepBoundaryWeights n (fun i => c*v i) d=(stepBoundaryWeights n v d).map (c*·) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [stepBoundaryWeights,List.map_cons]
      rw [ih]
      congr 1
      ring

lemma stepBoundaryWeights_blend {n : ℕ} (q r e : Fin (n+1)→Time) (d : Fin n→ℝ≥0) (t : Time) :
    stepBoundaryWeights n (fun i => (blendControlNodes r e t i:ℝ)-blendControlNodes q e t i) d=
      (stepBoundaryWeights n (fun i => (r i:ℝ)-q i) d).map ((1-(t:ℝ))*·) := by
  rw [← stepBoundaryWeights_scale]
  congr 1
  funext i
  simp only [blendControlNodes]
  ring

theorem finiteStepControlJet_tail_order (g : Jet3) (n : ℕ)
    (q r : Fin (n+1)→Time) (d : Fin n→ℝ≥0) (hq : Monotone q) (hr : Monotone r)
    (h0 : q 0=r 0) (h1 : q (Fin.last n)=r (Fin.last n))
    (ht : ∀ zs : List ℝ, zs.IsSuffix (stepBoundaryWeights n (fun i => (r i:ℝ)-q i) d) →
      0≤zs.sum) (x : ℝ) :
    (finiteStepControlJet g n r d).f x≤(finiteStepControlJet g n q d).f x := by
  let e := uniformControlNodes n
  have he : StrictMono e := uniformControlNodes_strict n
  let F := fun s : ℝ => (parametricHeatJet g
    (linearStepIntervals n (fun i => q i) (fun i => e i) d) s).f x
  let G := fun s : ℝ => (parametricHeatJet g
    (linearStepIntervals n (fun i => r i) (fun i => e i) d) s).f x
  have hF : ContinuousAt F 0 :=
    (BoundedContinuousFunction.evalCLM ℝ x).continuous.continuousAt.comp
      (parametricHeatJet_continuousAt _ _ _ (fun p hp =>
        (linearStepIntervals_continuous n _ _ d p hp).continuousAt))
  have hG : ContinuousAt G 0 :=
    (BoundedContinuousFunction.evalCLM ℝ x).continuous.continuousAt.comp
      (parametricHeatJet_continuousAt _ _ _ (fun p hp =>
        (linearStepIntervals_continuous n _ _ d p hp).continuousAt))
  have hi (s : ℝ) (hs : s∈Ioo (0:ℝ) 1) : G s≤F s := by
    let t : Time := ⟨s,hs.1.le,hs.2.le⟩
    change (parametricHeatJet g _ (t:ℝ)).f x≤(parametricHeatJet g _ (t:ℝ)).f x
    rw [linearStepIntervals_eval,linearStepIntervals_eval]
    apply finiteStepControlJet_tail_order_strict g n _ _ d
      (blendControlNodes_strict q e t hq he hs.1) (blendControlNodes_strict r e t hr he hs.1)
    · apply Subtype.ext
      simp only [blendControlNodes,h0]
    · apply Subtype.ext
      simp only [blendControlNodes,h1]
    · intro zs hz
      rw [stepBoundaryWeights_blend] at hz
      obtain ⟨ys,hy,rfl⟩ := List.suffix_map_iff.mp hz
      rw [List.sum_map_mul_left]
      simpa using mul_nonneg (sub_nonneg.mpr hs.2.le) (ht ys hy)
  let : NeBot (𝓝[Ioo (0:ℝ) 1] 0) := left_nhdsWithin_Ioo_neBot zero_lt_one
  have hlim : G 0≤F 0 := le_of_tendsto_of_tendsto hG.continuousWithinAt.tendsto
    hF.continuousWithinAt.tendsto (eventually_mem_nhdsWithin.mono fun s hs => hi s hs)
  simpa only [F,G,linearStepIntervals_start] using hlim

lemma stepBoundaryWeights_ofFn (n : ℕ) (v : Fin (n+2)→ℝ) (d : Fin (n+1)→ℝ≥0) :
    stepBoundaryWeights (n+1) v d=
      List.ofFn (fun i : Fin n => ((d i.succ:ℝ)-(d i.castSucc:ℝ))*v i.succ.castSucc) := by
  induction n with
  | zero => simp [stepBoundaryWeights]
  | succ n ih =>
    rw [stepBoundaryWeights,List.ofFn_succ,ih]
    rfl

lemma weightedControlCoefficient_gap (n : ℕ) (w : Fin (n+2)→ℝ) (hw : ∀ i, 0≤w i) (i : Fin n) :
    (weightedControlCoefficient (n+1) w hw i.succ:ℝ)-
      weightedControlCoefficient (n+1) w hw i.castSucc=w i.succ.castSucc := by
  have he (j : Fin (n+2)) :
      (if j ≤ i.succ.castSucc then w j else 0)=
        (if j ≤ i.castSucc.castSucc then w j else 0)+(if j=i.succ.castSucc then w j else 0) := by
    by_cases hj : j=i.succ.castSucc
    · subst j
      have hn : ¬i.succ.castSucc ≤ i.castSucc.castSucc := by
        simp only [Fin.le_iff_val_le_val,Fin.val_castSucc,Fin.val_succ]
        omega
      simp only [le_refl,ite_true,hn,ite_false,zero_add]
    · have hle : j ≤ i.succ.castSucc ↔ j ≤ i.castSucc.castSucc := by
        simp only [Fin.le_iff_val_le_val,Fin.val_castSucc,Fin.val_succ]
        have hne : j.val≠i.val+1 := by simpa [Fin.ext_iff] using hj
        omega
      simp only [hj,hle,ite_false,add_zero]
  change (∑ j, if j ≤ i.succ.castSucc then w j else 0)-
    (∑ j, if j ≤ i.castSucc.castSucc then w j else 0)=_
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

lemma paddedControl_boundaryWeights (n : ℕ) (w : Fin (n+1)→ℝ) (hw : ∀ i, 0≤w i)
    (q r : Fin (n+1)→Time) :
    stepBoundaryWeights (n+2)
      (fun i => (paddedControlNodes r i:ℝ)-paddedControlNodes q i)
      (weightedControlCoefficient (n+2) (paddedControlWeights w) (paddedControlWeights_nonneg w hw))=
        List.ofFn (fun i => w i*((r i:ℝ)-q i)) := by
  rw [stepBoundaryWeights_ofFn]
  congr 1
  funext i
  rw [weightedControlCoefficient_gap]
  simp [paddedControlWeights,paddedControlNodes,Fin.castSucc_succ]

lemma listOfFn_suffix_sum_nonneg (n : ℕ) (v : Fin n→ℝ)
    (ht : ∀ k : ℕ, 0≤∑ i, if k ≤ i.val then v i else 0) :
    ∀ zs : List ℝ, zs.IsSuffix (List.ofFn v) → 0≤zs.sum := by
  induction n with
  | zero =>
    intro zs hz
    simpa using (show zs=[] from by simpa using hz) ▸ (le_refl (0:ℝ))
  | succ n ih =>
    intro zs hz
    rw [List.ofFn_succ] at hz
    obtain ⟨ys,hys⟩ := hz
    cases ys with
    | nil =>
      have he : zs=v 0 ::List.ofFn (fun i => v i.succ) := by simpa using hys
      rw [he,← List.ofFn_succ,List.sum_ofFn]
      simpa using ht 0
    | cons a ys =>
      have he : ys++zs=List.ofFn (fun i => v i.succ) := (List.cons.inj hys).2
      apply ih (fun i => v i.succ) ?_ zs ⟨ys,he⟩
      intro k
      have H := ht (k+1)
      rw [Fin.sum_univ_succ] at H
      simpa only [Fin.val_zero,(show ¬k+1≤0 by omega),ite_false,zero_add,Fin.val_succ,
        Nat.add_le_add_iff_right] using H

theorem sourceWeightedTrial_control_tail_order (n : ℕ) (w : Fin (n+1)→ℝ)
    (q r : Fin (n+1)→Time) (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1)
    (hq : Monotone q) (hr : Monotone r)
    (ht : ∀ k : ℕ, 0≤∑ i, if k ≤ i.val then w i*((r i:ℝ)-q i) else 0)
    (g : Jet3) (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) :
    controlValue P g.f (weightedStepTrial w r hw hw1)≤
      controlValue P g.f (weightedStepTrial w q hw hw1) := by
  rw [sourceWeightedTrial_controlValue n w r hw hw1 hr g P hB,
    sourceWeightedTrial_controlValue n w q hw hw1 hq g P hB]
  apply finiteStepControlJet_tail_order g (n+2) _ _ _ (paddedControlNodes_mono q hq)
    (paddedControlNodes_mono r hr)
  · simp [paddedControlNodes]
  · simp [paddedControlNodes]
  · rw [paddedControl_boundaryWeights n w hw q r]
    exact listOfFn_suffix_sum_nonneg (n+1) _ ht

end SphericalPerceptronFreeEnergy
end

end OAI
