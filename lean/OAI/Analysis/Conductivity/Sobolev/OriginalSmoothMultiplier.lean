import Mathlib
import OAI.Analysis.Conductivity.Sources.PhysicalBlockDomain
import OAI.Analysis.Conductivity.Variational.PhysicalTerminalBands

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable {χ : R3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)

def originalMulComponentCLM (i : Fin 4) : H1 →L[ℝ] Lp ℝ 2 ballMeasure :=
  Fin.cases ((compactMultiplierCLM hχ.continuous hc).comp weakValueL)
    (fun j => ((compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ (EuclideanSpace.single j 1))).comp weakValueL)+
      ((compactMultiplierCLM hχ.continuous hc).comp (weakDirectionL (EuclideanSpace.single j 1)))) i

def originalMulJetCLM : H1 →L[ℝ] JetSpace :=
  (lpFourJetCLM ballMeasure).comp (ContinuousLinearMap.pi (originalMulComponentCLM hχ hc))

lemma originalMulComponentCLM_value (u : H1) :
    originalMulComponentCLM hχ hc 0 u=ᵐ[ballMeasure] fun x => χ x*weakValue u x := by
  filter_upwards [compactMultiplierCLM_ae hχ.continuous hc (weakValueL u),weakValueL_apply_ae u]
    with x hx hu
  exact hx.trans (congrArg (χ x*·) hu)

lemma originalMulComponentCLM_gradient (u : H1) (j : Fin 3) :
    originalMulComponentCLM hχ hc j.succ u=ᵐ[ballMeasure] fun x =>
      fderiv ℝ χ x (EuclideanSpace.single j 1)*weakValue u x+χ x*weakGradient u x j := by
  have h0 := compactMultiplierCLM_ae ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ (EuclideanSpace.single j 1)) (weakValueL u)
  have h1 := compactMultiplierCLM_ae hχ.continuous hc (weakDirectionL (EuclideanSpace.single j 1) u)
  filter_upwards [h0,h1,weakValueL_apply_ae u,weakDirectionL_apply_ae u (EuclideanSpace.single j 1),
    Lp.coeFn_add
      (compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hc.fderiv_apply ℝ (EuclideanSpace.single j 1)) (weakValueL u))
      (compactMultiplierCLM hχ.continuous hc (weakDirectionL (EuclideanSpace.single j 1) u))]
    with x h0 h1 hu hd ha
  change (compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ (EuclideanSpace.single j 1)) (weakValueL u)+
    compactMultiplierCLM hχ.continuous hc (weakDirectionL (EuclideanSpace.single j 1) u)) x=_
  rw [ha]
  simp only [Pi.add_apply,h0,h1,hu,hd,EuclideanSpace.inner_single_left,RCLike.conj_to_real,one_mul]

lemma originalMulJetCLM_ae (u : H1) :
    originalMulJetCLM hχ hc u=ᵐ[ballMeasure] fun x =>
      WithLp.toLp 2 (Fin.cases (χ x*weakValue u x)
        (fun j => fderiv ℝ χ x (EuclideanSpace.single j 1)*weakValue u x+χ x*weakGradient u x j)) := by
  filter_upwards [lpFourJetCLM_ae ballMeasure (fun i => originalMulComponentCLM hχ hc i u),
    originalMulComponentCLM_value hχ hc u,ae_all_iff.mpr (originalMulComponentCLM_gradient hχ hc u)]
    with x hj hv hg
  change lpFourJetCLM ballMeasure (fun i => originalMulComponentCLM hχ hc i u) x=_
  rw [hj]
  ext i
  exact Fin.cases hv hg i

lemma originalMulJetCLM_smooth {f : R3 → ℝ} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    originalMulJetCLM hχ hc (smoothH1 f hf)=(smoothH1 (χ*f) (hχ.mul hf)).val := by
  apply Lp.ext
  filter_upwards [originalMulJetCLM_ae hχ hc (smoothH1 f hf),smoothH1_value f hf,smoothH1_gradient f hf,
    (smoothJet_memLp (hχ.mul hf)).coeFn_toLp] with x hm hv hg hs
  change (smoothH1 (χ*f) (hχ.mul hf)).val x=smoothJet (χ*f) x at hs
  rw [hm,hs]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change χ x*weakValue (smoothH1 f hf) x=χ x*f x
    rw [hv]
  · change fderiv ℝ χ x (EuclideanSpace.single j 1)*weakValue (smoothH1 f hf) x+
      χ x*weakGradient (smoothH1 f hf) x j=gradient (χ*f) x j
    rw [hv,hg]
    have hj (g : R3 → ℝ) : gradient g x j=fderiv ℝ g x (EuclideanSpace.single j 1) := by
      have h : inner ℝ (EuclideanSpace.single j 1) (gradient g x)=
          (starRingEnd ℝ) (fderiv ℝ g x (EuclideanSpace.single j 1)) := inner_gradient_right
      simpa only [EuclideanSpace.inner_single_left,RCLike.conj_to_real,one_mul] using h
    rw [hj,hj,fderiv_mul (hχ.differentiable (by simp) x) (hf.differentiable (by simp) x)]
    simp only [add_apply,smul_apply,smul_eq_mul]
    ring

lemma originalMulJetCLM_mem_zero (hs : tsupport χ⊆ball) (u : H1) :
    originalMulJetCLM hχ hc u∈zeroTraceAmbient := by
  have hclosed : IsClosed {u : H1 | originalMulJetCLM hχ hc u∈zeroTraceAmbient} :=
    (Submodule.isClosed_topologicalClosure _).preimage (originalMulJetCLM hχ hc).continuous
  apply (closure_minimal (s:={u : H1 | u.val∈smoothJets}) ?_ hclosed) (smoothH1_dense u)
  rintro v ⟨f,hf,hm,he⟩
  have hv : v=smoothH1 f hf := Subtype.ext he
  rw [hv]
  change originalMulJetCLM hχ hc (smoothH1 f hf)∈zeroTraceAmbient
  rw [originalMulJetCLM_smooth]
  exact smoothH1_mem_H10 (χ*f) (hχ.mul hf) (hc.mul_right) ((tsupport_mul_subset_left).trans hs)

include hχ hc in

theorem original_smooth_mul_exists (hs : tsupport χ⊆ball) (u : H1) :
    ∃ v : H1,v∈H10 ∧ weakValue v=ᵐ[ballMeasure] fun x => χ x*weakValue u x := by
  have hz := originalMulJetCLM_mem_zero hχ hc hs u
  refine ⟨⟨originalMulJetCLM hχ hc u,zeroTraceAmbient_le_H1Space hz⟩,hz,?_⟩
  filter_upwards [originalMulJetCLM_ae hχ hc u] with x hx
  exact congrArg (fun z : JetFiber => z 0) hx

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
lemma LocalLipAt.add {E : Type*} [PseudoMetricSpace E] {f g : E → ℝ} {x : E}
    (hf : LocalLipAt f x) (hg : LocalLipAt g x) : LocalLipAt (fun y => f y+g y) x := by
  exact (localLipAt_of_contDiffAt
    (show ContDiffAt ℝ 1 (fun p : ℝ×ℝ => p.1+p.2) (f x,g x) by fun_prop)).comp
    (f:=fun y => (f y,g y)) (x:=x) (hf.prodMk hg)

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

def terminalProfileParent (η : ℝ) (j : Fin 2) (y : Coord3) : ℝ :=
  centralBasisSlopes j 0*z.compression 0*max (terminalTime 0 y) 0*
    (1-Real.smoothTransition (terminalTime 0 y/η-1))

def terminalProfileChild (η : ℝ) (j : Fin 2) (k : Fin 2) (y : Coord3) : ℝ :=
  (z.terminalValue k.succ j-z.terminalValue 0 j+
    centralBasisSlopes j k.succ*z.compression k.succ*min (terminalTime k.succ y) 0)*
    Real.smoothTransition (terminalTime k.succ y/η+2)

def terminalProfile (η : ℝ) (j : Fin 2) (y : Coord3) : ℝ :=
  z.terminalProfileParent η j y+∑ k : Fin 2,z.terminalProfileChild η j k y

lemma terminalTime_locallyLipschitz (i : Fin 3) : LocallyLipschitz (terminalTime i) := by
  refine Fin.cases locallyLipschitz_sourceCollarTime (fun k => ?_) i
  exact locallyLipschitz_sourceCollarTime.comp
    ((sourceChildInverse_contDiff (actualChildSign k)).of_le (show (1:WithTop ℕ∞)≤↑(⊤:ℕ∞) by simp)).locallyLipschitz

lemma terminalProfileParent_localLip (η : ℝ) (j : Fin 2) (y : Coord3) :
    LocalLipAt (z.terminalProfileParent η j) y := by
  have hmax : LocallyLipschitz (fun x => max (terminalTime 0 x) 0) :=
    (terminalTime_locallyLipschitz 0).max (LipschitzWith.const (0:ℝ)).locallyLipschitz
  have hcut : ContDiff ℝ 1 (fun t : ℝ => 1-Real.smoothTransition (t/η-1)) :=
    contDiff_const.sub ((Real.smoothTransition.contDiff (n:=1)).comp (by fun_prop))
  exact ((localLipAt_of_contDiffAt (contDiffAt_const (c:=centralBasisSlopes j 0*z.compression 0))).mul
    (hmax y)).mul (hcut.locallyLipschitz.comp (terminalTime_locallyLipschitz 0) y)

lemma terminalProfileChild_localLip (η : ℝ) (j : Fin 2) (k : Fin 2) (y : Coord3) :
    LocalLipAt (z.terminalProfileChild η j k) y := by
  have hmin : LocallyLipschitz (fun x => min (terminalTime k.succ x) 0) :=
    (terminalTime_locallyLipschitz k.succ).min (LipschitzWith.const (0:ℝ)).locallyLipschitz
  have ha : ContDiff ℝ 1 (fun t : ℝ => z.terminalValue k.succ j-z.terminalValue 0 j+
      centralBasisSlopes j k.succ*z.compression k.succ*t) := by fun_prop
  have hb : ContDiff ℝ 1 (fun t : ℝ => Real.smoothTransition (t/η+2)) :=
    (Real.smoothTransition.contDiff (n:=1)).comp (by fun_prop)
  exact LocalLipAt.mul (ha.locallyLipschitz.comp hmin y)
    (hb.locallyLipschitz.comp (terminalTime_locallyLipschitz k.succ) y)

lemma terminalProfile_localLip (η : ℝ) (j : Fin 2) (y : Coord3) :
    LocalLipAt (z.terminalProfile η j) y := by
  change LocalLipAt (fun x => z.terminalProfileParent η j x+∑ k : Fin 2,z.terminalProfileChild η j k x) y
  simp only [Fin.sum_univ_two]
  exact (z.terminalProfileParent_localLip η j y).add
    ((z.terminalProfileChild_localLip η j 0 y).add (z.terminalProfileChild_localLip η j 1 y))

lemma terminalProfileParent_zero_left (η : ℝ) (j : Fin 2) {y : Coord3}
    (hy : terminalTime 0 y≤0) : z.terminalProfileParent η j y=0 := by
  simp [terminalProfileParent,max_eq_right hy]

lemma terminalProfileParent_zero_right {η : ℝ} (hη : 0<η) (j : Fin 2) {y : Coord3}
    (hy : 2*η≤terminalTime 0 y) : z.terminalProfileParent η j y=0 := by
  have hh : 1≤terminalTime 0 y/η-1 := by rw [le_sub_iff_add_le,le_div_iff₀ hη]; linarith
  simp [terminalProfileParent,Real.smoothTransition.one_of_one_le hh]

lemma terminalProfileChild_zero {η : ℝ} (hη : 0<η) (j : Fin 2) (k : Fin 2) {y : Coord3}
    (hy : terminalTime k.succ y≤-2*η) : z.terminalProfileChild η j k y=0 := by
  have hh : terminalTime k.succ y/η+2≤0 := by have hh : terminalTime k.succ y/η≤ -2 := (div_le_iff₀ hη).mpr (by linarith); linarith
  simp [terminalProfileChild,Real.smoothTransition.zero_of_nonpos hh]

lemma terminalTime_far_parent (k : Fin 2) {y : Coord3}
    (hy : -centralThickness≤terminalTime k.succ y) : 2*centralThickness≤terminalTime 0 y := by
  have hh := sourceExpandedChild_far_parent k hy
  change 2*centralThickness≤ sourceCollarTime ((sourceChildHomeomorph (actualChildSign k))
    ((sourceChildHomeomorph (actualChildSign k)).symm y)) at hh
  simpa only [Homeomorph.apply_symm_apply,terminalTime,Fin.cases_zero] using hh

lemma terminalProfile_zero_outside {η : ℝ} (hη : 0<η) (hηc : 2*η<centralThickness)
    (j : Fin 2) {y : Coord3} (hy : terminalTime 0 y≤0) : z.terminalProfile η j y=0 := by
  rw [terminalProfile,z.terminalProfileParent_zero_left η j hy,zero_add]
  apply Finset.sum_eq_zero
  intro k _
  apply z.terminalProfileChild_zero hη j k
  by_contra hn
  have hc : -centralThickness≤terminalTime k.succ y := by linarith [lt_of_not_ge hn]
  have hh := terminalTime_far_parent k hc
  have : 0<centralThickness := by norm_num [centralThickness]
  linarith

lemma terminalProfile_H10 {η : ℝ} (hη : 0<η) (hηc : 2*η<centralThickness) (j : Fin 2) :
    ∃ w : H1,w∈H10 ∧ weakValue w=ᵐ[ballMeasure] fun x => z.terminalProfile η j (WithLp.ofLp x) := by
  have hz (y : Coord3) (hy : 5/2<‖WithLp.toLp 2 y‖) : z.terminalProfile η j y=0 := by
    apply z.terminalProfile_zero_outside hη hηc j
    by_contra hn
    have hd := (sourceCollarTime_pos_iff_domain y).mp (lt_of_not_ge hn)
    have hb := sourceClosure_subset_ball (subset_closure hd)
    simp only [Metric.mem_ball,dist_zero_right] at hb
    linarith
  obtain ⟨w,hw,he⟩ := compact_localLip_H1_pi (z.terminalProfile_localLip η j)
    (R:=5/2) (by norm_num) hz
  exact ⟨w,hw,he.mono (fun _ h => h.1)⟩

lemma terminalProfile_parent_band {η : ℝ} (hη : 0<η) (hηc : 2*η<centralThickness)
    (j : Fin 2) {y : Coord3} (h0 : 0≤terminalTime 0 y) (hy : terminalTime 0 y≤η) :
    z.terminalProfile η j y=centralBasisSlopes j 0*z.compression 0*terminalTime 0 y := by
  have hh : terminalTime 0 y/η-1≤0 := by rw [sub_nonpos,div_le_iff₀ hη]; simpa using hy
  have hz : ∑ k : Fin 2,z.terminalProfileChild η j k y=0 := by
    apply Finset.sum_eq_zero
    intro k _
    apply z.terminalProfileChild_zero hη j k
    by_contra hn
    have hh := terminalTime_far_parent k (show -centralThickness≤terminalTime k.succ y by linarith)
    linarith
  simp [terminalProfile,terminalProfileParent,max_eq_left h0,hz,Real.smoothTransition.zero_of_nonpos hh]

lemma terminalProfile_child_band {η : ℝ} (hη : 0<η) (hηc : 2*η<centralThickness)
    (j : Fin 2) (k : Fin 2) {y : Coord3} (hy : -η≤terminalTime k.succ y) :
    z.terminalProfile η j y=z.terminalValue k.succ j-z.terminalValue 0 j+
      centralBasisSlopes j k.succ*z.compression k.succ*min (terminalTime k.succ y) 0 := by
  have hc : -centralThickness≤terminalTime k.succ y := by linarith
  have hh := terminalTime_far_parent k hc
  have hp := z.terminalProfileParent_zero_right hη j (show 2*η≤terminalTime 0 y by linarith)
  have hb : 1≤terminalTime k.succ y/η+2 := by have hh : -1≤terminalTime k.succ y/η := (le_div_iff₀ hη).mpr (by linarith); linarith
  have ho (l : Fin 2) (hl : l≠k) : z.terminalProfileChild η j l y=0 := by
    apply z.terminalProfileChild_zero hη j l
    have hh := sourceExpandedChild_other k l (Ne.symm hl) hc
    change terminalTime l.succ y< -centralThickness at hh
    linarith
  rw [terminalProfile,hp,zero_add,Finset.sum_eq_single k]
  · simp only [terminalProfileChild,Real.smoothTransition.one_of_one_le hb,mul_one]
  · exact fun l _ hl => ho l hl
  · simp

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

end OAI
