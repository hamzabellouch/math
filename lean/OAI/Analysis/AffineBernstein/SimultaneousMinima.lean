import Mathlib
import OAI.Analysis.AffineBernstein.EntireGlobalDet
import OAI.Analysis.AffineBernstein.LinearizedNormalization
import OAI.Analysis.AffineBernstein.SupersolutionHighSet

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section SimultaneousMinima

/-- Any finite family of nonnegative entire supersolutions with infimum zero
has simultaneous arbitrarily small values. This uses generated normalizations,
not uniform-ellipticity assumptions. -/
theorem centered_balanced_simultaneous_minima {n : ℕ} (hn : 1 ≤ n)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u) (hzero : u 0=0) (hdzero : fderiv ℝ u 0=0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hbal : SectionBalance univ u ρ)
    {ι : Type*} [Fintype ι] (F : ι → Space n → ℝ)
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (hpos : ∀ i x, 0 ≤ F i x)
    (hLF : ∀ i x, inverseHessianTrace u (F i) x ≤ 0)
    (hsmall : ∀ i ε, 0 < ε → ∃ x, F i x < ε) {η : ℝ} (hη : 0 < η) :
    ∃ x, ∀ i, F i x < η := by
  classical
  obtain ⟨R,hR,Hnorm⟩ := centered_normalization_at_points hn hu hp hm hzero hdzero hρ hρ1 hbal
  let K := Metric.closedBall (0:Space n) (1/16:ℝ)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKpos : 0 < volume K := (Metric.measure_ball_pos volume (0:Space n) (by norm_num : (0:ℝ)<1/16)).trans_le
    (measure_mono Metric.ball_subset_closedBall)
  have hKreal : 0 < (volume K).toReal := ENNReal.toReal_pos hKpos.ne' hK.measure_lt_top.ne
  let β := (volume K).toReal/((Fintype.card ι:ℝ)+1)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβeq : ((Fintype.card ι:ℝ)+1)*β=(volume K).toReal := by dsimp [β]; field_simp
  obtain ⟨ε,hε,Hε⟩ := normalized_supersolution_high_set_small hn hρ hρ1 hR hη hβ
  choose a ha using fun i => hsmall i ε hε
  obtain ⟨t,ht,A,hv,Hpts⟩ := Hnorm (Finset.univ.image a)
  let G := fun i x => F i (A x)
  let B := fun i => {x | x ∈ K ∧ η ≤ G i x}
  have hGB (i : ι) : (volume (B i)).toReal < β := by
    apply Hε (normalizedFunction u A t) hv (G i) (contDiff_comp_cle (hF i) A)
      (fun x => hpos i (A x)) ?_ (A.symm (a i)) (Hpts (a i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩))
    · simpa only [G,ContinuousLinearEquiv.apply_symm_apply] using (ha i).le
    · intro x
      rw [show G i=(fun y => F i (A y)) from rfl,inverseHessianTrace_normalized_comp hu (hF i) hp A ht]
      exact mul_nonpos_of_nonneg_of_nonpos ht.le (hLF i (A x))
  have hBfin (i : ι) : volume (B i) ≠ ⊤ := ne_top_of_le_ne_top hK.measure_lt_top.ne
    (measure_mono fun _ hx => hx.1)
  have hgood : ∃ x ∈ K, ∀ i, G i x < η := by
    by_contra H
    push Not at H
    have hsub : K ⊆ ⋃ i, B i := by
      intro x hx
      obtain ⟨i,hi⟩ := H x hx
      exact mem_iUnion.mpr ⟨i,hx,hi⟩
    have hmass : volume K ≤ ∑ i, volume (B i) :=
      (measure_mono hsub).trans (measure_iUnion_fintype_le volume B)
    have hfin : (∑ i, volume (B i)) ≠ ⊤ := by
      exact ENNReal.sum_ne_top.mpr (fun i _ => hBfin i)
    have Hreal := ENNReal.toReal_mono hfin hmass
    rw [ENNReal.toReal_sum (fun i _ => hBfin i)] at Hreal
    have Hsum : (∑ i, (volume (B i)).toReal) ≤ (Fintype.card ι:ℝ)*β := by
      simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
        Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hGB i).le)
    nlinarith
  obtain ⟨x,_,Hx⟩ := hgood
  exact ⟨A x,Hx⟩

theorem balanced_simultaneous_minima {n : ℕ} (hn : 1 ≤ n)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hbal : SectionBalance univ u ρ) {ι : Type*} [Fintype ι] (F : ι → Space n → ℝ)
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (hpos : ∀ i x, 0 ≤ F i x)
    (hLF : ∀ i x, inverseHessianTrace u (F i) x ≤ 0)
    (hsmall : ∀ i ε, 0 < ε → ∃ x, F i x < ε) {η : ℝ} (hη : 0 < η) :
    ∃ x, ∀ i, F i x < η := by
  let v := tangentShift u 0 0
  have hv : ContDiff ℝ ∞ v := contDiffOn_univ.mp (contDiffOn_tangentShift hu.contDiffOn 0 0)
  have hh (x : Space n) : hessian v x = hessian u x := hessian_tangentShift isOpen_univ hu.contDiffOn 0 0 (mem_univ x)
  have hvp (x : Space n) : (hessian v x).PosDef := hh x ▸ hp x
  have hvm := affineMaximalOn_tangentShift isOpen_univ hu.contDiffOn hm 0 0
  have hv0 : v 0=0 := by simp [v,tangentShift,tangentHeight]
  have hdv0 : fderiv ℝ v 0=0 := by
    dsimp [v]
    rw [fderiv_tangentShift (hu.differentiable (by simp) 0)]
    exact sub_self _
  apply centered_balanced_simultaneous_minima hn hv hvp hvm hv0 hdv0 hρ hρ1
    (sectionBalance_tangentShift hu hbal 0 0) F hF hpos ?_ hsmall hη
  intro i x
  simpa only [inverseHessianTrace,hh] using hLF i x

end SimultaneousMinima


end
end AffineBernstein
end

end OAI
