import Mathlib
import OAI.Analysis.AffineBernstein.NormalizedCriticalDensity
import OAI.Analysis.AffineBernstein.VarianceSeparation
import OAI.Analysis.AffineBernstein.LinearizedNormalization
import OAI.Analysis.AffineBernstein.EllipticComparison

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section BoundedHarmonic

lemma inverseHessianTrace_constant {n : ℕ} (u : Space n → ℝ) (c : ℝ) (x : Space n) :
    inverseHessianTrace u (fun _ => c) x = 0 := by
  simp [inverseHessianTrace,hessian]

/-- A quantitative oscillation reduction on an actual normalized section.
This is proved from the ABP low-set and logarithmic energy estimates above. -/
theorem normalized_harmonic_no_two_extremes {n : ℕ} (hn : 1 ≤ n) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R) {d : ℝ} (hd : 0 < d) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v : Space n → ℝ, BalancedNormalized ρ R v →
      ∀ F : Space n → ℝ, ContDiff ℝ ∞ F → (∀ x, 0 ≤ F x ∧ F x ≤ d) →
      (∀ x, inverseHessianTrace v F x = 0) →
      ∀ a ∈ Metric.ball (0:Space n) (1/64:ℝ), ∀ b ∈ Metric.ball (0:Space n) (1/64:ℝ),
        ¬(F a ≤ ε ∧ d-F b ≤ ε) := by
  obtain ⟨δ,hδ,Hδ⟩ := normalized_critical_density hn hρ hρ1 hR
  obtain ⟨V,hV,HV⟩ := normalized_log_variance hρ hρ1 hR (n := n)
  let T : ℝ := V/δ^2+2
  have hδs : 0 < δ^2 := sq_pos_of_pos hδ
  have hT : 2 ≤ T := by
    have H : 0 ≤ V/δ^2 := div_nonneg hV hδs.le
    dsimp [T]; linarith
  have hDT : δ^2*T=V+2*δ^2 := by dsimp [T]; field_simp [ne_of_gt hδ]
  have hbig : V < δ^2*T^2 := by
    have hsq : T ≤ T^2 := by nlinarith
    have H := mul_le_mul_of_nonneg_left hsq hδs.le
    nlinarith
  let ε := d/(8*Real.exp T)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hE : 1 ≤ Real.exp T := Real.one_le_exp (by linarith)
  have hεeq : 8*ε*Real.exp T=d := by dsimp [ε]; field_simp
  have hεsmall : 8*ε ≤ d := by nlinarith
  refine ⟨ε,hε,?_⟩
  intro v hv F hF hFrange hLF a ha b hb hab
  let s := fun x => F x+ε
  let r := fun x => d-F x+ε
  have hs : ContDiff ℝ ∞ s := hF.add contDiff_const
  have hr : ContDiff ℝ ∞ r := (contDiff_const.sub hF).add contDiff_const
  have hspos (x : Space n) : 0 < s x := by dsimp [s]; linarith [(hFrange x).1]
  have hrpos (x : Space n) : 0 < r x := by dsimp [r]; linarith [(hFrange x).2]
  have hLs (x : Space n) : inverseHessianTrace v s x ≤ 0 := by
    rw [show s=(fun y => F y+ε) from rfl,inverseHessianTrace_add_constant,hLF]
  have hLr (x : Space n) : inverseHessianTrace v r x ≤ 0 := by
    rw [show r=(fun y => (d-F y)+ε) from rfl,inverseHessianTrace_add_constant,
      inverseHessianTrace_sub isOpen_univ contDiffOn_const hF.contDiffOn (mem_univ x),
      inverseHessianTrace_constant,hLF,sub_zero]
  let K := Metric.closedBall (0:Space n) (1/16:ℝ)
  let A := {x | x ∈ K ∧ s x ≤ 4*ε}
  let B := {x | x ∈ K ∧ r x ≤ 4*ε}
  have hA := compact_sublevel_in_compact (isCompact_closedBall (0:Space n) (1/16:ℝ)) hs.continuous (4*ε)
  have hB := compact_sublevel_in_compact (isCompact_closedBall (0:Space n) (1/16:ℝ)) hr.continuous (4*ε)
  have hAl : δ ≤ (volume A).toReal := by
    have H := Hδ v hv s hs (fun x => (hspos x).le) hLs a ha (2*ε) (by positivity)
      (by dsimp [s]; linarith [hab.1])
    simpa only [show 2*(2*ε)=4*ε by ring] using H
  have hBl : δ ≤ (volume B).toReal := by
    have H := Hδ v hv r hr (fun x => (hrpos x).le) hLr b hb (2*ε) (by positivity)
      (by dsimp [r]; linarith [hab.2])
    simpa only [show 2*(2*ε)=4*ε by ring] using H
  have hlogeq : Real.log (d/2)-Real.log (4*ε)=T := by
    rw [← Real.log_div (by positivity : d/2≠0) (by positivity : 4*ε≠0)]
    have he : (d/2)/(4*ε)=Real.exp T := by dsimp [ε]; field_simp; ring
    rw [he,Real.log_exp]
  have hsep : ∀ x ∈ A, ∀ y ∈ B, T ≤ Real.log (s y)-Real.log (s x) := by
    intro x hx y hy
    have hylo : d/2 ≤ s y := by
      have HY : r y ≤ 4*ε := hy.2
      dsimp [r] at HY
      dsimp [s]
      linarith
    have hxl := Real.log_le_log (hspos x) hx.2
    have hyl := Real.log_le_log (by positivity : (0:ℝ)<d/2) hylo
    linarith
  have hlow := variance_lower_of_separated_sets (isCompact_closedBall (0:Space n) (1/16:ℝ)) hA hB
    (fun _ hx => hx.1) (fun _ hx => hx.1) (hs.log (fun x => (hspos x).ne')).continuous
    (by linarith : 0 ≤ T) hsep
  have hupper := HV v hv s hs hspos hLs
  have hprod : δ^2 ≤ (volume A).toReal*(volume B).toReal := by
    simpa only [pow_two] using mul_le_mul hAl hBl hδ.le (ENNReal.toReal_nonneg)
  have H := mul_le_mul_of_nonneg_right hprod (sq_nonneg T)
  exact (not_lt_of_ge (H.trans (hlow.trans hupper))) hbig

/-- Bounded harmonic Liouville for the genuine inverse-Hessian operator of
an entire balanced affine-maximal graph. No CG/TW theorem is assumed. -/
theorem centered_balanced_bounded_harmonic_constant {n : ℕ} (hn : 1 ≤ n)
    {u F : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u) (hzero : u 0=0) (hdzero : fderiv ℝ u 0=0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hbal : SectionBalance univ u ρ)
    (hF : ContDiff ℝ ∞ F) (hFb : BddBelow (range F)) (hFa : BddAbove (range F))
    (hLF : ∀ x, inverseHessianTrace u F x=0) : ∀ x y, F x=F y := by
  classical
  let m := sInf (range F)
  let M := sSup (range F)
  have hbounds (x : Space n) : m ≤ F x ∧ F x ≤ M :=
    ⟨csInf_le hFb ⟨x,rfl⟩,le_csSup hFa ⟨x,rfl⟩⟩
  have hne : (range F).Nonempty := ⟨F 0,⟨0,rfl⟩⟩
  have hMm : m ≤ M := (hbounds 0).1.trans (hbounds 0).2
  suffices he : M=m by intro x y; linarith [(hbounds x).1,(hbounds x).2,(hbounds y).1,(hbounds y).2]
  by_contra hneM
  have hd : 0 < M-m := sub_pos.mpr (lt_of_le_of_ne hMm (Ne.symm hneM))
  obtain ⟨R,hR,Hnorm⟩ := centered_normalization_at_points hn hu hp hm hzero hdzero hρ hρ1 hbal
  obtain ⟨ε,hε,Hε⟩ := normalized_harmonic_no_two_extremes hn hρ hρ1 hR hd
  obtain ⟨fa,⟨a,rfl⟩,ha⟩ := exists_lt_of_csInf_lt hne (show m < m + ε by linarith)
  obtain ⟨fb,⟨b,rfl⟩,hb⟩ := exists_lt_of_lt_csSup hne (show M - ε < M by linarith)
  obtain ⟨t,ht,A,hv,Hpts⟩ := Hnorm {a,b}
  let G := fun x => F (A x)-m
  have hG : ContDiff ℝ ∞ G := (contDiff_comp_cle hF A).sub contDiff_const
  have hGr (x : Space n) : 0 ≤ G x ∧ G x ≤ M-m := by
    dsimp [G]
    constructor <;> linarith [(hbounds (A x)).1,(hbounds (A x)).2]
  have hLG (x : Space n) : inverseHessianTrace (normalizedFunction u A t) G x=0 := by
    rw [show G=(fun y => F (A y)-m) from rfl,inverseHessianTrace_sub_constant,
      inverseHessianTrace_normalized_comp hu hF hp A ht,hLF,mul_zero]
  exact Hε (normalizedFunction u A t) hv G hG hGr hLG
    (A.symm a) (Hpts a (by simp)) (A.symm b) (Hpts b (by simp))
    (by simp only [G,ContinuousLinearEquiv.apply_symm_apply]; constructor <;> linarith)

end BoundedHarmonic


end
end AffineBernstein
end

end OAI
