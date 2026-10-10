import OAI.Analysis.LipschitzHilbert.Fourier.NormalizedSymbolRepresentation

namespace OAI

/-! A fixed smooth annular selector. Multiplying the separated selector
by this cutoff gives the required support away from the reference slope. -/
noncomputable section
open scoped ContDiff FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def selectorInner (a : ℝ) (ha : 0<a) : ContDiffBump (0 : ℝ) :=
  ⟨a/2,a,by positivity,by linarith⟩

def selectorOuter (b : ℝ) (hb : 0<b) : ContDiffBump (0 : ℝ) :=
  ⟨b,2*b,hb,by linarith⟩

def annularCutoff (a b : ℝ) (ha : 0<a) (hb : 0<b) : SchwartzMap ℝ ℝ :=
  ((selectorOuter b hb).hasCompactSupport.mul_right
    (f' := fun U => 1-selectorInner a ha U)).toSchwartzMap
      ((selectorOuter b hb).contDiff.mul
        (contDiff_const.sub (selectorInner a ha).contDiff))

theorem annularCutoff_apply (a b : ℝ) (ha : 0<a) (hb : 0<b) (U : ℝ) :
    annularCutoff a b ha hb U=selectorOuter b hb U*(1-selectorInner a ha U) := rfl

theorem annularCutoff_nonneg (a b : ℝ) (ha : 0<a) (hb : 0<b) (U : ℝ) :
    0≤annularCutoff a b ha hb U :=
  mul_nonneg (selectorOuter b hb).nonneg (sub_nonneg.mpr (selectorInner a ha).le_one)

theorem annularCutoff_le_one (a b : ℝ) (ha : 0<a) (hb : 0<b) (U : ℝ) :
    annularCutoff a b ha hb U≤1 := by
  have hi := (selectorInner a ha).nonneg (x := U)
  have ho := (selectorOuter b hb).le_one (x := U)
  calc
    _ ≤ selectorOuter b hb U*1 :=
      mul_le_mul_of_nonneg_left (by linarith only [hi]) (selectorOuter b hb).nonneg
    _ ≤ 1 := by simpa only [mul_one] using ho

theorem annularCutoff_one (a b : ℝ) (ha : 0<a) (hb : 0<b) (U : ℝ)
    (hlo : a≤|U|) (hhi : |U|≤b) : annularCutoff a b ha hb U=1 := by
  have hi : selectorInner a ha U=0 :=
    (selectorInner a ha).zero_of_le_dist (by simpa [selectorInner, Real.dist_eq] using hlo)
  have ho : selectorOuter b hb U=1 :=
    (selectorOuter b hb).one_of_mem_closedBall (by simpa [selectorOuter, Real.dist_eq] using hhi)
  rw [annularCutoff_apply, hi, ho]
  norm_num

theorem annularCutoff_support (a b : ℝ) (ha : 0<a) (hb : 0<b) (U : ℝ)
    (h : annularCutoff a b ha hb U≠0) : a/2 < |U| ∧ |U|<2*b := by
  constructor
  · by_contra hn
    have hi : selectorInner a ha U=1 :=
      (selectorInner a ha).one_of_mem_closedBall
        (by simpa [selectorInner, Real.dist_eq] using le_of_not_gt hn)
    apply h
    rw [annularCutoff_apply, hi, sub_self, mul_zero]
  · by_contra hn
    have ho : selectorOuter b hb U=0 :=
      (selectorOuter b hb).zero_of_le_dist
        (by simpa [selectorOuter, Real.dist_eq] using le_of_not_gt hn)
    apply h
    rw [annularCutoff_apply, ho, zero_mul]

def localizedSelector (chi : SchwartzMap ℝ ℝ) (S : SchwartzMap SymbolSpace ℂ)
    (q : ℕ) (nu : SymbolSpace) (U : ℝ) : ℂ :=
  (chi U : ℂ)*weightedSelector S q nu U

theorem localizedSelector_bound (chi : SchwartzMap ℝ ℝ) (hchi : ∀ U, |chi U|≤1)
    (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (nu : SymbolSpace) (U : ℝ) :
    ‖localizedSelector chi S q nu U‖≤symbolCoefficientBound S q*symbolWeight q nu := by
  rw [localizedSelector, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (hchi U) (norm_nonneg _)).trans
    (by simpa only [one_mul] using weightedSelector_bound S q nu U)

theorem localizedSelector_support (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (nu : SymbolSpace) (U : ℝ)
    (h : localizedSelector (annularCutoff a b ha hb) S q nu U≠0) : a/2 < |U| ∧ |U|<2*b := by
  apply annularCutoff_support a b ha hb U
  intro hz
  apply h
  simp only [localizedSelector, hz, Complex.ofReal_zero, zero_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
