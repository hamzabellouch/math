import Mathlib
import OAI.Analysis.AffineBernstein.JointTubeMetrics
import OAI.Analysis.AffineBernstein.MatrixCombination

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section TubeCombination
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]

lemma tubeBasePair_linearCombination {H : S × E → ℝ} (b : Module.Basis ι ℝ S)
    {q : S × E} (hp : 0 ≤ H q) (hB : (tubeBaseMatrix H q b).PosDef)
    (v : S × E → ℝ) (α : J → S × E → ℝ) (a : J → ℝ)
    (hd : ∀ i, dirDeriv (b i, (0 : E)) v q = ∑ j, a j*dirDeriv (b i, (0 : E)) (α j) q) :
    tubeBasePair H b v v q ≤ (∑ j, a j^2)*(∑ j, tubeBasePair H b (α j) (α j) q) := by
  have hv : (fun i => dirDeriv (b i,(0:E)) v q) =
      (fun i => ∑ j, a j*dirDeriv (b i,(0:E)) (α j) q) := funext hd
  have hc := inverseMatrixPair_combination hB a (fun j i => dirDeriv (b i,(0:E)) (α j) q)
  have hm := mul_le_mul_of_nonneg_left hc hp
  change H q * inverseMatrixPair (tubeBaseMatrix H q b) (fun i => dirDeriv (b i,(0:E)) v q)
    (fun i => dirDeriv (b i,(0:E)) v q) ≤ _
  rw [hv]
  have hr : (∑ j, a j^2)*(∑ j, tubeBasePair H b (α j) (α j) q) =
      H q*((∑ j, a j^2)*(∑ j, inverseMatrixPair (tubeBaseMatrix H q b)
        (fun i => dirDeriv (b i,(0:E)) (α j) q) (fun i => dirDeriv (b i,(0:E)) (α j) q))) := by
    change (∑ j, a j^2)*(∑ j, H q*inverseMatrixPair (tubeBaseMatrix H q b)
      (fun i => dirDeriv (b i,(0:E)) (α j) q) (fun i => dirDeriv (b i,(0:E)) (α j) q)) = _
    rw [← Finset.mul_sum]
    ring
  rw [hr]
  exact hm

end TubeCombination

/- The manuscript's positive base orthant. -/
def positiveOrthant (k : ℕ) : Set (Space k) := {s | ∀ i, 0 < s i}

def logSpace {k : ℕ} (s : Space k) : Space k :=
  (EuclideanSpace.equiv (Fin k) ℝ).symm (fun i => Real.log (s i))

def expSpace {k : ℕ} (s : Space k) : Space k :=
  (EuclideanSpace.equiv (Fin k) ℝ).symm (fun i => Real.exp (s i))

@[simp] lemma logSpace_apply {k : ℕ} (s : Space k) (i : Fin k) : logSpace s i = Real.log (s i) := rfl
@[simp] lemma expSpace_apply {k : ℕ} (s : Space k) (i : Fin k) : expSpace s i = Real.exp (s i) := rfl

lemma isOpen_positiveOrthant (k : ℕ) : IsOpen (positiveOrthant k) := by
  change IsOpen {s : Space k | ∀ i, 0 < s i}
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (EuclideanSpace.proj i).continuous

lemma expSpace_mem_positive {k : ℕ} (s : Space k) : expSpace s ∈ positiveOrthant k :=
  fun index => Real.exp_pos (s index)

@[simp] lemma logSpace_expSpace {k : ℕ} (s : Space k) : logSpace (expSpace s) = s := by
  ext i
  simp

lemma expSpace_logSpace {k : ℕ} {s : Space k} (hs : s ∈ positiveOrthant k) :
    expSpace (logSpace s) = s := by
  ext i
  exact Real.exp_log (hs i)

lemma contDiff_expSpace {k : ℕ} : ContDiff ℝ ∞ (expSpace : Space k → Space k) := by
  apply (EuclideanSpace.equiv (Fin k) ℝ).symm.contDiff.comp
  exact contDiff_pi.mpr fun i => (EuclideanSpace.proj i).contDiff.exp

lemma contDiffAt_logSpace {k : ℕ} {s : Space k} (hs : s ∈ positiveOrthant k) :
    ContDiffAt ℝ ∞ logSpace s := by
  apply (EuclideanSpace.equiv (Fin k) ℝ).symm.contDiff.contDiffAt.comp
  exact contDiffAt_pi.mpr fun i => (EuclideanSpace.proj i).contDiff.contDiffAt.log (hs i).ne'

/- Extension by zero of a compact test in logarithmic coordinates; a negative
coordinate must not be silently sent through Real.log. -/
def logPullback {k : ℕ} (φ : Space k → ℝ) (s : Space k) : ℝ :=
  @ite ℝ (s ∈ positiveOrthant k) (Classical.propDecidable _) (φ (logSpace s)) 0

lemma logPullback_of_positive {k : ℕ} (φ : Space k → ℝ) {s : Space k}
    (hs : s ∈ positiveOrthant k) : logPullback φ s = φ (logSpace s) := ite_eq_left hs

lemma logPullback_eventuallyEq {k : ℕ} (φ : Space k → ℝ) {s : Space k}
    (hs : s ∈ positiveOrthant k) : logPullback φ =ᶠ[nhds s] φ ∘ logSpace := by
  filter_upwards [(isOpen_positiveOrthant k).mem_nhds hs] with x hx
  exact logPullback_of_positive φ hx

lemma support_logPullback_subset {k : ℕ} (φ : Space k → ℝ) :
    Function.support (logPullback φ) ⊆ expSpace '' tsupport φ := by
  intro s hs
  have hp : s ∈ positiveOrthant k := by
    by_contra hn
    exact hs (ite_eq_right hn)
  refine ⟨logSpace s,subset_closure ?_,expSpace_logSpace hp⟩
  change φ (logSpace s) ≠ 0
  change logPullback φ s ≠ 0 at hs
  simpa only [logPullback_of_positive φ hp] using hs

lemma tsupport_logPullback_subset {k : ℕ} {φ : Space k → ℝ} (hc : HasCompactSupport φ) :
    tsupport (logPullback φ) ⊆ expSpace '' tsupport φ :=
  closure_minimal (support_logPullback_subset φ) (hc.isCompact.image contDiff_expSpace.continuous).isClosed

lemma hasCompactSupport_logPullback {k : ℕ} {φ : Space k → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (logPullback φ) :=
  (hc.isCompact.image contDiff_expSpace.continuous).of_isClosed_subset isClosed_closure
    (tsupport_logPullback_subset hc)

lemma contDiff_logPullback {k : ℕ} {φ : Space k → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) : ContDiff ℝ ∞ (logPullback φ) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : s ∈ positiveOrthant k
  · exact (hφ.contDiffAt.comp s (contDiffAt_logSpace hs)).congr_of_eventuallyEq
      (logPullback_eventuallyEq φ hs)
  · have hn : s ∉ expSpace '' tsupport φ := by
      rintro ⟨x,_,rfl⟩
      exact hs (expSpace_mem_positive x)
    have he : logPullback φ =ᶠ[nhds s] (fun _ => 0) := by
      filter_upwards [(hc.isCompact.image contDiff_expSpace.continuous).isClosed.isOpen_compl.mem_nhds hn] with x hx
      by_contra hzero
      exact hx (support_logPullback_subset φ hzero)
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma tsupport_logPullback_subset_logDomain {k : ℕ} {φ : Space k → ℝ} {D : Set (Space k)}
    (hD : D ⊆ positiveOrthant k) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ logSpace '' D) :
    tsupport (logPullback φ) ⊆ D := by
  intro s hsp
  obtain ⟨x,hx,rfl⟩ := tsupport_logPullback_subset hc hsp
  obtain ⟨y,hy,rfl⟩ := hs hx
  simpa only [expSpace_logSpace (hD hy)] using hy

end AffineBernstein
end

end OAI
