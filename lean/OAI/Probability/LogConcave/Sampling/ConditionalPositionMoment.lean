import Mathlib
import OAI.Probability.LogConcave.Sampling.QuadraticExpectation

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical BigOperators NNReal RealInnerProductSpace

namespace Appell
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [DecidableEq ι]

lemma inverseMoment_contDiffAt {m : E → Finset ι → ℝ} {p : E}
    (hm : ∀s,ContDiffAt ℝ (⊤:ℕ∞) (fun x => m x s) p) (s : Finset ι) :
    ContDiffAt ℝ (⊤:ℕ∞) (fun x => inverseMoment (m x) s) p := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s=∅
    · subst s
      simp only [inverseMoment_empty]
      exact contDiffAt_const
    simp_rw [inverseMoment_nonempty _ hs]
    apply ContDiffAt.neg
    apply ContDiffAt.sum
    intro t ht
    exact (hm (s\t)).mul (ih t (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.mem_powerset.mp (Finset.mem_erase.mp ht).2,(Finset.mem_erase.mp ht).1⟩))

end Appell

lemma conditionalMeanScalar_joint_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2<1) {h : Point d → ℝ} (hc : Continuous h)
    (hg : Appell.HasGrowth h) (p : ℝ × Point d) (hp : p.1^2<1) :
    ContDiffAt ℝ (⊤:ℕ∞) (fun q : ℝ × Point d => conditionalMeanScalar F x r q.1 h q.2) p := by
  obtain ⟨m,hm,C,ht⟩ := hF.hasGaussianLowerTail x hr hl
  have hp' : 0 < m +(conditionalParameter p).2 := by dsimp [conditionalParameter]; positivity
  have hh := (contDiffAt_quadraticExpectation (hF.continuous_potential x r)
    hc ht hg (conditionalParameter p) hp').comp p (conditionalParameter_smooth hp)
  apply hh.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt (continuous_fst.pow 2) continuous_const).mem_nhds hp] with q hq
  exact conditional_integral_quadratic hF x hr hl hq q.2 h

def conditionalPositionMoment {d : ℕ} {ι : Type*} [DecidableEq ι]
    (F : Point d → ℝ) (x : Point d) (r : ℝ) (v : ι → Point d) (s : Finset ι)
    (p : ℝ × Point d) : ℝ :=
  conditionalMeanScalar F x r p.1 (fun z => ∏i∈s,inner ℝ (v i) z) p.2

def conditionalMixedMoment {d : ℕ} {ι : Type*} [DecidableEq ι]
    (F : Point d → ℝ) (x : Point d) (r : ℝ) (u : Point d)
    (v : ι → Point d) (s : Finset ι) (p : ℝ × Point d) : ℝ :=
  conditionalMeanScalar F x r p.1
    (fun z => (∏i∈s,inner ℝ (v i) z)*inner ℝ u (primitiveField F x r z)) p.2

lemma conditionalPositionMoment_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2<1) {ι : Type*} [DecidableEq ι]
    (v : ι → Point d) (s : Finset ι) (p : ℝ × Point d) (hp : p.1^2<1) :
    ContDiffAt ℝ (⊤:ℕ∞) (conditionalPositionMoment F x r v s) p :=
  conditionalMeanScalar_joint_smooth hF x hr hl
    (continuous_finsetProd _ (fun _ _ => continuous_const.inner continuous_id))
    (Appell.HasGrowth.prod s (fun i _ => Appell.HasGrowth.linear (innerSL ℝ (v i)))) p hp

lemma conditionalMixedMoment_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2<1) {ι : Type*} [DecidableEq ι]
    (u : Point d) (v : ι → Point d) (s : Finset ι) (p : ℝ × Point d) (hp : p.1^2<1) :
    ContDiffAt ℝ (⊤:ℕ∞) (conditionalMixedMoment F x r u v s) p :=
  conditionalMeanScalar_joint_smooth hF x hr hl
    ((continuous_finsetProd _ (fun _ _ => continuous_const.inner continuous_id)).mul
      (continuous_const.inner (primitiveField_contDiff hF x r).continuous))
    ((Appell.HasGrowth.prod s (fun i _ => Appell.HasGrowth.linear (innerSL ℝ (v i)))).mul
      (primitiveField_inner_growth hF x u hr)) p hp

end LogConcaveSampling

end

end

end

end OAI
