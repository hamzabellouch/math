import Mathlib
import OAI.Analysis.MatrixSigning.Potential.UnpackKkt
import OAI.Analysis.MatrixSigning.Potential.TightSystem
import OAI.Analysis.MatrixSigning.Calculus.LocalMinSecondNonnegative

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ}

private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

local instance valueFeasibleOperatorNormedAddCommGroup :
    NormedAddCommGroup (H d →L[ℝ] H d) := inferInstance
local instance valueFeasibleOperatorNormedSpace : NormedSpace ℝ (H d →L[ℝ] H d) := inferInstance
local instance valueFeasiblePairNormedAddCommGroup : NormedAddCommGroup (Pair d) := inferInstance
local instance valueFeasiblePairNormedSpace : NormedSpace ℝ (Pair d) := inferInstance

lemma value_le_feasible [NeZero d] (ε : ℝ) (hε : 0 ≤ ε) (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d) (z : Point d) (hz : z ∈ feasible S η) :
    value ε S η ≤ objective ε z := by
  have hb : BddBelow (objective ε '' feasible S η) := by
    refine ⟨0,?_⟩
    rintro r ⟨w,hw,rfl⟩
    obtain ⟨ht,hX,hY⟩ := trace_bounds_of_feasible S η hη hw
    simp only [objective,realTrace_add]
    exact add_nonneg ht (mul_nonneg hε (add_nonneg hX hY))
  exact csInf_le hb ⟨z,hz,rfl⟩

lemma tightSystem_eq_neg_residual (t : ℝ) (S : H d) (η : H d →L[ℝ] H d) (z : Pair d) :
    tightSystem t S η z = -residual S η (t,z) := by
  apply Prod.ext <;> change _ = -_ <;> dsimp only [tightSystem,residual] <;> abel

theorem exists_smooth_feasible_majorant [NeZero d]
    (ε : ℝ) (hε : 0 < ε) (S : ℝ → H d) (η : ℝ → (H d →L[ℝ] H d)) (a : ℝ)
    (hS : ContDiffAt ℝ ∞ S a) (hη : ContDiffAt ℝ ∞ η a)
    (hηpos : ∀ A ∈ psdCone d, η a A ∈ psdCone d) (hηsym : SymmetricMap (η a))
    {K : ℝ} (hS₁ : -K • (Hermitian.one : H d) ≤ S a) (hS₂ : S a ≤ K • (Hermitian.one : H d))
    (z : Point d) (hz : z ∈ feasible (S a) (η a))
    (hmin : ∀ w ∈ feasible (S a) (η a), objective ε z ≤ objective ε w) :
    ∃ g : ℝ → Pair d, g a = z.2 ∧ ContDiffAt ℝ ∞ g a ∧
      ∀ᶠ s in 𝓝 a, (z.1,g s) ∈ feasible (S s) (η s) ∧
        residual (S s) (η s) (z.1,g s) = 0 := by
  obtain ⟨P,Q,hP,hQ,_,_,_,hPX,hQY,ht,_,_⟩ :=
    kkt (S a) (η a) hηpos hηsym hε hS₁ hS₂ z hz hmin
  obtain ⟨J,hJ,_⟩ := linConstraint_positive_inverse z.2.1 z.2.2 P Q (η a)
    hηpos hz.1.1 hz.1.2 hP hQ hε hPX hQY
  have hJ' : J.toContinuousLinearMap = linConstraint z.2.1 z.2.2 (η a) := by
    apply ContinuousLinearMap.ext
    intro v
    exact hJ v
  obtain ⟨f,hf,hfc,hfe⟩ := exists_smooth_tight_branch z.1 (S a,η a) z.2 hz.1.1 hz.1.2 J hJ'
  let g : ℝ → Pair d := fun s => f (S s,η s)
  have hg : g a = z.2 := hf
  have hgc : ContDiffAt ℝ ∞ g a := hfc.comp a (hS.prodMk hη)
  have hge : ∀ᶠ s in 𝓝 a, residual (S s) (η s) (z.1,g s) = 0 := by
    filter_upwards [(hS.continuousAt.prodMk hη.continuousAt).eventually hfe] with s hs
    have ht' : residual (S a) (η a) (z.1,z.2) = 0 := ht
    simpa only [tightSystem_eq_neg_residual,ht',neg_zero,neg_eq_zero] using hs
  have hXg : ∀ᶠ s in 𝓝 a, (g s).1 ∈ pd d := by
    apply hgc.fst.continuousAt.eventually
    apply isOpen_pd.mem_nhds
    change (g a).1 ∈ pd d
    rw [hg]
    exact hz.1.1
  have hYg : ∀ᶠ s in 𝓝 a, (g s).2 ∈ pd d := by
    apply hgc.snd.continuousAt.eventually
    apply isOpen_pd.mem_nhds
    change (g a).2 ∈ pd d
    rw [hg]
    exact hz.1.2
  refine ⟨g,hg,hgc,?_⟩
  filter_upwards [hge,hXg,hYg] with s hs hx hy
  refine ⟨⟨⟨hx,hy⟩,?_,?_⟩,hs⟩ <;> rw [hs] <;> exact le_rfl

theorem value_derivatives_majorant [NeZero d]
    (ε : ℝ) (hε : 0 < ε) (S : ℝ → H d) (η : ℝ → (H d →L[ℝ] H d)) (a : ℝ)
    (hS : ContDiffAt ℝ ∞ S a) (hη : ContDiffAt ℝ ∞ η a)
    (hηpos : ∀ᶠ s in 𝓝 a, ∀ A ∈ psdCone d, η s A ∈ psdCone d)
    (hηsym : ∀ᶠ s in 𝓝 a, SymmetricMap (η s))
    {K : ℝ} (hS₁ : -K • (Hermitian.one : H d) ≤ S a) (hS₂ : S a ≤ K • (Hermitian.one : H d))
    (z : Point d) (hz : z ∈ feasible (S a) (η a))
    (hmin : ∀ w ∈ feasible (S a) (η a), objective ε z ≤ objective ε w) :
    ∃ g : ℝ → Pair d, g a = z.2 ∧ ContDiffAt ℝ ∞ g a ∧
      (∀ᶠ s in 𝓝 a, residual (S s) (η s) (z.1,g s) = 0) ∧
      deriv (fun s => value ε (S s) (η s)) a = deriv (fun s => objective ε (z.1,g s)) a ∧
      deriv (deriv (fun s => value ε (S s) (η s))) a ≤
        deriv (deriv (fun s => objective ε (z.1,g s))) a := by
  obtain ⟨g,hg,hgc,hge⟩ := exists_smooth_feasible_majorant ε hε S η a hS hη
    hηpos.self_of_nhds hηsym.self_of_nhds hS₁ hS₂ z hz hmin
  have hv := contDiffAt_value ε hε S η a hS hη hηpos.self_of_nhds hηsym hS₁ hS₂ z hz hmin
  have ho : ContDiffAt ℝ ∞ (fun s => objective ε (z.1,g s)) a :=
    (contDiff_objective ε).contDiffAt.comp a (contDiffAt_const.prodMk hgc)
  have heq : value ε (S a) (η a) = objective ε (z.1,g a) := by
    rw [hg]
    exact value_eq_of_min ε (S a) (η a) z hz hmin
  have hle : ∀ᶠ s in 𝓝 a, value ε (S s) (η s) ≤ objective ε (z.1,g s) := by
    filter_upwards [hge,hηpos] with s hs hp
    exact value_le_feasible ε hε.le (S s) (η s) hp (z.1,g s) hs.1
  obtain ⟨hd,hdd⟩ := CurrentKS.Analysis.majorant_derivatives
    (contDiffAt_infty.mp hv 2) (contDiffAt_infty.mp ho 2) heq hle
  exact ⟨g,hg,hgc,hge.mono fun _ hs => hs.2,hd,hdd⟩

end
end CurrentKS.Variational

end OAI
