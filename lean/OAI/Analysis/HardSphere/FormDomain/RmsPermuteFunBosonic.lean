import Mathlib
import OAI.Analysis.HardSphere.Geometry.FirstVariation
import OAI.Analysis.HardSphere.Geometry.TestVector

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
variable {N : ℕ} {L : Length} {a : ℝ}

lemma rmsPermute_fun_bosonic (f : SmoothTest N L a) (ε : ℝ) (τ : Equiv.Perm (Fin N))
    (X : Configuration N L) :
    rmsTestFun (fun σ ↦ f.permute σ) ε (permuteConfiguration τ X)=
      rmsTestFun (fun σ ↦ f.permute σ) ε X := by
  unfold rmsTestFun HilbertRegularization.regularize
  have hsum : ‖testVector (fun σ ↦ f.permute σ) (permuteConfiguration τ X)‖^2=
      ‖testVector (fun σ ↦ f.permute σ) X‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq,testVector,SmoothTest.permute,Function.comp_apply]
    exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ ↦ ‖f.toFun (permuteConfiguration σ X)‖^2)
  rw [hsum]

lemma rmsPermute_bosonic (f : SmoothTest N L a) {ε : ℝ} (hε : 0<ε) :
    bosonic (SmoothTest.rms (fun σ ↦ f.permute σ) hε).jet.1 := by
  intro τ
  let g := SmoothTest.rms (fun σ ↦ f.permute σ) hε
  have hg : (g.jet.1 : Configuration N L → ℂ)=ᵐ[volume] g.toFun := g.memLp.coeFn_toLp
  have hgt := (measurePreserving_permute τ).quasiMeasurePreserving.ae_eq_comp hg
  filter_upwards [hgt,hg] with X hX hY
  exact hX.trans ((rmsPermute_fun_bosonic f ε τ X).trans hY.symm)

lemma IsGroundVector.rayleigh_smooth_all {u : Jet N L} (hu : IsGroundVector N L a u)
    (f : SmoothTest N L a) : energy u*‖f.jet.1‖^2≤energy f.jet := by
  classical
  let e : ℕ → ℝ := fun k ↦ 1/((k:ℝ)+1)
  have he (k) : 0<e k := by dsimp [e]; positivity
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hle (k : ℕ) : energy u*‖(SmoothTest.rms (fun σ ↦ f.permute σ) (he k)).jet.1‖^2≤
      ∑ σ : Equiv.Perm (Fin N), energy (f.permute σ).jet :=
    (hu.rayleigh _ (subset_closure (Set.mem_range_self _)) (rmsPermute_bosonic f (he k))).trans
      (rmsTest_energy_le _ (he k))
  have hl := le_of_tendsto ((rmsTest_norm_limit (fun σ ↦ f.permute σ) he he0).const_mul (energy u))
    (Eventually.of_forall hle)
  have hn (σ : Equiv.Perm (Fin N)) : ‖(f.permute σ).jet.1‖=‖f.jet.1‖ := by
    rw [f.jet_permute]
    exact Lp.norm_compMeasurePreserving _ _
  simp only [hn] at hl
  simp only [SmoothTest.jet_permute,energy_permutationJet,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hl
  have hc : 0<(Fintype.card (Equiv.Perm (Fin N)) : ℝ) := by exact_mod_cast Fintype.card_pos
  nlinarith

lemma IsGroundVector.rayleigh_all {u : Jet N L} (hu : IsGroundVector N L a u)
    (v : Jet N L) (hv : v∈dirichletDomain N L a) : energy u*‖v.1‖^2≤energy v := by
  have hc : IsClosed {w : Jet N L | energy u*‖w.1‖^2≤energy w} := by
    apply isClosed_le (continuous_const.mul (continuous_fst.norm.pow 2))
    exact continuous_finsetSum _ (fun p _ ↦ ((continuous_apply p).comp continuous_snd).norm.pow 2)
  apply closure_minimal ?_ hc hv
  rintro _ ⟨f,rfl⟩
  exact hu.rayleigh_smooth_all f
end HardSphere

end

end OAI
