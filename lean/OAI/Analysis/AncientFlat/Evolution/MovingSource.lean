import OAI.Analysis.AncientFlat.Evolution.SourceEvolution
import OAI.Analysis.AncientFlat.Evolution.MovingCoefficients
import OAI.Analysis.AncientFlat.Evolution.DilationContinuity

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian Topology
namespace ParametrixDilation
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
lemma continuous_dil_joint : Continuous (fun p : ℝ × C₀(V,ℂ) => dil p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact tendsto_dil_apply continuousAt_fst continuousAt_snd
lemma holder_dil {H γ : ℝ} (_hH : 0≤H) (u : C₀(V,ℂ))
    (hu : ∀ x y, ‖u x-u y‖≤H*‖x-y‖^γ) (s : ℝ) (x y : V) :
    ‖dil s u x-dil s u y‖≤(H*Real.exp (-s/4)^γ)*‖x-y‖^γ := by
  calc
    _≤H*‖Real.exp (-s/4) • x-Real.exp (-s/4) • y‖^γ := hu _ _
    _=_ := by
      rw [←smul_sub,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le,
        Real.mul_rpow (Real.exp_pos _).le (norm_nonneg _)]
      ring
end ParametrixDilation
namespace FlatSimilarity
open ParametrixDilation ParametrixEvolution
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
lemma continuous_movingSource (f : ℝ →ᵇ C₀(V,ℂ)) :
    Continuous (fun t => dil (-unitClamp t) (f t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact tendsto_dil_apply (unitClamp_lipschitz.continuous.continuousAt.neg) f.continuous.continuousAt
def movingSource (f : ℝ →ᵇ C₀(V,ℂ)) : ℝ →ᵇ C₀(V,ℂ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => dil (-unitClamp t) (f t))
    (continuous_movingSource f) ‖f‖
    (fun t => (norm_dil_le _ _).trans (f.norm_coe_le_norm t))
@[simp] lemma movingSource_apply (f : ℝ →ᵇ C₀(V,ℂ)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (x : V) :
    movingSource f t x=f t (Real.exp (t/4) • x) := by
  change f t (Real.exp (- -unitClamp t/4) • x)=_
  rw [neg_neg,unitClamp_eq ht]
lemma movingSource_holder (f : ℝ →ᵇ C₀(V,ℂ)) (γ : ℝ) (hγ : 0≤γ)
    (hf : ∃ H : ℝ, 0≤H ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ x y, ‖f t x-f t y‖≤H*‖x-y‖^γ) :
    ∃ H : ℝ, 0≤H ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ x y,
      ‖movingSource f t x-movingSource f t y‖≤H*‖x-y‖^γ := by
  obtain ⟨H,hH,hf⟩ := hf
  refine ⟨H*Real.exp (1/4)^γ,by positivity,fun t ht x y => ?_⟩
  change ‖dil (-unitClamp t) (f t) x-dil (-unitClamp t) (f t) y‖≤_
  apply (holder_dil hH (f t) (hf t ht) _ x y).trans
  rw [neg_neg,unitClamp_eq ht]
  gcongr
  exact ht.2

def shiftedSource (f : ℝ →ᵇ C₀(V,ℂ)) (s : ℝ) : ℝ →ᵇ C₀(V,ℂ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => dil s (f (s+t)))
    ((dil s).continuous.comp (f.continuous.comp (continuous_const.add continuous_id))) ‖f‖
    (fun t => (norm_dil_le _ _).trans (f.norm_coe_le_norm (s+t)))
lemma shiftedSource_holder (f : ℝ →ᵇ C₀(V,ℂ)) (γ : ℝ)
    (hf : ∃ H : ℝ, 0≤H ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ x y, ‖f t x-f t y‖≤H*‖x-y‖^γ)
    {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    ∃ H : ℝ, 0≤H ∧ ∀ t ∈ Icc (0:ℝ) (1-s), ∀ x y,
      ‖shiftedSource f s t x-shiftedSource f s t y‖≤H*‖x-y‖^γ := by
  obtain ⟨H,hH,hf⟩ := hf
  refine ⟨H*Real.exp (-s/4)^γ,by positivity,fun t ht x y => ?_⟩
  apply holder_dil hH (f (s+t)) (hf _ ⟨by linarith [hs.1,ht.1],by linarith [ht.2]⟩)
lemma shifted_movingSource_zero (f : ℝ →ᵇ C₀(V,ℂ)) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    shiftedSource (movingSource f) s 0=f s := by
  apply ZeroAtInftyContinuousMap.ext
  intro x
  change movingSource f (s+0) (Real.exp (-s/4) • x)=_
  rw [add_zero,movingSource_apply f hs,smul_smul,←Real.exp_add]
  rw [show s/4 + -s/4=0 by ring,Real.exp_zero,one_smul]
end FlatSimilarity

end

end OAI
