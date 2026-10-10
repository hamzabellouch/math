import Mathlib
import OAI.Analysis.Conductivity.Walls.ParametricWallTensors

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

lemma wallMomentAmplitude_parametric_smooth {χ η : ℝ → ℝ} (σ lam : ℝ)
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hη : ContDiff ℝ (↑(⊤:ℕ∞)) η) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : Coord3×(ℝ×ℝ) => wallMomentAmplitude χ η σ lam q.1 q.2) := by
  simp_rw [wallMomentAmplitude_sum]
  apply ContDiff.sum
  intro i _
  exact ((contDiff_apply ℝ ℝ i).comp contDiff_fst).smul
    ((wallMomentTest_smooth σ lam hχ hη i).comp contDiff_snd)

lemma wallMomentAmplitude_zero (χ η : ℝ → ℝ) (σ lam : ℝ) :
    wallMomentAmplitude χ η σ lam 0=0 := by
  funext q; simp [wallMomentAmplitude]

lemma wallMomentAmplitude_compact {χ η : ℝ → ℝ} (σ lam : ℝ)
    (hχ : HasCompactSupport χ) (hη : HasCompactSupport η) (c : Coord3) :
    HasCompactSupport (wallMomentAmplitude χ η σ lam c) ∧
      tsupport (wallMomentAmplitude χ η σ lam c)⊆tsupport χ×ˢtsupport η := by
  have hh := surface_product_compact (f:=fun s => χ s*(c ⬝ᵥ wallMomentBasis σ lam s))
    hχ.mul_right hη
  exact ⟨hh.1,hh.2.trans (prod_mono tsupport_mul_subset_left Subset.rfl)⟩

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def wallTransferFamily (χ : Box3 → ℝ) (v : P×Box3 → ℝ)
    (θ η : ℝ → ℝ) (σ lam : ℝ) (q : (P×Coord3)×Coord3) : Mat3 :=
  wallHomogeneousTensor χ (fun y => v (q.1.1,y))
    (wallMomentAmplitude θ η σ lam q.1.2) q.2

lemma wallTransferFamily_smoothOn {χ : Box3 → ℝ} {v : P×Box3 → ℝ}
    {θ η : ℝ → ℝ} (σ lam : ℝ)
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v)
    (hθ : ContDiff ℝ (↑(⊤:ℕ∞)) θ) (hη : ContDiff ℝ (↑(⊤:ℕ∞)) η)
    {V : Set P} (hV : IsOpen V)
    (hne : ∀ p∈V,∀ x∈tsupport χ,wallQuotient (wallDerivative (fun y => v (p,y))) x≠0) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (wallTransferFamily χ v θ η σ lam) ((V×ˢuniv)×ˢuniv) := by
  exact wallHomogeneousTensor_parametric_smoothOn hχ
    (hv.comp (contDiff_fst.fst.prodMk contDiff_snd))
    ((wallMomentAmplitude_parametric_smooth σ lam hθ hη).comp
      (contDiff_fst.snd.prodMk contDiff_snd))
    (hV.prod isOpen_univ) (fun p hp => hne p.1 hp.1)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
lemma wallTransferFamily_zero (χ : Box3 → ℝ) (v : P×Box3 → ℝ)
    (θ η : ℝ → ℝ) (σ lam : ℝ) (p : P) (x : Coord3) :
    wallTransferFamily χ v θ η σ lam ((p,0),x)=0 := by
  dsimp [wallTransferFamily]
  rw [wallMomentAmplitude_zero]
  change wallHomogeneousTensor χ (fun y => v (p,y)) (fun _ => 0) x=0
  rw [wallHomogeneousTensor_zero]
  rfl

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
lemma compact_parameter_nonzero_neighborhood {f : P×Box3 → ℝ} (hf : Continuous f)
    {p : P} {K : Set Box3} (hK : IsCompact K) (hne : ∀ x∈K,f (p,x)≠0) :
    ∃ V : Set P,IsOpen V ∧ p∈V ∧ ∀ q∈V,∀ x∈K,f (q,x)≠0 := by
  have hh : ∀ᶠ q in 𝓝 p,∀ x∈K,f (q,x)≠0 := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    exact hf.continuousAt.eventually_ne (hne x hx)
  obtain ⟨V,hsub,hV,hp⟩ := mem_nhds_iff.mp hh
  exact ⟨V,hV,hp,fun q hq => hsub hq⟩

end ScalarConductivity

end
end

end OAI
