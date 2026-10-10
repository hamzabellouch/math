import OAI.Analysis.AncientFlat.Evolution.SourceDuhamel
import OAI.Analysis.AncientFlat.Evolution.MovingEvaluation

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian Topology
namespace ParametrixDilation
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
lemma fderiv_scale_apply (r : ℝ) (f : V → ℂ) (hf : Differentiable ℝ f) (x z : V) :
    fderiv ℝ (fun y => f (r • y)) x z=fderiv ℝ f (r • x) (r • z) := by
  let g : V →L[ℝ] V := r • ContinuousLinearMap.id ℝ V
  have hh := (hf (g x)).hasFDerivAt.comp x g.hasFDerivAt
  exact congrArg (fun a : V →L[ℝ] ℂ => a z) hh.fderiv
end ParametrixDilation
namespace FlatSimilarity
open ParametrixDilation ParametrixEvolution
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
lemma MovesWithSource.autonomous {Af Bf : V → ℝ} {f : ℝ →ᵇ C₀(V,ℂ)}
    {d : C₀(V,ℂ)} {u : ℝ → C₀(V,ℂ)} (hu : MovesWithSource Af Bf f d u)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    (∀ x : V, HasDerivAt (fun r => dil r (u r) x)
      (f t x-(Af x/16 : ℝ) • Δ (Δ (fun y => dil t (u t) y)) x-
        (1/2+Bf x : ℝ) • dil t (u t) x-
        (1/4 : ℝ) • (fderiv ℝ (fun y => dil t (u t) y) x x)) t) := by
  have hcd := hu.2.2.1 t ht
  have hdf : Differentiable ℝ (fun x => u t x) := hcd.differentiable (by norm_num)
  obtain ⟨p,hp,hpe⟩ := hu.2.2.2.2 t ht
  intro x
  have hy : HasDerivAt (fun r : ℝ => Real.exp (-r/4) • x)
      ((-1/4*Real.exp (-t/4)) • x) t := by
    have hh := ((hasDerivAt_id t).neg.div_const 4).exp
    change HasDerivAt (fun r : ℝ => Real.exp (-r/4)) (Real.exp (-t/4)*(-1/4)) t at hh
    convert hh.smul_const x using 1; try rfl
    congr 1
    ring
  have hh := hasDerivAt_moving_eval hp hy (hdf (Real.exp (-t/4) • x))
  change HasDerivAt (fun r => u r (Real.exp (-r/4) • x)) _ t
  convert hh using 1 <;> try rfl
  rw [hpe]
  have he : Real.exp (t/4) • Real.exp (-t/4) • x=x := by
    rw [smul_smul,←Real.exp_add,show t/4+-t/4=0 by ring,Real.exp_zero,one_smul]
  rw [he]
  change f t x-(Af x/16 : ℝ) • Δ (Δ (fun y => u t (Real.exp (-t/4) • y))) x-
    (1/2+Bf x : ℝ) • u t (Real.exp (-t/4) • x)-
    (1/4 : ℝ) • (fderiv ℝ (fun y => u t (Real.exp (-t/4) • y)) x x)=_
  rw [bilaplacian_scale _ _ hcd,exp_quarter_four,fderiv_scale_apply _ _ hdf]
  simp only [mul_smul,ContinuousLinearMap.map_smul_of_tower]
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_ofNat,Complex.ofReal_neg]
  ring_nf
  rfl
end FlatSimilarity

end

end OAI
