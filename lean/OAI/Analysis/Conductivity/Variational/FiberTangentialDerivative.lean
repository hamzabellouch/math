import Mathlib
import OAI.Analysis.Conductivity.Walls.WallHomogeneous
import OAI.Analysis.Conductivity.Flux.FiberDivergenceBounds

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

omit [ProperSpace E] in
lemma wallAlong_fixed_normal (d : E) (a : ℝ) {f : E×ℝ → ℝ}
    (hf : Differentiable ℝ f) (p : E×ℝ) :
    wallAlong d (fun q : E×ℝ => f (q.1,a)) p=wallAlong d f (p.1,a) := by
  have hh := (hf (p.1,a)).hasFDerivAt.comp p
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk (hasFDerivAt_const (𝕜 := ℝ) a p))
  simp only [Function.comp_def] at hh
  rw [wallAlong,hh.fderiv]
  rfl

lemma wallAlong_fiberPrimitive (d : E) (a : ℝ) {f : E×ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (p : E×ℝ) :
    wallAlong d (fiberPrimitive a f) p=fiberPrimitive a (wallAlong d f) p := by
  have hP := wallPrimitive_smooth hf
  have hQ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun q : E×ℝ => wallPrimitive f (q.1,a)) :=
    hP.comp (contDiff_fst.prodMk contDiff_const)
  change fderiv ℝ (fun p => wallPrimitive f p-wallPrimitive f (p.1,a)) p (d,0)=_
  rw [fderiv_fun_sub (hP.differentiable (by simp) p) (hQ.differentiable (by simp) p),
    sub_apply]
  change wallAlong d (wallPrimitive f) p-wallAlong d (fun q => wallPrimitive f (q.1,a)) p=_
  rw [wallAlong_fixed_normal d a (hP.differentiable (by simp)),
    wallAlong_primitive d hf,wallAlong_primitive d hf]
  rfl

lemma compactFiberMarginal_fderiv (d : E) {a b : ℝ}
    {f : E×ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (x : E) :
    fderiv ℝ (compactFiberMarginal a b f) x d=
      compactFiberMarginal a b (wallAlong d f) x := by
  have he : compactFiberMarginal a b f=fun x => fiberPrimitive a f (x,b) := by
    funext x
    exact (fiberPrimitive_eq_integral a hf.continuous (x,b)).symm
  have hh := ((fiberPrimitive_smooth a hf).differentiable (by simp) (x,b)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const (𝕜 := ℝ) b x))
  simp only [Function.comp_def,id_eq] at hh
  rw [he,hh.fderiv]
  change wallAlong d (fiberPrimitive a f) (x,b)=_
  rw [wallAlong_fiberPrimitive d a hf,
    fiberPrimitive_eq_integral a (wallAlong_smooth d hf).continuous]
  rfl

omit [ProperSpace E] in
lemma wallAlong_compact {f : E×ℝ → ℝ} (hs : HasCompactSupport f) (d : E) :
    HasCompactSupport (wallAlong d f) := hs.fderiv_apply ℝ (d,0)

omit [ProperSpace E] in
lemma wallAlong_tsupport (d : E) (f : E×ℝ → ℝ) :
    tsupport (wallAlong d f)⊆tsupport f := tsupport_fderiv_apply_subset ℝ (d,0)

lemma fiberPrimitive_tangential_bound (d : E) {a b : ℝ} (hab : a≤b)
    {f : E×ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hv : ∀ p∈tsupport f,p.2∈Ioo a b)
    (hz : ∀ x,(∫ t in a..b,f (x,t))=0)
    {M : ℝ} (hM : 0≤M) (hbound : ∀ p,|wallAlong d f p|≤M) (p : E×ℝ) :
    |wallAlong d (fiberPrimitive a f) p|≤(b-a)*M := by
  rw [wallAlong_fiberPrimitive d a hf]
  apply fiberPrimitive_abs_bound hab (wallAlong_smooth d hf).continuous _ _ hM hbound p
  · intro q hq
    exact hv q (wallAlong_tsupport d f (subset_tsupport _ hq))
  · intro x
    change compactFiberMarginal a b (wallAlong d f) x=0
    rw [←compactFiberMarginal_fderiv d hf]
    have he : compactFiberMarginal a b f=fun _ => (0:ℝ) := funext hz
    rw [he]
    simp

end ScalarConductivity

end

end OAI
