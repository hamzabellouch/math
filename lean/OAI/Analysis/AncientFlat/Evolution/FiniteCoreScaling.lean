import OAI.Analysis.AncientFlat.Evolution.FiniteCoreCalculus

namespace OAI
noncomputable section
open scoped ContDiff Laplacian
namespace CompactCoreFinite
open CompactCore
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
lemma laplacian_mul (f : V → ℂ) (hf : ContDiff ℝ 2 f) (a : ℂ) :
    Δ (fun x => a*f x)=fun x => a*Δ f x := by
  funext x
  exact InnerProductSpace.laplacian_smul a (hf.contDiffAt)
omit [FiniteDimensional ℝ V] in
lemma correction_mul (f : V → ℂ) (hf : ContDiff ℝ 2 f) (a : ℂ) :
    correction (fun x => a*f x)=fun x => a*correction f x := correction_smul f hf a
lemma laplacian_sub (f g : V → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    Δ (f-g)=Δ f-Δ g := by
  funext x
  exact hf.contDiffAt.laplacian_sub
    hg.contDiffAt
lemma compact_expand (f : V → ℂ) (hf : ContDiff ℝ 4 f) (x : V) :
    compactOp f x-flatOp f x=(errorTwo f x+errorFour f x)/16 := by
  have hl := laplacian_smooth f hf
  have hc := correction_smooth f hf
  simp only [compactOp,flatOp,sphereLap,laplacian_sub _ _ hl hc,
    correction_sub _ _ hl hc,Pi.sub_apply,errorTwo,errorFour]
  ring
lemma errorTwo_scaled (f : V → ℂ) (hf : ContDiff ℝ 4 f) (q : ℝ) (x : V) :
    errorTwo (fun y => f (q • y)) x=(q:ℂ)^2*errorTwo f (q • x) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hl := laplacian_smooth f hf
  have hc := correction_smooth f hf
  have hs : ContDiff ℝ 2 (fun y => (Δ f) (q • y)) := hl.comp (by fun_prop)
  simp only [errorTwo,correction_scaled f hf2 q,laplacian_scaled _ hc q,
    laplacian_scaled f hf2 q,correction_mul _ hs ((q:ℂ)^2),correction_scaled _ hl q]
  ring
omit [FiniteDimensional ℝ V] in
lemma errorFour_scaled (f : V → ℂ) (hf : ContDiff ℝ 4 f) (q : ℝ) (x : V) :
    errorFour (fun y => f (q • y)) x=errorFour f (q • x) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  simp only [errorFour,correction_scaled f hf2 q,
    correction_scaled _ (correction_smooth f hf) q]
lemma flat_scaled (f : V → ℂ) (hf : ContDiff ℝ 4 f) (q : ℝ) (x : V) :
    flatOp (fun y => f (q • y)) x=(q:ℂ)^4*flatOp f (q • x) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hl := laplacian_smooth f hf
  have hs : ContDiff ℝ 2 (fun y => (Δ f) (q • y)) := hl.comp (by fun_prop)
  simp only [flatOp,laplacian_scaled f hf2 q,laplacian_mul _ hs ((q:ℂ)^2),
    laplacian_scaled _ hl q]
  ring

theorem compact_scaled (f : V → ℂ) (hf : ContDiff ℝ 4 f) (q : ℝ) (x : V) :
    (q:ℂ)^4*compactOp f (q • x)-flatOp (fun y => f (q • y)) x=
      (q:ℂ)^2/16*errorTwo (fun y => f (q • y)) x+
      (q:ℂ)^4/16*errorFour (fun y => f (q • y)) x := by
  rw [flat_scaled f hf q x,errorTwo_scaled f hf q x,errorFour_scaled f hf q x]
  have he := compact_expand f hf (q • x)
  linear_combination (q:ℂ)^4*he
end CompactCoreFinite

end

end OAI
