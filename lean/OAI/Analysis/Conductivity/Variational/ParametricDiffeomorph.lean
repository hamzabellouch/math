import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology

section Slice
variable {P E : Type*} [TopologicalSpace P] [TopologicalSpace E]

lemma fiberInverse_fst (Y : OpenPartialHomeomorph (P×E) (P×E))
    (hY : ∀ p x,(Y (p,x)).1=p) {p : P} {y : E} (hy : (p,y)∈Y.target) :
    (Y.symm (p,y)).1=p := by
  have he := congrArg Prod.fst (Y.right_inv hy)
  rw [hY] at he
  exact he

def fiberSlice (Y : OpenPartialHomeomorph (P×E) (P×E))
    (hY : ∀ p x,(Y (p,x)).1=p) (p : P) : OpenPartialHomeomorph E E where
  toFun x := (Y (p,x)).2
  invFun y := (Y.symm (p,y)).2
  source := {x | (p,x)∈Y.source}
  target := {y | (p,y)∈Y.target}
  map_source' := by
    intro x hx
    have he : (p,(Y (p,x)).2)=Y (p,x) := Prod.ext (hY p x).symm rfl
    change (p,(Y (p,x)).2)∈Y.target
    rw [he]; exact Y.map_source hx
  map_target' := by
    intro y hy
    have he : (p,(Y.symm (p,y)).2)=Y.symm (p,y) := Prod.ext (fiberInverse_fst Y hY hy).symm rfl
    change (p,(Y.symm (p,y)).2)∈Y.source
    rw [he]; exact Y.map_target hy
  left_inv' := by
    intro x hx
    have he : (p,(Y (p,x)).2)=Y (p,x) := Prod.ext (hY p x).symm rfl
    rw [he,Y.left_inv hx]
  right_inv' := by
    intro y hy
    have he : (p,(Y.symm (p,y)).2)=Y.symm (p,y) := Prod.ext (fiberInverse_fst Y hY hy).symm rfl
    rw [he,Y.right_inv hy]
  open_source := Y.open_source.preimage (continuous_const.prodMk continuous_id)
  open_target := Y.open_target.preimage (continuous_const.prodMk continuous_id)
  continuousOn_toFun := continuous_snd.continuousOn.comp
    (Y.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hx => hx))
    (fun _ _ => mem_univ _)
  continuousOn_invFun := continuous_snd.continuousOn.comp
    (Y.symm.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hx => hx))
    (fun _ _ => mem_univ _)
end Slice

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_parametric_diffeomorph
    {φ : P×E → E} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (p : P) (x : E)
    (L : E ≃L[ℝ] E)
    (hL : fderiv ℝ (fun y => φ (p,y)) x=(L : E →L[ℝ] E))
    {U : Set (P×E)} (hU : IsOpen U) (hpx : (p,x)∈U) :
    ∃ Y : OpenPartialHomeomorph (P×E) (P×E),
      (p,x)∈Y.source ∧ Y.source⊆U ∧
      (∀ q y,Y (q,y)=(q,φ (q,y))) ∧
      ContDiff ℝ (↑(⊤:ℕ∞)) Y ∧ ContDiffOn ℝ (↑(⊤:ℕ∞)) Y.symm Y.target := by
  let D := fderiv ℝ φ (p,x)
  let F : P×E → P×E := fun q => (q.1,φ q)
  have hF : ContDiff ℝ (↑(⊤:ℕ∞)) F := contDiff_fst.prodMk hφ
  have hD : D.comp (ContinuousLinearMap.inr ℝ P E)=(L : E →L[ℝ] E) := by
    have hd := (hφ.differentiable (by simp) (p,x)).hasFDerivAt.comp x
      ((hasFDerivAt_const p x).prodMk (hasFDerivAt_id x))
    have he := hd.fderiv
    change fderiv ℝ (fun y => φ (p,y)) x=D.comp (ContinuousLinearMap.inr ℝ P E) at he
    exact he.symm.trans hL
  let D₀ : P×E →L[ℝ] P×E := (ContinuousLinearMap.fst ℝ P E).prod D
  have hdF : HasFDerivAt F D₀ (p,x) := hasFDerivAt_fst.prodMk
    ((hφ.differentiable (by simp) (p,x)).hasFDerivAt)
  have hsurj : Function.Surjective D₀ := by
    rintro ⟨a,b⟩
    refine ⟨(a,L.symm (b-D (a,0))),?_⟩
    change (a,D (a,L.symm (b-D (a,0))))=(a,b)
    apply Prod.ext
    · rfl
    change D (a,L.symm (b-D (a,0)))=b
    have he : (a,L.symm (b-D (a,0)))=(a,0)+(0,L.symm (b-D (a,0))) := by simp
    rw [he,map_add]
    have hh := congrArg (fun (A : E →L[ℝ] E) => A (L.symm (b-D (a,0)))) hD
    change D (0,L.symm (b-D (a,0)))=L (L.symm (b-D (a,0))) at hh
    rw [hh,L.apply_symm_apply]
    abel
  let e : (P×E) ≃L[ℝ] (P×E) := (LinearEquiv.ofBijective D₀.toLinearMap
    ⟨LinearMap.injective_iff_surjective.mpr hsurj,hsurj⟩).toContinuousLinearEquiv
  have he : (e : P×E →L[ℝ] P×E)=D₀ := rfl
  have hde : HasFDerivAt F (e : P×E →L[ℝ] P×E) (p,x) := he.symm ▸ hdF
  let Y₀ := hF.contDiffAt.toOpenPartialHomeomorph F hde (by simp)
  let V := U∩{q | IsUnit (fderiv ℝ F q)}
  have hV : IsOpen V := hU.inter (Units.isOpen.preimage (hF.continuous_fderiv (by simp)))
  have hpV : (p,x)∈V := by
    refine ⟨hpx,?_⟩
    change IsUnit (fderiv ℝ F (p,x))
    rw [hde.fderiv]
    exact ⟨e.toUnit,rfl⟩
  let Y := Y₀.restr V
  have heq : (Y : P×E → P×E)=F := rfl
  have hs : Y.source=Y₀.source∩V := by
    simp only [Y,OpenPartialHomeomorph.restr_source,hV.interior_eq]
  refine ⟨Y,?_,?_,fun _ _ => rfl,heq ▸ hF,?_⟩
  · rw [hs]
    exact ⟨hF.contDiffAt.mem_toOpenPartialHomeomorph_source hde (by simp),hpV⟩
  · rw [hs]; exact fun _ hx => hx.2.1
  · intro y hy
    have hx := (hs ▸ Y.map_target hy).2.2
    obtain ⟨v,hv⟩ := hx
    let A : (P×E) ≃L[ℝ] (P×E) := ContinuousLinearEquiv.ofUnit v
    have hA : (A : P×E →L[ℝ] P×E)=fderiv ℝ Y (Y.symm y) := by
      change (v : P×E →L[ℝ] P×E)=_
      simpa only [heq] using hv
    have hd : HasFDerivAt Y (A : P×E →L[ℝ] P×E) (Y.symm y) := by
      rw [hA,heq]
      exact (hF.differentiable (by simp) _).hasFDerivAt
    exact (Y.contDiffAt_symm hy hd (heq ▸ hF.contDiffAt)).contDiffWithinAt

end ScalarConductivity

end

end OAI
