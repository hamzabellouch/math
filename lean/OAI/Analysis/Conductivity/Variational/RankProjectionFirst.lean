import Mathlib
import OAI.Analysis.Conductivity.Fourier.UndoAngularWeakPair

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Matrix

lemma TwoFieldRankRegular.projectFirst {u : Coord3 → Fin 2 → ℝ} {O : Set Coord3}
    (hO : IsOpen O) (hs : ContDiffOn ℝ (↑(⊤ : ℕ∞)) u O)
    (h : TwoFieldRankRegular u O) :
    TwoFieldRankRegular (fun x => ![u x 0,0]) O := by
  rcases h with h|h|⟨κ,hκ⟩
  · right; left
    have hs0 : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => u x 0) O :=
      (contDiff_apply ℝ ℝ (0:Fin 2)).comp_contDiffOn hs
    refine ⟨fun x => u x 0,![1,0],0,hs0,⟨0,by simp⟩,?_,?_⟩
    · intro x hx hz
      have hd := ((hs.differentiableOn (by simp)) x hx).differentiableAt (hO.mem_nhds hx)
      have he := ((ContinuousLinearMap.proj (0:Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
      have hn := (h x hx).ne_zero (0:Fin 2)
      apply hn
      ext i
      have hi := congrArg (fun D : Coord3 →L[ℝ] ℝ => D (Pi.single i 1)) hz
      change fderiv ℝ (fun y => u y 0) x = _ at he
      rw [he] at hi
      exact hi
    · intro x hx j
      fin_cases j <;> simp
  · obtain ⟨v,l,κ,hv,hl,hd,he⟩ := h
    by_cases hl0 : l 0=0
    · right; right
      refine ⟨![κ 0,0],?_⟩
      intro x hx
      ext j
      fin_cases j <;> simp [he x hx,hl0]
    · right; left
      refine ⟨v,![l 0,0],![κ 0,0],hv,⟨0,hl0⟩,hd,?_⟩
      intro x hx j
      fin_cases j <;> simp [he x hx]
  · right; right
    exact ⟨![κ 0,0],fun x hx => by dsimp only; rw [hκ x hx]⟩

lemma RegularPatch.projectFirst {u : Coord3 → Fin 2 → ℝ}
    {A : Coord3 → Symmetric3} {O : Set Coord3} (h : RegularPatch u A O) :
    RegularPatch (fun x => ![u x 0,0]) A O := by
  refine ⟨h.1,?_,h.2.2.1,h.2.2.2.projectFirst h.1 h.2.1⟩
  apply contDiffOn_pi.mpr
  intro j
  fin_cases j
  · change ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => u x 0) O
    exact (contDiff_apply ℝ ℝ (0:Fin 2)).comp_contDiffOn h.2.1
  · exact contDiffOn_const

lemma mem_regularRegion_projectFirst {u : Coord3 → Fin 2 → ℝ}
    {A : Coord3 → Symmetric3} {U : Set Coord3} {x : Coord3}
    (h : x∈regularRegion u A U) :
    x∈regularRegion (fun y => ![u y 0,0]) A U := by
  obtain ⟨O,hOU,hO,hx⟩ := mem_regularRegion_iff.mp h
  exact mem_regularRegion_iff.mpr ⟨O,hOU,hO.projectFirst,hx⟩

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma fderiv_projectFirst {u : Coord3 → Fin 2 → ℝ} {x : Coord3}
    (hu : DifferentiableAt ℝ u x) :
    gradientColumns (fderiv ℝ (fun y => ![u y 0,0]) x)=
      fun i => ![gradientColumns (fderiv ℝ u x) i 0,0] := by
  have hproj : HasFDerivAt (fun y => ![u y 0,0])
      (ContinuousLinearMap.pi (fun j : Fin 2 => if j=0 then
        (ContinuousLinearMap.proj (0:Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ u x) else 0)) x := by
    apply hasFDerivAt_pi.mpr
    intro j
    fin_cases j
    · change HasFDerivAt (fun y => u y 0) ((ContinuousLinearMap.proj (0:Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ u x)) x
      simpa only [Function.comp_def,ContinuousLinearMap.proj_apply] using ((ContinuousLinearMap.proj (0:Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp x hu.hasFDerivAt)
    · simpa using (hasFDerivAt_const (0:ℝ) x)
  rw [hproj.fderiv]
  ext i j
  fin_cases j <;> simp [gradientColumns]

namespace WeakFiniteTensorPair

def projectFirst {U : Set Coord3} (w : WeakFiniteTensorPair U) : WeakFiniteTensorPair U where
  v x := ![w.v x 0,0]
  E := w.E
  symm := w.symm
  smooth := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · change ContDiff ℝ 2 (fun x => w.v x 0)
      exact (contDiff_apply ℝ ℝ (0:Fin 2)).comp w.smooth
    · exact contDiff_const
  measurable := w.measurable
  elliptic := w.elliptic
  regular := by
    filter_upwards [w.regular] with x hx
    exact fun hxU => mem_regularRegion_projectFirst (hx hxU)
  G x i := ![w.G x i 0,0]
  flux_C1 := by
    apply contDiff_pi.mpr; intro i
    apply contDiff_pi.mpr; intro j
    fin_cases j
    · change ContDiff ℝ 1 (fun x => w.G x i 0)
      exact (contDiff_apply ℝ ℝ (0:Fin 2)).comp ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp w.flux_C1)
    · exact contDiff_const
  constitution := by
    filter_upwards [w.constitution] with x hx
    rw [fderiv_projectFirst (w.smooth.differentiable (by norm_num) x)]
    ext i j
    fin_cases j
    · exact congrFun (congrFun hx i) 0
    · change (∑ k,w.E x i k*0)=0
      simp
  weak j ψ hc hs := by
    fin_cases j
    · exact w.weak 0 ψ hc hs
    · change (∫ x,fderiv ℝ ψ.val x (0:Coord3))=0
      simp

end WeakFiniteTensorPair
end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma linearTensorPullback_refl (E : Coord3 → Mat3) :
    linearTensorPullback (ContinuousLinearEquiv.refl ℝ Coord3) E=E := by
  funext x
  change operatorMatrix (ContinuousLinearMap.id ℝ Coord3)*E x*
    (operatorMatrix (ContinuousLinearMap.id ℝ Coord3))ᵀ=E x
  rw [operatorMatrix_id,Matrix.one_mul,Matrix.transpose_one,Matrix.mul_one]

namespace WeakFiniteTensorPair

def output {U : Set Coord3} (w : WeakFiniteTensorPair U)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) (b : Fin 2 → ℝ) : WeakFiniteTensorPair U :=
  ((w.linear (ContinuousLinearEquiv.refl ℝ Coord3) Q).translate 0 b).onEq (by ext x; simp)

@[simp] lemma output_v {U : Set Coord3} (w : WeakFiniteTensorPair U)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) (b : Fin 2 → ℝ) (x : Coord3) :
    (w.output Q b).v x=Q (w.v x)+b := by
  change Q (w.v (x-0))+b=_
  rw [sub_zero]

@[simp] lemma output_E {U : Set Coord3} (w : WeakFiniteTensorPair U)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) (b : Fin 2 → ℝ) :
    (w.output Q b).E=w.E := by
  funext x
  change linearTensorPullback (ContinuousLinearEquiv.refl ℝ Coord3) w.E (x-0)=_
  rw [linearTensorPullback_refl,sub_zero]

end WeakFiniteTensorPair

def scaleSecondEquiv (L : ℝ) (hL : L≠0) : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearEquiv.piCongrRight (fun i : Fin 2 =>
    (LinearEquiv.smulOfNeZero ℝ ℝ (if i=0 then 1 else L)
      (by split_ifs; norm_num; exact hL)).toContinuousLinearEquiv)

@[simp] lemma scaleSecondEquiv_apply (L : ℝ) (hL : L≠0) (v : Fin 2 → ℝ) (i : Fin 2) :
    scaleSecondEquiv L hL v i=(if i=0 then 1 else L)*v i := rfl

end ScalarConductivity

end

end OAI
