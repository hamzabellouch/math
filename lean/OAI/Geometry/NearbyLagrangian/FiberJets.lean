import Mathlib
import OAI.Geometry.NearbyLagrangian.Phase

namespace OAI

/-! Triangular regular systems and fiber jet coordinates. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport

open ContinuousLinearMap
open scoped Topology ContDiff InnerProductSpace

section Triangular

variable {E W A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup A] [NormedSpace ℝ A]

def triangularSystem (B : E × W → A) (a : E × W → E) (s : E × E → E)
    (q : (E × W) × (E × E)) : A × (E × E) :=
  (B q.1, q.2.1 - a q.1, q.2.2 + s (q.2.2,q.2.1) - q.1.1)

def triangularDerivative (B' : E × W →L[ℝ] A) (a' : E × W →L[ℝ] E)
    (s' : E × E →L[ℝ] E) : ((E × W) × (E × E)) →L[ℝ] A × (E × E) :=
  let f := fst ℝ (E × W) (E × E)
  let p := (fst ℝ E E).comp (snd ℝ (E × W) (E × E))
  let X := (snd ℝ E E).comp (snd ℝ (E × W) (E × E))
  (B'.comp f).prod ((p - a'.comp f).prod
    (X + s'.comp (X.prod p) - (fst ℝ E W).comp f))

lemma hasFDerivAt_triangularSystem {B : E × W → A} {a : E × W → E}
    {s : E × E → E} {B' : E × W →L[ℝ] A} {a' : E × W →L[ℝ] E}
    {s' : E × E →L[ℝ] E} {q : (E × W) × (E × E)}
    (hB : HasFDerivAt B B' q.1) (ha : HasFDerivAt a a' q.1)
    (hs : HasFDerivAt s s' (q.2.2,q.2.1)) :
    HasFDerivAt (triangularSystem B a s) (triangularDerivative B' a' s') q := by
  exact (hB.comp q (hasFDerivAt_fst)).prodMk
    (((hasFDerivAt_fst.comp q hasFDerivAt_snd).sub (ha.comp q hasFDerivAt_fst)).prodMk
      (((hasFDerivAt_snd.comp q hasFDerivAt_snd).add
        (hs.comp q ((hasFDerivAt_snd.comp q hasFDerivAt_snd).prodMk
          (hasFDerivAt_fst.comp q hasFDerivAt_snd)))).sub
        (hasFDerivAt_fst.comp q hasFDerivAt_fst)))

theorem triangularDerivative_surjective {B' : E × W →L[ℝ] A}
    {a' : E × W →L[ℝ] E} {s' : E × E →L[ℝ] E}
    (hB : Function.Surjective B')
    (hs : Function.Surjective (ContinuousLinearMap.id ℝ E + s'.comp (inl ℝ E E))) :
    Function.Surjective (triangularDerivative B' a' s') := by
  rintro ⟨b,e,f⟩
  obtain ⟨v,hv⟩ := hB b
  let p := e + a' v
  obtain ⟨X,hX⟩ := hs (f + v.1 - s' (0,p))
  refine ⟨(v,p,X), ?_⟩
  change (B' v, p-a' v, X+s' (X,p)-v.1) = (b,e,f)
  have hsadd : s' (X,p) = s' (X,0) + s' (0,p) := by
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using s'.map_add (X,0) (0,p)
  have hX' : X + s' (X,0) = f + v.1 - s' (0,p) := hX
  apply Prod.ext hv
  apply Prod.ext
  · dsimp only [p]
    abel
  · rw [hsadd]
    calc
      X + (s' (X,0) + s' (0,p)) - v.1 =
          (X+s' (X,0)) + s' (0,p) - v.1 := by abel
      _ = f := by rw [hX']; abel

theorem regular_triangularSystem {B : E × W → A} {a : E × W → E}
    {s : E × E → E} {q : (E × W) × (E × E)}
    (hB : DifferentiableAt ℝ B q.1) (ha : DifferentiableAt ℝ a q.1)
    (hs : DifferentiableAt ℝ s (q.2.2,q.2.1))
    (hreg : Function.Surjective (fderiv ℝ B q.1))
    (htwist : Function.Surjective
      (ContinuousLinearMap.id ℝ E + (fderiv ℝ s (q.2.2,q.2.1)).comp (inl ℝ E E))) :
    Function.Surjective (fderiv ℝ (triangularSystem B a s) q) := by
  rw [(hasFDerivAt_triangularSystem hB.hasFDerivAt ha.hasFDerivAt hs.hasFDerivAt).fderiv]
  exact triangularDerivative_surjective hreg htwist

def supportedCoordinates : (E × (W × (E × E))) ≃L[ℝ] ((E × W) × (E × E)) where
  toFun q := ((q.1+q.2.2.1,q.2.1),(q.2.2.2,q.1))
  invFun q := (q.2.2,q.1.2,q.1.1-q.2.2,q.2.1)
  map_add' q r := by
    apply Prod.ext
    · apply Prod.ext
      · change q.1+r.1+(q.2.2.1+r.2.2.1) = (q.1+q.2.2.1)+(r.1+r.2.2.1)
        abel
      · rfl
    · rfl
  map_smul' t q := by ext <;> simp [smul_add]
  left_inv q := by ext <;> simp
  right_inv q := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end Triangular

section FiberDerivatives

variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup W] [NormedSpace ℝ W]

def fiberJetCoordinates :
    (W × (E × E) →L[ℝ] ℝ) ≃L[ℝ] ((W →L[ℝ] ℝ) × (E × E)) :=
  (coprodEquivL (𝕜 := ℝ) (E := W) (F := E × E) (G := ℝ) ℝ).symm.trans
    ((ContinuousLinearEquiv.refl ℝ (W →L[ℝ] ℝ)).prodCongr
      ((coprodEquivL (𝕜 := ℝ) (E := E) (F := E) (G := ℝ) ℝ).symm.trans
        (((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.trans
          (ContinuousLinearEquiv.neg ℝ)).prodCongr
          (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv)))

def fiberDifferential (G : E × (W × (E × E)) → ℝ)
    (q : E × (W × (E × E))) : W × (E × E) →L[ℝ] ℝ :=
  (fderiv ℝ G q).comp (inr ℝ E (W × (E × E)))

omit [CompleteSpace E] in
lemma fiberDifferential_congr {G H : E × (W × (E × E)) → ℝ}
    {q : E × (W × (E × E))} (h : G =ᶠ[𝓝 q] H) :
    fiberDifferential G =ᶠ[𝓝 q] fiberDifferential H :=
  h.fderiv.mono fun _ he => congrArg (fun a => a.comp (inr ℝ E (W × (E × E)))) he

lemma fiberJetCoordinates_apply (L : W × (E × E) →L[ℝ] ℝ) :
    fiberJetCoordinates (E := E) (W := W) L =
      (L.comp (inl ℝ W (E × E)),
        -(InnerProductSpace.toDual ℝ E).symm
          (L.comp ((inr ℝ W (E × E)).comp (inl ℝ E E))),
        (InnerProductSpace.toDual ℝ E).symm
          (L.comp ((inr ℝ W (E × E)).comp (inr ℝ E E)))) := by
  rfl

lemma fiberJetCoordinates_fiberDifferential {G : E × (W × (E × E)) → ℝ}
    {q : E × (W × (E × E))} (hG : DifferentiableAt ℝ G q) :
    fiberJetCoordinates (fiberDifferential G q) =
      (fderiv ℝ (fun w => G (q.1,w,q.2.2.1,q.2.2.2)) q.2.1,
        -(InnerProductSpace.toDual ℝ E).symm
          (fderiv ℝ (fun z => G (q.1,q.2.1,z,q.2.2.2)) q.2.2.1),
        (InnerProductSpace.toDual ℝ E).symm
          (fderiv ℝ (fun p => G (q.1,q.2.1,q.2.2.1,p)) q.2.2.2)) := by
  have hv : DifferentiableAt ℝ (fun v : W × (E × E) => G (q.1,v)) q.2 :=
    hG.comp q.2 (differentiableAt_const q.1 |>.prodMk differentiableAt_id)
  have hV := hG.hasFDerivAt.comp q.2 (f := fun v => (q.1,v))
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)
  have hw := hv.hasFDerivAt.comp q.2.1 (f := fun w => (w,q.2.2))
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.2.1 q.2.2)
  have hz := hv.hasFDerivAt.comp q.2.2.1 (f := fun z => (q.2.1,z,q.2.2.2))
    ((hasFDerivAt_prodMk_right (𝕜 := ℝ) q.2.1 q.2.2).comp q.2.2.1
      (f := fun z => (z,q.2.2.2)) (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.2.2.1 q.2.2.2))
  have hp := hv.hasFDerivAt.comp q.2.2.2 (f := fun p => (q.2.1,q.2.2.1,p))
    ((hasFDerivAt_prodMk_right (𝕜 := ℝ) q.2.1 q.2.2).comp q.2.2.2
      (f := fun p => (q.2.2.1,p)) (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.2.2.1 q.2.2.2))
  simp only [Function.comp_def] at hV hw hz hp
  rw [fiberJetCoordinates_apply, hw.fderiv, hz.fderiv, hp.fderiv, hV.fderiv]
  rfl

def totalPhase (F : E × W → ℝ) (σ : E × E → ℝ) (κ : E → W → E → ℝ)
    (q : E × (W × (E × E))) : ℝ :=
  shiftedPhase F σ κ q.1 q.2.1 q.2.2.1 q.2.2.2

def mixedDisplacement (σ : E × E → ℝ) (q : E × E) : E :=
  (InnerProductSpace.toDual ℝ E).symm (verticalDifferential σ q.1 q.2)

lemma innerSL_mixedDisplacement (σ : E × E → ℝ) (X p : E) :
    innerSL ℝ (mixedDisplacement σ (X,p)) = verticalDifferential σ X p :=
  (InnerProductSpace.toDual ℝ E).apply_symm_apply _

end FiberDerivatives

end NearbyLagrangian.Transport

end

end OAI
