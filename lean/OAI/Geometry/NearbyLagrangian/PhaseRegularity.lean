import Mathlib
import OAI.Geometry.NearbyLagrangian.StepData
import OAI.Geometry.NearbyLagrangian.FiberJets

namespace OAI

/-! Regularity of pure and exterior phases and the cutoff transition. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport

open ContinuousLinearMap Filter
open scoped Topology ContDiff InnerProductSpace

variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [CompleteSpace E] in
lemma verticalDifferential_eq_partial {F : E × W → ℝ} {q : E × W}
    (hF : DifferentiableAt ℝ F q) :
    verticalDifferential F q.1 q.2 = fderiv ℝ (fun w => F (q.1,w)) q.2 := by
  exact ((hF.hasFDerivAt.comp q.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)).fderiv).symm

omit [CompleteSpace E] in
lemma differentiableAt_purePhase {F : E × W → ℝ} {σ : E × E → ℝ}
    {q : E × (W × (E × E))}
    (hF : DifferentiableAt ℝ F (q.1+q.2.2.1,q.2.1))
    (hσ : DifferentiableAt ℝ σ (q.1,q.2.2.2)) :
    DifferentiableAt ℝ (totalPhase F σ (fun _ _ _ => 1)) q := by
  have hs : DifferentiableAt ℝ (fun r : E × (W × (E × E)) =>
      (r.1+r.2.2.1,r.2.1)) q :=
    (differentiableAt_fst.add differentiableAt_snd.snd.fst).prodMk
      differentiableAt_snd.fst
  have hsp : DifferentiableAt ℝ (fun r : E × (W × (E × E)) => (r.1,r.2.2.2)) q :=
    differentiableAt_fst.prodMk differentiableAt_snd.snd.snd
  unfold totalPhase shiftedPhase
  simp only [one_smul]
  exact
    ((hF.comp q hs).add (hσ.comp q hsp)).sub
        (DifferentiableAt.inner ℝ
          (differentiableAt_snd.snd.fst : DifferentiableAt ℝ (fun r : E × (W × (E × E)) => r.2.2.1) q)
          (differentiableAt_snd.snd.snd : DifferentiableAt ℝ (fun r : E × (W × (E × E)) => r.2.2.2) q))

lemma purePhase_fiberDerivative {F : E × W → ℝ} {σ : E × E → ℝ}
    {q : E × (W × (E × E))}
    (hF : DifferentiableAt ℝ F (q.1+q.2.2.1,q.2.1))
    (hσ : DifferentiableAt ℝ σ (q.1,q.2.2.2)) :
    fiberJetCoordinates (fiberDifferential (totalPhase F σ (fun _ _ _ => 1)) q) =
      triangularSystem (fun v => verticalDifferential F v.1 v.2)
        (fun v => baseGradient F v.1 v.2) (mixedDisplacement σ) (supportedCoordinates q) := by
  have hF' : DifferentiableAt ℝ F (q.1 + (1:ℝ) • q.2.2.1,q.2.1) := by
    simpa only [one_smul] using hF
  have hσp := hσ.comp q.2.2.2
    (differentiableAt_const q.1 |>.prodMk differentiableAt_id)
  have hw := (hasFDerivAt_shiftedPhase_w σ q.1 q.2.1 q.2.2.1 q.2.2.2
    (κ := fun _ _ _ => 1) hF' (differentiableAt_const _)).fderiv
  have hz := (hasFDerivAt_shiftedPhase_z σ q.1 q.2.1 q.2.2.1 q.2.2.2
    (κ := fun _ _ _ => 1) hF' (differentiableAt_const _)).fderiv
  have hp := (hasFDerivAt_shiftedPhase_p F (fun _ _ _ => 1) q.1 q.2.1 q.2.2.1 q.2.2.2 hσp).fderiv
  simp only [fderiv_const_apply, smul_zero, add_zero, one_smul] at hw hz
  rw [fiberJetCoordinates_fiberDifferential (differentiableAt_purePhase hF hσ)]
  simp only [totalPhase]
  rw [hw, hz, hp, ← verticalDifferential_eq_partial hσ]
  change (verticalDifferential F (q.1+q.2.2.1) q.2.1,
      -(InnerProductSpace.toDual ℝ E).symm
        (baseDifferential F (q.1+q.2.2.1) q.2.1 - innerSL ℝ q.2.2.2),
      (InnerProductSpace.toDual ℝ E).symm
        (verticalDifferential σ q.1 q.2.2.2 - innerSL ℝ q.2.2.1)) =
    (verticalDifferential F (q.1+q.2.2.1) q.2.1,
      q.2.2.2-baseGradient F (q.1+q.2.2.1) q.2.1,
      q.1+mixedDisplacement σ (q.1,q.2.2.2)-(q.1+q.2.2.1))
  have hz' : (InnerProductSpace.toDual ℝ E).symm (innerSL ℝ q.2.2.1) = q.2.2.1 :=
    (InnerProductSpace.toDual ℝ E).symm_apply_apply _
  have hp' : (InnerProductSpace.toDual ℝ E).symm (innerSL ℝ q.2.2.2) = q.2.2.2 :=
    (InnerProductSpace.toDual ℝ E).symm_apply_apply _
  simp only [map_sub, hz', hp']
  apply Prod.ext
  · rfl
  apply Prod.ext
  · change -(baseGradient F (q.1+q.2.2.1) q.2.1 - q.2.2.2) = _
    abel_nf
  · change mixedDisplacement σ (q.1,q.2.2.2) - q.2.2.1 = _
    abel_nf

omit [CompleteSpace E] in
lemma differentiableAt_verticalDifferential {F : E × W → ℝ} {q : E × W}
    (hF : ContDiffAt ℝ ∞ F q) :
    DifferentiableAt ℝ (fun v => verticalDifferential F v.1 v.2) q := by
  have hd := (hF.fderiv_right (m := 1) (by exact WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
  exact (((compL ℝ W (E × W) ℝ).flip (inr ℝ E W)).differentiableAt.comp q hd)

lemma differentiableAt_baseGradient {F : E × W → ℝ} {q : E × W}
    (hF : ContDiffAt ℝ ∞ F q) :
    DifferentiableAt ℝ (fun v => baseGradient F v.1 v.2) q := by
  have hd := (hF.fderiv_right (m := 1) (by exact WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
  have hb : DifferentiableAt ℝ (fun v => baseDifferential F v.1 v.2) q :=
    (((compL ℝ E (E × W) ℝ).flip (inl ℝ E W)).differentiableAt.comp q hd)
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt.comp q hb

lemma differentiableAt_mixedDisplacement {σ : E × E → ℝ} {q : E × E}
    (hσ : ContDiffAt ℝ ∞ σ q) : DifferentiableAt ℝ (mixedDisplacement σ) q :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt.comp q
    (differentiableAt_verticalDifferential hσ)

theorem regular_purePhase {F : E × W → ℝ} {σ : E × E → ℝ}
    {q : E × (W × (E × E))}
    (hF : ContDiffAt ℝ ∞ F (q.1+q.2.2.1,q.2.1))
    (hσ : ContDiffAt ℝ ∞ σ (q.1,q.2.2.2))
    (hreg : Function.Surjective
      (fderiv ℝ (fun v : E × W => verticalDifferential F v.1 v.2) (q.1+q.2.2.1,q.2.1)))
    (htwist : Function.Surjective (ContinuousLinearMap.id ℝ E +
      (fderiv ℝ (mixedDisplacement σ) (q.1,q.2.2.2)).comp (inl ℝ E E))) :
    Function.Surjective (fderiv ℝ (fiberDifferential (totalPhase F σ (fun _ _ _ => 1))) q) := by
  have hB := differentiableAt_verticalDifferential hF
  have ha := differentiableAt_baseGradient hF
  have hs := differentiableAt_mixedDisplacement hσ
  have hF1 : ContDiffAt ℝ 1 F (q.1+q.2.2.1,q.2.1) := hF.of_le (by simp)
  have hσ1 : ContDiffAt ℝ 1 σ (q.1,q.2.2.2) := hσ.of_le (by simp)
  have cF : Continuous (fun r : E × (W × (E × E)) => (r.1+r.2.2.1,r.2.1)) :=
    (continuous_fst.add continuous_snd.snd.fst).prodMk continuous_snd.fst
  have cσ : Continuous (fun r : E × (W × (E × E)) => (r.1,r.2.2.2)) :=
    continuous_fst.prodMk continuous_snd.snd.snd
  have eF := (cF.continuousAt (x := q)).eventually
    ((hF1.eventually (by simp)).mono fun _ h => h.differentiableAt one_ne_zero)
  have eσ := (cσ.continuousAt (x := q)).eventually
    ((hσ1.eventually (by simp)).mono fun _ h => h.differentiableAt one_ne_zero)
  let D := triangularDerivative (fderiv ℝ (fun v : E × W => verticalDifferential F v.1 v.2)
    (q.1+q.2.2.1,q.2.1))
    (fderiv ℝ (fun v : E × W => baseGradient F v.1 v.2) (q.1+q.2.2.1,q.2.1))
    (fderiv ℝ (mixedDisplacement σ) (q.1,q.2.2.2))
  have hD : Function.Surjective D := triangularDerivative_surjective hreg htwist
  have ht := hasFDerivAt_triangularSystem hB.hasFDerivAt ha.hasFDerivAt hs.hasFDerivAt
    (q := supportedCoordinates q)
  have hi : HasFDerivAt (fun v : ((W →L[ℝ] ℝ) × (E × E)) =>
      (fiberJetCoordinates (E := E) (W := W)).symm v)
      (fiberJetCoordinates (E := E) (W := W)).symm.toContinuousLinearMap
      (triangularSystem (fun v => verticalDifferential F v.1 v.2)
        (fun v => baseGradient F v.1 v.2) (mixedDisplacement σ) (supportedCoordinates q)) :=
    (fiberJetCoordinates (E := E) (W := W)).symm.toContinuousLinearMap.hasFDerivAt
  have hc : HasFDerivAt (fun r : E × (W × (E × E)) => supportedCoordinates r)
      (supportedCoordinates (E := E) (W := W)).toContinuousLinearMap q :=
    (supportedCoordinates (E := E) (W := W)).toContinuousLinearMap.hasFDerivAt
  have hu1 : HasFDerivAt (fun r : E × (W × (E × E)) =>
      triangularSystem (fun v => verticalDifferential F v.1 v.2)
        (fun v => baseGradient F v.1 v.2) (mixedDisplacement σ) (supportedCoordinates r))
      (D.comp (supportedCoordinates (E := E) (W := W)).toContinuousLinearMap) q :=
    ht.comp q hc
  have hu := hi.comp q (g := fun v : ((W →L[ℝ] ℝ) × (E × E)) =>
      (fiberJetCoordinates (E := E) (W := W)).symm v) (f := fun r : E × (W × (E × E)) =>
      triangularSystem (fun v => verticalDifferential F v.1 v.2)
        (fun v => baseGradient F v.1 v.2) (mixedDisplacement σ) (supportedCoordinates r)) hu1
  have he : fiberDifferential (totalPhase F σ (fun _ _ _ => 1)) =ᶠ[𝓝 q]
      fun r => (fiberJetCoordinates (E := E) (W := W)).symm
        (triangularSystem (fun v => verticalDifferential F v.1 v.2)
          (fun v => baseGradient F v.1 v.2) (mixedDisplacement σ) (supportedCoordinates r)) := by
    filter_upwards [eF,eσ] with r hrF hrσ
    exact ((fiberJetCoordinates (E := E) (W := W)).eq_symm_apply).mpr
      (purePhase_fiberDerivative hrF hrσ)
  simp only [Function.comp_def] at hu
  rw [he.fderiv_eq, hu.fderiv]
  exact (fiberJetCoordinates (E := E) (W := W)).symm.surjective.comp
    (hD.comp (supportedCoordinates (E := E) (W := W)).surjective)

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport

open ContinuousLinearMap Filter
open scoped Topology ContDiff InnerProductSpace

section OutsideLinear

variable {E W A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup A] [NormedSpace ℝ A]

def outsideShift (τ : ℝ) : E × (W × (E × E)) →L[ℝ] E × W :=
  let X := fst ℝ E (W × (E × E))
  let w := (fst ℝ W (E × E)).comp (snd ℝ E (W × (E × E)))
  let z := (fst ℝ E E).comp ((snd ℝ W (E × E)).comp (snd ℝ E (W × (E × E))))
  (X + τ • z).prod w

def forgetMomentum : E × (W × (E × E)) →L[ℝ] E × (W × E) :=
  (fst ℝ E (W × (E × E))).prod
    (((fst ℝ W (E × E)).comp (snd ℝ E (W × (E × E)))).prod
      ((fst ℝ E E).comp ((snd ℝ W (E × E)).comp (snd ℝ E (W × (E × E))))))

def outsideDerivative (B' : E × W →L[ℝ] A) (a' : E × (W × E) →L[ℝ] E)
    (τ : ℝ) : E × (W × (E × E)) →L[ℝ] A × (E × E) :=
  let z := (fst ℝ E E).comp ((snd ℝ W (E × E)).comp (snd ℝ E (W × (E × E))))
  let p := (snd ℝ E E).comp ((snd ℝ W (E × E)).comp (snd ℝ E (W × (E × E))))
  (B'.comp (outsideShift τ)).prod ((p - a'.comp forgetMomentum).prod (-z))

theorem outsideDerivative_surjective {B' : E × W →L[ℝ] A}
    {a' : E × (W × E) →L[ℝ] E} {τ : ℝ} (hB : Function.Surjective B') :
    Function.Surjective (outsideDerivative B' a' τ) := by
  rintro ⟨b,e,f⟩
  obtain ⟨v,hv⟩ := hB b
  let z := -f
  let X := v.1 - τ • z
  let p := e + a' (X,v.2,z)
  refine ⟨(X,v.2,z,p), ?_⟩
  change (B' (X+τ • z,v.2), p-a' (X,v.2,z), -z) = (b,e,f)
  dsimp only [X,p,z]
  simp only [sub_add_cancel, add_sub_cancel_right, neg_neg]
  exact Prod.ext hv rfl

omit [NormedAddCommGroup A] [NormedSpace ℝ A] in
lemma hasFDerivAt_outsideShift {ζ : E → ℝ} {q : E × (W × (E × E))}
    (hζ : DifferentiableAt ℝ ζ q.1) (hz : q.2.2.1 = 0) :
    HasFDerivAt (fun r : E × (W × (E × E)) => (r.1 + ζ r.1 • r.2.2.1,r.2.1))
      (outsideShift (ζ q.1)) q := by
  have hX : HasFDerivAt (fun r : E × (W × (E × E)) => r.1)
      (fst ℝ E (W × (E × E))) q := hasFDerivAt_fst
  have hZ : HasFDerivAt (fun r : E × (W × (E × E)) => r.2.2.1)
      ((fst ℝ E E).comp ((snd ℝ W (E × E)).comp (snd ℝ E (W × (E × E))))) q :=
    hasFDerivAt_fst.comp q (hasFDerivAt_snd.comp q hasFDerivAt_snd)
  have hh := hX.add ((hζ.hasFDerivAt.comp q hX).smul hZ)
  simp only [hz, smulRight_zero, add_zero] at hh
  exact hh.prodMk (hasFDerivAt_fst.comp q hasFDerivAt_snd)

def outsideSystem (B : E × W → A) (a : E × (W × E) → E) (ζ : E → ℝ)
    (q : E × (W × (E × E))) : A × (E × E) :=
  (B (q.1 + ζ q.1 • q.2.2.1,q.2.1), q.2.2.2 - a (q.1,q.2.1,q.2.2.1), -q.2.2.1)

lemma hasFDerivAt_outsideSystem {B : E × W → A} {a : E × (W × E) → E}
    {ζ : E → ℝ} {q : E × (W × (E × E))}
    (hB : DifferentiableAt ℝ B (q.1,q.2.1))
    (ha : DifferentiableAt ℝ a (q.1,q.2.1,q.2.2.1))
    (hζ : DifferentiableAt ℝ ζ q.1) (hz : q.2.2.1 = 0) :
    HasFDerivAt (outsideSystem B a ζ)
      (outsideDerivative (fderiv ℝ B (q.1,q.2.1))
        (fderiv ℝ a (q.1,q.2.1,q.2.2.1)) (ζ q.1)) q := by
  have hB' : HasFDerivAt B (fderiv ℝ B (q.1,q.2.1)) (q.1+ζ q.1 • q.2.2.1,q.2.1) := by
    simpa only [hz, smul_zero, add_zero] using hB.hasFDerivAt
  exact (hB'.comp q (hasFDerivAt_outsideShift hζ hz)).prodMk
    (((hasFDerivAt_snd.comp q (hasFDerivAt_snd.comp q hasFDerivAt_snd)).sub
      (ha.hasFDerivAt.comp q (forgetMomentum (E := E) (W := W)).hasFDerivAt)).prodMk
      (hasFDerivAt_fst.comp q (hasFDerivAt_snd.comp q hasFDerivAt_snd)).neg)

end OutsideLinear

section OutsideFiber

variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup W] [NormedSpace ℝ W]

def outsideMomentum (F : E × W → ℝ) (ζ : E → ℝ) (v : E × (W × E)) : E :=
  ζ v.1 • baseGradient F (v.1+ζ v.1 • v.2.2) v.2.1

omit [CompleteSpace E] in
lemma differentiableAt_outsidePhase {F : E × W → ℝ} {ζ : E → ℝ}
    {q : E × (W × (E × E))}
    (hF : DifferentiableAt ℝ F (q.1+ζ q.1 • q.2.2.1,q.2.1))
    (hζ : DifferentiableAt ℝ ζ q.1) :
    DifferentiableAt ℝ (totalPhase F (fun _ => 0) (fun X _ _ => ζ X)) q := by
  have hZ : DifferentiableAt ℝ (fun r : E × (W × (E × E)) => r.2.2.1) q :=
    differentiableAt_snd.snd.fst
  have hP : DifferentiableAt ℝ (fun r : E × (W × (E × E)) => r.2.2.2) q :=
    differentiableAt_snd.snd.snd
  have hv : DifferentiableAt ℝ (fun r : E × (W × (E × E)) =>
      (r.1+ζ r.1 • r.2.2.1,r.2.1)) q :=
    (differentiableAt_fst.add ((hζ.comp q differentiableAt_fst).smul hZ)).prodMk
      differentiableAt_snd.fst
  unfold totalPhase shiftedPhase
  simp only [add_zero]
  exact (hF.comp q hv).sub (hZ.inner ℝ hP)

lemma outsidePhase_fiberDerivative {F : E × W → ℝ} {ζ : E → ℝ}
    {q : E × (W × (E × E))}
    (hF : DifferentiableAt ℝ F (q.1+ζ q.1 • q.2.2.1,q.2.1))
    (hζ : DifferentiableAt ℝ ζ q.1) :
    fiberJetCoordinates (fiberDifferential
      (totalPhase F (fun _ => 0) (fun X _ _ => ζ X)) q) =
      outsideSystem (fun v => verticalDifferential F v.1 v.2) (outsideMomentum F ζ) ζ q := by
  have hw := (hasFDerivAt_shiftedPhase_w (fun _ => 0) q.1 q.2.1 q.2.2.1 q.2.2.2
    (κ := fun X _ _ => ζ X) hF (differentiableAt_const _)).fderiv
  have hz := (hasFDerivAt_shiftedPhase_z (fun _ => 0) q.1 q.2.1 q.2.2.1 q.2.2.2
    (κ := fun X _ _ => ζ X) hF (differentiableAt_const _)).fderiv
  have hp := (hasFDerivAt_shiftedPhase_p F (σ := fun _ => 0) (fun X _ _ => ζ X)
    q.1 q.2.1 q.2.2.1 q.2.2.2 (differentiableAt_const (0:ℝ))).fderiv
  simp only [fderiv_const_apply, smul_zero, add_zero] at hw hz
  simp only [fderiv_const_apply, zero_sub] at hp
  rw [fiberJetCoordinates_fiberDifferential (differentiableAt_outsidePhase hF hζ)]
  simp only [totalPhase]
  rw [hw,hz,hp]
  have hz' : (InnerProductSpace.toDual ℝ E).symm (innerSL ℝ q.2.2.1) = q.2.2.1 :=
    (InnerProductSpace.toDual ℝ E).symm_apply_apply _
  have hp' : (InnerProductSpace.toDual ℝ E).symm (innerSL ℝ q.2.2.2) = q.2.2.2 :=
    (InnerProductSpace.toDual ℝ E).symm_apply_apply _
  simp only [map_sub, map_neg, map_smul, hz', hp']
  apply Prod.ext
  · rfl
  apply Prod.ext
  · change -(ζ q.1 • baseGradient F (q.1+ζ q.1 • q.2.2.1) q.2.1 - q.2.2.2) =
      q.2.2.2 - ζ q.1 • baseGradient F (q.1+ζ q.1 • q.2.2.1) q.2.1
    abel
  · rfl

end OutsideFiber

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport

open ContinuousLinearMap Filter
open scoped Topology ContDiff InnerProductSpace

variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma differentiableAt_outsideMomentum {F : E × W → ℝ} {ζ : E → ℝ}
    {v : E × (W × E)}
    (hF : ContDiffAt ℝ ∞ F (v.1+ζ v.1 • v.2.2,v.2.1))
    (hζ : DifferentiableAt ℝ ζ v.1) :
    DifferentiableAt ℝ (outsideMomentum F ζ) v := by
  have hs : DifferentiableAt ℝ (fun r : E × (W × E) =>
      (r.1+ζ r.1 • r.2.2,r.2.1)) v :=
    (differentiableAt_fst.add ((hζ.comp v differentiableAt_fst).smul
      differentiableAt_snd.snd)).prodMk differentiableAt_snd.fst
  change DifferentiableAt ℝ (fun r : E × (W × E) =>
    ζ r.1 • baseGradient F (r.1+ζ r.1 • r.2.2) r.2.1) v
  have hg : DifferentiableAt ℝ (fun r : E × (W × E) =>
      baseGradient F (r.1+ζ r.1 • r.2.2) r.2.1) v :=
    (differentiableAt_baseGradient hF).comp v
      (g := fun t : E × W => baseGradient F t.1 t.2)
      (f := fun r : E × (W × E) => (r.1+ζ r.1 • r.2.2,r.2.1)) hs
  exact (hζ.comp v differentiableAt_fst).smul hg

theorem regular_outsidePhase {F : E × W → ℝ} {ζ : E → ℝ}
    {q : E × (W × (E × E))}
    (hF : ContDiffAt ℝ ∞ F (q.1,q.2.1))
    (hζ : ContDiffAt ℝ ∞ ζ q.1) (hz : q.2.2.1 = 0)
    (hreg : Function.Surjective
      (fderiv ℝ (fun v : E × W => verticalDifferential F v.1 v.2) (q.1,q.2.1))) :
    Function.Surjective (fderiv ℝ (fiberDifferential
      (totalPhase F (fun _ => 0) (fun X _ _ => ζ X))) q) := by
  have hB := differentiableAt_verticalDifferential hF
  have hF' : ContDiffAt ℝ ∞ F (q.1+ζ q.1 • q.2.2.1,q.2.1) := by
    simpa only [hz,smul_zero,add_zero] using hF
  have hzd : DifferentiableAt ℝ ζ q.1 := hζ.differentiableAt (by simp)
  have ha := differentiableAt_outsideMomentum (F := F) (ζ := ζ)
    (v := (q.1,q.2.1,q.2.2.1)) hF' hzd
  let D := outsideDerivative (fderiv ℝ (fun v : E × W => verticalDifferential F v.1 v.2)
    (q.1,q.2.1)) (fderiv ℝ (outsideMomentum F ζ) (q.1,q.2.1,q.2.2.1)) (ζ q.1)
  have hD : Function.Surjective D := outsideDerivative_surjective hreg
  have ht := hasFDerivAt_outsideSystem hB ha hzd hz
  have hi : HasFDerivAt (fun v : ((W →L[ℝ] ℝ) × (E × E)) =>
      (fiberJetCoordinates (E := E) (W := W)).symm v)
      (fiberJetCoordinates (E := E) (W := W)).symm.toContinuousLinearMap
      (outsideSystem (fun v => verticalDifferential F v.1 v.2) (outsideMomentum F ζ) ζ q) :=
    (fiberJetCoordinates (E := E) (W := W)).symm.toContinuousLinearMap.hasFDerivAt
  have hu := hi.comp q (g := fun v : ((W →L[ℝ] ℝ) × (E × E)) =>
      (fiberJetCoordinates (E := E) (W := W)).symm v)
    (f := outsideSystem (fun v => verticalDifferential F v.1 v.2) (outsideMomentum F ζ) ζ) ht
  have hF1 : ContDiffAt ℝ 1 F (q.1+ζ q.1 • q.2.2.1,q.2.1) := hF'.of_le (by simp)
  have hζ1 : ContDiffAt ℝ 1 ζ q.1 := hζ.of_le (by simp)
  have cF : ContinuousAt (fun r : E × (W × (E × E)) =>
      (r.1+ζ r.1 • r.2.2.1,r.2.1)) q :=
    (continuousAt_fst.add ((hζ.continuousAt.comp continuousAt_fst).smul
      continuousAt_snd.snd.fst)).prodMk continuousAt_snd.fst
  have eF := cF.eventually
    ((hF1.eventually (by simp)).mono fun _ h => h.differentiableAt one_ne_zero)
  have eζ := (continuous_fst.continuousAt (x := q)).eventually
    ((hζ1.eventually (by simp)).mono fun _ h => h.differentiableAt one_ne_zero)
  have he : fiberDifferential (totalPhase F (fun _ => 0) (fun X _ _ => ζ X)) =ᶠ[𝓝 q]
      fun r => (fiberJetCoordinates (E := E) (W := W)).symm
        (outsideSystem (fun v => verticalDifferential F v.1 v.2) (outsideMomentum F ζ) ζ r) := by
    filter_upwards [eF,eζ] with r hrF hrζ
    exact ((fiberJetCoordinates (E := E) (W := W)).eq_symm_apply).mpr
      (outsidePhase_fiberDerivative hrF hrζ)
  simp only [Function.comp_def] at hu
  rw [he.fderiv_eq, hu.fderiv]
  exact (fiberJetCoordinates (E := E) (W := W)).symm.surjective.comp hD

lemma twist_surjective_of_norm_lt_one {L : E →L[ℝ] E} (hL : ‖L‖ < 1) :
    Function.Surjective (ContinuousLinearMap.id ℝ E + L) := by
  have h : IsUnit (1 - -L) := isUnit_one_sub_of_norm_lt_one (by simpa only [norm_neg] using hL)
  have h' : IsUnit (ContinuousLinearMap.id ℝ E + L) := by
    simpa only [sub_neg_eq_add, ContinuousLinearMap.one_def] using h
  exact (ContinuousLinearMap.isUnit_iff_bijective.mp h').2

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport.StepData

open ContinuousLinearMap Filter Set
open scoped Topology ContDiff InnerProductSpace

variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup W] [NormedSpace ℝ W]
variable (S : StepData (E := E) (W := W))

omit [CompleteSpace E] in
lemma cutoff_near_critical {q : E × (W × (E × E))}
    (hw : ‖q.2.1‖ < S.R) (hz : ‖q.2.2.1‖ < S.δ₀) :
    (fun r : E × (W × (E × E)) => S.κ r.1 r.2.1 r.2.2.1) =ᶠ[𝓝 q]
      fun r => S.ζ r.1 := by
  have eχ := (continuous_snd.fst.continuousAt (x := q)).eventually
    (eq_one_near_of_norm_lt S.χ_one hw)
  have eβ := (continuous_snd.snd.fst.continuousAt (x := q)).eventually
    (eq_one_near_of_norm_lt S.β_one hz)
  filter_upwards [eχ,eβ] with r hrχ hrβ
  simp only [κ, productCutoff, hrχ, hrβ, mul_one]

omit [CompleteSpace E] in
lemma phase_near_supported {q : E × (W × (E × E))}
    (hw : ‖q.2.1‖ < S.R) (hz : ‖q.2.2.1‖ < S.δ₀)
    (hζ : S.ζ =ᶠ[𝓝 q.1] fun _ => 1) :
    totalPhase S.F S.σ S.κ =ᶠ[𝓝 q] totalPhase S.F S.σ (fun _ _ _ => 1) := by
  have eζ := (continuous_fst.continuousAt (x := q)).eventually hζ
  filter_upwards [S.cutoff_near_critical hw hz, eζ] with r hr hζr
  simp only [totalPhase, shiftedPhase, hr, hζr]

omit [CompleteSpace E] in
lemma phase_near_outside {q : E × (W × (E × E))}
    (hw : ‖q.2.1‖ < S.R) (hz : ‖q.2.2.1‖ < S.δ₀)
    (hσ : ∀ᶠ Y in 𝓝 q.1, ∀ p, S.σ (Y,p) = 0) :
    totalPhase S.F S.σ S.κ =ᶠ[𝓝 q]
      totalPhase S.F (fun _ => 0) (fun X _ _ => S.ζ X) := by
  have eσ := (continuous_fst.continuousAt (x := q)).eventually hσ
  filter_upwards [S.cutoff_near_critical hw hz, eσ] with r hr hσr
  simp only [totalPhase, shiftedPhase, hr, hσr]

theorem regular_at_newCritical
    (old_regular : ∀ x ∈ S.U, ∀ w, verticalDifferential S.F x w = 0 →
      Function.Surjective (fderiv ℝ (fun v : E × W => verticalDifferential S.F v.1 v.2) (x,w)))
    (mixed_small : ∀ X ∈ S.U, ∀ p,
      ‖(fderiv ℝ (mixedDisplacement S.σ) (X,p)).comp (inl ℝ E E)‖ < 1)
    (q : S.NewCritical) :
    Function.Surjective (fderiv ℝ (fiberDifferential (totalPhase S.F S.σ S.κ)) q.val) := by
  let r := q.val
  have hU : r.1 ∈ S.U := q.property.1
  have hc : IsShiftedCritical S.F S.σ S.κ r.1 r.2.1 r.2.2.1 r.2.2.2 := q.property.2
  obtain ⟨hw,hz⟩ := S.new_critical_bounds hU hc
  have ho := (S.new_to_old hU hc).1
  have hshift := S.shift_mem r.1 hU r.2.1 r.2.2.1
  change Function.Surjective (fderiv ℝ (fiberDifferential (totalPhase S.F S.σ S.κ)) r)
  rcases S.cover r.1 hU with hζ | hσ
  · have hk : S.κ r.1 r.2.1 r.2.2.1 = 1 := by
      exact (S.cutoff_near_critical hw hz).self_of_nhds.trans hζ.self_of_nhds
    have hs : S.shiftedBase r.1 r.2.1 r.2.2.1 = r.1+r.2.2.1 := by
      simp only [shiftedBase,hk,one_smul]
    change S.shiftedBase r.1 r.2.1 r.2.2.1 ∈ S.U at hshift
    rw [hs] at ho hshift
    have hreg := regular_purePhase (S.smooth_F _ hshift r.2.1)
      (S.smooth_σ.contDiffAt (x := (r.1,r.2.2.2)))
      (old_regular _ hshift _ ho) (twist_surjective_of_norm_lt_one (mixed_small _ hU _))
    rw [(fiberDifferential_congr (S.phase_near_supported hw hz hζ)).fderiv_eq]
    exact hreg
  · have H := (shiftedCritical_iff_outside
      (S.diff_F hshift r.2.1) hσ.self_of_nhds (S.diff_κ_w _ _ _)
      (S.diff_κ_z _ _ _) (S.diff_phase hU _ _ _)).mp hc
    have hs : S.shiftedBase r.1 r.2.1 r.2.2.1 = r.1 := by
      simp only [shiftedBase,H.1,smul_zero,add_zero]
    rw [hs] at ho
    have hreg := regular_outsidePhase (S.smooth_F _ hU r.2.1)
      (S.smooth_ζ.contDiffAt (x := r.1)) H.1 (old_regular _ hU _ ho)
    rw [(fiberDifferential_congr (S.phase_near_outside hw hz hσ)).fderiv_eq]
    exact hreg

end NearbyLagrangian.Transport.StepData

end

end OAI
