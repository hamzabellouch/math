import Mathlib
import OAI.Geometry.NearbyLagrangian.Phase

namespace OAI

/-! Critical equations and supported and exterior output identities. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport

open Filter Set
open scoped Topology
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma fderiv_triple_eq_zero_iff {f : W × (E × E) → ℝ} {w : W} {z p : E}
    (hf : DifferentiableAt ℝ f (w,z,p)) :
    fderiv ℝ f (w,z,p) = 0 ↔
      fderiv ℝ (fun w => f (w,z,p)) w = 0 ∧
      fderiv ℝ (fun z => f (w,z,p)) z = 0 ∧
      fderiv ℝ (fun p => f (w,z,p)) p = 0 := by
  have hw := (hf.hasFDerivAt.comp w (f := fun w' => (w',z,p))
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) w (z,p))).fderiv
  have hz := (hf.hasFDerivAt.comp z (f := fun z' => (w,z',p))
    ((hasFDerivAt_prodMk_right (𝕜 := ℝ) w (z,p)).comp z
      (f := fun z' => (z',p)) (hasFDerivAt_prodMk_left (𝕜 := ℝ) z p))).fderiv
  have hp := (hf.hasFDerivAt.comp p (f := fun p' => (w,z,p'))
    ((hasFDerivAt_prodMk_right (𝕜 := ℝ) w (z,p)).comp p
      (f := fun p' => (z,p')) (hasFDerivAt_prodMk_right (𝕜 := ℝ) z p))).fderiv
  simp only [Function.comp_def] at hw hz hp
  rw [hw, hz, hp]
  constructor
  · intro h
    simp [h]
  · rintro ⟨hw, hz, hp⟩
    apply ContinuousLinearMap.ext
    intro v
    have h1 := congrArg (fun A : W →L[ℝ] ℝ => A v.1) hw
    have h2 := congrArg (fun A : E →L[ℝ] ℝ => A v.2.1) hz
    have h3 := congrArg (fun A : E →L[ℝ] ℝ => A v.2.2) hp
    change fderiv ℝ f (w,z,p) (v.1,0,0) = 0 at h1
    change fderiv ℝ f (w,z,p) (0,v.2.1,0) = 0 at h2
    change fderiv ℝ f (w,z,p) (0,0,v.2.2) = 0 at h3
    have he : v = (v.1,0,0) + (0,v.2.1,0) + (0,0,v.2.2) := by
      ext <;> simp
    rw [he, map_add, map_add, h1, h2, h3]
    simp

def verticalPhase (F : E × W → ℝ) (σ : E × E → ℝ)
    (κ : E → W → E → ℝ) (X : E) (v : W × (E × E)) : ℝ :=
  shiftedPhase F σ κ X v.1 v.2.1 v.2.2

def IsShiftedCritical (F : E × W → ℝ) (σ : E × E → ℝ)
    (κ : E → W → E → ℝ) (X : E) (w : W) (z p : E) : Prop :=
  fderiv ℝ (verticalPhase F σ κ X) (w,z,p) = 0

lemma differentiableAt_verticalPhase {F : E × W → ℝ} {σ : E × E → ℝ}
    {κ : E → W → E → ℝ} {X : E} {w : W} {z p : E}
    (hF : DifferentiableAt ℝ F (X + κ X w z • z,w))
    (hσ : DifferentiableAt ℝ (fun p => σ (X,p)) p)
    (hκ : DifferentiableAt ℝ (fun v : W × (E × E) => κ X v.1 v.2.1) (w,z,p)) :
    DifferentiableAt ℝ (verticalPhase F σ κ X) (w,z,p) := by
  have hs : DifferentiableAt ℝ (fun v : W × (E × E) =>
      (X + κ X v.1 v.2.1 • v.2.1, v.1)) (w,z,p) :=
    ((hκ.smul differentiableAt_snd.fst).const_add X).prodMk differentiableAt_fst
  exact ((hF.comp (w,z,p) hs).add (hσ.comp (w,z,p) differentiableAt_snd.snd)).sub
    (differentiableAt_snd.fst.inner ℝ differentiableAt_snd.snd)

lemma norm_w_lt_of_shiftedCritical {F : E × W → ℝ} {σ : E × E → ℝ}
    {ζ β : E → ℝ} {χ : W → ℝ} {X : E} {w : W} {z p : E}
    {R c C δ₀ δ₁ : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hδ₀ : 0 ≤ δ₀)
    (hδ₁ : 0 ≤ δ₁) (hsmall : C * δ₀ * δ₁ < c)
    (hF : DifferentiableAt ℝ F (X + productCutoff ζ β χ X w z • z,w))
    (hσ : DifferentiableAt ℝ (fun p => σ (X,p)) p)
    (hχ : DifferentiableAt ℝ χ w)
    (hphase : DifferentiableAt ℝ (verticalPhase F σ (productCutoff ζ β χ) X) (w,z,p))
    (hζ : ζ X ∈ Icc (0:ℝ) 1) (hβ : β z ∈ Icc (0:ℝ) 1)
    (hσb : ‖fderiv ℝ (fun p => σ (X,p)) p‖ < δ₀)
    (hcutoff : w ≠ 0 → ‖fderiv ℝ χ w‖ ≤ δ₁ / ‖w‖)
    (hbase : R ≤ ‖w‖ →
      ‖baseDifferential F (X + productCutoff ζ β χ X w z • z) w‖ ≤ C * ‖w‖^2)
    (hvertical : R ≤ ‖w‖ → c * ‖w‖ ≤
      ‖verticalDifferential F (X + productCutoff ζ β χ X w z • z) w‖)
    (hcrit : IsShiftedCritical F σ (productCutoff ζ β χ) X w z p) : ‖w‖ < R := by
  have H := (fderiv_triple_eq_zero_iff hphase).mp hcrit
  have hz : ‖z‖ ≤ δ₀ := (displacement_bound_of_critical_p hσ hσb H.2.2).le
  by_contra hn
  have hlarge := le_of_not_gt hn
  have hw : w ≠ 0 := norm_pos_iff.mp (hR.trans_le hlarge)
  have hκ : DifferentiableAt ℝ (fun w => productCutoff ζ β χ X w z) w :=
    hχ.const_smul (ζ X * β z)
  have hd : ‖fderiv ℝ (fun w => productCutoff ζ β χ X w z) w‖ ≤ δ₁ / ‖w‖ :=
    (norm_fderiv_productCutoff_w_le ζ β X z hχ hζ hβ).trans (hcutoff hw)
  exact shiftedPhase_w_ne_zero hF hκ hw hC hδ₀ hδ₁ (hbase hlarge)
    (hvertical hlarge) hz hd hsmall H.1

lemma shiftedCritical_iff {F : E × W → ℝ} {σ : E × E → ℝ}
    {κ : E → W → E → ℝ} {X : E} {w : W} {z p : E}
    (hF : DifferentiableAt ℝ F (X + κ X w z • z,w))
    (hσ : DifferentiableAt ℝ (fun p => σ (X,p)) p)
    (hκw : DifferentiableAt ℝ (fun w => κ X w z) w)
    (hκz : DifferentiableAt ℝ (κ X w) z)
    (hphase : DifferentiableAt ℝ (verticalPhase F σ κ X) (w,z,p)) :
    IsShiftedCritical F σ κ X w z p ↔
      verticalDifferential F (X+κ X w z • z) w +
        (baseDifferential F (X+κ X w z • z) w z) •
          fderiv ℝ (fun w => κ X w z) w = 0 ∧
      κ X w z • baseDifferential F (X+κ X w z • z) w +
        (baseDifferential F (X+κ X w z • z) w z) •
          fderiv ℝ (κ X w) z = innerSL ℝ p ∧
      fderiv ℝ (fun p => σ (X,p)) p = innerSL ℝ z := by
  rw [IsShiftedCritical, fderiv_triple_eq_zero_iff hphase]
  change (fderiv ℝ (fun w => shiftedPhase F σ κ X w z p) w = 0 ∧
    fderiv ℝ (fun z => shiftedPhase F σ κ X w z p) z = 0 ∧
    fderiv ℝ (fun p => shiftedPhase F σ κ X w z p) p = 0) ↔ _
  rw [(hasFDerivAt_shiftedPhase_w σ X w z p hF hκw).fderiv,
    (hasFDerivAt_shiftedPhase_z σ X w z p hF hκz).fderiv,
    (hasFDerivAt_shiftedPhase_p F κ X w z p hσ).fderiv,
    sub_eq_zero, sub_eq_zero]

lemma shiftedCritical_iff_supported {F : E × W → ℝ} {σ : E × E → ℝ}
    {κ : E → W → E → ℝ} {X : E} {w : W} {z p : E}
    (hF : DifferentiableAt ℝ F (X+z,w))
    (hσ : DifferentiableAt ℝ (fun p => σ (X,p)) p)
    (hκw : (fun w => κ X w z) =ᶠ[𝓝 w] fun _ => 1)
    (hκz : κ X w =ᶠ[𝓝 z] fun _ => 1)
    (hphase : DifferentiableAt ℝ (verticalPhase F σ κ X) (w,z,p)) :
    IsShiftedCritical F σ κ X w z p ↔
      verticalDifferential F (X+z) w = 0 ∧
      baseDifferential F (X+z) w = innerSL ℝ p ∧
      fderiv ℝ (fun p => σ (X,p)) p = innerSL ℝ z := by
  have hk : κ X w z = 1 := hκw.eq_of_nhds
  have hdw := (hasFDerivAt_const (𝕜 := ℝ) (1:ℝ) w).congr_of_eventuallyEq hκw
  have hdz := (hasFDerivAt_const (𝕜 := ℝ) (1:ℝ) z).congr_of_eventuallyEq hκz
  have HF : DifferentiableAt ℝ F (X + κ X w z • z,w) := by simpa [hk] using hF
  simpa only [hk, one_smul, hdw.fderiv, hdz.fderiv, smul_zero, add_zero] using
    shiftedCritical_iff HF hσ hdw.differentiableAt hdz.differentiableAt hphase

lemma shifted_output_supported {F : E × W → ℝ} {σ : E × E → ℝ}
    {κ : E → W → E → ℝ} {X : E} {w : W} {z p : E}
    (hF : DifferentiableAt ℝ F (X+z,w))
    (hσ : DifferentiableAt ℝ (fun X => σ (X,p)) X)
    (hκX : (fun X => κ X w z) =ᶠ[𝓝 X] fun _ => 1)
    (ha : baseDifferential F (X+z) w = innerSL ℝ p) :
    fderiv ℝ (fun X => shiftedPhase F σ κ X w z p) X =
      innerSL ℝ p + fderiv ℝ (fun X => σ (X,p)) X := by
  have hk : κ X w z = 1 := hκX.eq_of_nhds
  have hd := (hasFDerivAt_const (𝕜 := ℝ) (1:ℝ) X).congr_of_eventuallyEq hκX
  have HF : DifferentiableAt ℝ F (X + κ X w z • z,w) := by simpa [hk] using hF
  simpa only [hk, one_smul, hd.fderiv, smul_zero, add_zero, ha] using
    (hasFDerivAt_shiftedPhase_X X w z p HF hd.differentiableAt hσ).fderiv

lemma shiftedCritical_iff_outside {F : E × W → ℝ} {σ : E × E → ℝ}
    {κ : E → W → E → ℝ} {X : E} {w : W} {z p : E}
    (hF : DifferentiableAt ℝ F (X + κ X w z • z,w))
    (hσ : ∀ p, σ (X,p) = 0)
    (hκw : DifferentiableAt ℝ (fun w => κ X w z) w)
    (hκz : DifferentiableAt ℝ (κ X w) z)
    (hphase : DifferentiableAt ℝ (verticalPhase F σ κ X) (w,z,p)) :
    IsShiftedCritical F σ κ X w z p ↔
      z = 0 ∧ verticalDifferential F X w = 0 ∧
      κ X w 0 • baseDifferential F X w = innerSL ℝ p := by
  have hs : (fun p => σ (X,p)) = fun _ => 0 := funext hσ
  have hd : DifferentiableAt ℝ (fun p => σ (X,p)) p := by
    rw [hs]; exact differentiableAt_const _
  rw [shiftedCritical_iff hF hd hκw hκz hphase, hs,
    (hasFDerivAt_const (𝕜 := ℝ) (0:ℝ) p).fderiv]
  constructor
  · rintro ⟨hw, hz, hp⟩
    have hz0 : z = 0 := (innerSL_inj (𝕜 := ℝ)).mp (by simpa only [map_zero] using hp.symm)
    refine ⟨hz0, ?_, ?_⟩
    · simpa only [hz0, smul_zero, add_zero, map_zero, zero_smul] using hw
    · simpa only [hz0, smul_zero, add_zero, map_zero, zero_smul] using hz
  · rintro ⟨rfl, hw, hz⟩
    simpa only [smul_zero, add_zero, map_zero, zero_smul] using
      (show verticalDifferential F X w = 0 ∧
        κ X w 0 • baseDifferential F X w = innerSL ℝ p ∧
        (0 : E →L[ℝ] ℝ) = 0 from ⟨hw,hz,rfl⟩)

lemma shifted_output_outside {F : E × W → ℝ} {σ : E × E → ℝ}
    {κ : E → W → E → ℝ} {X : E} {w : W} {p : E}
    (hF : DifferentiableAt ℝ F (X,w))
    (hσ : (fun X => σ (X,p)) =ᶠ[𝓝 X] fun _ => 0)
    (hκ : DifferentiableAt ℝ (fun X => κ X w 0) X) :
    fderiv ℝ (fun X => shiftedPhase F σ κ X w 0 p) X = baseDifferential F X w := by
  have hs := (hasFDerivAt_const (𝕜 := ℝ) (0:ℝ) X).congr_of_eventuallyEq hσ
  have HF : DifferentiableAt ℝ F (X + κ X w 0 • 0,w) := by simpa using hF
  simpa only [smul_zero, add_zero, map_zero, zero_smul, hs.fderiv] using
    (hasFDerivAt_shiftedPhase_X X w 0 p HF hκ hs.differentiableAt).fderiv

end NearbyLagrangian.Transport

end

end OAI
