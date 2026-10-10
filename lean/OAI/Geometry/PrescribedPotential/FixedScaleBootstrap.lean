import Mathlib
import OAI.Geometry.PrescribedPotential.NonlinearSobolevGain
import OAI.Geometry.PrescribedPotential.LinearizedCommutator

namespace OAI

/-! Fixed Scale Bootstrap. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)
local instance fixedBootNG (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance fixedBootNS (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance fixedBootTG (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance fixedBootCS (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

 

def LinearizedGain (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (u : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2)) : Prop :=
  ∀ (w : D.localizers.RealSobolev ((k : ℝ)+2))
      (f : D.localizers.RealSobolev ((k+1 : ℕ) : ℝ)),
    D.realVolumeDerivative k hk
      (D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) ((k : ℝ)+2) (by push_cast; linarith) u) w =
      D.localizers.realLower ((k+1 : ℕ) : ℝ) (k : ℝ) (by push_cast; linarith) f →
    ∃ z : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2),
      D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) ((k : ℝ)+2) (by push_cast; linarith) z = w

 
lemma linearizedGain_nhds (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (x₀ : X) :
    ∀ᶠ u in 𝓝 (0 : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2)),
      D.LinearizedGain k hk u := by
  filter_upwards [D.linearizedVolume_local_gain (k+1) k (by omega) hk (by omega) x₀]
    with u hu
  intro w f hf
  have he : D.linearizedVolume k hk x₀
      (D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) ((k : ℝ)+2) (by push_cast; linarith) u)
      (w,0) = D.pairLower ((k+1 : ℕ) : ℝ) (k : ℝ) (by push_cast; linarith)
        (f,D.realEvaluation ((k : ℝ)+2) x₀ w) := by
    rw [D.linearizedVolume_apply_zero_scalar,D.pairLower_apply]
    exact Prod.ext hf rfl
  obtain ⟨z,hz,_⟩ := hu (w,0) (f,D.realEvaluation ((k : ℝ)+2) x₀ w) he
  exact ⟨z.1,congrArg Prod.fst hz⟩

 
omit [ConnectedSpace X] in
lemma linearized_derivative_equation (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (v : EC d) (u : D.localizers.RealSobolev (((k+2 : ℕ) : ℝ)+2))
    (w : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2))
    (f : D.localizers.RealSobolev ((k+2 : ℕ) : ℝ))
    (hf : D.realVolumeDerivative (k+1) (by omega)
      (D.localizers.realLower (((k+2 : ℕ) : ℝ)+2) (((k+1 : ℕ) : ℝ)+2)
        (by push_cast; linarith) u) w =
      D.localizers.realLower ((k+2 : ℕ) : ℝ) ((k+1 : ℕ) : ℝ) (by push_cast; linarith) f) :
    let u₁ := D.localizers.realLower (((k+2 : ℕ) : ℝ)+2) (((k+1 : ℕ) : ℝ)+2)
      (by push_cast; linarith) u
    D.realVolumeDerivative k hk
      (D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) ((k : ℝ)+2) (by push_cast; linarith) u₁)
      (D.potentialDerivative k p v w) =
    D.localizers.realLower ((k+1 : ℕ) : ℝ) (k : ℝ) (by push_cast; linarith)
      (D.densityDerivative (k+1) p v f +
        (D.realRemainderDerivative (k+1) (by omega) p v u₁ w -
          D.realVolumeSecond (k+1) (by omega) u₁ w
            (D.potentialDerivative (k+1) p v u))) := by
  let : NormedAddCommGroup (D.localizers.RealSobolev ((k+1 : ℕ) : ℝ)) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev ((k+1 : ℕ) : ℝ)) := inferInstance
  let : NormedAddCommGroup (D.localizers.RealSobolev (k : ℝ)) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev (k : ℝ)) := inferInstance
  have hh := D.linearized_commutator_weak k hk p v u w
  dsimp only at hh ⊢
  rw [hf, D.densityDerivative_lower (k+1) k (by omega)] at hh
  simpa only [map_add] using hh

 

omit [ConnectedSpace X] in
lemma linearizedGain_succ (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (u : D.localizers.RealSobolev (((k+2 : ℕ) : ℝ)+2))
    (hG : D.LinearizedGain k hk
      (D.localizers.realLower (((k+2 : ℕ) : ℝ)+2) (((k+1 : ℕ) : ℝ)+2)
        (by push_cast; linarith) u)) :
    D.LinearizedGain (k+1) (by omega) u := by
  intro w f hf
  let u₁ := D.localizers.realLower (((k+2 : ℕ) : ℝ)+2) (((k+1 : ℕ) : ℝ)+2)
    (by push_cast; linarith) u
  have hDer (p : ι) (v : EC d) : ∃ z : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2),
      D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) ((k : ℝ)+2)
        (by push_cast; linarith) z = D.potentialDerivative k p v w := by
    exact hG _ _ (D.linearized_derivative_equation k hk p v u w f hf)
  obtain ⟨z,hz⟩ := D.derivative_lifts_gain k w hDer
  refine ⟨D.localizers.realLower ((k+4 : ℕ) : ℝ) (((k+1+1 : ℕ) : ℝ)+2)
    (by push_cast; linarith) z, ?_⟩
  rw [Localizers.realLower_lower]
  exact hz

 
omit [ConnectedSpace X] in
lemma nonlinear_gain_of_linearizedGain (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (u : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2))
    (hG : D.LinearizedGain k hk u) (F : RealSmooth A)
    (hF : D.realVolume (k+1) (by omega) u = D.localizers.realEmbed ((k+1 : ℕ) : ℝ) F) :
    ∃ z : D.localizers.RealSobolev (((k+2 : ℕ) : ℝ)+2),
      D.localizers.realLower (((k+2 : ℕ) : ℝ)+2) (((k+1 : ℕ) : ℝ)+2)
        (by push_cast; linarith) z = u := by
  have hDer (p : ι) (v : EC d) : ∃ z : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2),
      D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) ((k : ℝ)+2)
        (by push_cast; linarith) z = D.potentialDerivative k p v u := by
    apply hG (D.potentialDerivative k p v u)
      (D.localizers.realEmbed ((k+1 : ℕ) : ℝ) (D.realLocalizedDerivative p v F) +
        D.realNonlinearRemainder (k+1) (by omega) p v u)
    exact D.nonlinear_commutator_solution k hk p v u F hF
  obtain ⟨z,hz⟩ := D.derivative_lifts_gain k u hDer
  refine ⟨D.localizers.realLower ((k+4 : ℕ) : ℝ) (((k+2 : ℕ) : ℝ)+2)
    (by push_cast; linarith) z, ?_⟩
  rw [Localizers.realLower_lower]
  exact hz

 
omit [ConnectedSpace X] in
lemma realVolume_lift_solution (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (u : D.localizers.RealSobolev ((k : ℝ)+2))
    (v : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2))
    (hv : D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) ((k : ℝ)+2) (by push_cast; linarith) v = u)
    (F : RealSmooth A) (hF : D.realVolume k hk u = D.localizers.realEmbed (k : ℝ) F) :
    D.realVolume (k+1) (by omega) v = D.localizers.realEmbed ((k+1 : ℕ) : ℝ) F := by
  apply D.localizers.realLower_injective
    (by push_cast; linarith : (k : ℝ) ≤ ((k+1 : ℕ) : ℝ))
  exact (D.realVolume_lower (k+1) k (by omega) hk (by omega) v).symm.trans
    ((congrArg (D.realVolume k hk) hv).trans
      (hF.trans (D.localizers.realLower_embed (by push_cast; linarith only) F).symm))

 

omit [ConnectedSpace X] in
lemma nonlinear_all_order_lift (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (u : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2))
    (hG : D.LinearizedGain k hk u) (F : RealSmooth A)
    (hF : D.realVolume (k+1) (by omega) u = D.localizers.realEmbed ((k+1 : ℕ) : ℝ) F)
    (l : ℕ) (hl : k ≤ l) :
    ∃ z : D.localizers.RealSobolev (((l+1 : ℕ) : ℝ)+2),
      D.localizers.realLower (((l+1 : ℕ) : ℝ)+2) (((k+1 : ℕ) : ℝ)+2)
        (by exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_right hl 1) 2) z = u ∧
      D.LinearizedGain l (by omega) z ∧
      D.realVolume (l+1) (by omega) z = D.localizers.realEmbed ((l+1 : ℕ) : ℝ) F := by
  induction l, hl using Nat.le_induction with
  | base =>
    refine ⟨u,?_,hG,hF⟩
    apply Subtype.ext
    exact congrArg (fun T : D.localizers.Sobolev (((k+1 : ℕ) : ℝ)+2) →L[ℝ]
      D.localizers.Sobolev (((k+1 : ℕ) : ℝ)+2) => T u.val) (D.localizers.lower_self _)
  | succ l hl ih =>
    obtain ⟨z,hz,hGz,hFz⟩ := ih
    obtain ⟨v,hv⟩ := D.nonlinear_gain_of_linearizedGain l (by omega) z hGz F hFz
    refine ⟨v,?_,?_,?_⟩
    · calc
        D.localizers.realLower (((l+1+1 : ℕ) : ℝ)+2) (((k+1 : ℕ) : ℝ)+2) _ v =
            D.localizers.realLower (((l+1 : ℕ) : ℝ)+2) (((k+1 : ℕ) : ℝ)+2) _
              (D.localizers.realLower (((l+2 : ℕ) : ℝ)+2) (((l+1 : ℕ) : ℝ)+2) _ v) :=
          (D.localizers.realLower_lower _ _ v).symm
        _ = u := by rw [hv,hz]
    · apply D.linearizedGain_succ l (by omega) v
      rwa [hv]
    · exact D.realVolume_lift_solution (l+1) (by omega) z v hv F hFz

omit [ConnectedSpace X] in
lemma allRegular_of_real_lifts (k : ℕ)
    (u : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2))
    (hL : ∀ m : ℕ, ∃ z : D.localizers.RealSobolev (((k+m+1 : ℕ) : ℝ)+2),
      D.localizers.realLower (((k+m+1 : ℕ) : ℝ)+2) (((k+1 : ℕ) : ℝ)+2)
        (by push_cast; linarith only [Nat.cast_nonneg (α := ℝ) m]) z = u) :
    D.localizers.AllRegular
      (D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) 0 (by positivity) u).val := by
  intro m
  obtain ⟨z,hz⟩ := hL m
  refine ⟨D.localizers.lower (((k+m+1 : ℕ) : ℝ)+2) (m : ℝ) z.val,?_⟩
  have hm : (m : ℝ) ≤ ((k+m+1 : ℕ) : ℝ)+2 := by
    push_cast
    linarith only [Nat.cast_nonneg (α := ℝ) k]
  have hh := congrArg
    (D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) 0 (by positivity)) hz
  have hh' := (D.localizers.realLower_lower _ _ z).symm.trans hh
  exact (D.localizers.lower_lower hm (Nat.cast_nonneg m) z.val).trans
    (congrArg Subtype.val hh')

omit [ConnectedSpace X] in
lemma real_smooth_of_allRegular (s : ℝ) (hs : 0 ≤ s)
    (hStrong : (Module.finrank ℝ (EC d) : ℝ) < 2*s)
    (u : D.localizers.RealSobolev s)
    (hreg : D.localizers.AllRegular (D.localizers.realLower s 0 hs u).val) :
    ∃ φ : RealSmooth A, D.localizers.realEmbed s φ = u := by
  obtain ⟨f,hf⟩ := D.allRegular_smooth hreg
  have he : D.localizers.embed s f = u.val := by
    apply D.localizers.lower_injective hs
    exact (D.localizers.lower_embed hs f).trans hf
  have hr (x : X) : (f x).im = 0 := by
    have hh := D.localizers.real_strong hStrong u x
    rw [← he,D.localizers.strong_embed s hStrong f] at hh
    exact hh
  exact ⟨⟨f,hr⟩,Subtype.ext he⟩

 

omit [ConnectedSpace X] in
lemma nonlinear_smooth_of_linearizedGain (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (u : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2))
    (hG : D.LinearizedGain k hk u) (F : RealSmooth A)
    (hF : D.realVolume (k+1) (by omega) u = D.localizers.realEmbed ((k+1 : ℕ) : ℝ) F) :
    ∃ φ : RealSmooth A, D.localizers.realEmbed (((k+1 : ℕ) : ℝ)+2) φ = u := by
  have hStrong : (Module.finrank ℝ (EC d) : ℝ) < 2 * (((k+1 : ℕ) : ℝ)+2) := by
    have hk' : (Module.finrank ℝ (EC d) : ℝ) < (k : ℝ) := by exact_mod_cast hk
    push_cast
    linarith only [hk',Nat.cast_nonneg (α := ℝ) k]
  apply D.real_smooth_of_allRegular _ (by positivity) hStrong u
  apply D.allRegular_of_real_lifts k u
  intro m
  obtain ⟨z,hz,_,_⟩ := D.nonlinear_all_order_lift k hk u hG F hF (k+m) (by omega)
  exact ⟨z,hz⟩

 

def FixedSpatialSmoothness (s : ℕ) (hs : Module.finrank ℝ (EC d) < s) : Prop :=
  ∀ᶠ u in 𝓝 (0 : D.localizers.RealSobolev (((s+1 : ℕ) : ℝ)+2)),
    ∀ F : RealSmooth A,
      D.realVolume (s+1) (by omega) u = D.localizers.realEmbed ((s+1 : ℕ) : ℝ) F →
      ∃ φ : RealSmooth A, D.localizers.realEmbed (((s+1 : ℕ) : ℝ)+2) φ = u

 

theorem fixed_spatial_smoothness (s : ℕ) (hs : Module.finrank ℝ (EC d) < s) (x₀ : X) :
    D.FixedSpatialSmoothness s hs := by
  filter_upwards [D.linearizedGain_nhds s hs x₀] with u hu
  intro F hF
  exact D.nonlinear_smooth_of_linearizedGain s hs u hu F hF

end GluingData
end GlobalElliptic

end
end

end OAI
