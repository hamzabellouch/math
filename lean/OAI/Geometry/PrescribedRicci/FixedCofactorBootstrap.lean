import Mathlib
import OAI.Geometry.PrescribedRicci.FiniteCofactorPatch
import OAI.Geometry.PrescribedRicci.FixedCofactorStep
import OAI.Geometry.PrescribedPotential.GlobalSmooth
import OAI.Geometry.PrescribedPotential.NonlinearSobolevGain
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.RealSobolev

namespace OAI

/-! Fixed Cofactor Bootstrap. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)
local instance fixedCofactorBootNG (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance fixedCofactorBootNS (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance fixedCofactorBootTG (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance fixedCofactorBootCS (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

lemma lift_over_lift {s t r : ℝ} (hst : t ≤ s) (htr : r ≤ t)
    (u : D.localizers.RealSobolev r) (v : D.localizers.RealSobolev t)
    (hv : D.localizers.realLower t r htr v = u)
    (h : ∃ z : D.localizers.RealSobolev s, D.localizers.realLower s t hst z = v) :
    ∃ z : D.localizers.RealSobolev s, D.localizers.realLower s r (htr.trans hst) z = u := by
  obtain ⟨z,hz⟩ := h
  refine ⟨z,?_⟩
  rw [← D.localizers.realLower_lower hst htr z,hz,hv]

lemma cofactor_small_lifted (k l : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hl : Module.finrank ℝ (EC d) < l) (hkl : k ≤ l)
    (hs : (Module.finrank ℝ (EC d):ℝ) < 2*(k:ℝ))
    (ht : (Module.finrank ℝ (EC d):ℝ) < 2*(l:ℝ))
    (u : D.localizers.RealSobolev ((k:ℝ)+2))
    (v : D.localizers.RealSobolev ((l:ℝ)+2))
    (hv : D.localizers.realLower ((l:ℝ)+2) ((k:ℝ)+2) (by exact_mod_cast Nat.add_le_add_right hkl 2) v = u)
    (hu : D.CofactorSmall k hk hs u.val) : D.CofactorSmall l hl ht v.val := by
  apply D.cofactor_small_of_lower l k hl hk hkl ht hs v.val
  have he := congrArg Subtype.val hv
  change D.localizers.lower _ _ v.val = u.val at he
  rw [he]
  exact hu

lemma cofactor_lift_step (k l : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hl : Module.finrank ℝ (EC d) < l) (hkl : k ≤ l)
    (hs : (Module.finrank ℝ (EC d):ℝ) < 2*((k+1:ℕ):ℝ))
    (ht : (Module.finrank ℝ (EC d):ℝ) < 2*((l+1:ℕ):ℝ))
    (u : D.localizers.RealSobolev (((k+1:ℕ):ℝ)+2))
    (v : D.localizers.RealSobolev (((l+1:ℕ):ℝ)+2))
    (hv : D.localizers.realLower (((l+1:ℕ):ℝ)+2) (((k+1:ℕ):ℝ)+2)
      (by exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_right hkl 1) 2) v = u)
    (hu : D.CofactorSmall (k+1) (by omega) hs u.val) (F : RealSmooth A)
    (hF : D.realVolume (k+1) (by omega) u = D.localizers.realEmbed ((k+1:ℕ):ℝ) F) :
    ∃ z : D.localizers.RealSobolev (((l+2:ℕ):ℝ)+2),
      D.localizers.realLower (((l+2:ℕ):ℝ)+2) (((k+1:ℕ):ℝ)+2) (by push_cast; exact_mod_cast Nat.add_le_add_right (by omega : k+1 ≤ l+2) 2) z = u := by
  have hsmall : D.CofactorSmall (l+1) (by omega) ht v.val := D.cofactor_small_lifted (k+1) (l+1) (by omega) (by omega) (by omega) hs ht u v hv hu
  have hEq : D.realVolume (l+1) (by omega) v = D.localizers.realEmbed ((l+1:ℕ):ℝ) F := D.cofactor_lift_equation (k+1) (l+1) (by omega) (by omega) (by omega) u v hv F hF
  have hgain := D.cofactor_nonlinear_step l hl ht v hsmall F hEq
  obtain ⟨z,hz⟩ := hgain
  refine ⟨z,?_⟩
  have hst : (((l+1:ℕ):ℝ)+2) ≤ (((l+2:ℕ):ℝ)+2) := by push_cast; linarith only
  have htr : (((k+1:ℕ):ℝ)+2) ≤ (((l+1:ℕ):ℝ)+2) := by exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_right hkl 1) 2
  rw [← D.localizers.realLower_lower (s:=((l+2:ℕ):ℝ)+2) (t:=((l+1:ℕ):ℝ)+2)
    (r:=((k+1:ℕ):ℝ)+2) hst htr z, hz, hv]

lemma cofactor_solution_lifts (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hs : (Module.finrank ℝ (EC d):ℝ) < 2*((k+1:ℕ):ℝ))
    (u : D.localizers.RealSobolev (((k+1:ℕ):ℝ)+2))
    (hu : D.CofactorSmall (k+1) (by omega) hs u.val) (F : RealSmooth A)
    (hF : D.realVolume (k+1) (by omega) u = D.localizers.realEmbed ((k+1:ℕ):ℝ) F) :
    ∀ n : ℕ, ∃ z : D.localizers.RealSobolev (((k+n+1:ℕ):ℝ)+2),
      D.localizers.realLower (((k+n+1:ℕ):ℝ)+2) (((k+1:ℕ):ℝ)+2)
        (by push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) n]) z = u := by
  intro n
  induction n with
  | zero =>
    refine ⟨u,?_⟩
    apply Subtype.ext
    change D.localizers.lower _ _ u.val = u.val
    rw [D.localizers.lower_self,ContinuousLinearMap.id_apply]
  | succ n ih =>
    obtain ⟨v,hv⟩ := ih
    have ht : (Module.finrank ℝ (EC d):ℝ) < 2*((k+n+1:ℕ):ℝ) :=
      hs.trans_le (by exact_mod_cast Nat.mul_le_mul_left 2 (by omega : k+1 ≤ k+n+1))
    have hh := D.cofactor_lift_step k (k+n) hk (by omega) (by omega) hs ht u v hv hu F hF
    exact D.realLift_transport _ _ _ _ _ (by congr 2) u hh

lemma realLift_order_witness (s t : ℝ) (k : ℕ) (hs : 0 ≤ s) (hst : s ≤ t)
    (hkt : (k:ℝ) ≤ t) (u : D.localizers.RealSobolev s) (v : D.localizers.RealSobolev t)
    (hv : D.localizers.realLower t s hst v = u) :
    ∃ w : D.localizers.Sobolev (k:ℝ), D.localizers.lower (k:ℝ) 0 w =
      D.localizers.lower s 0 u.val := by
  refine ⟨D.localizers.lower t (k:ℝ) v.val, ?_⟩
  rw [D.localizers.lower_lower hkt (Nat.cast_nonneg k)]
  rw [← D.localizers.lower_lower hst hs v.val]
  exact congrArg (D.localizers.lower s 0) (congrArg Subtype.val hv)

lemma cofactor_solution_allRegular (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hs : (Module.finrank ℝ (EC d):ℝ) < 2*((k+1:ℕ):ℝ))
    (u : D.localizers.RealSobolev (((k+1:ℕ):ℝ)+2))
    (hu : D.CofactorSmall (k+1) (by omega) hs u.val) (F : RealSmooth A)
    (hF : D.realVolume (k+1) (by omega) u = D.localizers.realEmbed ((k+1:ℕ):ℝ) F) :
    D.localizers.AllRegular (D.localizers.lower (((k+1:ℕ):ℝ)+2) 0 u.val) := by
  intro n
  have hb : 0 ≤ ((k+1:ℕ):ℝ)+2 := by positivity
  have hnb : ((k+1:ℕ):ℝ)+2 ≤ ((k+n+1:ℕ):ℝ)+2 := by
    push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) n]
  have hnv : (n:ℝ) ≤ ((k+n+1:ℕ):ℝ)+2 := by
    push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) k]
  obtain ⟨v,hv⟩ := D.cofactor_solution_lifts k hk hs u hu F hF n
  exact D.realLift_order_witness _ _ n hb hnb hnv u v hv

 

theorem cofactor_solution_smooth (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hs : (Module.finrank ℝ (EC d):ℝ) < 2*((k+1:ℕ):ℝ))
    (u : D.localizers.RealSobolev (((k+1:ℕ):ℝ)+2))
    (hu : D.CofactorSmall (k+1) (by omega) hs u.val) (F : RealSmooth A)
    (hF : D.realVolume (k+1) (by omega) u = D.localizers.realEmbed ((k+1:ℕ):ℝ) F) :
    ∃ φ : RealSmooth A, D.localizers.realEmbed (((k+1:ℕ):ℝ)+2) φ = u := by
  obtain ⟨f,hf⟩ := D.allRegular_smooth (D.cofactor_solution_allRegular k hk hs u hu F hF)
  have he : D.localizers.embed (((k+1:ℕ):ℝ)+2) f = u.val := by
    apply D.localizers.lower_injective (by positivity : 0 ≤ ((k+1:ℕ):ℝ)+2)
    rw [D.localizers.lower_embed (by positivity)]
    exact hf
  have hb : (Module.finrank ℝ (EC d):ℝ) < 2*(((k+1:ℕ):ℝ)+2) := by linarith only [hs]
  have hr (x : X) : (f x).im = 0 := by
    have hh := D.localizers.real_strong hb u x
    rw [← he,D.localizers.strong_embed _ hb] at hh
    exact hh
  exact ⟨⟨f,hr⟩,Subtype.ext he⟩

end GluingData
end GlobalElliptic

end
end

end OAI
