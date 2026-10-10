import Mathlib
import OAI.Geometry.PrescribedRicci.CofactorWeakEquation
import OAI.Geometry.PrescribedPotential.GlobalCompletion
import OAI.Geometry.PrescribedRicci.RoughEllipticGain

namespace OAI

/-! Tame Cofactor Gain. -/

section

 

noncomputable section
open Set Filter Topology Matrix _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution
open scoped ContDiff SchwartzMap Classical BoundedContinuousFunction Matrix.Norms.Elementwise
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart FrozenPoisson MetricLocalization
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)
local instance tameCofactorGainNG (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance tameCofactorGainNS (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance tameCofactorGainTG (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance tameCofactorGainCS (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

lemma cofactor_local_gain (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hs : (Module.finrank ℝ (EC d):ℝ) < 2*((k+1:ℕ):ℝ))
    (u : D.localizers.RealSobolev (((k+1:ℕ):ℝ)+2))
    (hu : D.CofactorSmall (k+1) (by omega) hs u.val)
    (w : D.localizers.RealSobolev ((k:ℝ)+2))
    (F : D.localizers.RealSobolev ((k+1:ℕ):ℝ))
    (hF : D.realVolumeDerivative k hk
      (D.localizers.realLower (((k+1:ℕ):ℝ)+2) ((k:ℝ)+2) (by push_cast; linarith) u) w =
      D.localizers.realLower ((k+1:ℕ):ℝ) (k:ℝ) (by push_cast; linarith) F) (p : ι) :
    MemSobolev (((k+1:ℕ):ℝ)+2) 2 (D.localizers.distribution ((k:ℝ)+2) p w.val) := by
  let a := fun i j => D.cofactorLocal (k+1) (by omega) p i j u.val
  let E := roughCutoff (D.patch p).matrix (k+1) (by omega) (D.weightCore p) a
    (lowerCoord ((k:ℝ)+2) (((k+1:ℕ):ℝ)+1) (by push_cast; linarith)
      (D.outerCompleted ((k:ℝ)+2) p w.val))
  let f : L2 (EC d) := lowerCoord ((k:ℝ)+2) ((k+1:ℕ):ℝ) (by push_cast; linarith)
    (w.val.val p)-F.val.val p-E
  let w₂ := lowerCoord ((k:ℝ)+2) 2 (by linarith [Nat.cast_nonneg (α:=ℝ) k]) (w.val.val p)
  have he := D.cofactor_weak_equation k hk hs p u w
  dsimp only [cofactorWeakLeft,cofactorWeakRight,Prod.fst,Prod.snd] at he
  rw [hF] at he
  have hFl : D.localizers.distribution (k:ℝ) p
      ((D.localizers.realLower ((k+1:ℕ):ℝ) (k:ℝ) (by push_cast; linarith) F).val) =
      D.localizers.distribution ((k+1:ℕ):ℝ) p F.val :=
    D.localizers.distribution_lower (by push_cast; linarith) p F.val
  rw [hFl] at he
  change frozenDifferential (D.patch p).matrix (realize ((k:ℝ)+2) (w.val.val p)) +
    ((perturbation (stdOrthonormalBasis ℝ (EC d))
      (D.cofactorBCF (k+1) (by omega) hs p u.val) w₂ : L2 (EC d)) : 𝓢'(EC d,ℂ)) =
      realize ((k+1:ℕ):ℝ) (F.val.val p) + realize ((k+1:ℕ):ℝ) E at he
  have hx : (1^2:ℂ) • realize 2 w₂ - frozenDifferential (D.patch p).matrix (realize 2 w₂) -
      ((perturbation (stdOrthonormalBasis ℝ (EC d))
        (fun i j => strongEmbedding ((k+1:ℕ):ℝ) hs (a i j)) w₂ : L2 (EC d)) : 𝓢'(EC d,ℂ)) =
      realize ((k+1:ℕ):ℝ) f := by
    simp only [one_pow,one_smul,f,map_sub,realize_lowerCoord,w₂]
    change realize ((k:ℝ)+2) (w.val.val p) -
      frozenDifferential (D.patch p).matrix (realize ((k:ℝ)+2) (w.val.val p)) -
      ((perturbation (stdOrthonormalBasis ℝ (EC d)) (D.cofactorBCF (k+1) (by omega) hs p u.val)
        (lowerCoord ((k:ℝ)+2) 2 (by linarith [Nat.cast_nonneg (α:=ℝ) k]) (w.val.val p)) : L2 (EC d)) : 𝓢'(EC d,ℂ)) = _
    rw [sub_sub,he]
    abel
  have hg := rough_equation_memSobolev (D.patch p).matrix (D.patch p).positive 1 le_rfl
    (stdOrthonormalBasis ℝ (EC d)) (k+1) (by omega) hs a f w₂ (hu p) hx
  simpa only [w₂,realize_lowerCoord,Localizers.distribution_apply] using hg

lemma real_sobolev_of_local_order (k l : ℕ) (hkl : l ≤ k)
    (w : D.localizers.RealSobolev (l:ℝ))
    (hw : ∀ p, MemSobolev (k:ℝ) 2 (D.localizers.distribution (l:ℝ) p w.val)) :
    ∃ z : D.localizers.RealSobolev (k:ℝ),
      D.localizers.realLower (k:ℝ) (l:ℝ) (by exact_mod_cast hkl) z = w := by
  let w₀ := D.localizers.lower (l:ℝ) 0 w.val
  have hh (p : ι) : MemSobolev (k:ℝ) 2 (D.localizers.distribution 0 p w₀) := by
    rw [D.localizers.distribution_lower (Nat.cast_nonneg l)]
    exact hw p
  obtain ⟨z,hz⟩ := D.sobolev_of_local_order k w₀ hh
  have he : D.localizers.lower (k:ℝ) (l:ℝ) z = w.val := by
    apply D.localizers.lower_injective (Nat.cast_nonneg l)
    rw [D.localizers.lower_lower (by exact_mod_cast hkl) (Nat.cast_nonneg l)]
    exact hz
  have hm := D.mem_real_of_lower k l hkl z (he.symm ▸ w.property)
  exact ⟨⟨z,hm⟩,Subtype.ext he⟩

lemma real_sobolev_of_local_order_eq (k l : ℕ) (hkl : l ≤ k) (s t : ℝ)
    (hs : (k:ℝ) = s) (ht : (l:ℝ) = t)
    (w : D.localizers.RealSobolev t)
    (hw : ∀ p, MemSobolev s 2 (D.localizers.distribution t p w.val)) :
    ∃ z : D.localizers.RealSobolev s,
      D.localizers.realLower s t (by rw [← hs,← ht]; exact_mod_cast hkl) z = w := by
  subst s; subst t
  exact D.real_sobolev_of_local_order k l hkl w hw

 

theorem cofactor_global_gain (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hs : (Module.finrank ℝ (EC d):ℝ) < 2*((k+1:ℕ):ℝ))
    (u : D.localizers.RealSobolev (((k+1:ℕ):ℝ)+2))
    (hu : D.CofactorSmall (k+1) (by omega) hs u.val)
    (w : D.localizers.RealSobolev ((k:ℝ)+2))
    (F : D.localizers.RealSobolev ((k+1:ℕ):ℝ))
    (hF : D.realVolumeDerivative k hk
      (D.localizers.realLower (((k+1:ℕ):ℝ)+2) ((k:ℝ)+2) (by push_cast; linarith) u) w =
      D.localizers.realLower ((k+1:ℕ):ℝ) (k:ℝ) (by push_cast; linarith) F) :
    ∃ z : D.localizers.RealSobolev (((k+1:ℕ):ℝ)+2),
      D.localizers.realLower (((k+1:ℕ):ℝ)+2) ((k:ℝ)+2) (by push_cast; linarith) z = w := by
  exact D.real_sobolev_of_local_order_eq (k+3) (k+2) (by omega)
    (((k+1:ℕ):ℝ)+2) ((k:ℝ)+2) (by push_cast; ring) (by push_cast; rfl)
    w (D.cofactor_local_gain k hk hs u hu w F hF)

end GluingData
end GlobalElliptic

end
end

end OAI
