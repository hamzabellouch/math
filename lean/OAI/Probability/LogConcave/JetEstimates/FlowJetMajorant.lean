import Mathlib
import OAI.Probability.LogConcave.JetEstimates.SmoothTensorCurve

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open Set Function
open scoped Classical BigOperators RealInnerProductSpace

def flowJetMajorant (A : ℕ → ℝ) (hA : ∀k,0≤A k) (n : ℕ) : ℝ :=
  (smoothTensorCurve_bounds A hA n).choose
lemma flowJetMajorant_nonneg (A : ℕ → ℝ) (hA : ∀k,0≤A k) (n : ℕ) :
    0≤flowJetMajorant A hA n := (smoothTensorCurve_bounds A hA n).choose_spec.1

def flowCorrectionMajorant (A : ℕ → ℝ) (hA : ∀k,0≤A k) (n : ℕ) : ℝ :=
  ∑c : OrderedFinpartition n,A c.length*∏i,flowJetMajorant A hA (c.partSize i)
lemma flowCorrectionMajorant_nonneg (A : ℕ → ℝ) (hA : ∀k,0≤A k) (n : ℕ) :
    0≤flowCorrectionMajorant A hA n :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (hA _) (Finset.prod_nonneg (fun _ _ => flowJetMajorant_nonneg A hA _)))

lemma multilinearTensor_sub {d n : ℕ} (f g : Point d → Point d)
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (hg : ContDiff ℝ (⊤:ℕ∞) g) (y : Point d) :
    multilinearTensor (iteratedFDeriv ℝ n (fun z => f z-g z) y)=
      multilinearTensor (iteratedFDeriv ℝ n f y)-multilinearTensor (iteratedFDeriv ℝ n g y) := by
  change multilinearTensor (iteratedFDeriv ℝ n (f-g) y)=_
  rw [iteratedFDeriv_sub_apply (hf.contDiffAt.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤)))
    (hg.contDiffAt.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤)))]
  ext c
  simp only [multilinearTensor,sub_apply,inner_sub_right,Pi.sub_apply]

theorem smoothTensorCurve_correction {d n : ℕ} (hn : 0<n) (A : ℕ → ℝ) (hA : ∀k,0≤A k)
    {R b η : ℝ} (hR : 0<R) (hR1 : R≤1) (hb : 0≤b) (hb1 : b≤1) (hη : 0≤η)
    (X : ℝ × Point d → Point d) (V : ℝ → Point d → Point d)
    (hX : SmoothTensorCurve d A R b X V)
    (hv : ∀k u,u∈Icc 0 b → ∀z,AllSplitBound
      (multilinearTensor (iteratedFDeriv ℝ k (V u) z)) (η*A k/R^(k-1)))
    {t : ℝ} (ht : t∈Icc 0 b) (y : Point d) :
    AllSplitBound (multilinearTensor (iteratedFDeriv ℝ n (fun z => X (t,z)-z) y))
      (η*flowCorrectionMajorant A hA n/R^(n-1)) := by
  let T (u : ℝ) := multilinearTensor (iteratedFDeriv ℝ n (fun z => X (u,z)) y)-
    multilinearTensor (iteratedFDeriv ℝ n (id : Point d → Point d) y)
  let D (u : ℝ) := multilinearTensor (iteratedFDeriv ℝ n (fun z => V u (X (u,z))) y)
  let M (k : ℕ) := (η*A k)/R^(k-1)
  let N (k : ℕ) := flowJetMajorant A hA k/R^(k-1)
  have hM (k : ℕ) : 0≤M k := by exact div_nonneg (mul_nonneg hη (hA k)) (pow_nonneg hR.le _)
  have hN (k : ℕ) : 0≤N k := div_nonneg (flowJetMajorant_nonneg A hA _) (pow_nonneg hR.le _)
  have hflow (k : ℕ) (u : ℝ) (hu : u∈Icc 0 b) :
      AllSplitBound (multilinearTensor (iteratedFDeriv ℝ k (fun z => X (u,z)) y)) (N k) :=
    (smoothTensorCurve_bounds A hA k).choose_spec.2 d R b X V hR hR1 hb hb1 hX u hu y
  have hbound (u : ℝ) (hu : u∈Ico 0 b) :
      AllSplitBound (D u) (η*flowCorrectionMajorant A hA n/R^(n-1)) := by
    have hs : ContDiff ℝ (⊤:ℕ∞) (fun z => X (u,z)) := hX.smooth.comp (contDiff_const.prodMk contDiff_id)
    have hvs := (hX.velocity_smooth u ⟨hu.1,hu.2.le⟩).contDiffAt (x:=X (u,y))
    have he := iteratedFDeriv_comp_allSplit y
      (hs.contDiffAt.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤)))
      (hvs.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))) M N hM hN
      (fun k hk => hv k u ⟨hu.1,hu.2.le⟩ (X (u,y)))
      (fun k hk => hflow k u ⟨hu.1,hu.2.le⟩)
    have heq : (∑c : OrderedFinpartition n,M c.length*∏i,N (c.partSize i))=
        η*flowCorrectionMajorant A hA n/R^(n-1) := by
      dsimp only [M,N]
      rw [partition_sum_scale hn (fun k => η*A k) (flowJetMajorant A hA) R]
      simp only [flowCorrectionMajorant,←Finset.mul_sum,mul_assoc]
    rw [heq] at he
    exact he
  have hinit : AllSplitBound (T 0) 0 := by
    have he : (fun z => X (0,z))=(id : Point d → Point d) := funext hX.initial
    dsimp only [T]
    rw [he,sub_self]
    exact allSplitBound_zero
  have hpos : 0≤η*flowCorrectionMajorant A hA n/R^(n-1) :=
    div_nonneg (mul_nonneg hη (flowCorrectionMajorant_nonneg A hA n)) (pow_nonneg hR.le _)
  have hg := allSplit_gronwall (T:=T) (D:=D) (K:=0)
    ((spatialTensor_continuous hX.smooth y).sub continuous_const).continuousOn
    (fun u hu => ((spatialTensor_time_deriv hX.smooth (V u) u
      (hX.equation u ⟨hu.1,hu.2.le⟩) y).sub_const _).hasDerivWithinAt)
    (le_refl (0:ℝ)) hpos (le_refl (0:ℝ)) hinit
    (fun u hu => by simpa only [zero_mul,zero_add] using hbound u hu) ht
  simp only [gronwallBound_K0,zero_add,sub_zero] at hg
  have hfinal := hg.mono (mul_nonneg hpos ht.1) (mul_le_of_le_one_right hpos (ht.2.trans hb1))
  have hs : ContDiff ℝ (⊤:ℕ∞) (fun z => X (t,z)) := hX.smooth.comp (contDiff_const.prodMk contDiff_id)
  rw [multilinearTensor_sub (fun z => X (t,z)) (fun z => z) hs contDiff_id]
  exact hfinal
end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
