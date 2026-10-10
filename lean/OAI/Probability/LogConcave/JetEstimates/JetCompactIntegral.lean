import Mathlib
import OAI.Probability.LogConcave.JetEstimates.SplitBundle

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace JetCalculus
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma jet_compact_integral {f : E × ℝ → ℝ} (hf : ContDiff ℝ (⊤:ℕ∞) f)
    {s : Set ℝ} (hs : IsCompact s) {ι : Type} (v : ι → E) (l : List ι) (y : E) :
    jet v l (fun y => ∫t in s,f (y,t)) y=
      ∫t in s,jet (fun i => (v i,0)) l f (y,t) := by
  induction l generalizing y with
  | nil => rfl
  | cons k l ih =>
    let J := jet (fun i => (v i,0)) l f
    have hJ : ContDiff ℝ (⊤:ℕ∞) J := smooth_jet hf _ _
    have he : jet v l (fun y => ∫t in s,f (y,t))=fun y => ∫t in s,J (y,t) := funext ih
    change dir (v k) (jet v l (fun y => ∫t in s,f (y,t))) y=_
    rw [he]
    have hd := CompactIntegral.parametric_hasFDerivAt (hJ.of_le (by simp)) hs y
    unfold dir
    rw [hd.fderiv]
    have hI : IntegrableOn (fun t => (fderiv ℝ J (y,t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) s :=
      (((hJ.continuous_fderiv (by simp)).comp (continuous_const.prodMk continuous_id)).clm_comp
        continuous_const).continuousOn.integrableOn_compact hs
    rw [ContinuousLinearMap.integral_apply hI]
    rfl
end JetCalculus

namespace TensorEnergy
lemma AllSplitBound.compact_integral {S : Type} [Fintype S] [DecidableEq S] {d : ℕ}
    {A : ℝ → (S → Fin d) → ℝ} {s : Set ℝ} (hs : IsCompact s)
    (hA : ∀c,Continuous (fun t => A t c)) {B : ℝ} (hB : 0≤B)
    (hb : ∀t∈s,AllSplitBound (A t) B) :
    AllSplitBound (fun c => ∫t in s,A t c) (volume.real s*B) := by
  have hc : Continuous A := continuous_pi hA
  have hi : IntegrableOn A s := hc.continuousOn.integrableOn_compact hs
  have he : (fun c => ∫t in s,A t c)=∫t in s,A t := by
    funext c
    exact ((ContinuousLinearMap.proj c : ((S → Fin d) → ℝ) →L[ℝ] ℝ).integral_comp_comm hi)
  rw [he]
  have hbi := (splitBundle (S:=S) (d:=d)).integral_comp_comm hi
  have hbound := norm_setIntegral_le_of_norm_le_const (μ:=volume) (s:=s)
    (f:=fun t => splitBundle (A t)) hs.measure_lt_top
    (fun t ht => bundle_norm_le hB (hb t ht))
  rw [hbi] at hbound
  exact (allSplitBound_bundle _).mono (norm_nonneg _) (by simpa only [mul_comm] using hbound)

lemma array_iterated_eq_jet {d n : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    {g : Point d → (S → Fin d) → ℝ} (hg : ContDiff ℝ (⊤:ℕ∞) g)
    (y : Point d) (c : S ⊕ Fin n → Fin d) :
    arrayTensor (iteratedFDeriv ℝ n g y) c=
      JetCalculus.jet (fun i => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr i)))
        (List.finRange n) (fun z => g z (fun s => c (Sum.inl s))) y := by
  let L : ((S → Fin d) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (fun s => c (Sum.inl s))
  change _=JetCalculus.jet _ _ (L ∘ g) y
  rw [JetCalculus.jet_finRange_eq_iteratedFDeriv (L.contDiff.comp hg),
    L.iteratedFDeriv_comp_left hg.contDiffAt (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))]
  rfl

lemma array_iterated_joint_jet {d n : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    {g : Point d × ℝ → (S → Fin d) → ℝ} (hg : ContDiff ℝ (⊤:ℕ∞) g)
    (y : Point d) (t : ℝ) (c : S ⊕ Fin n → Fin d) :
    arrayTensor (iteratedFDeriv ℝ n (fun z => g (z,t)) y) c=
      JetCalculus.jet (fun i => (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr i)),(0:ℝ)))
        (List.finRange n) (fun z => g z (fun s => c (Sum.inl s))) (y,t) := by
  have hz : ContDiff ℝ (⊤:ℕ∞) (fun z => g (z,t)) := hg.comp (contDiff_id.prodMk contDiff_const)
  rw [array_iterated_eq_jet hz]
  exact JetCalculus.jet_left_slice
    ((ContinuousLinearMap.proj _ : ((S → Fin d) → ℝ) →L[ℝ] ℝ).contDiff.comp hg) _ _ _ _

lemma arrayTensor_compact_integral {d n : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    {g : Point d × ℝ → (S → Fin d) → ℝ} (hg : ContDiff ℝ (⊤:ℕ∞) g)
    {s : Set ℝ} (hs : IsCompact s) (y : Point d) (c : S ⊕ Fin n → Fin d) :
    arrayTensor (iteratedFDeriv ℝ n (fun z => ∫t in s,g (z,t)) y) c=
      ∫t in s,arrayTensor (iteratedFDeriv ℝ n (fun z => g (z,t)) y) c := by
  rw [array_iterated_eq_jet (CompactIntegral.smooth_parametric hg hs)]
  have he : (fun z => (∫t in s,g (z,t)) (fun s => c (Sum.inl s)))=
      fun z => ∫t in s,g (z,t) (fun s => c (Sum.inl s)) := by
    funext z
    exact ((ContinuousLinearMap.proj (fun s => c (Sum.inl s)) : ((S → Fin d) → ℝ) →L[ℝ] ℝ).integral_comp_comm
      ((hg.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hs)).symm
  have hc : ContDiff ℝ (⊤:ℕ∞) (fun z => g z (fun s => c (Sum.inl s))) :=
    (ContinuousLinearMap.proj _ : ((S → Fin d) → ℝ) →L[ℝ] ℝ).contDiff.comp hg
  rw [he,JetCalculus.jet_compact_integral hc hs]
  apply integral_congr_ae
  filter_upwards [] with t
  exact (array_iterated_joint_jet hg y t c).symm

lemma compactIntegral_iterated_split {d n : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    {g : Point d × ℝ → (S → Fin d) → ℝ} (hg : ContDiff ℝ (⊤:ℕ∞) g)
    {s : Set ℝ} (hs : IsCompact s) (y : Point d) {B : ℝ} (hB : 0≤B)
    (hb : ∀t∈s,AllSplitBound (arrayTensor (iteratedFDeriv ℝ n (fun z => g (z,t)) y)) B) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n (fun z => ∫t in s,g (z,t)) y)) (volume.real s*B) := by
  have hc (c : S ⊕ Fin n → Fin d) : Continuous
      (fun t => arrayTensor (iteratedFDeriv ℝ n (fun z => g (z,t)) y) c) := by
    simp_rw [array_iterated_joint_jet hg]
    exact (JetCalculus.smooth_jet
      ((ContinuousLinearMap.proj _ : ((S → Fin d) → ℝ) →L[ℝ] ℝ).contDiff.comp hg) _ _).continuous.comp
      (continuous_const.prodMk continuous_id)
  have he : arrayTensor (iteratedFDeriv ℝ n (fun z => ∫t in s,g (z,t)) y)=
      fun c => ∫t in s,arrayTensor (iteratedFDeriv ℝ n (fun z => g (z,t)) y) c :=
    funext (arrayTensor_compact_integral hg hs y)
  rw [he]
  exact AllSplitBound.compact_integral hs hc hB hb
end TensorEnergy
end LogConcaveSampling

end

end

end

end OAI
