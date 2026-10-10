import Mathlib
import OAI.Probability.LogConcave.Sampling.TransportMajorant
import OAI.Probability.LogConcave.JetEstimates.ArrayRelabel

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function
open scoped Classical NNReal BigOperators
open TensorEnergy

def composedJetMajorant (n : ℕ) : ℝ :=
  ∑c : OrderedFinpartition n,normalizedTensorMajorant (c.length+2) 1*∏i,transportMajorant (c.partSize i)
lemma composedJetMajorant_nonneg (n : ℕ) : 0≤composedJetMajorant n :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (normalizedTensorMajorant_nonneg _ _)
    (Finset.prod_nonneg (fun _ _ => transportMajorant_nonneg _)))

lemma backwardFirstJet_iterated_split {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hR : 0<R) (hRT : R^2≤1-T^2)
    (hT0 : 0≤T) (hT1 : T<1) (t : Icc (0:ℝ) T) (y : Point d) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n
      (fun z => matrixArray d (conditionalFirstJet F x r ((lam:ℝ)*r)
        (t,terminalBackward hF x hr.le hl hT0 hT1 (t,z)))) y))
      (((lam:ℝ)*r)*composedJetMajorant n/R^n) := by
  let f := probabilityTransport hF x hr.le hl hT0 hT1 ⟨T,hT0,le_rfl⟩ t
  let g := fun z => matrixArray d (conditionalFirstJet F x r ((lam:ℝ)*r) (t,z))
  have hf : ContDiff ℝ (⊤:ℕ∞) f := probabilityTransport_smooth hF x hr.le hl hT0 hT1 _ _
  have ht2 : (t:ℝ)^2<1 := by nlinarith [t.2.1,t.2.2]
  have hg0 : ContDiff ℝ (⊤:ℕ∞) (fun z => conditionalFirstJet F x r ((lam:ℝ)*r) (t,z)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    exact (conditionalFirstJet_smooth hF x hr hlam hl ((t:ℝ),z) ht2).comp z
      (contDiffAt_const.prodMk contDiffAt_id)
  have hg : ContDiff ℝ (⊤:ℕ∞) g := (matrixArray d).contDiff.comp hg0
  have htR : R^2≤1-(t:ℝ)^2 := by nlinarith [t.2.1,t.2.2]
  have hh := array_composition_scale (n:=n) y hf hg
    (fun k => ((lam:ℝ)*r)*normalizedTensorMajorant (k+2) 1) transportMajorant
    (fun k => mul_nonneg (mul_nonneg lam.2 hr.le) (normalizedTensorMajorant_nonneg _ _))
    transportMajorant_nonneg R hR 0
    (fun order _ => by simpa only [Nat.add_zero] using
      conditionalFirstJet_iterated_split (n:=order) hF x hr hlam hl t.2.1 (t.2.2.trans_lt hT1) hR htR (f y))
    (fun _ _ => transportMajorant_bound hF x hr hlam hl hR hRT hT0 hT1 _ _ y)
  have he : (fun z => matrixArray d (conditionalFirstJet F x r ((lam:ℝ)*r)
        (t,terminalBackward hF x hr.le hl hT0 hT1 (t,z))))=g ∘ f := by
    funext z
    rw [terminalBackward_eq]
    rfl
  rw [he]
  simpa only [Nat.add_zero,composedJetMajorant,Finset.mul_sum,mul_assoc] using hh

def kernelMajorant (n : ℕ) : ℝ :=
  ∑s∈(Finset.univ : Finset (Fin n)).powerset,jacobianMajorant s.card*composedJetMajorant (n-s.card)
lemma kernelMajorant_nonneg (n : ℕ) : 0≤kernelMajorant n :=
  Finset.sum_nonneg (fun _ _ =>
    mul_nonneg (jacobianMajorant_nonneg _) (composedJetMajorant_nonneg _))

lemma steinIntegrand_iterated_split {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hR : 0<R) (hRT : R^2≤1-T^2)
    (hT0 : 0≤T) (hT1 : T<1) (t : Icc (0:ℝ) T) (y : Point d) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n
      (fun z => matrixArray d (steinIntegrand hF x hr hl hT0 hT1 (t,z))) y))
      (((lam:ℝ)*r)*kernelMajorant n/R^n) := by
  have hf : ContDiff ℝ (⊤:ℕ∞) (fun z => terminalJacobian hF x hr hl hT0 hT1 (t,z)) :=
    (terminalJacobian_smooth hF x hr hl hT0 hT1).comp
    (contDiff_const.prodMk (contDiff_id (E:=Point d)))
  have hg : ContDiff ℝ (⊤:ℕ∞) (fun z => conditionalFirstJet F x r ((lam:ℝ)*r)
      (t,terminalBackward hF x hr.le hl hT0 hT1 (t,z))) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    apply (conditionalFirstJet_smooth hF x hr hlam hl _ (by nlinarith [t.2.1,t.2.2])).comp z
    exact contDiffAt_const.prodMk
      (((terminalBackward_smooth hF x hr.le hl hT0 hT1).comp (contDiff_const.prodMk contDiff_id)).contDiffAt)
  have hh := matrixComposition_split (n:=n) hf hg
    (fun k => jacobianMajorant k/R^k) (fun k => ((lam:ℝ)*r)*composedJetMajorant k/R^k)
    (fun k => div_nonneg (jacobianMajorant_nonneg _) (pow_nonneg hR.le _))
    (fun k => div_nonneg (mul_nonneg (mul_nonneg lam.2 hr.le) (composedJetMajorant_nonneg _)) (pow_nonneg hR.le _)) y
    (fun _ _ => terminalJacobian_iterated_split hF x hr hlam hl hR hRT hT0 hT1 t y)
    (fun _ _ => backwardFirstJet_iterated_split hF x hr hlam hl hR hRT hT0 hT1 t y)
  have he (s : Finset (Fin n)) :
      (jacobianMajorant s.card/R^s.card)*(((lam:ℝ)*r)*composedJetMajorant (n-s.card)/R^(n-s.card))=
        ((lam:ℝ)*r)*(jacobianMajorant s.card*composedJetMajorant (n-s.card))/R^n := by
    rw [div_mul_div_comm,←pow_add,Nat.add_sub_of_le ((Finset.card_le_univ s).trans_eq (Fintype.card_fin n))]
    ring
  simp_rw [he] at hh
  simpa only [steinIntegrand,smoothTimeClip_eq hT0 hT1 t.2,kernelMajorant,
    ←Finset.sum_div,←Finset.mul_sum] using hh
end LogConcaveSampling

end

end

end

end OAI
