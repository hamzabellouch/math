import Mathlib
import OAI.Probability.LogConcave.JetEstimates.JetRightSlice

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

def scaledMeanJet {d : ℕ} {κ : Type*} (F : Point d → ℝ) (x : Point d) (r : ℝ)
    (v : κ → Point d) (l : List κ) (i : Fin d) (p : ℝ × Point d) : ℝ :=
  (p.1^l.length)⁻¹*JetCalculus.jet (fun j => (0,v j)) l (jointMean F x r i) p

lemma scaledMeanJet_eq_U {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    {κ : Type*} (v : κ → Point d) (l : List κ) (i : Fin d) (y : Point d) :
    scaledMeanJet F x r v l i (ρ,y)=
      conditionalU F x r ρ y (EuclideanSpace.basisFun (Fin d) ℝ i) ((lam:ℝ)*r) v l := by
  have hp : ρ^2<1 := by nlinarith
  have hj := JetCalculus.jet_right_slice_at (fun z => jointMean_smooth_at hF x hr.le hl (p:=(ρ,z)) hp i) v l
  have hm : conditionalMeanScalar F x r ρ
      (fun z => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i) (primitiveField F x r z))=
      fun z => jointMean F x r i (ρ,z) :=
    (funext (conditionalFieldMean_inner hF x hr.le hl hρ0.le hρ1 _)).symm
  have hU := conditionalFieldMean_jet_U hF x hr hlam hl hρ0.le hρ1
    (EuclideanSpace.basisFun (Fin d) ℝ i) y v l
  rw [hm] at hU
  unfold scaledMeanJet
  rw [←congrFun hj y,hU]
  field_simp [hρ0.ne']

theorem material_scaledMeanJet {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    {κ : Type*} [DecidableEq κ] (v : κ → Point d) (l : List κ) (hlN : l.Nodup)
    (i : Fin d) (y : Point d) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (scaledMeanJet F x r v l i) (ρ,y)=
      (ρ^(l.length+1))⁻¹*JetCalculus.gadj (JetCalculus.spaceBasis d)
        (fun k z => jointScore F x r k (ρ,z))
        (fun k => JetCalculus.dir (JetCalculus.spaceBasis d k)
          (JetCalculus.jet v l (fun z => jointMean F x r i (ρ,z)))) y+
        2*r*(ρ^l.length)⁻¹*∑s∈l.toFinset.powerset.erase ∅,∑k,
          JetCalculus.jet v (l.filter (fun j => j∈s)) (fun z => jointMean F x r k (ρ,z)) y*
            JetCalculus.dir (JetCalculus.spaceBasis d k)
              (JetCalculus.jet v (l.filter (fun j => j∉s)) (fun z => jointMean F x r i (ρ,z))) y := by
  have hp : ρ^2<1 := by nlinarith
  have hJ (z : Point d) := jointMean_smooth_at hF x hr.le hl (p:=(ρ,z)) hp i
  have hc := JetCalculus.hasDerivAt_inv_nat_pow hρ0.ne' l.length
  have he := JetCalculus.mdir_time_mul_at (JetCalculus.spaceBasis d) r (jointMean F x r)
    hc.differentiableAt ((JetCalculus.smooth_jet_at (hJ y) (fun j => (0,v j)) l).differentiableAt (by simp))
  change JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (scaledMeanJet F x r v l i) (ρ,y)=_ at he
  rw [he,hc.deriv]
  change -↑l.length*ρ⁻¹*(ρ^l.length)⁻¹*JetCalculus.jet (fun j => (0,v j)) l (jointMean F x r i) (ρ,y)+
    (ρ^l.length)⁻¹*JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
      (JetCalculus.jet (fun j => (0,v j)) l (jointMean F x r i)) (ρ,y)=_
  rw [material_mean_jet hF x hr hlam hl hρ0 hρ1 v l hlN i y]
  rw [←congrFun (JetCalculus.jet_right_slice_at hJ v l) y]
  simp only [pow_succ,mul_inv_rev]
  ring

end LogConcaveSampling

end

end

end

end OAI
