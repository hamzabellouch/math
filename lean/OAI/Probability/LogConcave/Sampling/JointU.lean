import Mathlib
import OAI.Probability.LogConcave.Sampling.ScaledMeanJet
import OAI.Probability.LogConcave.JetEstimates.GadjScalar

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Filter
open scoped Topology Classical BigOperators NNReal RealInnerProductSpace

def jointU {d : ℕ} {κ : Type*} (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (v : κ → Point d) (l : List κ) (i : Fin d) (p : ℝ × Point d) : ℝ :=
  conditionalU F x r p.1 p.2 (EuclideanSpace.basisFun (Fin d) ℝ i) L v l

lemma jointU_eventually_scaled {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    {κ : Type*} (v : κ → Point d) (l : List κ) (i : Fin d) (y : Point d) :
    jointU F x r ((lam:ℝ)*r) v l i=ᶠ[nhds (ρ,y)]scaledMeanJet F x r v l i := by
  have hn : ∀ᶠp : ℝ × Point d in nhds (ρ,y),p.1∈Set.Ioo (0:ℝ) 1 :=
    continuousAt_fst.eventually (Ioo_mem_nhds hρ0 hρ1)
  filter_upwards [hn] with p hp
  exact (scaledMeanJet_eq_U hF x hr hlam hl hp.1 hp.2 v l i p.2).symm

lemma jointU_smooth_pos {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    {κ : Type*} (v : κ → Point d) (l : List κ) (i : Fin d) (y : Point d) :
    ContDiffAt ℝ (⊤:ℕ∞) (jointU F x r ((lam:ℝ)*r) v l i) (ρ,y) := by
  apply ContDiffAt.congr_of_eventuallyEq _ (jointU_eventually_scaled hF x hr hlam hl hρ0 hρ1 v l i y)
  unfold scaledMeanJet
  exact ((contDiffAt_fst.pow _).inv (pow_ne_zero _ hρ0.ne')).mul
    (JetCalculus.smooth_jet_at (jointMean_smooth_at hF x hr.le hl (by nlinarith) i) _ l)

lemma split_power_cancel {κ : Type*} [DecidableEq κ] (l : List κ) (s : Finset κ)
    {ρ : ℝ} (hρ : ρ≠0) :
    (ρ^l.length)⁻¹*ρ^(l.filter (fun j => j∈s)).length*
      ρ^((l.filter (fun j => j∉s)).length+1)=ρ := by
  have hl : l.length=(l.filter (fun j => j∈s)).length+(l.filter (fun j => j∉s)).length := by
    simpa only [←decide_not] using l.length_eq_length_filter_add (fun j => decide (j∈s))
  rw [hl,pow_add,pow_succ]
  field_simp

theorem material_conditionalU_pos {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    {κ : Type*} [DecidableEq κ] (v : κ → Point d) (l : List κ) (hlN : l.Nodup)
    (i : Fin d) (y : Point d) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
      (jointU F x r ((lam:ℝ)*r) v l i) (ρ,y)=
      JetCalculus.gadj (JetCalculus.spaceBasis d) (fun k z => jointScore F x r k (ρ,z))
        (fun k z => jointU F x r ((lam:ℝ)*r)
          (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k)) (Sum.inr ()::l.map Sum.inl) i (ρ,z)) y+
      2*r*ρ*∑s∈l.toFinset.powerset.erase ∅,∑k,
        jointU F x r ((lam:ℝ)*r) v (l.filter (fun j => j∈s)) k (ρ,y)*
          jointU F x r ((lam:ℝ)*r) (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k))
            (Sum.inr ()::(l.filter (fun j => j∉s)).map Sum.inl) i (ρ,y) := by
  have he := (JetCalculus.mdir_eventuallyEq (1,0) jointSpace r (M:=jointMean F x r) (fun _ => EventuallyEq.rfl)
    (jointU_eventually_scaled hF x hr hlam hl hρ0 hρ1 v l i y)).eq_of_nhds
  rw [he,material_scaledMeanJet hF x hr hlam hl hρ0 hρ1 v l hlN]
  have hU (k : Fin d) := conditionalU_smooth_pos hF x hr hlam hl hρ0 hρ1
    (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k)) (Sum.inr ()::l.map Sum.inl)
      (EuclideanSpace.basisFun (Fin d) ℝ i)
  have hdir := dir_mean_jet_eq_scaled_U hF x hr hlam hl hρ0.le hρ1 v l i
  simp_rw [hdir]
  rw [JetCalculus.gadj_scalar _ _ (fun k => (hU k).differentiable (by simp))]
  dsimp only
  have hscale : (ρ^(l.length+1))⁻¹*ρ^(l.length+1)=1 := inv_mul_cancel₀ (pow_ne_zero _ hρ0.ne')
  rw [←mul_assoc,hscale,one_mul]
  congr 1
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [mean_jet_eq_scaled_U hF x hr hlam hl hρ0.le hρ1,
    dir_mean_jet_eq_scaled_U hF x hr hlam hl hρ0.le hρ1]
  dsimp only
  have hs := split_power_cancel l s hρ0.ne'
  unfold jointU
  calc
    _ = 2*r*((ρ^l.length)⁻¹*ρ^(l.filter (fun j => j∈s)).length*
        ρ^((l.filter (fun j => j∉s)).length+1))*
        (conditionalU F x r ρ y (EuclideanSpace.basisFun (Fin d) ℝ k) ((lam:ℝ)*r) v
          (l.filter (fun j => j∈s))*conditionalU F x r ρ y (EuclideanSpace.basisFun (Fin d) ℝ i)
            ((lam:ℝ)*r) (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k))
              (Sum.inr ()::(l.filter (fun j => j∉s)).map Sum.inl)) := by ring
    _ = _ := by rw [hs]

end LogConcaveSampling

end

end

end

end OAI
