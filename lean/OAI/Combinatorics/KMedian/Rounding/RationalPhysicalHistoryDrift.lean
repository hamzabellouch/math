import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalPhysicalDrift
import OAI.Combinatorics.KMedian.Sparse.SparseBoundedDrift

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential FixedBatch Analytic CopyState
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}

theorem histories_drift (d₀ : F → F → ℚ) (location : F → X) (client : X)
    (hd₀ : ∀ i j, dist (location i) (location j)=(d₀ i j:ℝ))
    (g β p φ : ℚ) (P : ℕ → ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A S₀ : Finset (Copy (F := F) Δ)) (T : ℕ)
    {h R ζ : ℝ} (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : ∀ t < T, 0 < (P t:ℝ)) (hP1 : ∀ t < T, (P t:ℝ) ≤ 1/2)
    (hA : 1 ≤ mass (g:ℝ) A) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hφ1 : (φ:ℝ) ≤ 1)
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction (g:ℝ))
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1/4)
    (he : ∀ t < T, |(P t:ℝ)-Analytic.P (Real.exp (-(t:ℝ)*h))| ≤ ζ)
    (hactive : S₀ ⊆ A) (hm₀ : mass (g:ℝ) S₀=1)
    (hR0 : 0 ≤ R) (hdR : ∀ i ∈ S₀, dist client (location i.1) ≤ R)
    (hR : ∃ i ∈ S₀, R=dist client (location i.1)) :
    (histories d₀ g β p φ P hp hφ hupper A T).expectation (fun z =>
      potential (Real.exp (-(T:ℝ)*h)) (g:ℝ) (fun i => dist client (location i.1))
        (replay g β (fun t => Real.exp (-(t:ℝ)*h))
          (fun (_ : Unit) f => dist client (location f)) (fun _ => S₀) z ())
        (GroupCap.cap R (fun f => dist client (location f)) (integral Δ z.1.1))) ≤
      (1+2/Real.exp 1)*PhysicalPotential.cost (g:ℝ) (fun i => dist client (location i.1)) S₀+
      (T:ℝ)*(h*((g:ℝ)+12*ζ)*PhysicalPotential.cost (g:ℝ) (fun i => dist client (location i.1)) S₀+
        batchConstant Δ*h*((φ:ℝ)+h)*R) := by
  let x := fun t : ℕ => Real.exp (-(t:ℝ)*h)
  let d := fun f => dist client (location f)
  let κ := fun t => step (Δ := Δ) d₀ g β p φ (P t) hp hφ hupper
  let V := fun t (z : SparseHistories.History (State F Δ g β)) =>
    potential (x t) (g:ℝ) (fun i => d i.1)
      (replay g β x (fun (_ : Unit) => d) (fun _ => S₀) z ())
      (GroupCap.cap R d (integral Δ z.1.1))
  let V₀ := PhysicalPotential.cost (g:ℝ) (fun i => d i.1) S₀
  let E := h*((g:ℝ)+12*ζ)*V₀+batchConstant Δ*h*((φ:ℝ)+h)*R
  have hx0 : ∀ t, 0 ≤ x t := fun _ => (Real.exp_pos _).le
  have hx1 : ∀ t, x t ≤ 1 := fun t => Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg t)) hh0)
  have hxs : ∀ t, x (t+1)=x t*Real.exp (-h) := by
    intro t
    dsimp only [x]
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hstep : ∀ t < T, ∀ i : Fin (SparseHistories.tree κ (A,none) t).length,
      (κ t (SparseHistories.tree κ (A,none) t).states[i.val].1).expectation
        (fun s => V (t+1) (SparseHistories.extend (SparseHistories.tree κ (A,none) t).states[i.val] s)) ≤
      V t (SparseHistories.tree κ (A,none) t).states[i.val]+E := by
    intro t ht i
    let z := (SparseHistories.tree κ (A,none) t).states[i.val]
    let S := replay g β x (fun (_ : Unit) => d) (fun _ => S₀) z ()
    have hz : z.2.length=t := SparseHistories.past_length κ (A,none) t i
    have ha : S ⊆ z.1.1 := histories_alive d₀ g β p φ P hp hφ hupper A t
      x (fun (_ : Unit) => d) (fun _ => S₀) (fun _ => hactive) i ()
    have hs : S ⊆ S₀ := replay_subset g β x (fun (_ : Unit) => d) (fun _ => S₀) z ()
    have hm := histories_mass d₀ g β p φ P hp hφ hupper A t hg.le hunit hA i
    have htstep := step_drift d₀ location client hd₀ g β p φ (P t) hp hφ hupper z.1 S S₀
      hprob hg hg1 hunit (hP t ht) (hP1 t ht) hm (hx0 t) (hx1 t) hh0 hh1 hφ1
      hsmall hζ0 hζ1 (he t ht) ha hs hm₀ hR0 hdR hR
    have hv : ∀ s, V (t+1) (SparseHistories.extend z s)=
        potential (x t*Real.exp (-h)) (g:ℝ) (fun i => d i.1)
          (labels g β (x t) (fun (_ : Unit) => d) s (fun _ => S) ())
          (GroupCap.cap R d (integral Δ s.1)) := by
      intro s
      dsimp only [V]
      rw [replay_extend,hz,hxs]
      rfl
    change (κ t z.1).expectation (fun s => V (t+1) (SparseHistories.extend z s)) ≤ V t z+E
    simp_rw [hv]
    apply htstep.trans
    have hc := cost_mono hg.le (d := fun i : Copy (F := F) Δ => d i.1)
      (fun _ _ => dist_nonneg) hs
    have hc' := mul_le_mul_of_nonneg_left hc
      (show 0 ≤ h*((g:ℝ)+12*ζ) from mul_nonneg hh0 (by positivity))
    change V t z+h*((g:ℝ)+12*ζ)*PhysicalPotential.cost (g:ℝ) (fun i => d i.1) S+
      batchConstant Δ*h*((φ:ℝ)+h)*R ≤ V t z+E
    dsimp only [E,V₀]
    linarith only [hc']
  have ht := SparseHistories.accumulated_drift_up_to κ (A,none) V (fun _ => E) T hstep
  have hinit : V 0 ((A,none),[])=(1+2/Real.exp 1)*V₀ := by
    change potential (x 0) (g:ℝ) (fun i => d i.1) S₀ (GroupCap.cap R d (integral Δ A))=_
    simp only [x,Nat.cast_zero,neg_zero,zero_mul,Real.exp_zero]
    rw [potential,hm₀,sub_self,zero_mul,add_zero,← coefficient_eq]
    rw [coefficient,sub_self,mul_zero,add_zero,A_one]
  rw [hinit] at ht
  simpa only [sum_const,card_range,nsmul_eq_mul,V,V₀,E,x,d,κ,histories] using ht

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
