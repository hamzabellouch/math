import Mathlib
import OAI.Combinatorics.UniformKServer.PilotEdits

namespace OAI

noncomputable section

/-! Linear adapted auxiliary potentials commute with posterior filtering. -/
namespace UniformKServer.PilotEdits
open Finset
open scoped Classical
variable {X Ω : Type} [Fintype X] [Fintype Ω] {k : ℕ}

def linearPotential (μ b : X→ℝ) : ℝ := ∑ p,μ p*b p

theorem linear_filtering (F : Flow X Ω k) (t : ℕ) (b : Ω→X→ℝ)
    (hb : ∀ ω v, (F.filtration t).r ω v→b ω=b v) :
    average F.weight (fun ω=>linearPotential (F.filtered t ω) (b ω))=
      average F.weight (fun ω=>linearPotential (F.post t ω) (b ω)) := by
  have hp (p : X) := F.filtering t (fun ω=>b ω p) (fun ω v hv=>congrFun (hb ω v hv) p) p
  unfold average linearPotential
  simp only [mul_sum]
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro p _
  have he : (∑ ω,F.weight ω*b ω p*(F.filtered t ω p-F.post t ω p))=
      (∑ ω,F.weight ω*(F.filtered t ω p*b ω p))-
      (∑ ω,F.weight ω*(F.post t ω p*b ω p)) := by
    rw [←sum_sub_distrib]
    apply sum_congr rfl
    intro ω _
    ring
  linarith only [hp p,he]

theorem linear_bounds (F : Flow X Ω k) (t : ℕ) (ω : Ω) (b : X→ℝ) (M : ℝ)
    (hb : ∀ p,0≤b p ∧ b p≤M) :
    0≤linearPotential (F.post t ω) b ∧ linearPotential (F.post t ω) b≤k*M := by
  constructor
  · exact sum_nonneg (fun p _=>mul_nonneg (F.post_nonneg t ω p) (hb p).1)
  · calc
      _≤∑ p,F.post t ω p*M := sum_le_sum (fun p _=>mul_le_mul_of_nonneg_left (hb p).2 (F.post_nonneg t ω p))
      _=_ := by rw [←sum_mul,F.post_total]

theorem linear_edits (F : Flow X Ω k) (H : ℕ) (b : ℕ→Ω→X→ℝ) (M : ℝ)
    (hb : ∀ t ω p,0≤b t ω p ∧ b t ω p≤M)
    (hmeas : ∀ t ω v,(F.filtration t).r ω v→b t ω=b t v)
    (cost allowance : ℕ→Ω→ℝ)
    (hstep : ∀ t<H,∀ ω,cost t ω+linearPotential (F.post (t+1) ω) (b (t+1) ω)-
      linearPotential (F.filtered t ω) (b t ω)≤allowance t ω) :
    (∑ t∈range H,average F.weight (cost t))≤
      (∑ t∈range H,average F.weight (allowance t))+k*M := by
  let Φ : ℕ→ℝ := fun t=>average F.weight (fun ω=>linearPotential (F.post t ω) (b t ω))
  have hs (t : ℕ) (ht : t<H) : average F.weight (cost t)+Φ (t+1)-Φ t≤average F.weight (allowance t) := by
    have h := average_mono F.weight _ _ F.weight_nonneg (hstep t ht)
    rw [average_sub,average_add,linear_filtering F t (b t) (hmeas t)] at h
    exact h
  have htel (T : ℕ) (hT : T≤H) :
      (∑ t∈range T,average F.weight (cost t))+Φ T≤Φ 0+(∑ t∈range T,average F.weight (allowance t)) := by
    induction T with
    | zero => simp
    | succ T ih =>
      have h := ih (by omega)
      have ht := hs T (by omega)
      rw [sum_range_succ,sum_range_succ]
      linarith
  have hn : 0≤Φ H := sum_nonneg (fun ω _=>mul_nonneg (F.weight_nonneg ω) (linear_bounds F H ω (b H ω) M (hb H ω)).1)
  have hi : Φ 0≤k*M := by
    have h := average_mono F.weight _ (fun _=>(k:ℝ)*M) F.weight_nonneg
      (fun ω=>(linear_bounds F 0 ω (b 0 ω) M (hb 0 ω)).2)
    simpa only [Φ,average,←sum_mul,F.weight_total,one_mul] using h
  have h := htel H le_rfl
  linarith

end UniformKServer.PilotEdits

end

end OAI
