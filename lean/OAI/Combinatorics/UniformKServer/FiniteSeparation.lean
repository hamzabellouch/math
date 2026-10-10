import Mathlib
import OAI.Combinatorics.UniformKServer.FiniteProbability

namespace OAI

noncomputable section

/-! The exact finite separation step, with normalization and the empty-index
case handled from the stated hypotheses. No minimax theorem is assumed. -/
namespace UniformKServer.FiniteSeparation
open Finset FiniteProbability
open scoped Classical
variable {I : Type} [Fintype I]

theorem dual_sum (f : StrongDual ℝ (I→ℝ)) (x : I→ℝ) :
    f x=∑i,f (Pi.single i 1)*x i := by
  have hx : x=∑i,x i • (Pi.single i (1:ℝ)) := by
    ext j
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
    simp
  calc
    f x=f (∑i,x i • (Pi.single i (1:ℝ))) := congrArg f hx
    _=∑i,f (Pi.single i 1)*x i := by
      simp only [map_sum,map_smul,smul_eq_mul,mul_comm]

theorem finite_minimax (K : Set (I→ℝ)) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (hcompact : IsCompact K)
    (hlaw : ∀ P : Law I,∃x∈K,P.expect x≤0) :
    ∃x∈K,∀i,x i≤0 := by
  by_contra hn
  have hd : Disjoint (Set.Iic (0:I→ℝ)) K := by
    apply Set.disjoint_left.mpr
    intro x hx hK
    exact hn ⟨x,hK,hx⟩
  obtain ⟨f,u,v,hlo,huv,hhi⟩ := geometric_hahn_banach_closed_compact
    (convex_Iic (0:I→ℝ)) isClosed_Iic hconv hcompact hd
  have hu : 0<u := by simpa using hlo 0 (Set.mem_Iic.mpr le_rfl)
  let c : I→ℝ := fun i=>f (Pi.single i 1)
  have hc (i : I) : 0≤c i := by
    by_contra hn
    have hn' : c i<0 := lt_of_not_ge hn
    let a : ℝ := (u+1)/(c i)
    have ha : a≤0 := div_nonpos_of_nonneg_of_nonpos (by linarith) hn'.le
    have hm : a • Pi.single i (1:ℝ)∈Set.Iic (0:I→ℝ) := by
      intro j
      simp only [Pi.smul_apply,smul_eq_mul,Pi.single_apply,Pi.zero_apply]
      split_ifs <;> simp [ha]
    have hh := hlo _ hm
    rw [map_smul] at hh
    change a*c i<u at hh
    have he : a*c i=u+1 := div_mul_cancel₀ _ (ne_of_lt hn')
    rw [he] at hh
    linarith
  let total : ℝ := ∑i,c i
  have ht : 0<total := by
    have hnn : 0≤total := sum_nonneg fun i _=>hc i
    by_contra hn
    have hz : total=0 := le_antisymm (le_of_not_gt hn) hnn
    have hcz (i : I) : c i=0 := by
      have hs := single_le_sum (fun i _=>hc i) (mem_univ i)
      change c i≤total at hs
      rw [hz] at hs
      exact le_antisymm hs (hc i)
    obtain ⟨x,hx⟩ := hne
    have hh := hhi x hx
    rw [dual_sum] at hh
    change v<∑i,c i*x i at hh
    simp only [hcz,zero_mul,sum_const_zero] at hh
    linarith
  let P : Law I := ⟨fun i=>c i/total,fun i=>div_nonneg (hc i) ht.le,by
    rw [←sum_div]
    exact div_self (ne_of_gt ht)⟩
  obtain ⟨x,hx,hp⟩ := hlaw P
  have he : P.expect x=f x/total := by
    rw [dual_sum]
    simp only [Law.expect,P,div_mul_eq_mul_div,←sum_div]
    rfl
  rw [he] at hp
  have hh := hhi x hx
  have hf : f x≤0 := by simpa only [zero_mul] using (div_le_iff₀ ht).mp hp
  linarith

end UniformKServer.FiniteSeparation

end

end OAI
