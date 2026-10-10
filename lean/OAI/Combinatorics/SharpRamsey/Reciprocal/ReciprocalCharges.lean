import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.Reciprocal

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype ι] [DecidableEq ι]

theorem projective_integer_incidence
    (p : Law (ι→Projectivization K (Module.Dual K V)×Projectivization K V))
    (i j : ι) (MA MB κ ρ ε c : ℝ) (d r : ℕ)
    (hMA : 0<MA) (hMB : 0<MB) (hρ : 0<ρ) (hc : 0<c)
    (hcap : c≤1-(Module.finrank K V:ℝ)*ρ) (hr : r≤d+1)
    (hγ : 0<1-(Module.finrank K V:ℝ)*ρ-ε)
    (hκ : log (2/(1-(Module.finrank K V:ℝ)*ρ-ε))≤κ)
    (hu : (r:ℝ)-1 < (d:ℝ)+1-(log MA+3*κ)/log (Nat.card K))
    (hv : (d:ℝ)-r < (d:ℝ)+1-(log MB+3*κ)/log (Nat.card K))
    (hconsistent : ∀ x,p.mass x≠0 →
      (x i).1.rep (x j).2.rep=0 → (x j).1.rep (x i).2.rep=0) :
    ((p.marginal i).fst.prod (p.marginal j).snd).event (univ.filter (fun ay =>
      goodFirst (p.marginal i) MA ((d:ℝ)*log (Nat.card K)) κ ε ay.1 ∧
      goodSecond (p.marginal j) MB ((d:ℝ)*log (Nat.card K)) κ ε ay.2 ∧
      ay.1.rep ay.2.rep=0))≤
      2*(pairInformation p i j:ℝ)/ρ^2+
        2*((pairInformation p i j:ℝ)+
          (directedCollision p Projectivization.rep Projectivization.rep ρ r (d+1-r) i j:ℝ))/c^2 := by
  classical
  let : DecidableEq (Projectivization K (Module.Dual K V)×Projectivization K V) := Classical.decEq _
  let : DecidableEq ((Projectivization K (Module.Dual K V)×Projectivization K V)×
      (Projectivization K (Module.Dual K V)×Projectivization K V)) := Classical.decEq _
  let p₂ := p.map (fun x => (x i,x j))
  have hi : p₂.fst=p.marginal i := by
    rw [←Law.map_fst,Law.map_map]; rfl
  have hj : p₂.snd=p.marginal j := by
    rw [←Law.map_snd,Law.map_map]; rfl
  let ga := goodFirst (p.marginal i) MA ((d:ℝ)*log (Nat.card K)) κ ε
  let gb := goodSecond (p.marginal j) MB ((d:ℝ)*log (Nat.card K)) κ ε
  have hcon : ∀ z,p₂.mass z≠0 →
      z.1.1.rep z.2.2.rep=0 → z.2.1.rep z.1.2.rep=0 := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := p.map_support (fun x => (x i,x j)) z hz
    exact hconsistent x hx
  have hb := reciprocal_incidence_collision p₂ Projectivization.rep Projectivization.rep
    hρ hc hcap ga gb hcon
  have he : p₂.event (univ.filter (coreCollision p₂.fst p₂.snd
      Projectivization.rep Projectivization.rep ρ ga gb))≤
      (directedCollision p Projectivization.rep Projectivization.rep ρ r (d+1-r) i j:ℝ) := by
    rw [hi,hj]
    have hm := p.event_map (fun x => (x i,x j))
      (univ.filter (coreCollision (p.marginal i) (p.marginal j)
        Projectivization.rep Projectivization.rep ρ ga gb))
    refine hm.le.trans ?_
    apply p.event_mono
    intro x hx
    have hh := (mem_filter.mp hx).2
    simp only [mem_filter,mem_univ,true_and] at hh
    have hranks := projective_integer_ranks (p.marginal i) (p.marginal j)
      MA MB κ ρ ε d r hMA hMB hρ.le hr hγ hκ hu hv (x i).1 (x j).2 hh.1 hh.2.1
    exact mem_filter.mpr ⟨mem_univ _,hranks.1,hranks.2,hh.2.2⟩
  rw [hi,hj] at hb he
  change _≤2*mutualInfo p₂/ρ^2+2*(mutualInfo p₂+_)/c^2
  exact hb.trans (add_le_add le_rfl
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl he)
        (by norm_num : (0 : ℝ) ≤ 2)) (sq_nonneg c)))

end
end SharpLogRamsey.Selection

end

end OAI
