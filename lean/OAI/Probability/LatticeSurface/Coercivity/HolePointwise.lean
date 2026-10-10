import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.BadClusters
import OAI.Probability.LatticeSurface.Coercivity.FilledHull
import OAI.Probability.LatticeSurface.Coercivity.GridClosedLabels
import OAI.Probability.LatticeSurface.Coercivity.HoleEdges
import OAI.Probability.LatticeSurface.Coercivity.HoleExtension
import OAI.Probability.LatticeSurface.Coercivity.HoleGeometry
import OAI.Probability.LatticeSurface.Coercivity.HoleIncident
import OAI.Probability.LatticeSurface.Coercivity.HoleSize
import OAI.Probability.LatticeSurface.Coercivity.HoleStar
import OAI.Probability.LatticeSurface.Coercivity.HullMore
import OAI.Probability.LatticeSurface.Coercivity.HullRims
import OAI.Probability.LatticeSurface.Coercivity.OuterHulls

namespace OAI

noncomputable section

open scoped BigOperators

namespace SparseHoles

lemma lipschitz_int_line (u : ℤ → ℝ) (K : ℝ)
    (hu : ∀ i, |u (i+1)-u i| ≤ K) (a b : ℤ) :
    |u b-u a| ≤ K*((b-a).natAbs:ℝ) := by
  have hn : ∀ a : ℤ, ∀ n : ℕ, |u (a+n)-u a| ≤ K*n := by
    intro a n
    induction n with
    | zero => simp
    | succ n ih =>
      have hh := hu (a+n)
      have ht := abs_add_le (u (a+n+1)-u (a+n)) (u (a+n)-u a)
      have he : u (a+n+1)-u (a+n)+(u (a+n)-u a)=u (a+n+1)-u a := by ring
      rw [he] at ht
      simp only [Nat.cast_add,Nat.cast_one] at *
      simpa only [add_assoc] using (show |u (a+n+1)-u a| ≤ K*((n:ℝ)+1) by nlinarith)
  by_cases h : a ≤ b
  · have he : a+((b-a).toNat:ℤ)=b := by omega
    have hnat : (b-a).toNat=(b-a).natAbs := by omega
    have hh := hn a (b-a).toNat
    rw [he,hnat] at hh
    exact hh
  · have he : b+((a-b).toNat:ℤ)=a := by omega
    have hnat : (a-b).toNat=(b-a).natAbs := by omega
    have hh := hn b (a-b).toNat
    rw [he,hnat,abs_sub_comm] at hh
    exact hh

lemma grid_lipschitz (u : Vertex → ℝ) (K : ℝ)
    (hu : ∀ x y, grid.Adj x y → |u y-u x| ≤ K) (x y : Vertex) :
    |u y-u x| ≤ K*((y.1-x.1).natAbs+(y.2-x.2).natAbs:ℕ) := by
  have hrow := lipschitz_int_line (fun i => u (i,x.2)) K
    (fun i => hu _ _ (adj_right i x.2)) x.1 y.1
  have hcol := lipschitz_int_line (fun j => u (y.1,j)) K
    (fun j => hu _ _ (adj_up y.1 j)) x.2 y.2
  have ht := abs_add_le (u y-u (y.1,x.2)) (u (y.1,x.2)-u x)
  have he : u y-u (y.1,x.2)+(u (y.1,x.2)-u x)=u y-u x := by ring
  rw [he] at ht
  push_cast
  simpa only [Prod.eta,mul_add] using (show |u y-u x| ≤ K*((y.1-x.1).natAbs:ℝ)+K*((y.2-x.2).natAbs:ℝ) by linarith)

lemma representative_distance (H : Finset Vertex) {z : Vertex} (hz : z∈H) :
    ((representative H).1-z.1).natAbs ≤ diameter H+1 ∧
    ((representative H).2-z.2).natAbs ≤ diameter H+1 := by
  obtain ⟨_,x,hx,hx1,hx2⟩ := representative_mem H ⟨z,hz⟩
  have hh := le_diameter H hx hz
  have h1 := natAbs_sub_triangle (representative H).1 x.1 z.1
  have h2 := natAbs_sub_triangle (representative H).2 x.2 z.2
  constructor <;> omega

lemma filling_error (L : Finset (Finset Vertex)) (hL : HoleFamily L)
    (u : Vertex → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ x y,grid.Adj x y → |u y-u x| ≤ K) (z : Vertex) :
    |u z-extension L u z| ≤ 2*K*(1+(siteDiameter L z:ℝ)) := by
  classical
  by_cases hz : ∃ H∈L,z∈H
  · obtain ⟨H,hH,hzH⟩ := hz
    rw [show extension L u z=u (representative H) from congrArg u (fillSite_hole L hL hH hzH)]
    rw [abs_sub_comm]
    have hh := grid_lipschitz u K hu z (representative H)
    have hd := representative_distance H hzH
    have hdH : diameter H ≤ siteDiameter L z := by
      calc
        diameter H = (if incidentClosed H z then diameter H else 0) := (ite_eq_left (Or.inl hzH)).symm
        _ ≤ siteDiameter L z := Finset.le_sup (f := fun H => if incidentClosed H z then diameter H else 0) hH
    have he : (((representative H).1-z.1).natAbs+((representative H).2-z.2).natAbs:ℕ) ≤ 2*(siteDiameter L z+1) := by omega
    refine hh.trans ?_
    have hc : ((((representative H).1-z.1).natAbs+((representative H).2-z.2).natAbs:ℕ):ℝ) ≤ 2*((siteDiameter L z:ℝ)+1) := by exact_mod_cast he
    nlinarith
  · simp only [extension,fillSite,dite_eq_right hz,sub_self,abs_zero]
    positivity

end SparseHoles

end

end OAI
