import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.BadClusters
import OAI.Probability.LatticeSurface.Coercivity.FilledHull
import OAI.Probability.LatticeSurface.Coercivity.GridClosedLabels
import OAI.Probability.LatticeSurface.Coercivity.GridSpreadTrace
import OAI.Probability.LatticeSurface.Coercivity.GridTrace
import OAI.Probability.LatticeSurface.Coercivity.GridTraceAnalytic
import OAI.Probability.LatticeSurface.Coercivity.GridTraceGeometry
import OAI.Probability.LatticeSurface.Coercivity.GridTraceKernel
import OAI.Probability.LatticeSurface.Coercivity.GridTraceMain
import OAI.Probability.LatticeSurface.Coercivity.GridTraceScale
import OAI.Probability.LatticeSurface.Coercivity.GridTraceTelescope
import OAI.Probability.LatticeSurface.Coercivity.HoleEdges
import OAI.Probability.LatticeSurface.Coercivity.HoleExtension
import OAI.Probability.LatticeSurface.Coercivity.HoleGeometry
import OAI.Probability.LatticeSurface.Coercivity.HoleIncident
import OAI.Probability.LatticeSurface.Coercivity.HoleSize
import OAI.Probability.LatticeSurface.Coercivity.HoleStar
import OAI.Probability.LatticeSurface.Coercivity.HullMore
import OAI.Probability.LatticeSurface.Coercivity.HullRims
import OAI.Probability.LatticeSurface.Coercivity.OuterHulls
import OAI.Probability.LatticeSurface.Coercivity.PinSpread

namespace OAI

noncomputable section

open scoped BigOperators

namespace SparseHoles

noncomputable def coordinate (b : Bool) (z : Vertex) : ℤ := if b then z.1 else z.2

lemma coordinate_dist (b : Bool) (x y : Vertex) :
    |(coordinate b x:ℝ)-coordinate b y|≤GridTrace.dist₁ x y := by
  cases b <;> simp only [coordinate,Bool.false_eq_true,ite_false,ite_true,GridTrace.dist₁]
  · exact le_add_of_nonneg_left (abs_nonneg _)
  · exact le_add_of_nonneg_right (abs_nonneg _)

lemma coordinate_step (b : Bool) {x y : Vertex} (h : star.Adj x y) :
    coordinate b y≤coordinate b x+1 := by
  cases b <;> simp only [coordinate,Bool.false_eq_true,ite_false,ite_true]
  · have hh := h.2.2;omega
  · have hh := h.2.1;omega

lemma diameter_axis (P : Finset Vertex) (hP : P.Nonempty) :
    ∃ b : Bool, ∃ x∈P,∃ y∈P,
      coordinate b x≤coordinate b y ∧ (coordinate b y-coordinate b x).toNat=diameter P := by
  obtain ⟨x,hx,hxD⟩ := Finset.exists_mem_eq_sup P hP
    (fun x => P.sup (fun y => max (x.1-y.1).natAbs (x.2-y.2).natAbs))
  obtain ⟨y,hy,hyD⟩ := Finset.exists_mem_eq_sup P hP
    (fun y => max (x.1-y.1).natAbs (x.2-y.2).natAbs)
  have he : diameter P=max (x.1-y.1).natAbs (x.2-y.2).natAbs := hxD.trans hyD
  by_cases h : (x.1-y.1).natAbs ≤ (x.2-y.2).natAbs
  · rw [max_eq_right h] at he
    by_cases hxy : x.2≤y.2
    · refine ⟨false,x,hx,y,hy,?_⟩;simp only [coordinate,Bool.false_eq_true,ite_false];omega
    · refine ⟨false,y,hy,x,hx,?_⟩;simp only [coordinate,Bool.false_eq_true,ite_false];omega
  · rw [max_eq_left (le_of_not_ge h)] at he
    by_cases hxy : x.1≤y.1
    · refine ⟨true,x,hx,y,hy,?_⟩;simp only [coordinate,ite_true];omega
    · refine ⟨true,y,hy,x,hx,?_⟩;simp only [coordinate,ite_true];omega

lemma connected_pin_measure (N : ℕ) (hN : 1≤N) (P : Finset Vertex)
    (hPQ : P⊆GridTrace.square N) (hP : (star.induce (P:Set Vertex)).Connected)
    (R : ℝ) (hR : 1≤R) (hdiam : (N:ℝ)≤R*(diameter P:ℝ)) :
    ∃ ν : Vertex → ℝ,
      (∀ z,0≤ν z) ∧ (∀ z,z∉P → ν z=0) ∧
      (∑ z∈GridTrace.square N,ν z)=1 ∧
      ∀ z r,0≤r → (∑ y∈GridTrace.ball N z r,ν y)≤2*R*((r+1)/(N:ℝ)) := by
  classical
  have hne : P.Nonempty := by
    obtain ⟨x⟩ := hP.nonempty
    exact ⟨x,x.property⟩
  obtain ⟨b,x,hx,y,hy,hxy,hspan⟩ := diameter_axis P hne
  have hproj : ∀ k∈Finset.Icc (coordinate b x) (coordinate b y),∃ z∈P,coordinate b z=k := by
    intro k hk
    exact GridTrace.connected_projection P (star.induce (P:Set Vertex)) hP.preconnected
      (coordinate b) (fun {_ _} hab => coordinate_step b hab) ⟨x,hx⟩ ⟨y,hy⟩ k
      (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
  obtain ⟨ν,hν,hνP,hmass,hball⟩ := GridTrace.projection_pin_measure N P hPQ
    (coordinate b) (coordinate_dist b) (coordinate b x) (coordinate b y) hxy hproj
  refine ⟨ν,hν,hνP,hmass,?_⟩
  intro z r hr
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hden : (0:ℝ)<(coordinate b y-coordinate b x+1:ℤ) := by exact_mod_cast (show (0:ℤ)<coordinate b y-coordinate b x+1 by omega)
  have he : ((coordinate b y-coordinate b x+1:ℤ):ℝ)=(diameter P:ℝ)+1 := by
    have hh : coordinate b y-coordinate b x=(diameter P:ℤ) := by omega
    rw [Int.cast_add,hh,Int.cast_natCast,Int.cast_one]
  have hNR : (N:ℝ)≤R*((diameter P:ℝ)+1) := by nlinarith
  calc
    _ ≤ (2*r+1)/(coordinate b y-coordinate b x+1:ℤ) := hball z r hr
    _ ≤ 2*R*((r+1)/(N:ℝ)) := by
      apply (div_le_iff₀ hden).mpr
      rw [he]
      rw [show 2*R*((r+1)/(N:ℝ))*((diameter P:ℝ)+1)=
        (2*R*(r+1)*((diameter P:ℝ)+1))/(N:ℝ) by ring]
      apply (le_div_iff₀ hNp).mpr
      nlinarith [mul_le_mul_of_nonneg_right hNR (show (0:ℝ)≤2*r+1 by linarith)]

end SparseHoles

end

end OAI
