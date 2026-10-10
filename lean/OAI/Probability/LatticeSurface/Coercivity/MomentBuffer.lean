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
import OAI.Probability.LatticeSurface.Coercivity.HoleLocal
import OAI.Probability.LatticeSurface.Coercivity.HolePointwise
import OAI.Probability.LatticeSurface.Coercivity.HoleSize
import OAI.Probability.LatticeSurface.Coercivity.HoleStar
import OAI.Probability.LatticeSurface.Coercivity.HullMore
import OAI.Probability.LatticeSurface.Coercivity.HullRims
import OAI.Probability.LatticeSurface.Coercivity.OuterHulls
import OAI.Probability.LatticeSurface.Convexity.WeightedHolder
import OAI.Probability.LatticeSurface.Moments.CoercivityEnergy

namespace OAI

noncomputable section

open scoped BigOperators

namespace SparseHoles

lemma square_eq_box (N : ℕ) : GridTrace.square N=box (0,0) (N,N) := rfl

lemma square_card (N : ℕ) : (GridTrace.square N).card=(N+1)^2 := by
  simp only [GridTrace.square,Finset.card_product,Int.card_Icc]
  have h : ((N:ℤ)+1-0).toNat=N+1 := by omega
  rw [h,pow_two]

lemma buffer_card (N : ℕ) : (buffer N).card=(5*N+1)^2 := by
  simp only [buffer,box,Finset.card_product,Int.card_Icc]
  have h : (3*(N:ℤ)+1- -(2*N)).toNat=5*N+1 := by omega
  rw [h,pow_two]

lemma square_card_bound (N : ℕ) (hN : 1≤N) : ((GridTrace.square N).card:ℝ)+1≤5*(N:ℝ)^2 := by
  rw [square_card];push_cast
  have h : (1:ℝ)≤N := by exact_mod_cast hN
  nlinarith [sq_nonneg ((N:ℝ)-1)]

lemma buffer_edges_bound (N : ℕ) (hN : 1≤N) :
    ((incidentEdges (buffer N)).card:ℝ)+1≤145*(N:ℝ)^2 := by
  have hc := incidentEdges_card (buffer N)
  rw [buffer_card] at hc
  have hc' : ((incidentEdges (buffer N)).card:ℝ)≤4*(5*(N:ℝ)+1)^2 := by exact_mod_cast hc
  have h : (1:ℝ)≤N := by exact_mod_cast hN
  nlinarith [sq_nonneg ((N:ℝ)-1)]

lemma moment_buffer (N : ℕ) (hN : 1≤N) (d : Vertex → ℕ) (D : ℝ)
    (hDN : D<(N:ℝ))
    (hm : (∑ z∈GridTrace.square N,(d z+1:ℝ)^12)≤D*(N:ℝ)^2) :
    ∀ z∈GridTrace.square N,d z≤N := by
  classical
  intro z hz
  by_contra h
  have hdz : (N:ℝ)<d z+1 := by exact_mod_cast (show N<d z+1 by omega)
  have hd1 : (1:ℝ)≤d z+1 := by linarith [show (0:ℝ)≤d z from Nat.cast_nonneg _]
  have hs : (d z+1:ℝ)^12≤D*(N:ℝ)^2 :=
    (Finset.single_le_sum (fun x hx => by positivity) hz).trans hm
  have hpp : (d z+1:ℝ)^3≤(d z+1:ℝ)^12 := pow_le_pow_right₀ hd1 (by norm_num)
  have hnp : (0:ℝ)<N := by exact_mod_cast hN
  have hpow : (N:ℝ)^3<(d z+1:ℝ)^3 := pow_lt_pow_left₀ hdz hnp.le (by norm_num)
  have hh := mul_lt_mul_of_pos_right hDN (sq_pos_of_pos hnp)
  nlinarith

lemma square_lipschitz (N : ℕ) (u : Vertex → ℝ) (K : ℝ) (hK : 0≤K)
    (hu : ∀ x y,grid.Adj x y → |u y-u x|≤K) {x y : Vertex}
    (hx : x∈GridTrace.square N) (hy : y∈GridTrace.square N) :
    |u y-u x|≤2*K*(N:ℝ) := by
  have hx' : 0≤x.1 ∧ x.1≤N ∧ 0≤x.2 ∧ x.2≤N := by
    simpa only [GridTrace.square,Finset.mem_product,Finset.mem_Icc,and_assoc] using hx
  have hy' : 0≤y.1 ∧ y.1≤N ∧ 0≤y.2 ∧ y.2≤N := by
    simpa only [GridTrace.square,Finset.mem_product,Finset.mem_Icc,and_assoc] using hy
  have h1 : (y.1-x.1).natAbs≤N := by omega
  have h2 : (y.2-x.2).natAbs≤N := by omega
  have hd : (((y.1-x.1).natAbs+(y.2-x.2).natAbs:ℕ):ℝ)≤2*(N:ℝ) := by exact_mod_cast (show (y.1-x.1).natAbs+(y.2-x.2).natAbs≤2*N by omega)
  exact (grid_lipschitz u K hu x y).trans (by have hh := mul_le_mul_of_nonneg_left hd hK; nlinarith)

lemma bounded_square_test (N : ℕ) (w u : Vertex → ℝ) (C K : ℝ) (hK : 0≤K)
    (hw : (∑ z∈GridTrace.square N,|w z|)≤C)
    (hu : ∀ x y,grid.Adj x y → |u y-u x|≤K)
    (ha : (∑ z∈GridTrace.square N,w z)=0 ∨ ∃ x∈GridTrace.square N,u x=0) :
    |∑ z∈GridTrace.square N,w z*u z|≤2*K*C*(N:ℝ) := by
  classical
  have haux (x : Vertex) (hx : x∈GridTrace.square N) :
      |∑ z∈GridTrace.square N,w z*(u z-u x)|≤2*K*C*(N:ℝ) := by
    calc
      _ ≤ ∑ z∈GridTrace.square N,|w z*(u z-u x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z∈GridTrace.square N,|w z| *(2*K*(N:ℝ)) := by
        apply Finset.sum_le_sum
        intro z hz
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (square_lipschitz N u K hK hu hx hz) (abs_nonneg _)
      _ = (∑ z∈GridTrace.square N,|w z|)*(2*K*(N:ℝ)) := (Finset.sum_mul _ _ _).symm
      _ ≤ C*(2*K*(N:ℝ)) := mul_le_mul_of_nonneg_right hw (by positivity)
      _ = _ := by ring
  rcases ha with hz|⟨x,hx,hux⟩
  · have hx : (0,0)∈GridTrace.square N := by simp [GridTrace.square]
    have hh := haux (0,0) hx
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hz,zero_mul,sub_zero] at hh
    exact hh
  · simpa only [hux,sub_zero] using haux x hx

end SparseHoles

end

end OAI
