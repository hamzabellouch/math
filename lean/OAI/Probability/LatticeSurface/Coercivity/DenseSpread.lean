import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.GridSpreadTrace
import OAI.Probability.LatticeSurface.Coercivity.GridTrace
import OAI.Probability.LatticeSurface.Coercivity.GridTraceAnalytic
import OAI.Probability.LatticeSurface.Coercivity.GridTraceGeometry
import OAI.Probability.LatticeSurface.Coercivity.GridTraceKernel
import OAI.Probability.LatticeSurface.Coercivity.GridTraceMain
import OAI.Probability.LatticeSurface.Coercivity.GridTraceScale
import OAI.Probability.LatticeSurface.Coercivity.GridTraceTelescope
import OAI.Probability.LatticeSurface.Coercivity.PinSpread

namespace OAI

noncomputable section

open scoped BigOperators

namespace GridTrace

lemma abs_int_le_floor {a b : ℤ} {r : ℝ} (hr : 0≤r) (h : |(a:ℝ)-b|≤r) :
    b-(⌊r⌋₊:ℤ)≤a ∧ a≤b+⌊r⌋₊ := by
  have he : ((a-b).natAbs:ℝ)=|(a:ℝ)-b| := by
    rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs,Int.cast_sub]
  have hn : (a-b).natAbs≤⌊r⌋₊ := (Nat.le_floor_iff hr).mpr (by rw [he];exact h)
  have hn' : ((a-b).natAbs:ℤ)≤(⌊r⌋₊:ℤ) := by exact_mod_cast hn
  rw [Int.natCast_natAbs,abs_le] at hn'
  omega

lemma ball_card_strip (N : ℕ) (z : Vertex) (r : ℝ) (hr : 0≤r) :
    ((ball N z r).card:ℝ)≤(2*r+1)*((N:ℝ)+1) := by
  classical
  let n := ⌊r⌋₊
  have hsub : ball N z r ⊆ (Finset.Icc (z.1-(n:ℤ)) (z.1+n)) ×ˢ Finset.Icc (0:ℤ) N := by
    intro x hx
    obtain ⟨hxQ,hx⟩ := Finset.mem_filter.mp hx
    obtain ⟨hx1,hx2⟩ := Finset.mem_product.mp hxQ
    have hh : |(x.1:ℝ)-z.1|≤r := by
      have ha := abs_nonneg ((z.2:ℝ)-x.2)
      dsimp [dist₁] at hx
      rw [abs_sub_comm] at hx
      linarith
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (abs_int_le_floor hr hh),hx2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_product,Int.card_Icc,Int.card_Icc] at hcard
  have h1 : (z.1+n+1-(z.1-n)).toNat=2*n+1 := by omega
  have h2 : ((N:ℤ)+1-0).toNat=N+1 := by omega
  rw [h1,h2] at hcard
  have hn : (n:ℝ)≤r := Nat.floor_le hr
  have hc : ((ball N z r).card:ℝ)≤(2*(n:ℝ)+1)*((N:ℝ)+1) := by exact_mod_cast hcard
  exact hc.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

lemma dense_spread (N : ℕ) (hN : 1≤N) (C : ℝ) (hC : 0≤C) (ν : Vertex → ℝ)
    (hν : ∀ x∈square N,ν x≤C/(N:ℝ)^2) :
    ∀ z r,0≤r → (∑ x∈ball N z r,ν x)≤4*C*((r+1)/(N:ℝ)) := by
  intro z r hr
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  calc
    _ ≤ ∑ x∈ball N z r,C/(N:ℝ)^2 := Finset.sum_le_sum (fun x hx => hν x (Finset.mem_filter.mp hx).1)
    _ = ((ball N z r).card:ℝ)*(C/(N:ℝ)^2) := by simp
    _ ≤ ((2*r+1)*((N:ℝ)+1))*(C/(N:ℝ)^2) :=
      mul_le_mul_of_nonneg_right (ball_card_strip N z r hr) (by positivity)
    _ ≤ (4*((N:ℝ)*(r+1)))*(C/(N:ℝ)^2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    _ = _ := by field_simp

lemma signed_spread_trace (p α C : ℝ) (hp : 1<p) (hp2 : p<2)
    (hα : 2-p<α) (hC : 0<C) :
    ∃ K : ℝ,0<K ∧ ∀ N : ℕ,1≤N → ∀ w v : Vertex → ℝ,
      (∑ x∈square N,|w x|)≤C →
      (∀ z∈square N,∀ r : ℝ,0≤r → r≤2*(N:ℝ) →
        (∑ y∈ball N z r,|w y|)≤C*((r+1)/(N:ℝ))^α) →
      |(∑ x∈square N,w x*v x)-(∑ x∈square N,w x)*mean N v|≤
        K*(N:ℝ)^(1-2/p)*(energy N p v)^(1/p) := by
  classical
  obtain ⟨K,hK,h⟩ := spread_trace p α C hp hp2 hα hC
  refine ⟨2*K,by positivity,?_⟩
  intro N hN w v hmass hspread
  let a : Vertex → ℝ := fun x => max (w x) 0
  let b : Vertex → ℝ := fun x => max (-w x) 0
  have habs (x) : a x≤|w x| := max_le (le_abs_self _) (abs_nonneg _)
  have hbabs (x) : b x≤|w x| := max_le (neg_le_abs _) (abs_nonneg _)
  have hw (x) : w x=a x-b x := by
    dsimp [a,b]
    rcases le_total 0 (w x) with hh|hh
    · rw [max_eq_left hh,max_eq_right (by linarith)];ring
    · rw [max_eq_right hh,max_eq_left (by linarith)];ring
  have ha := h N hN a v (fun x hx => le_max_right _ _)
    ((Finset.sum_le_sum fun x hx => habs x).trans hmass)
    (fun z hz r hr hrN => (Finset.sum_le_sum fun x hx => habs x).trans (hspread z hz r hr hrN))
  have hb := h N hN b v (fun x hx => le_max_right _ _)
    ((Finset.sum_le_sum fun x hx => hbabs x).trans hmass)
    (fun z hz r hr hrN => (Finset.sum_le_sum fun x hx => hbabs x).trans (hspread z hz r hr hrN))
  have he : (∑ x∈square N,w x*v x)-(∑ x∈square N,w x)*mean N v =
      ((∑ x∈square N,a x*v x)-(∑ x∈square N,a x)*mean N v)-
      ((∑ x∈square N,b x*v x)-(∑ x∈square N,b x)*mean N v) := by
    simp_rw [hw,sub_mul,Finset.sum_sub_distrib]
    ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

end GridTrace

end

end OAI
