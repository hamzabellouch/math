import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.EllipseMesh

namespace OAI

section
section
noncomputable section
open Set Function

namespace CriticalPercolation.EuclideanEllipse

def gridPoint (N K i k : ℕ) : ℝ×ℝ := ((i : ℝ)/N,(k : ℝ)*Real.pi/K)

lemma gridPoint_mem {N K i k : ℕ} (hN : 0<N) (hK : 0<K) (hi : i≤N) (hk : k≤K) :
    gridPoint N K i k∈parameterDisk := by
  have hNr : 0<(N : ℝ) := Nat.cast_pos.mpr hN
  have hKr : 0<(K : ℝ) := Nat.cast_pos.mpr hK
  have hir : (i : ℝ)≤N := Nat.cast_le.mpr hi
  have hkr : (k : ℝ)≤K := Nat.cast_le.mpr hk
  change (0≤(i : ℝ)/N ∧ 0≤(k : ℝ)*Real.pi/K) ∧ (i : ℝ)/N≤1 ∧ (k : ℝ)*Real.pi/K≤Real.pi
  exact ⟨⟨by positivity,by positivity⟩,(div_le_one hNr).mpr hir,
    (div_le_iff₀ hKr).mpr (by nlinarith [Real.pi_pos])⟩

lemma gridPoint_dist {N K : ℕ} (hN : 0<N) (hK : 0<K) (i k : ℕ) (a b : ℕ)
    (ha : a≤1) (hb : b≤1) :
    dist (gridPoint N K i k) (gridPoint N K (i+a) (k+b)) ≤ max (1/(N : ℝ)) (Real.pi/K) := by
  have hNr : 0<(N : ℝ) := Nat.cast_pos.mpr hN
  have hKr : 0<(K : ℝ) := Nat.cast_pos.mpr hK
  rw [Prod.dist_eq]
  have hfirst : dist (gridPoint N K i k).1 (gridPoint N K (i+a) (k+b)).1≤1/(N : ℝ) := by
    change |(i : ℝ)/N-(i+a : ℕ)/N|≤_
    rw [Nat.cast_add]
    have he : (i : ℝ)/N-((i : ℝ)+a)/N= -(a : ℝ)/N := by ring
    rw [he,abs_div,abs_neg,abs_of_nonneg (Nat.cast_nonneg a),abs_of_pos hNr]
    exact div_le_div_of_nonneg_right (by exact_mod_cast ha) hNr.le
  have hsecond : dist (gridPoint N K i k).2 (gridPoint N K (i+a) (k+b)).2≤Real.pi/K := by
    change |(k : ℝ)*Real.pi/K-(k+b : ℕ)*Real.pi/K|≤_
    rw [Nat.cast_add]
    have he : (k : ℝ)*Real.pi/K-((k : ℝ)+b)*Real.pi/K= -((b : ℝ)*Real.pi)/K := by ring
    rw [he,abs_div,abs_neg,abs_of_nonneg (by positivity : 0≤(b : ℝ)*Real.pi),abs_of_pos hKr]
    apply div_le_div_of_nonneg_right _ hKr.le
    have hb' : (b : ℝ)≤1 := by exact_mod_cast hb
    nlinarith [Real.pi_pos]
  exact max_le_max hfirst hsecond

lemma exists_grid_mesh (delta : ℝ) (hdelta : 0<delta) :
    ∃ N K : ℕ, 0<N ∧ 0<K ∧ max (1/(N : ℝ)) (Real.pi/K)<delta ∧ Real.pi/K<Real.pi/32 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (1/delta)
  obtain ⟨K,hK⟩ := exists_nat_gt (max (Real.pi/delta) 32)
  have hNr : 0<(N : ℝ) := lt_trans (by positivity) hN
  have hKr : 0<(K : ℝ) := lt_trans (by norm_num : (0 : ℝ)<32) ((le_max_right _ _).trans_lt hK)
  have hNm : 1/(N : ℝ)<delta := (div_lt_iff₀ hNr).mpr (by
    have := (div_lt_iff₀ hdelta).mp hN
    nlinarith)
  have hKm : Real.pi/(K : ℝ)<delta := (div_lt_iff₀ hKr).mpr (by
    have := (div_lt_iff₀ hdelta).mp ((le_max_left _ _).trans_lt hK)
    nlinarith)
  have hK32 : Real.pi/(K : ℝ)<Real.pi/32 := div_lt_div_of_pos_left Real.pi_pos (by norm_num)
    ((le_max_right _ _).trans_lt hK)
  exact ⟨N,K,Nat.cast_pos.mp hNr,Nat.cast_pos.mp hKr,max_lt hNm hKm,hK32⟩

lemma gridPoint_angular_step (N K k : ℕ) (hK : 0<K) :
    |(gridPoint N K (0 : ℕ) (k+1)).2-(gridPoint N K 0 k).2|=Real.pi/K := by
  change |((k+1 : ℕ) : ℝ)*Real.pi/K-(k : ℝ)*Real.pi/K|=_
  rw [Nat.cast_add,Nat.cast_one]
  have he : ((k : ℝ)+1)*Real.pi/K-(k : ℝ)*Real.pi/K=Real.pi/K := by ring
  rw [he,abs_of_nonneg (by positivity)]

theorem exists_grid_comparison (W U zeta : ℝ) (hW : 0<W) (hWU : W≤U) (hzeta : 0<zeta) :
    ∃ N K : ℕ, 0<N ∧ 0<K ∧ Real.pi/K<Real.pi/32 ∧
      ∀ i≤N, ∀ k≤K, ∀ a≤1, ∀ b≤1, i+a≤N → k+b≤K → ∀ z : ℂ,
        ‖diskNormalize W U (gridPoint N K i k) (diskExpand W U (gridPoint N K (i+a) (k+b)) z)-z‖≤zeta*‖z‖ := by
  obtain ⟨delta,hd,hcomp⟩ := diskNormalize_uniform_comparison W U zeta hW hWU hzeta
  obtain ⟨N,K,hN,hK,hm,hangle⟩ := exists_grid_mesh delta hd
  refine ⟨N,K,hN,hK,hangle,?_⟩
  intro i hi k hk a ha b hb hia hkb z
  exact hcomp _ (gridPoint_mem hN hK hi hk) _ (gridPoint_mem hN hK hia hkb)
    ((gridPoint_dist hN hK i k a b ha hb).trans_lt hm) z

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
