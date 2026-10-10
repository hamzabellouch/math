import Mathlib
import OAI.Probability.SKBarriers.Dynamics.GreedyInvariant
import OAI.Probability.SKBarriers.Dynamics.PredictableGrid

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical MeasureTheory Set
namespace SK.Analytic

structure GreedyScaleBounds (n B H p : ℕ) (t ρ d b b' q : ℝ) : Prop where
  p_pos : 0<p
  B_pos : 0<B
  HB : H<B
  packingH : ⌈2/b^2⌉₊≤H
  t_pos : 0<t
  rho_pos : 0<ρ
  d_nonneg : 0≤d
  b_pos : 0<b
  packing : 3*t<b^2/2
  cutoff : 3*t<b
  total_error : 6*p*ρ^20<t
  small_cutoff : 2*t+6*p*ρ^20+2*(n:ℝ)^(-(1:ℝ)/100)<b'
  separation : 12*p*ρ^20+4*(n:ℝ)^(-(1:ℝ)/100)<3*ρ
  width : ρ^8<t/2
  small_width : 6*p*ρ^20+2*(n:ℝ)^(-(1:ℝ)/100)+ρ^20+d/2<ρ^8
  large_width : 6*p*ρ^20+2*(n:ℝ)^(-(1:ℝ)/100)+ρ^20+3*d/2≤2*ρ
  jump : d/2≤ρ^20
  eta : 2*(n:ℝ)^(-(1:ℝ)/100)<2*ρ^20
  high : 2*t+6*p*ρ^20+2*(n:ℝ)^(-(1:ℝ)/100)+2*ρ^20<q
  grid_range : 4*p*ρ≤t

theorem gridThresholds_range {n p : ℕ} (hn : 0<n) {t ρ : ℝ} (hρ : 0<ρ)
    (hp : 4*p*ρ≤t) (z : Fin p → Fin n) : ∀i<p,gridThresholds n p t ρ z i∈Icc t (2*t) := by
  intro i hi
  rw [gridThresholds,dite_eq_left hi]
  have H := thresholdGrid_mem hn hρ (t+4*i*ρ) (z ⟨i,hi⟩)
  have hiR : (i:ℝ)+1≤p := by exact_mod_cast hi
  have h0 : 0≤4*(i:ℝ)*ρ := by positivity
  have h1 : 4*(i:ℝ)*ρ+ρ≤4*p*ρ := by nlinarith only [mul_nonneg (show 0≤(p:ℝ)-i-1 by linarith only [hiR]) hρ.le,hρ]
  constructor <;> linarith only [H.1,H.2,h0,h1,hp]

theorem gridThresholds_spacing {n p : ℕ} (hn : 0<n) {t ρ : ℝ} (hρ : 0<ρ)
    (z : Fin p → Fin n) : ∀i j,i<j → j<p → 3*ρ≤gridThresholds n p t ρ z j-gridThresholds n p t ρ z i := by
  intro i j hij hj
  rw [gridThresholds,dite_eq_left hj,gridThresholds,dite_eq_left (hij.trans hj)]
  have Hi := thresholdGrid_mem hn hρ (t+4*i*ρ) (z ⟨i,hij.trans hj⟩)
  have Hj := thresholdGrid_mem hn hρ (t+4*j*ρ) (z ⟨j,hj⟩)
  have hR : (i:ℝ)+1≤j := by exact_mod_cast hij
  have hM := mul_nonneg (show 0≤(j:ℝ)-i-1 by linarith only [hR]) hρ.le
  nlinarith only [Hi.2,Hj.1,hM]

theorem greedy_no_passage {n : ℕ} (hn : 0<n) (μ : ProbabilityMeasure ℝ)
    (pool : ℕ → Finset (Config n)) (fallback : ℕ → Config n)
    (hf : ∀j,fallback j∈pool j) (base : ℕ → Config n) (x : ℕ → Config n)
    (B H s m : ℕ) (t ρ d b b' q : ℝ) (G : GreedyScaleBounds n B H (B*s) t ρ d b b' q)
    (hcount : (B*s)*((4*ρ^8/ρ+1/(n:ℝ))/ρ^4)+(m+1)*(2*(6*(B*s)*ρ^20)/ρ+1/(n:ℝ))^s<1)
    (hjump : ∀ z k, k < m → |overlap z (x (k+1))-overlap z (x k)|≤d)
    (hcoverage : ∀ j < B*s,∀v : ℕ → Config n,(∀ i < j,v i∈pool i) →
      ∀ u ≤ m,(∀ i, j/B*B ≤ i → i<j → |overlap (v i) (x u)|≤3*t) →
      ∃w∈pool j,q≤overlap w (x u) ∧ ∀ i, j/B*B ≤ i → i<j → |overlap (v i) w|≤3*t)
    (hsigned : ∀i j,i<j → j<B*s → ∀v∈pool i,∀w∈pool j,∀ k ≤ m,
      (![v,w,x k] : ReplicaConfig n 3)∉signedLockingSet n q b)
    (hbank : ∀i k j,i<k → k<j → j<B*s → ∀v∈pool i,∀z∈pool k,∀w∈pool j,
      (![z,v,w] : ReplicaConfig n 3)∉signedLockingSet n b b' ∧
      (![z,v,flip w] : ReplicaConfig n 3)∉signedLockingSet n b b')
    (hnarrow : ∀i j,i<j → j<B*s → ∀v∈pool i,∀w∈pool j,∀ k ≤ m,
      (![v,x k,w] : ReplicaConfig n 3)∉narrowLockingSet n μ t ρ) :
    0<overlap (bankPick pool fallback B x t q 0 base 0) (x m) := by
  by_contra hpos
  have hpass : overlap (bankPick pool fallback B x t q 0 base 0) (x m)≤0 := le_of_not_gt hpos
  let p := B*s
  let P := (FiniteLaw.uniformFin n hn).iid (Fin p)
  let bad (z : Fin p → Fin n) := ∃i : Fin p,ρ^4 < (μ:Measure ℝ).real
    (Icc (thresholdGrid n (t+4*i.val*ρ) ρ (z i)-2*ρ^8) (thresholdGrid n (t+4*i.val*ρ) ρ (z i)+2*ρ^8))
  let W (k : Fin (m+1)) (z : Fin p → Fin n) := ∀i : Fin p,i.val%B=0 →
    |overlap (greedyReference base (bankPick pool fallback B x t q) x (gridThresholds n p t ρ z) b m i.val) (x k.val)-
      thresholdGrid n (t+4*i.val*ρ) ρ (z i)|≤6*p*ρ^20
  have hall : ∀z,bad z ∨ ∃k : Fin (m+1),W k z := by
    intro z
    by_cases hz : bad z
    · exact Or.inl hz
    · right
      have hm : ∀i<p,(μ:Measure ℝ).real (Icc (gridThresholds n p t ρ z i-2*ρ^8) (gridThresholds n p t ρ z i+2*ρ^8))≤ρ^4 := by
        intro i hi
        rw [gridThresholds,dite_eq_left hi]
        exact le_of_not_gt (fun H => hz ⟨⟨i,hi⟩,H⟩)
      obtain ⟨k,hk,Hk⟩ := greedy_marker_windows hn μ pool fallback hf base x (gridThresholds n p t ρ z)
        B H p m t ρ d b b' q G.p_pos G.B_pos G.HB G.packingH G.t_pos G.rho_pos G.d_nonneg G.b_pos
        G.packing G.cutoff G.total_error G.small_cutoff G.separation G.width G.small_width G.large_width
        G.jump G.eta G.high (gridThresholds_range hn G.rho_pos G.grid_range z)
        (gridThresholds_spacing hn G.rho_pos z) hm hjump hcoverage hsigned hbank hnarrow hpass
      refine ⟨⟨k,by omega⟩,?_⟩
      intro i hi
      have he : i.val/B*B=i.val := by
        have H := Nat.mod_add_div i.val B
        rw [hi,zero_add,Nat.mul_comm] at H
        exact H
      have H := Hk (i.val/B) (by simpa only [he] using i.isLt)
      rw [he,gridThresholds,dite_eq_left i.isLt] at H
      exact H
  have h1 : 1≤P.prob bad+P.prob (fun z => ∃k : Fin (m+1),W k z) := by
    have he : P.prob (fun z => bad z ∨ ∃k : Fin (m+1),W k z)=1 := by
      unfold FiniteLaw.prob
      simp only [hall,ite_true,FiniteLaw.expect_const]
    rw [← he]
    exact P.prob_or _ _
  have hm := gridThresholds_good_mass hn μ p t ρ G.rho_pos
  have hw : P.prob (fun z => ∃k : Fin (m+1),W k z)≤(m+1)*(2*(6*p*ρ^20)/ρ+1/(n:ℝ))^s := by
    refine (P.prob_exists W).trans ?_
    calc
      _ ≤ ∑ _k : Fin (m+1),(2*(6*p*ρ^20)/ρ+1/(n:ℝ))^s := by
        apply Finset.sum_le_sum
        intro k _
        exact greedy_grid_windows_bound hn base (bankPick pool fallback B x t q) x B s m G.B_pos t ρ b
          (6*p*ρ^20) G.rho_pos (by positivity) k.val
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  change P.prob bad≤_ at hm
  simp only [p,Nat.cast_mul] at hm hw h1
  linarith only [h1,hm,hw,hcount]

end SK.Analytic

end
end

end OAI
