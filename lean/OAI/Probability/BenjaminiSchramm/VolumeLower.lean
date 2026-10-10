import OAI.Probability.BenjaminiSchramm.ProbabilityLower
import OAI.Probability.BenjaminiSchramm.OperatorSusceptibility

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem critical_volume_lower_of_upper [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hpc1 : (pc G : ℝ) < 1)
    (C : ℝ) (hC : 0 < C)
    (hvol : ∀ x n, 0 < n → criticalTail G (volumeEvent G) x n ≤ C / Real.sqrt n)
    (x : V) :
    ∃ a : ℝ, 0 < a ∧ ∀ n : ℕ, 0 < n → a / Real.sqrt n ≤ criticalTail G (volumeEvent G) x n := by
  obtain ⟨c,hc,hθ⟩ := percolationProbability_linear_lower G hconn hloc hqt x
  obtain ⟨d,_,hdeg⟩ := exists_degree_bound G hqt
  have hpc0 : 0 < (pc G : ℝ) := pc_pos G hloc hqt
  let D : ℝ := (pc G : ℝ) * (1-pc G)/2
  have hD : 0 < D := by dsimp [D]; positivity
  let L : ℝ := 2 + 2*(d : ℝ)/D
  have hL : 0 < L := by dsimp [L]; positivity
  let b : ℝ := min (1/2) (min ((1-pc G)/2) (c/(8*L*C)))
  have hb : 0 < b := lt_min (by norm_num)
    (lt_min (by positivity) (div_pos hc (by positivity)))
  have hbhalf : b ≤ 1/2 := min_le_left _ _
  have hbgap : b ≤ (1-pc G)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hbsmall : b ≤ c/(8*L*C) := (min_le_right _ _).trans (min_le_right _ _)
  have hbc : 8*L*C*b ≤ c := by
    have hh := (le_div_iff₀ (by positivity : 0 < 8*L*C)).mp hbsmall
    nlinarith
  refine ⟨c*b/(4*L),by positivity,fun n hn => ?_⟩
  let s : ℝ := Real.sqrt n
  have hs1 : 1 ≤ s := by
    dsimp [s]
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast hn)
  have hs : 0 < s := zero_lt_one.trans_le hs1
  let δ : ℝ := b/s
  have hδ : 0 < δ := div_pos hb hs
  have hδb : δ ≤ b := div_le_self hb.le hs1
  have hδhalf : δ ≤ 1/2 := hδb.trans hbhalf
  have hδgap : δ ≤ (1-pc G)/2 := hδb.trans hbgap
  let q : unitInterval := ⟨(pc G : ℝ)+δ,⟨by positivity,by linarith⟩⟩
  have hq : pc G < q := by change (pc G : ℝ) < pc G+δ; linarith
  have hq1 : (q : ℝ) < 1 := by change (pc G : ℝ)+δ < 1; linarith
  have hq0 : 0 < (q : ℝ) := hpc0.trans hq
  have hden : D ≤ (q : ℝ)*(1-q) := by
    have ht : (1-(pc G : ℝ))/2 ≤ 1-(q : ℝ) := by dsimp [q]; linarith
    have hm := mul_le_mul (show (pc G : ℝ) ≤ q from hq.le) ht
      (by positivity : 0 ≤ (1-(pc G : ℝ))/2) hq0.le
    dsimp [D]
    nlinarith
  let h : unitInterval := ⟨δ^2,⟨sq_nonneg _,by nlinarith⟩⟩
  have hh : (h : ℝ) ∈ Set.Ioo 0 1 := ⟨sq_pos_of_pos hδ,by dsimp [h]; nlinarith⟩
  have hmark (Q : Finset E) : markedConnectionPolynomial G Q x h (pc G) ≤
      (h : ℝ)*(2*C*s) + criticalTail G (volumeEvent G) x n := by
    have hsum : (∑ i ∈ Finset.range n, finiteClusterTail G Q x (i+1) (pc G)) ≤ 2*C*s := by
      calc
        _ ≤ ∑ i ∈ Finset.range n, C / Real.sqrt (i+1 : ℕ) :=
          Finset.sum_le_sum (fun i _ => (finiteClusterTail_le_criticalTail G Q x (i+1) (pc G) le_rfl).trans
            (hvol x (i+1) (by omega)))
        _ = C * ∑ i ∈ Finset.range n, 1 / Real.sqrt (i+1 : ℕ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ ≤ C*(2*s) := mul_le_mul_of_nonneg_left (sum_inverse_sqrt_le n) hC.le
        _ = _ := by ring
    exact (markedConnection_le_truncated_tails G Q x (pc G) h n).trans
      (add_le_add (mul_le_mul_of_nonneg_left hsum h.2.1)
        (finiteClusterTail_le_criticalTail G Q x n (pc G) le_rfl))
  have hghost (Q : Finset E) : markedConnectionPolynomial G Q x h q ≤
      L*((h : ℝ)*(2*C*s) + criticalTail G (volumeEvent G) x n) := by
    have ht := markedConnection_entropy_uniform G Q x (pc G) q h ⟨hpc0,hpc1⟩
      ⟨hq0,hq1⟩ hh d (fun z => (incident_filter_card_le_degree G hloc Q z).trans (hdeg z))
      D hD hden (by change ((pc G : ℝ)-((pc G : ℝ)+δ))^2 ≤ δ^2; nlinarith)
    exact ht.trans (mul_le_mul_of_nonneg_left (hmark Q) hL.le)
  have hupper := percolationProbability_le_of_marked_bounds G x q h hh.1 _ hghost
  have hlower := hθ q hq hq1
  have hδs : δ*s = b := div_mul_cancel₀ b hs.ne'
  have hbound : c*δ ≤ 2*(L*(δ^2*(2*C*s) + criticalTail G (volumeEvent G) x n)) := by
    dsimp only [q] at hlower
    dsimp only [h] at hupper
    linarith
  have hm := mul_le_mul_of_nonneg_right hbound hs.le
  have halg : (2*(L*(δ^2*(2*C*s) + criticalTail G (volumeEvent G) x n)))*s =
      4*L*C*b^2 + 2*L*(criticalTail G (volumeEvent G) x n*s) := by
    rw [←hδs]
    ring
  rw [halg,mul_assoc c δ s,hδs] at hm
  have hsmall : 4*L*C*b^2 ≤ c*b/2 := by
    have ht := mul_le_mul_of_nonneg_right hbc hb.le
    nlinarith
  apply (div_le_iff₀ hs).mpr
  apply (div_le_iff₀ (by positivity : 0 < 4*L)).mpr
  nlinarith

theorem critical_volume_powerTail_of_operator [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G) (hpc1 : (pc G : ℝ) < 1)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G (pc G) T) (x : V) :
    PowerTail (criticalTail G (volumeEvent G) x) (1/2) := by
  obtain ⟨C,hC,hvol⟩ := critical_volume_upper_of_operator G hconn hloc hqt hh hpc1 T hT
  obtain ⟨a,ha,hlo⟩ := critical_volume_lower_of_upper G hconn hloc hqt hpc1 C hC hvol x
  refine ⟨a,C,ha,hC,fun n hn => ?_⟩
  rw [Real.rpow_neg (Nat.cast_nonneg n),←Real.sqrt_eq_rpow]
  simpa only [div_eq_mul_inv] using And.intro (hlo n hn) (hvol x n hn)

theorem criticalVolumeInput_of_nonamenable [Infinite V]
    (G : BondGraph V E) (hh : 0 < hV G) : HutchcroftCriticalVolumeInput G := by
  intro hgraph hgap x
  let : Countable V := countable_vertices hgraph.locallyFinite hgraph.connected
  let : Countable E := countable_edges hgraph.locallyFinite
  have hp1 : (pc G : ℝ) < 1 :=
    (show (pc G : ℝ) < (ptwo G : ℝ) from hgap).trans_le (ptwo G).2.2
  obtain ⟨q,hq,hpq⟩ := lt_sSup_iff.mp hgap
  obtain ⟨T,hT⟩ := operatorBounded_of_le G hpq.le hq
  have hfin := critical_finite_general G hgraph.connected hgraph.locallyFinite hgraph.quasiTransitive hp1
  rw [criticalFiniteTail_eq G (volumeEvent G) x (hfin x)]
  exact critical_volume_powerTail_of_operator G hgraph.connected hgraph.locallyFinite
    hgraph.quasiTransitive hh hp1 T hT x

end Percolation.BenjaminiSchramm

end OAI
