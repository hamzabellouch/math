import OAI.Probability.BenjaminiSchramm.FullLayerProfile
import OAI.Probability.BenjaminiSchramm.LayerFirstMomentRate
import OAI.Probability.BenjaminiSchramm.NormalizedExponentComparison

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace Percolation.BenjaminiSchramm

lemma exponential_rate_le_of_bound (a b c C : ℝ) (hc : 0 < c)
    (h : ∀ n : ℕ, 0 < n → c*Real.exp (-a*n) ≤ C*Real.exp (-b*n)) : b ≤ a := by
  have hC : 0 < C := by
    have hh := h 1 (by norm_num)
    have hp : 0 < c*Real.exp (-a*(1 : ℕ)) := mul_pos hc (Real.exp_pos _)
    exact pos_of_mul_pos_left (hp.trans_le hh) (Real.exp_nonneg _)
  by_contra hn
  have hab : 0 < b-a := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨N,hN⟩ := exists_nat_gt ((Real.log C-Real.log c)/(b-a))
  let n := N+1
  have hh := Real.log_le_log (mul_pos hc (Real.exp_pos _)) (h n (Nat.succ_pos N))
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne',Real.log_mul hC.ne' (Real.exp_pos _).ne',
    Real.log_exp,Real.log_exp] at hh
  have hnn : (Real.log C-Real.log c)/(b-a) < (n : ℝ) :=
    hN.trans (by dsimp [n]; push_cast; linarith)
  have hn' := (div_lt_iff₀ hab).mp hnn
  linarith

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem adjustedHalfspaceHit_le_upLayerMoment
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (p : unitInterval) (C : ℝ≥0∞)
    (hrow : ∀ z, (∑' y, G.law p {ω | Percolation.Conn G.ends ω z y}) ≤ C)
    (n : ℕ) (hn : 0 < n) (x : V) :
    G.law p (G.adjustedHalfspaceHit a x 0 (R*n)) ≤ G.supAdjustedUpLayerMoment a R p n*C := by
  let f := G.adjustedLayerIndex a R 0 x
  let I := Percolation.internalEdges G.ends {v | 0 ≤ G.orbitAdjustedHeight a x v}
  let A := {v | R*n ≤ G.orbitAdjustedHeight a x v}
  have hj : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → f w ≤ f v+1 ∧ f v ≤ f w+1 := by
    intro e v w hv hw
    have hh := G.adjustedLayerIndex_edge_jump hc hl a R 0 hR hjump x v w e hv hw
    change f v-1 ≤ f w ∧ f w ≤ f v+1 at hh
    exact ⟨hh.2,by omega⟩
  have hx : f x < (n : ℤ) := by
    simp only [f,G.adjustedLayerIndex_self]
    exact_mod_cast hn
  have hA : ∀ y ∈ A, (n : ℤ) ≤ f y := by
    intro y hy
    change R*n ≤ G.orbitAdjustedHeight a x y at hy
    simp only [f,adjustedLayerIndex,add_zero,Int.floor_zero,sub_zero]
    apply Int.le_floor.mpr
    apply (le_div_iff₀ hR).mpr
    push_cast
    nlinarith
  have hindicator (ω : Set E) :
      (G.adjustedHalfspaceHit a x 0 (R*n)).indicator (fun _ => (1 : ℝ≥0∞)) ω ≤
        restrictedLayerCount G.ends I A ω x := by
    by_cases hω : ω ∈ G.adjustedHalfspaceHit a x 0 (R*n)
    · rw [Set.indicator_of_mem hω]
      obtain ⟨y,hy,hxy⟩ := hω
      apply le_trans _ (ENNReal.le_tsum y)
      exact (ite_eq_left ⟨hy,hxy⟩).symm.le
    · rw [Set.indicator_of_notMem hω]
      exact bot_le
  calc
    _ = ∫⁻ ω, (G.adjustedHalfspaceHit a x 0 (R*n)).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂G.law p :=
      (lintegral_indicator_one (G.measurableSet_adjustedHalfspaceHit _ _ _ _)).symm
    _ ≤ ∫⁻ ω, restrictedLayerCount G.ends I A ω x ∂G.law p := lintegral_mono hindicator
    _ ≤ _ := (first_layer_moment_bound_with_row G.ends p C hrow f hj I A x n hx hA).trans
      (mul_le_mul' (G.adjustedUpLayerMoment_le_sup a R p n x 0) le_rfl)

theorem crossing_rate_ge_layer_rate [Nonempty V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (p : unitInterval) (C : ℝ≥0∞) (hC : C < ⊤)
    (hrow : ∀ z, (∑' y, G.law p {ω | Percolation.Conn G.ends ω z y}) ≤ C)
    (α β : ℝ) (hα : 0 ≤ α)
    (hlower : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ,
      c*Real.exp (-(α+ε)*m) ≤ (G.infimalAdjustedCrossing a p m).toReal)
    (hupper : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      G.supAdjustedUpLayerMoment a R p n ≤ ENNReal.ofReal (K*Real.exp (-(β-ε)*n))) :
    β ≤ α*R := by
  have hcompare (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) : β-ε ≤ (α+δ)*R := by
    obtain ⟨c,hcpos,hcbd⟩ := hlower δ hδ
    obtain ⟨K,hK,hKbd⟩ := hupper ε hε
    have hc' : 0 < c*Real.exp (-(α+δ)) := mul_pos hcpos (Real.exp_pos _)
    apply exponential_rate_le_of_bound ((α+δ)*R) (β-ε)
      (c*Real.exp (-(α+δ))) (C.toReal*K) hc'
    intro n hn
    let m := ⌈R*(n : ℝ)⌉₊
    have hmlo : R*(n : ℝ) ≤ (m : ℝ) := Nat.le_ceil _
    have hmhi : (m : ℝ) ≤ R*(n : ℝ)+1 := (Nat.ceil_lt_add_one (mul_nonneg hR.le (Nat.cast_nonneg n))).le
    have hmin : G.infimalAdjustedCrossing a p m ≤
        G.law p (G.adjustedHalfspaceHit a (Classical.arbitrary V) 0 (R*n)) := by
      apply (iInf_le _ (Classical.arbitrary V)).trans
      apply measure_mono
      rintro ω ⟨y,hy,hxy⟩
      exact ⟨y,hmlo.trans hy,hxy⟩
    have he : ENNReal.ofReal (c*Real.exp (-(α+δ)*m)) ≤
        C*ENNReal.ofReal (K*Real.exp (-(β-ε)*n)) := by
      calc
        _ ≤ G.infimalAdjustedCrossing a p m := ENNReal.ofReal_le_of_le_toReal (hcbd m)
        _ ≤ G.supAdjustedUpLayerMoment a R p n*C := hmin.trans
          (G.adjustedHalfspaceHit_le_upLayerMoment hc hl a R hR hjump p C hrow n hn _)
        _ ≤ ENNReal.ofReal (K*Real.exp (-(β-ε)*n))*C := mul_le_mul' (hKbd n) le_rfl
        _ = _ := mul_comm _ _
    have her := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hC.ne ENNReal.ofReal_ne_top) he
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (mul_nonneg hK.le (Real.exp_nonneg _)),
      ENNReal.toReal_ofReal (mul_nonneg hcpos.le (Real.exp_nonneg _))] at her
    have hexp : Real.exp (-((α+δ)*R)*(n : ℝ)-(α+δ)) ≤ Real.exp (-(α+δ)*(m : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    calc
      _ = c*Real.exp (-((α+δ)*R)*(n : ℝ)-(α+δ)) := by rw [mul_assoc,←Real.exp_add]; congr 2; ring
      _ ≤ c*Real.exp (-(α+δ)*(m : ℝ)) := mul_le_mul_of_nonneg_left hexp hcpos.le
      _ ≤ _ := her.trans_eq (by ring)
  by_contra hn
  have hd : 0 < β-α*R := sub_pos.mpr (lt_of_not_ge hn)
  let ε := (β-α*R)/(2*(R+1))
  have hε : 0 < ε := div_pos hd (by positivity)
  have hh := hcompare ε ε hε hε
  have he : ε*(2*(R+1))=β-α*R := div_mul_cancel₀ _ (by positivity)
  nlinarith

end CriticalPercolation.BondGraph

end

end OAI
