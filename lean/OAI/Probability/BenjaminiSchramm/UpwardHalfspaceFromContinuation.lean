import OAI.Probability.BenjaminiSchramm.CeilingZeroBand

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem upward_halfspace_from_continuation
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (d : ℕ) (hd : ∀ u, (Percolation.finite_neighbors hl u).toFinset.card ≤ d)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e u v, u ∈ G.ends e → v ∈ G.ends e → |G.orbitAdjustedHeight a u v| ≤ R)
    (p : unitInterval) (hfin : ∀ x, ∀ᵐ ω ∂G.law p, (Percolation.cluster G.ends ω x).Finite)
    (U : ℝ) (hup : ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ r : ℝ, 0 ≤ r → ∀ x : V,
        (∫⁻ ω, (G.adjustedSlabBandCount a (-r) (k+r) (k-R) (k+R) ω x)^q ∂G.law p) ≤
          C*ENNReal.ofReal (Real.exp ((-1+ζ)*k+U*r)))
    (q t ρ : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (ht : 0 < t) (ht1 : t < 1)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 3/4)
    (D : ℝ≥0∞) (hD : D < ⊤)
    (hdown : ∀ s : ℝ, 0 ≤ s → ∀ z : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight a z v ≤ R})
        {v | -s-R ≤ G.orbitAdjustedHeight a z v ∧ G.orbitAdjustedHeight a z v ≤ -s+R} ω z)^q ∂G.law p) ≤
          D*ENNReal.ofReal (Real.exp (ρ*s))) :
    ∀ ζ : ℝ, 0 < ζ → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | 0 ≤ G.orbitAdjustedHeight a x v})
        {v | k-R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ k+R} ω x)^(q*t) ∂G.law p) ≤
          C*ENNReal.ofReal (Real.exp ((-1+ζ)*k)) := by
  intro ζ hζ
  let ε := min ζ (1/8)
  have hε : 0 < ε := lt_min hζ (by norm_num)
  have hεζ : ε ≤ ζ := min_le_left _ _
  have hε1 : ε ≤ 1/8 := min_le_right _ _
  have hqt : 0 < q*t := mul_pos hq ht
  have hqt1 : q*t < 1 := (mul_le_mul_of_nonneg_right hq1 ht.le).trans_lt (by simpa using ht1)
  obtain ⟨A,hA,hab⟩ := hup t ht ht1 ε hε
  obtain ⟨B,hB,hbb⟩ := hup (q*t) hqt hqt1 ε hε
  let K := (d : ℝ≥0∞)^t*A*D^t*
    ENNReal.ofReal (Real.exp (((-1+ε)+U)*R+t*ρ*(2*R)))
  have hK : K < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg ht.le (ENNReal.natCast_ne_top d)) hA)
      (ENNReal.rpow_lt_top_of_nonneg ht.le hD.ne)) ENNReal.ofReal_lt_top
  let B' := B*ENNReal.ofReal (Real.exp (U*R))
  have hB' : B' < ⊤ := ENNReal.mul_lt_top hB ENNReal.ofReal_lt_top
  let S : ℝ≥0∞ := ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(R/8)*n))
  have hS : S < ⊤ := by
    apply Summable.tsum_ofReal_lt_top
    simpa only [mul_comm] using Real.summable_exp_nat_mul_iff.mpr
      (neg_neg_of_pos (show 0 < R/8 by positivity))
  refine ⟨B'+K*S,ENNReal.add_lt_top.mpr ⟨hB',ENNReal.mul_lt_top hK hS⟩,fun k hk x => ?_⟩
  let f := G.orbitAdjustedHeight a x
  let W := {v | k-R ≤ f v ∧ f v ≤ k+R}
  let F (n : ℕ) := ∫⁻ ω, (restrictedLayerCount G.ends
    (Percolation.internalEdges G.ends {v | 0 ≤ f v ∧ f v ≤ k+R+(n : ℝ)*R}) W ω x)^(q*t) ∂G.law p
  let Z := ENNReal.ofReal (Real.exp ((-1+ε)*k))
  have h0 : F 0 ≤ B'*Z := by
    have hh := hbb k hk R hR.le x
    apply le_trans _ (hh.trans_eq ?_)
    · apply lintegral_mono
      intro ω
      apply ENNReal.rpow_le_rpow _ hqt.le
      rw [G.adjustedSlabBandCount_eq_restricted]
      apply restrictedLayerCount_mono_edges G.ends
      apply Percolation.internalEdges_mono G.ends
      intro v hv
      simp only [Nat.cast_zero,zero_mul,add_zero] at hv
      exact ⟨by dsimp [f] at hv; linarith [hv.1],hv.2⟩
    · dsimp [B',Z]
      rw [Real.exp_add ((-1+ε)*k) (U*R),ENNReal.ofReal_mul (Real.exp_nonneg _)]
      ac_rfl
  have hstep (n : ℕ) : F (n+1) ≤ F n+K*Z*ENNReal.ofReal (Real.exp (-(R/8)*n)) := by
    let b := k+R+(n : ℝ)*R
    let J := Percolation.internalEdges G.ends {v | 0 ≤ f v ∧ f v ≤ k+R+((n : ℝ)+1)*R}
    let L := D*ENNReal.ofReal (Real.exp (ρ*((n : ℝ)*R+2*R)))
    have hL (z : V) (hzlo : b < f z) (hzhi : f z ≤ b+R) :
        (∫⁻ ω, (restrictedLayerCount G.ends J W ω z)^q ∂G.law p) ≤ L := by
      let s := f z-k
      have hs : 0 ≤ s := by dsimp [s,b] at *; nlinarith [Nat.cast_nonneg (α := ℝ) n]
      have hh := hdown s hs z
      apply le_trans _ (hh.trans ?_)
      · apply lintegral_mono
        intro ω
        apply ENNReal.rpow_le_rpow _ hq.le
        apply (restrictedLayerCount_mono_edges G.ends ?_ W ω z).trans
        · apply restrictedLayerCount_mono_vertices G.ends
          intro v hv
          have he := G.orbitAdjustedHeight_change_base hc hl a x z v
          dsimp [s,f,W] at hv ⊢
          exact ⟨by linarith [hv.1],by linarith [hv.2]⟩
        · apply Percolation.internalEdges_mono G.ends
          intro v hv
          have he := G.orbitAdjustedHeight_change_base hc hl a x z v
          dsimp [J,f,b] at hv hzlo hzhi ⊢
          linarith [hv.2]
      · apply mul_le_mul' le_rfl
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ hρ
        dsimp [s,b] at *
        linarith
    have hI : ∀ᵐ ω ∂G.law p,
        (Percolation.cluster G.ends (ω ∩ Percolation.internalEdges G.ends {v | 0 ≤ f v ∧ f v ≤ b}) x).Finite := by
      filter_upwards [hfin x] with ω hω
      exact hω.subset fun v hv => Percolation.conn_mono G.ends inter_subset_left hv
    have hh := lower_slab_fractional_recurrence G.ends hl d hd (fun _ => p) f R 0 b
      (G.height_difference_jump hc hl a R hjump x) J
      (Percolation.internalEdges_mono G.ends (fun _ hv => hv.1)) x
      (by simp only [f,G.orbitAdjustedHeight_self]; exact ⟨le_rfl,by dsimp [b]; positivity⟩)
      (by simpa only [CriticalPercolation.BernoulliProduct.law_const,CriticalPercolation.BondGraph.law] using hI)
      W hq hq1 ht ht1.le L
      (fun z hzlo hzhi => by simpa only [CriticalPercolation.BernoulliProduct.law_const,
        CriticalPercolation.BondGraph.law] using hL z hzlo hzhi)
    simp only [CriticalPercolation.BernoulliProduct.law_const] at hh
    have htop : (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | 0 ≤ f v ∧ f v ≤ b})
        {v | b-R ≤ f v ∧ f v ≤ b} ω x)^t ∂G.law p) ≤
        A*ENNReal.ofReal (Real.exp ((-1+ε)*b+U*R)) := by
      apply le_trans _ (hab b (by dsimp [b]; positivity) R hR.le x)
      apply lintegral_mono
      intro ω
      apply ENNReal.rpow_le_rpow _ ht.le
      apply G.restrictedLayerCount_le_adjustedSlab
      · apply Percolation.internalEdges_mono G.ends
        intro v hv
        exact ⟨by dsimp [f] at hv; linarith [hv.1],by dsimp [f] at hv; linarith [hv.2]⟩
      · intro v hv
        exact ⟨hv.1,by dsimp [f] at hv; linarith [hv.2]⟩
    have hcast : ((n+1 : ℕ) : ℝ)=(n : ℝ)+1 := by norm_cast
    simp only [F,hcast]
    apply hh.trans
    apply add_le_add le_rfl
    apply (mul_le_mul' (mul_le_mul' le_rfl htop) le_rfl).trans
    dsimp [L]
    rw [ENNReal.mul_rpow_of_nonneg _ _ ht.le,ennreal_exp_rpow _ _ ht.le]
    have hrate : -1+ε+t*ρ ≤ -(1/8 : ℝ) := by
      have hh := mul_le_of_le_one_left hρ ht1.le
      linarith
    have he : ((-1+ε)*b+U*R)+(ρ*((n : ℝ)*R+2*R))*t ≤
        (((-1+ε)+U)*R+t*ρ*(2*R))+((-1+ε)*k+(-(R/8)*(n : ℝ))) := by
      have hh := mul_le_mul_of_nonneg_right hrate (mul_nonneg (Nat.cast_nonneg n) hR.le)
      dsimp [b]
      nlinarith
    calc
      _ = ((d : ℝ≥0∞)^t*A*D^t)*ENNReal.ofReal
          (Real.exp (((-1+ε)*b+U*R)+(ρ*((n : ℝ)*R+2*R))*t)) := by
        rw [Real.exp_add ((-1+ε)*b+U*R) ((ρ*((n : ℝ)*R+2*R))*t),
          ENNReal.ofReal_mul (Real.exp_nonneg _)]
        ac_rfl
      _ ≤ ((d : ℝ≥0∞)^t*A*D^t)*ENNReal.ofReal (Real.exp
          ((((-1+ε)+U)*R+t*ρ*(2*R))+((-1+ε)*k+(-(R/8)*(n : ℝ))))) :=
        mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr he))
      _ = _ := by
        dsimp [K,Z]
        rw [Real.exp_add (((-1+ε)+U)*R+t*ρ*(2*R)) ((-1+ε)*k+(-(R/8)*(n : ℝ))),
          ENNReal.ofReal_mul (Real.exp_nonneg _),Real.exp_add ((-1+ε)*k) (-(R/8)*(n : ℝ)),
          ENNReal.ofReal_mul (Real.exp_nonneg _)]
        ac_rfl
  have hF := geometric_increment_factored F B' K Z (R/8) h0 hstep
  have hlim := restrictedLayerMoment_iUnion G.ends
    (fun n : ℕ => Percolation.internalEdges G.ends {v | 0 ≤ f v ∧ f v ≤ k+R+(n : ℝ)*R})
    (internalEdges_upperSlabs_monotone G.ends f R 0 (k+R) hR.le) W x p hqt
  rw [internalEdges_upperSlabs_iUnion G.ends f R 0 (k+R) hR] at hlim
  have hh : (∫⁻ ω, (restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {v | 0 ≤ f v}) W ω x)^(q*t) ∂G.law p) ≤ (B'+K*S)*Z := by
    simp only [CriticalPercolation.BondGraph.law,Percolation.law] at hlim ⊢
    rw [hlim]
    exact iSup_le fun n => hF n
  apply hh.trans
  apply mul_le_mul' le_rfl
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (by linarith : -1+ε ≤ -1+ζ) hk

end CriticalPercolation.BondGraph

end

end OAI
