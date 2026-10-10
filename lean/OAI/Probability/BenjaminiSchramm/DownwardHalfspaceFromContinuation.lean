import OAI.Probability.BenjaminiSchramm.CeilingZeroBand

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem downward_halfspace_from_continuation
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (d : ℕ) (hd : ∀ u, (Percolation.finite_neighbors hl u).toFinset.card ≤ d)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e u v, u ∈ G.ends e → v ∈ G.ends e → |G.orbitAdjustedHeight a u v| ≤ R)
    (p : unitInterval) (hfin : ∀ x, ∀ᵐ ω ∂G.law p, (Percolation.cluster G.ends ω x).Finite)
    (L : ℝ) (hdown : G.lowerSlabFractionalProfile a p R L)
    (q t : ℝ) (hq : 0 < q) (hq1 : q < 1) (ht : 0 < t) (ht1 : t < 1)
    (D : ℝ≥0∞) (hD : D < ⊤)
    (hup : ∀ s : ℝ, 0 ≤ s → ∀ z : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | -R ≤ G.orbitAdjustedHeight a z v})
        {v | s-R ≤ G.orbitAdjustedHeight a z v ∧ G.orbitAdjustedHeight a z v ≤ s+R} ω z)^q ∂G.law p) ≤
          D*ENNReal.ofReal (Real.exp (-s/2))) :
    ∀ ζ : ℝ, 0 < ζ → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight a x v ≤ 0})
        {v | -k-R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ -k+R} ω x)^(q*t) ∂G.law p) ≤
          C*ENNReal.ofReal (Real.exp (ζ*k)) := by
  intro ζ hζ
  let ε := min ζ (t/4)
  have hε : 0 < ε := lt_min hζ (by positivity)
  have hεζ : ε ≤ ζ := min_le_left _ _
  have hεt : ε ≤ t/4 := min_le_right _ _
  have hqt : 0 < q*t := mul_pos hq ht
  have hqt1 : q*t < 1 := (mul_le_mul_of_nonneg_right hq1.le ht.le).trans_lt (by simpa using ht1)
  obtain ⟨A,hA,hab⟩ := hdown t ht ht1 ε hε
  obtain ⟨B,hB,hbb⟩ := hdown (q*t) hqt hqt1 ε hε
  let K := (d : ℝ≥0∞)^t*A*D^t
  have hK : K < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ht.le (ENNReal.natCast_ne_top d)) hA)
    (ENNReal.rpow_lt_top_of_nonneg ht.le hD.ne)
  let S : ℝ≥0∞ := ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(t*R/4)*n))
  have hS : S < ⊤ := by
    apply Summable.tsum_ofReal_lt_top
    simpa only [mul_comm] using Real.summable_exp_nat_mul_iff.mpr
      (neg_neg_of_pos (show 0 < t*R/4 by positivity))
  refine ⟨B+K*S,ENNReal.add_lt_top.mpr ⟨hB,ENNReal.mul_lt_top hK hS⟩,fun k hk x => ?_⟩
  let f := fun z => -G.orbitAdjustedHeight a x z
  let W := {v | -k-R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ -k+R}
  let F (n : ℕ) := ∫⁻ ω, (restrictedLayerCount G.ends
    (Percolation.internalEdges G.ends {v | -(k+(n : ℝ)*R) ≤ G.orbitAdjustedHeight a x v ∧
      G.orbitAdjustedHeight a x v ≤ 0}) W ω x)^(q*t) ∂G.law p
  let Z := ENNReal.ofReal (Real.exp (ε*k))
  have h0 : F 0 ≤ B*Z := by
    have hh := hbb k hk 0 (by norm_num) x
    simpa only [F,Nat.cast_zero,zero_mul,add_zero,sub_zero,mul_zero,add_zero,
      G.adjustedSlabBandCount_eq_restricted] using hh
  have hstep (n : ℕ) : F (n+1) ≤ F n+K*Z*ENNReal.ofReal (Real.exp (-(t*R/4)*n)) := by
    let b := k+(n : ℝ)*R
    let J := Percolation.internalEdges G.ends
      {v | -(k+((n : ℝ)+1)*R) ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ 0}
    let M := D*ENNReal.ofReal (Real.exp (-((n : ℝ)*R)/2))
    have hM (z : V) (hzlo : b < f z) (hzhi : f z ≤ b+R) :
        (∫⁻ ω, (restrictedLayerCount G.ends J W ω z)^q ∂G.law p) ≤ M := by
      let s := -k-G.orbitAdjustedHeight a x z
      have hs : 0 ≤ s := by
        dsimp [s,f,b] at *
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      apply le_trans _ ((hup s hs z).trans ?_)
      · apply lintegral_mono
        intro ω
        apply ENNReal.rpow_le_rpow _ hq.le
        apply (restrictedLayerCount_mono_edges G.ends ?_ W ω z).trans
        · apply restrictedLayerCount_mono_vertices G.ends
          intro v hv
          have he := G.orbitAdjustedHeight_change_base hc hl a x z v
          dsimp [s,W] at hv ⊢
          exact ⟨by linarith [hv.1],by linarith [hv.2]⟩
        · apply Percolation.internalEdges_mono G.ends
          intro v hv
          have he := G.orbitAdjustedHeight_change_base hc hl a x z v
          dsimp [J,f,b] at hv hzlo hzhi ⊢
          linarith [hv.1]
      · apply mul_le_mul' le_rfl
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        dsimp [s,f,b] at *
        linarith
    have hIeq : Percolation.internalEdges G.ends {v | 0 ≤ f v ∧ f v ≤ b}=
        Percolation.internalEdges G.ends {v | -b ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ 0} := by
      congr 1
      ext v
      dsimp [f]
      constructor <;> intro hv <;> constructor <;> linarith [hv.1,hv.2]
    have hI : ∀ᵐ ω ∂G.law p,
        (Percolation.cluster G.ends (ω ∩ Percolation.internalEdges G.ends {v | 0 ≤ f v ∧ f v ≤ b}) x).Finite := by
      filter_upwards [hfin x] with ω hω
      exact hω.subset fun v hv => Percolation.conn_mono G.ends inter_subset_left hv
    have hj : ∀ e u v, u ∈ G.ends e → v ∈ G.ends e → |f v-f u| ≤ R := by
      intro e u v hu hv
      simpa only [f,neg_sub_neg,abs_sub_comm] using
        G.height_difference_jump hc hl a R hjump x e u v hu hv
    have hh := lower_slab_fractional_recurrence G.ends hl d hd (fun _ => p) f R 0 b hj J
      (Percolation.internalEdges_mono G.ends (fun v hv => by dsimp [f]; linarith [hv.2])) x
      (by simp only [f,G.orbitAdjustedHeight_self,neg_zero]; exact ⟨le_rfl,by dsimp [b]; positivity⟩)
      (by simpa only [CriticalPercolation.BernoulliProduct.law_const,CriticalPercolation.BondGraph.law] using hI)
      W hq hq1.le ht ht1.le M
      (fun z hzlo hzhi => by simpa only [CriticalPercolation.BernoulliProduct.law_const,
        CriticalPercolation.BondGraph.law] using hM z hzlo hzhi)
    simp only [CriticalPercolation.BernoulliProduct.law_const,hIeq] at hh
    have htop : (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | -b ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ 0})
        {v | b-R ≤ f v ∧ f v ≤ b} ω x)^t ∂G.law p) ≤ A*ENNReal.ofReal (Real.exp (ε*b)) := by
      have hb := hab b (by dsimp [b]; positivity) 0 (by norm_num) x
      simp only [sub_zero,mul_zero,add_zero] at hb
      apply le_trans _ hb
      apply lintegral_mono
      intro ω
      apply ENNReal.rpow_le_rpow _ ht.le
      rw [G.adjustedSlabBandCount_eq_restricted]
      apply restrictedLayerCount_mono_vertices G.ends
      intro v hv
      dsimp [f] at hv
      exact ⟨by linarith [hv.2],by linarith [hv.1]⟩
    have hcast : ((n+1 : ℕ) : ℝ)=(n : ℝ)+1 := by norm_cast
    simp only [F,hcast]
    apply hh.trans
    apply add_le_add le_rfl
    apply (mul_le_mul' (mul_le_mul' le_rfl htop) le_rfl).trans
    dsimp [M]
    rw [ENNReal.mul_rpow_of_nonneg _ _ ht.le,ennreal_exp_rpow _ _ ht.le]
    have he : ε*b+(-((n : ℝ)*R)/2)*t ≤ ε*k+(-(t*R/4)*(n : ℝ)) := by
      have hh := mul_le_mul_of_nonneg_right hεt (mul_nonneg (Nat.cast_nonneg n) hR.le)
      dsimp [b]
      nlinarith
    calc
      _ = K*ENNReal.ofReal (Real.exp (ε*b+(-((n : ℝ)*R)/2)*t)) := by
        dsimp [K]
        rw [Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _)]
        ac_rfl
      _ ≤ K*ENNReal.ofReal (Real.exp (ε*k+(-(t*R/4)*(n : ℝ)))) :=
        mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr he))
      _ = _ := by
        dsimp [Z,K]
        rw [Real.exp_add (ε*k) (-(t*R/4)*(n : ℝ)),ENNReal.ofReal_mul (Real.exp_nonneg _),mul_assoc]
        ac_rfl
  have hF := geometric_increment_factored F B K Z (t*R/4) h0 hstep
  have he (n : ℕ) : -k-(n : ℝ)*R= -(k+(n : ℝ)*R) := by ring
  have hlim := restrictedLayerMoment_iUnion G.ends
    (fun n : ℕ => Percolation.internalEdges G.ends {v | -k-(n : ℝ)*R ≤ G.orbitAdjustedHeight a x v ∧
      G.orbitAdjustedHeight a x v ≤ 0})
    (internalEdges_lowerSlabs_shift_monotone G.ends _ R 0 (-k) hR.le) W x p hqt
  rw [internalEdges_lowerSlabs_shift_iUnion G.ends _ R 0 (-k) hR] at hlim
  have hh : (∫⁻ ω, (restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight a x v ≤ 0}) W ω x)^(q*t) ∂G.law p) ≤
        (B+K*S)*Z := by
    simp only [CriticalPercolation.BondGraph.law,Percolation.law] at hlim ⊢
    rw [hlim]
    apply iSup_le
    intro n
    simpa only [F,he,CriticalPercolation.BondGraph.law] using hF n
  apply hh.trans
  exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right hεζ hk)))

end CriticalPercolation.BondGraph

end

end OAI
