import OAI.Probability.BenjaminiSchramm.HalfspaceFractionalRecurrence
import OAI.Probability.BenjaminiSchramm.LayerMonotoneLimit
import OAI.Probability.BenjaminiSchramm.GeometricIncrement

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma internalEdges_ceilings_iUnion (f : V → ℝ) (R b : ℝ) (hR : 0 < R) :
    (⋃ n : ℕ, internalEdges G {z | f z ≤ b+(n : ℝ)*R})=Set.univ := by
  ext e
  simp only [Set.mem_univ,iff_true]
  have hp : ∀ s : Sym2 V, ∃ n : ℕ, ∀ z ∈ s, f z ≤ b+(n : ℝ)*R := by
    intro s
    induction s using Sym2.inductionOn with
    | _ u v =>
      obtain ⟨N,hN⟩ := exists_nat_gt (max ((f u-b)/R) ((f v-b)/R))
      refine ⟨N,fun z hz => ?_⟩
      have hu := (div_lt_iff₀ hR).mp ((le_max_left _ _).trans_lt hN)
      have hv := (div_lt_iff₀ hR).mp ((le_max_right _ _).trans_lt hN)
      rcases Sym2.mem_iff.mp hz with rfl | rfl <;> linarith
  obtain ⟨n,hn⟩ := hp (G e)
  exact mem_iUnion.mpr ⟨n,hn⟩

lemma internalEdges_ceilings_monotone (f : V → ℝ) (R b : ℝ) (hR : 0 ≤ R) :
    Monotone (fun n : ℕ => internalEdges G {z | f z ≤ b+(n : ℝ)*R}) := by
  intro n m hnm
  apply internalEdges_mono G
  intro z hz
  have hh := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnm : (n : ℝ) ≤ m) hR
  change f z ≤ b+(n : ℝ)*R at hz
  exact hz.trans (by linarith)

variable [Countable V] [Countable E]

theorem fullspace_fractional_from_ceiling_profiles
    (hl : LocallyFinite G) (d : ℕ)
    (hd : ∀ u, (finite_neighbors hl u).toFinset.card ≤ d)
    (h : V → V → ℝ) (hself : ∀ x, h x x=0)
    (hbase : ∀ x z v, h x v=h x z+h z v)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ x e u v, u ∈ G e → v ∈ G e → |h x v-h x u| ≤ R)
    (p : unitInterval) (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (q t α ρ : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (ht : 0 < t) (ht1 : t < 1)
    (hrate : α+t*ρ < 0)
    (htop : ∀ u ∈ ({t,q*t} : Set ℝ), ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
        (∫⁻ ω, (restrictedLayerCount G (internalEdges G {v | h x v ≤ k})
          {v | k-R ≤ h x v ∧ h x v ≤ k+R} ω x)^u ∂law p) ≤
            C*ENNReal.ofReal (Real.exp ((α+ε)*k)))
    (D : ℝ≥0∞) (hD : D < ⊤)
    (hcont : ∀ s : ℝ, 0 ≤ s → ∀ z : V,
      (∫⁻ ω, (restrictedLayerCount G (internalEdges G {v | h z v ≤ R})
        {v | -s-R ≤ h z v ∧ h z v ≤ -s+R} ω z)^q ∂law p) ≤
          D*ENNReal.ofReal (Real.exp (ρ*s))) :
    ∀ ζ : ℝ, 0 < ζ → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G Set.univ
        {v | k-R ≤ h x v ∧ h x v ≤ k+R} ω x)^(q*t) ∂law p) ≤
          C*ENNReal.ofReal (Real.exp ((α+ζ)*k)) := by
  intro ζ hζ
  let ε := min ζ (-(α+t*ρ)/2)
  have hε : 0 < ε := lt_min hζ (by linarith)
  have hεζ : ε ≤ ζ := min_le_left _ _
  have hεrate : ε ≤ -(α+t*ρ)/2 := min_le_right _ _
  have hqt : 0 < q*t := mul_pos hq ht
  obtain ⟨A,hA,hab⟩ := htop t (by simp) ε hε
  obtain ⟨B,hB,hbb⟩ := htop (q*t) (by simp) ε hε
  let K := (d : ℝ≥0∞)^t*A*D^t*ENNReal.ofReal (Real.exp ((max ρ 0*R)*t))
  have hK : K < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg ht.le (ENNReal.natCast_ne_top d)) hA)
      (ENNReal.rpow_lt_top_of_nonneg ht.le hD.ne)) ENNReal.ofReal_lt_top
  let s := -(α+t*ρ)*R/2
  have hs : 0 < s := by
    dsimp [s]
    exact div_pos (mul_pos (neg_pos.mpr hrate) hR) (by norm_num)
  let S : ℝ≥0∞ := ∑' n : ℕ, ENNReal.ofReal (Real.exp (-s*n))
  have hS : S < ⊤ := by
    apply Summable.tsum_ofReal_lt_top
    simpa only [mul_comm] using Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos hs)
  refine ⟨B+K*S,ENNReal.add_lt_top.mpr ⟨hB,ENNReal.mul_lt_top hK hS⟩,fun k hk x => ?_⟩
  let f := h x
  let W := {v | k-R ≤ f v ∧ f v ≤ k+R}
  let F (n : ℕ) := ∫⁻ ω, (restrictedLayerCount G
    (internalEdges G {v | f v ≤ k+(n : ℝ)*R}) W ω x)^(q*t) ∂law p
  let Z := ENNReal.ofReal (Real.exp ((α+ε)*k))
  have h0 : F 0 ≤ B*Z := by simpa only [F,Nat.cast_zero,zero_mul,add_zero] using hbb k hk x
  have hstep (n : ℕ) : F (n+1) ≤ F n+K*Z*ENNReal.ofReal (Real.exp (-s*n)) := by
    let b := k+(n : ℝ)*R
    let J := internalEdges G {v | f v ≤ k+((n : ℝ)+1)*R}
    let L := D*ENNReal.ofReal (Real.exp (ρ*((n : ℝ)*R)+max ρ 0*R))
    have hL (z : V) (hzlo : b < f z) (hzhi : f z ≤ b+R) :
        (∫⁻ ω, (restrictedLayerCount G J W ω z)^q ∂law p) ≤ L := by
      let r := f z-k
      have hr : 0 ≤ r := by dsimp [r,b] at *; nlinarith [Nat.cast_nonneg (α := ℝ) n]
      apply le_trans _ ((hcont r hr z).trans ?_)
      · apply lintegral_mono
        intro ω
        apply ENNReal.rpow_le_rpow _ hq.le
        apply (restrictedLayerCount_mono_edges G ?_ W ω z).trans
        · apply restrictedLayerCount_mono_vertices G
          intro v hv
          have he := hbase x z v
          dsimp [r,f,W] at hv ⊢
          exact ⟨by linarith [hv.1],by linarith [hv.2]⟩
        · apply internalEdges_mono G
          intro v hv
          have he := hbase x z v
          dsimp [J,f,b] at hv hzlo hzhi ⊢
          linarith
      · apply mul_le_mul' le_rfl
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hrlo : (n : ℝ)*R ≤ r := by dsimp [r,b] at *; linarith
        have hrhi : r ≤ (n : ℝ)*R+R := by dsimp [r,b] at *; linarith
        by_cases hρ : 0 ≤ ρ
        · rw [max_eq_left hρ]
          nlinarith
        · rw [max_eq_right (le_of_not_ge hρ)]
          nlinarith
    have hI : ∀ᵐ ω ∂law p, (cluster G (ω ∩ internalEdges G {v | f v ≤ b}) x).Finite := by
      filter_upwards [hfin x] with ω hω
      exact hω.subset fun v hv => conn_mono G inter_subset_left hv
    have hh := lower_halfspace_fractional_recurrence G hl d hd (fun _ => p) f R b
      (hjump x) J x (by simp only [f,hself]; dsimp [b]; positivity)
      (by simpa only [CriticalPercolation.BernoulliProduct.law_const,law] using hI)
      W hq hq1 ht ht1.le L
      (fun z hzlo hzhi => by simpa only [CriticalPercolation.BernoulliProduct.law_const,law] using hL z hzlo hzhi)
    simp only [CriticalPercolation.BernoulliProduct.law_const] at hh
    have htop' : (∫⁻ ω, (restrictedLayerCount G (internalEdges G {v | f v ≤ b})
        {v | b-R ≤ f v ∧ f v ≤ b} ω x)^t ∂law p) ≤
        A*ENNReal.ofReal (Real.exp ((α+ε)*b)) := by
      apply le_trans _ (hab b (by dsimp [b]; positivity) x)
      apply lintegral_mono
      intro ω
      apply ENNReal.rpow_le_rpow _ ht.le
      apply restrictedLayerCount_mono_vertices G
      intro v hv
      exact ⟨hv.1,hv.2.trans (by linarith)⟩
    have hcast : ((n+1 : ℕ) : ℝ)=(n : ℝ)+1 := by norm_cast
    simp only [F,hcast]
    apply hh.trans
    apply add_le_add le_rfl
    apply (mul_le_mul' (mul_le_mul' le_rfl htop') le_rfl).trans
    dsimp [L]
    rw [ENNReal.mul_rpow_of_nonneg _ _ ht.le,ennreal_exp_rpow _ _ ht.le]
    have he : (α+ε)*b+(ρ*((n : ℝ)*R)+max ρ 0*R)*t ≤
        (max ρ 0*R)*t+((α+ε)*k+(-s*(n : ℝ))) := by
      have hh := mul_le_mul_of_nonneg_right hεrate (mul_nonneg (Nat.cast_nonneg n) hR.le)
      dsimp [b,s]
      nlinarith
    calc
      _ = ((d : ℝ≥0∞)^t*A*D^t)*ENNReal.ofReal
          (Real.exp ((α+ε)*b+(ρ*((n : ℝ)*R)+max ρ 0*R)*t)) := by
        rw [Real.exp_add ((α+ε)*b) ((ρ*((n : ℝ)*R)+max ρ 0*R)*t),
          ENNReal.ofReal_mul (Real.exp_nonneg _)]
        ac_rfl
      _ ≤ ((d : ℝ≥0∞)^t*A*D^t)*ENNReal.ofReal (Real.exp
          ((max ρ 0*R)*t+((α+ε)*k+(-s*(n : ℝ))))) :=
        mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr he))
      _ = _ := by
        dsimp [K,Z]
        rw [Real.exp_add ((max ρ 0*R)*t) ((α+ε)*k+(-s*(n : ℝ))),
          ENNReal.ofReal_mul (Real.exp_nonneg _),Real.exp_add ((α+ε)*k) (-s*(n : ℝ)),
          ENNReal.ofReal_mul (Real.exp_nonneg _)]
        ac_rfl
  have hF := geometric_increment_factored F B K Z s h0 hstep
  have hlim := restrictedLayerMoment_iUnion G
    (fun n : ℕ => internalEdges G {v | f v ≤ k+(n : ℝ)*R})
    (internalEdges_ceilings_monotone G f R k hR.le) W x p hqt
  rw [internalEdges_ceilings_iUnion G f R k hR] at hlim
  rw [hlim]
  apply (iSup_le fun n => hF n).trans
  exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (by linarith : α+ε ≤ α+ζ) hk)))

end Percolation.BenjaminiSchramm

end

end OAI
