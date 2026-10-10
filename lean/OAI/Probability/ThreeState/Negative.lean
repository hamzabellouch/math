import Mathlib
import OAI.Probability.ThreeState.Couplings
import OAI.Probability.ThreeState.Noise

namespace OAI

/-! Signed small-channel and Dobrushin non-reconstruction regions. -/

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

 

theorem regular_small_negative_nonreconstruction (b : ℕ) (hb : 2 ≤ b) (lam : ℝ)
    (h : Admissible lam) (hl : lam ≤ 0) (hc : 4*(b:ℝ)*lam^2 ≤ 1) :
    Tendsto (regularAdvantage b lam h) atTop (𝓝 0) := by
  have hb0 : (0:ℝ) < b := by exact_mod_cast (show 0<b by omega)
  let L := Real.sqrt ((b:ℝ)⁻¹)
  have hL0 : 0 < L := Real.sqrt_pos.mpr (inv_pos.mpr hb0)
  have hLsq : L^2=(b:ℝ)⁻¹ := Real.sq_sqrt (inv_nonneg.mpr hb0.le)
  have hK : (b:ℝ)*L^2=1 := by rw [hLsq, mul_inv_cancel₀ hb0.ne']
  have hbr : (2:ℝ)≤b := by exact_mod_cast hb
  have hL1 : L≤1 := by nlinarith [sq_nonneg L]
  have hL : Admissible L := ⟨by linarith, hL1⟩
  have hlow : -L/2≤lam := by
    have hh : 4*lam^2≤L^2 := (mul_le_mul_iff_right₀ hb0).mp (by nlinarith only [hc,hK])
    nlinarith
  let r := lam/L
  have hr0 : -(1/2:ℝ)≤r := (le_div_iff₀ hL0).mpr (by linarith)
  have hr1 : r≤1 := (div_le_one hL0).mpr (by linarith)
  have hr : Admissible r := ⟨hr0,hr1⟩
  have heq : L*r=lam := by dsimp [r]; field_simp
  have hp : Admissible (L*r) := by rwa [heq]
  have ht := ordered_tendsto_zero_of_uniform_fixedpoints (PMF.pure b) L hL
    (regular_positive_critical_uniform b hb L hL hL0 hK)
  apply squeeze_zero (fun n => advantage_nonneg (regularLaw b lam h n))
    (g := fun n => advantage (orderedLaw (PMF.pure b) L hL n)) _ ht
  intro n
  have hg := orderedAdvantage_degrade (PMF.pure b) L r hL hr hp n
  have heLaw : orderedLaw (PMF.pure b) (L*r) hp n = orderedLaw (PMF.pure b) lam h n := by congr 1
  rw [heLaw] at hg
  exact (orderedAdvantage_dominates (PMF.pure b) lam h n).trans hg

 

theorem poisson_small_negative_nonreconstruction (d : ℝ) (hd : 1 < d) (lam : ℝ)
    (h : Admissible lam) (hl : lam ≤ 0) (hc : 4*d*lam^2 ≤ 1) :
    Tendsto (poissonAdvantage d hd lam h) atTop (𝓝 0) := by
  have hd0 : 0 < d := by linarith
  let L := Real.sqrt d⁻¹
  have hL0 : 0 < L := Real.sqrt_pos.mpr (inv_pos.mpr hd0)
  have hLsq : L^2=d⁻¹ := Real.sq_sqrt (inv_nonneg.mpr hd0.le)
  have hK : d*L^2=1 := by rw [hLsq, mul_inv_cancel₀ hd0.ne']
  have hL1 : L≤1 := by
    have hi : d⁻¹≤1 := (inv_le_one₀ hd0).mpr hd.le
    nlinarith [sq_nonneg L]
  have hL : Admissible L := ⟨by linarith, hL1⟩
  have hlow : -L/2≤lam := by
    have hh : 4*lam^2≤L^2 := (mul_le_mul_iff_right₀ hd0).mp (by nlinarith only [hc,hK])
    nlinarith
  let r := lam/L
  have hr0 : -(1/2:ℝ)≤r := (le_div_iff₀ hL0).mpr (by linarith)
  have hr1 : r≤1 := (div_le_one hL0).mpr (by linarith)
  have hr : Admissible r := ⟨hr0,hr1⟩
  have heq : L*r=lam := by dsimp [r]; field_simp
  have hp : Admissible (L*r) := by rwa [heq]
  have ht := ordered_tendsto_zero_of_uniform_fixedpoints (poissonOffspring d hd0.le) L hL
    (poisson_positive_critical_uniform d hd L hL hL0 hK)
  apply squeeze_zero (fun n => advantage_nonneg (poissonLaw d hd0.le lam h n))
    (g := fun n => advantage (orderedLaw (poissonOffspring d hd0.le) L hL n)) _ ht
  intro n
  have hg := orderedAdvantage_degrade (poissonOffspring d hd0.le) L r hL hr hp n
  have heLaw : orderedLaw (poissonOffspring d hd0.le) (L*r) hp n = orderedLaw (poissonOffspring d hd0.le) lam h n := by congr 1
  rw [heLaw] at hg
  exact (orderedAdvantage_dominates (poissonOffspring d hd0.le) lam h n).trans hg

end ThreeState

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical
noncomputable section

 

lemma compose_pairTV_bound {α:Type*} (p:PMF ℕ) (law:Spin→PMF α) (d lam x:ℝ)
    (h:Admissible lam) (hD:HasMean p (fun k:ℕ=>(k:ℝ)))
    (hmean:mean p (fun k:ℕ=>(k:ℝ))=d) (K:ℕ) (hK:2≤K)
    (hx0:0≤x) (hx1:x≤1) (hx:∀i j,tvMass (law i) (law j)≤x) (i j:Spin) :
    tvMass (composeLaw p law lam h i) (composeLaw p law lam h j) ≤
      d*|lam| *x-mass p K*(|lam| *x)^2 := by
  let t:ℝ:=|lam| *x
  have hl:|lam|≤1:=abs_le.mpr ⟨by linarith [h.1],h.2⟩
  have ht0:0≤t:=mul_nonneg (abs_nonneg _) hx0
  have ht1:t≤1 := calc
    t ≤ 1*x := mul_le_mul_of_nonneg_right hl hx0
    _ = x := one_mul x
    _ ≤ 1 := hx1
  have he:tvMass (edgeLaw law lam h i) (edgeLaw law lam h j)≤t := by
    rw [tvMass_edge]
    exact mul_le_mul_of_nonneg_left (hx i j) (abs_nonneg _)
  have hpoint (k:ℕ) : tvMass (iidVector (edgeLaw law lam h i) k) (iidVector (edgeLaw law lam h j) k)≤
      1-(1-t)^k := by
    apply (tvMass_iidVector_le _ _ k).trans
    have hp:=pow_le_pow_left₀ (by linarith : 0≤1-t) (by linarith : 1-t≤1-tvMass (edgeLaw law lam h i) (edgeLaw law lam h j)) k
    linarith
  have hs1:Summable (fun k:ℕ=>mass p k*((k:ℝ)*t)):=hD.mul_const t
  have hs2:Summable (fun k:ℕ=>if k=K then mass p K*t^2 else 0):=(hasSum_ite_eq K (mass p K*t^2)).summable
  have hu (k:ℕ) : mass p k*tvMass (iidVector (edgeLaw law lam h i) k) (iidVector (edgeLaw law lam h j) k)≤
      mass p k*((k:ℝ)*t)-(if k=K then mass p K*t^2 else 0) := by
    by_cases hk:k=K
    · subst k
      simp only [ite_true]
      have hb:=bernoulli_quadratic_lower t ht0 ht1 K hK
      have hv:=hpoint K
      have hh:=mul_le_mul_of_nonneg_left (show tvMass (iidVector (edgeLaw law lam h i) K) (iidVector (edgeLaw law lam h j) K)≤(K:ℝ)*t-t^2 by linarith) (mass_nonneg p K)
      nlinarith only [hh]
    · rw [ite_eq_right hk,sub_zero]
      have hb:=bernoulli_lower t ht0 ht1 k
      exact mul_le_mul_of_nonneg_left (by linarith [hpoint k]) (mass_nonneg p k)
  have hh:=Summable.tsum_le_tsum hu (summable_weighted_tv p
    (fun k=>iidVector (edgeLaw law lam h i) k) (fun k=>iidVector (edgeLaw law lam h j) k)) (hs1.sub hs2)
  have hsum: (∑'k:ℕ,mass p k*((k:ℝ)*t))=d*t := by
    change mean p (fun k:ℕ=>(k:ℝ)*t)=_
    rw [mean_mul_const,hmean]
  rw [hs1.tsum_sub hs2,hsum,tsum_ite_eq] at hh
  simpa only [composeLaw,tvMass_sigmaPMF,t,mul_assoc] using hh

lemma ordered_pairTV_decay (p:PMF ℕ) (d lam:ℝ) (h:Admissible lam)
    (hD:HasMean p (fun k:ℕ=>(k:ℝ))) (hmean:mean p (fun k:ℕ=>(k:ℝ))=d)
    (K:ℕ) (hK:2≤K) (hd:d*|lam|≤1) (n:ℕ) (i j:Spin) :
    tvMass (orderedLaw p lam h n i) (orderedLaw p lam h n j)≤decaySeq (mass p K*lam^2) n := by
  have hl:|lam|≤1:=abs_le.mpr ⟨by linarith [h.1],h.2⟩
  have hl2:lam^2≤1:=by nlinarith [sq_abs lam,abs_nonneg lam]
  have hc0:0 ≤ mass p K*lam^2:=mul_nonneg (mass_nonneg p K) (sq_nonneg lam)
  have hc1:mass p K*lam^2≤1 := calc
    mass p K*lam^2 ≤ 1*lam^2 := mul_le_mul_of_nonneg_right (mass_le_one p K) (sq_nonneg lam)
    _ = lam^2 := one_mul (lam^2)
    _ ≤ 1 := hl2
  induction n generalizing i j with
  | zero => exact tvMass_le_one _ _
  | succ n ih =>
    have hb:=decaySeq_bounds (mass p K*lam^2) hc0 hc1 n
    have hh:=compose_pairTV_bound p (orderedLaw p lam h n) d lam (decaySeq (mass p K*lam^2) n)
      h hD hmean K hK hb.1 hb.2 (fun i j=>ih i j) i j
    have hg:=mul_le_mul_of_nonneg_right hd hb.1
    change tvMass (composeLaw p (orderedLaw p lam h n) lam h i)
      (composeLaw p (orderedLaw p lam h n) lam h j)≤_
    change _≤decaySeq (mass p K*lam^2) n-(mass p K*lam^2)*(decaySeq (mass p K*lam^2) n)^2
    simp only [mul_pow,sq_abs] at hh
    nlinarith only [hh,hg]

 

theorem nonreconstruction_dobrushin (p:PMF ℕ) (d lam:ℝ) (h:Admissible lam)
    (hD:HasMean p (fun k:ℕ=>(k:ℝ))) (hmean:mean p (fun k:ℕ=>(k:ℝ))=d)
    (K:ℕ) (hK:2≤K) (hp:0 < mass p K) (hl:lam≠0) (hd:d*|lam|≤1) :
    Tendsto (fun n=>advantage (observedLaw p lam h n)) atTop (𝓝 0) := by
  have hal:|lam|≤1:=abs_le.mpr ⟨by linarith [h.1],h.2⟩
  have hl2:lam^2≤1:=by nlinarith [sq_abs lam,abs_nonneg lam]
  have hc:0 < mass p K*lam^2:=mul_pos hp (sq_pos_of_ne_zero hl)
  have hc1:mass p K*lam^2≤1 := calc
    mass p K*lam^2 ≤ 1*lam^2 := mul_le_mul_of_nonneg_right (mass_le_one p K) (sq_nonneg lam)
    _ = lam^2 := one_mul (lam^2)
    _ ≤ 1 := hl2
  apply squeeze_zero (fun n=>advantage_nonneg (observedLaw p lam h n)) _ (decaySeq_tendsto _ hc hc1)
  intro n
  exact (orderedAdvantage_dominates p lam h n).trans (advantage_le_pair_bound _ _
    (ordered_pairTV_decay p d lam h hD hmean K hK hd n))
end
end ThreeState

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical
noncomputable section

 
theorem regular_dobrushin_nonreconstruction (b:ℕ) (hb:2≤b) (lam:ℝ)
    (h:Admissible lam) (hd:(b:ℝ)*|lam|≤1) :
    Tendsto (regularAdvantage b lam h) atTop (𝓝 0) := by
  by_cases hl:lam=0
  · apply regular_small_negative_nonreconstruction b hb lam h (by simp [hl])
    simp [hl]
  · exact nonreconstruction_dobrushin (PMF.pure b) (b:ℝ) lam h
      (regular_moments b).hasMean (regular_moments b).first b hb
      (by simp [mass_pure]) hl hd

 

theorem poisson_dobrushin_nonreconstruction (d:ℝ) (hd:1<d) (lam:ℝ)
    (h:Admissible lam) (hD:d*|lam|≤1) :
    Tendsto (poissonAdvantage d hd lam h) atTop (𝓝 0) := by
  by_cases hl:lam=0
  · apply poisson_nonnegative_nonreconstruction d hd lam h (by simp [hl])
    simp [hl]
  · exact nonreconstruction_dobrushin (poissonOffspring d (by linarith)) d lam h
      (poisson_moments d (by linarith)).hasMean (poisson_moments d (by linarith)).first
      2 (by omega) (by rw [poisson_mass]; positivity) hl hD

 

theorem binary_negative_nonreconstruction (lam:ℝ) (h:Admissible lam) (hl:lam≤0) :
    Tendsto (regularAdvantage 2 lam h) atTop (𝓝 0) := by
  apply regular_dobrushin_nonreconstruction 2 (by omega) lam h
  rw [abs_of_nonpos hl]
  norm_num
  linarith [h.1]

 

theorem poisson_le_two_negative_nonreconstruction (d:ℝ) (hd:1<d) (hd2:d≤2)
    (lam:ℝ) (h:Admissible lam) (hl:lam≤0) :
    Tendsto (poissonAdvantage d hd lam h) atTop (𝓝 0) := by
  apply poisson_dobrushin_nonreconstruction d hd lam h
  have ha:|lam|≤1/2:=by rw [abs_of_nonpos hl];linarith [h.1]
  nlinarith [mul_nonneg (show 0≤d by linarith) (show 0≤1/2-|lam| by linarith)]
end
end ThreeState

end OAI
