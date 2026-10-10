import OAI.Dynamics.SmoothObstruction.ManifoldMatching

namespace OAI

section

open Filter Topology
open scoped Real

namespace SmoothObstruction.ScaleHierarchy

lemma lower_bound {b n p : ℝ} (hn : 1 ≤ n) (hp : 0 ≤ p)
    (hb : n ^ (-1 / 10 : ℝ) ≤ b) :
    n ^ (1 - p / 10) ≤ b ^ p * n := by
  have hnpos : 0 < n := by linarith
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hnpos.le _) hb hp
  rw [← Real.rpow_mul hnpos.le] at h
  calc
    n ^ (1-p/10) = n ^ ((-1/10:ℝ)*p+1) := by congr 1; ring
    _ = n ^ ((-1/10:ℝ)*p)*n := by rw [Real.rpow_add hnpos, Real.rpow_one]
    _ ≤ b^p*n := mul_le_mul_of_nonneg_right h hnpos.le

lemma square_dominates {b n p : ℝ} (hn : 1 ≤ n) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hb : n ^ (-1 / 10 : ℝ) ≤ b) : n ≤ (b ^ p * n)^2 := by
  have hnpos : 0 < n := by linarith
  calc
    n = n ^ (1:ℝ) := by simp
    _ ≤ n ^ ((1-p/10)*2) := Real.rpow_le_rpow_of_exponent_le hn (by linarith)
    _ = (n^(1-p/10))^2 := by rw [Real.rpow_mul hnpos.le, Real.rpow_two]
    _ ≤ (b^p*n)^2 := pow_le_pow_left₀ (Real.rpow_nonneg hnpos.le _)
      (lower_bound hn hp hb) 2

lemma ratio_tendsto_zero {ι : Type*} {l : Filter ι} {b : ι → ℝ} {p q : ℝ}
    (hqp : p < q) (hbpos : ∀ᶠ k in l, 0 < b k) (hb : Tendsto b l (𝓝 0)) :
    Tendsto (fun k => b k ^ q / b k ^ p) l (𝓝 0) := by
  have h := ((Real.continuous_rpow_const (show 0 ≤ q-p by linarith)).tendsto 0).comp hb
  simp only [Real.zero_rpow (show q-p ≠ 0 by linarith)] at h
  apply h.congr'
  filter_upwards [hbpos] with k hk
  exact Real.rpow_sub hk q p

/-- General separated-power budget. The floor and the original time scale are
unchanged; every fixed polynomial cost and exponential `b^q n` cost is absorbed. -/
theorem polynomial_decay {ι : Type*} {l : Filter ι} {b n : ι → ℝ}
    {p q c C : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hqp : p < q) (hc : 0 < c)
    (hbpos : ∀ᶠ k in l, 0 < b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop)
    (hfloor : ∀ᶠ k in l, n k ^ (-1 / 10 : ℝ) ≤ b k) (m : ℕ) :
    Tendsto (fun k => n k ^ m * Real.exp (C * b k ^ q * n k - c * b k ^ p * n k))
      l (𝓝 0) := by
  have hn1 : ∀ᶠ k in l, 1 ≤ n k := hn.eventually (eventually_ge_atTop 1)
  have hsmall : ∀ᶠ k in l, C*(b k^q/b k^p) ≤ c/2 := by
    apply Tendsto.eventually_le_const (show (0:ℝ)<c/2 by linarith)
    simpa using (ratio_tendsto_zero hqp hbpos hb).const_mul C
  have hP : Tendsto (fun k => b k^p*n k) l atTop := by
    apply tendsto_atTop_mono' l ?_
      ((tendsto_rpow_atTop (show (0:ℝ)<1-p/10 by linarith)).comp hn)
    filter_upwards [hn1,hfloor] with k hk hf
    exact lower_bound hk hp hf
  have hzero := ((isLittleO_pow_exp_pos_mul_atTop (2*m) (show (0:ℝ)<c/2 by linarith)).tendsto_div_nhds_zero).comp hP
  have hzero' : Tendsto (fun k => (b k^p*n k)^(2*m)*Real.exp (-(c/2)*(b k^p*n k))) l (𝓝 0) := by
    change Tendsto (fun k => (b k^p*n k)^(2*m) / Real.exp ((c/2)*(b k^p*n k))) l (𝓝 0) at hzero
    simpa only [div_eq_mul_inv, ← Real.exp_neg, neg_mul] using hzero
  apply squeeze_zero' _ _ hzero'
  · filter_upwards [hn1] with k hk
    exact mul_nonneg (pow_nonneg (by linarith) _) (Real.exp_pos _).le
  · filter_upwards [hn1,hfloor,hbpos,hsmall] with k hk hf hb hsmall
    have hbp := Real.rpow_pos_of_pos hb p
    have hCb : C*b k^q ≤ (c/2)*b k^p := by
      apply (div_le_iff₀ hbp).mp
      simpa only [mul_div_assoc] using hsmall
    have hexp : C*b k^q*n k-c*b k^p*n k ≤ -(c/2)*(b k^p*n k) := by
      have := mul_le_mul_of_nonneg_right hCb (show 0≤n k by linarith)
      nlinarith
    have hpow : n k^m ≤ (b k^p*n k)^(2*m) := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (by linarith) (square_dominates hk hp hp1 hf) m
    exact mul_le_mul hpow (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le
      (pow_nonneg (mul_nonneg hbp.le (by linarith)) _)
end SmoothObstruction.ScaleHierarchy

namespace SmoothObstruction.ShortBin
lemma bvp_nonneg (K a : ℝ) (n : ℕ) : 0≤bvpInverseBound K a n := by
  have hU : 0≤bvpGrowth K a n := by unfold bvpGrowth; positivity
  unfold bvpInverseBound
  positivity

lemma bvp_cost {K a : ℝ} (n : ℕ) (hK : 0≤K) (ha : 0≤a) :
    bvpInverseBound K a n ≤ 1000000*((n:ℝ)+1)*Real.exp (18*K+8*a*n) := by
  let U := bvpGrowth K a n
  let D := (2*U+U^4)*(n+n : ℕ)+U^2
  have hU : 1≤U := by dsimp [U,bvpGrowth]; linarith [Real.exp_pos (2*K+a*n)]
  have hU0 := le_trans (by norm_num : (0:ℝ)≤1) hU
  have he : 1≤Real.exp (2*K+a*n) := Real.one_le_exp_iff.mpr (by positivity)
  have hUe : U≤3*Real.exp (2*K+a*n) := by dsimp [U,bvpGrowth]; linarith
  have hU4 : U≤U^4 := by simpa using pow_le_pow_right₀ hU (show 1≤4 by omega)
  have hU24 : U^2≤U^4 := pow_le_pow_right₀ hU (by omega)
  have hU41 : 1≤U^4 := one_le_pow₀ hU
  have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
  have hD : D≤7*((n:ℝ)+1)*U^4 := by
    have hg := mul_le_mul_of_nonneg_right (show 2*U+U^4≤3*U^4 by linarith)
      (show (0:ℝ)≤(n+n:ℕ) by positivity)
    dsimp [D]
    push_cast at *
    nlinarith
  have hD0 : 0≤D := by dsimp [D]; positivity
  have hfactor : 1+2*D≤15*((n:ℝ)+1)*U^4 := by nlinarith
  have heK : 1≤Real.exp (2*K) := Real.one_le_exp_iff.mpr (by positivity)
  have hDe : D≤7*((n:ℝ)+1)*Real.exp (2*K)*U^8 := by
    calc
      D ≤ 7*((n:ℝ)+1)*U^4 := hD
      _ ≤ 7*((n:ℝ)+1)*Real.exp (2*K)*U^8 := by
        have hp : U^4≤U^8 := pow_le_pow_right₀ hU (by omega)
        have hp' : U^4≤Real.exp (2*K)*U^8 := le_trans hp (le_mul_of_one_le_left (by positivity) heK)
        nlinarith [mul_le_mul_of_nonneg_left hp' (show 0≤7*((n:ℝ)+1) by positivity)]
  have hQ : bvpInverseBound K a n≤127*((n:ℝ)+1)*Real.exp (2*K)*U^8 := by
    have h₁ : (U+U^4)*(4*Real.exp (2*K))≤(2*U^4)*(4*Real.exp (2*K)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h₂ := mul_le_mul h₁ hfactor (show 0≤1+2*D by positivity)
      (show 0≤(2*U^4)*(4*Real.exp (2*K)) by positivity)
    change (U+U^4)*(4*Real.exp (2*K))*(1+2*D)+D≤_
    nlinarith [h₂,hDe]
  have hp := pow_le_pow_left₀ hU0 hUe 8
  have hUE : U^8≤6561*Real.exp (16*K+8*a*n) := by
    calc
      U^8 ≤ (3*Real.exp (2*K+a*n))^8 := hp
      _ = 6561*Real.exp (16*K+8*a*n) := by
        rw [mul_pow,←Real.exp_nat_mul]
        norm_num
        ring
  calc
    bvpInverseBound K a n ≤ 127*((n:ℝ)+1)*Real.exp (2*K)*U^8 := hQ
    _ ≤ 127*((n:ℝ)+1)*Real.exp (2*K)*(6561*Real.exp (16*K+8*a*n)) :=
      mul_le_mul_of_nonneg_left hUE (by positivity)
    _ = 833247*((n:ℝ)+1)*Real.exp (18*K+8*a*n) := by
      calc
        _ = 833247*((n:ℝ)+1)*(Real.exp (2*K)*Real.exp (16*K+8*a*n)) := by ring
        _ = _ := by rw [←Real.exp_add]; congr 2; ring
    _ ≤ 1000000*((n:ℝ)+1)*Real.exp (18*K+8*a*n) := by gcongr; norm_num
end SmoothObstruction.ShortBin

namespace SmoothObstruction.ShortBin
open Filter Topology

/-- Explicit BVP cost is absorbed by the prescribed spatial exponent. -/
theorem bvp_decay {ι : Type*} {l : Filter ι} {b : ι → ℝ} {n : ι → ℕ}
    {K a : ι → ℝ} {p q c D : ℝ}
    (hp : 0≤p) (hp1 : p≤1) (hpq : p<q) (hc : 0<c)
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto (fun k => (n k:ℝ)) l atTop)
    (hfloor : ∀ᶠ k in l,(n k:ℝ)^(-1/10:ℝ)≤b k)
    (hK : ∀ᶠ k in l,0≤K k ∧ K k≤D*b k^q*n k)
    (ha : ∀ᶠ k in l,0≤a k ∧ a k≤D*b k^q) :
    Tendsto (fun k => bvpInverseBound (K k) (a k) (n k)*
      Real.exp (-c*b k^p*n k)) l (𝓝 0) := by
  have hz := (ScaleHierarchy.polynomial_decay (C:=26*D) hp hp1 hpq hc
    hbpos hb hn hfloor 1).const_mul 2000000
  simp only [pow_one,mul_zero] at hz
  have hn1 := hn.eventually (eventually_ge_atTop 1)
  apply squeeze_zero' (Filter.Eventually.of_forall fun k =>
    mul_nonneg (bvp_nonneg _ _ _) (Real.exp_pos _).le) _ hz
  filter_upwards [hK,ha,hn1] with k hK ha hn1
  have hexp : 18*K k+8*a k*n k≤26*D*b k^q*n k := by
    have hh := mul_le_mul_of_nonneg_right ha.2 (Nat.cast_nonneg (n k))
    nlinarith [hK.2]
  calc
    _ ≤ (1000000*((n k:ℝ)+1)*Real.exp (18*K k+8*a k*n k))*Real.exp (-c*b k^p*n k) :=
      mul_le_mul_of_nonneg_right (bvp_cost (n k) hK.1 ha.1) (Real.exp_pos _).le
    _ ≤ (1000000*(2*(n k:ℝ))*Real.exp (26*D*b k^q*n k))*Real.exp (-c*b k^p*n k) := by
      gcongr
      linarith
    _ = 2000000*((n k:ℝ)*Real.exp (26*D*b k^q*n k-c*b k^p*n k)) := by
      rw [sub_eq_add_neg,Real.exp_add]
      ring_nf

/-- Both nonlinear-contraction budgets hold at the original scales, with
no rescaling of `r`, `δ` or the horizon. -/
theorem bvp_spatial_budgets {ι : Type*} {l : Filter ι} {b : ι → ℝ} {n : ι → ℕ}
    {K a : ι → ℝ} {D C : ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto (fun k => (n k:ℝ)) l atTop)
    (hfloor : ∀ᶠ k in l,(n k:ℝ)^(-1/10:ℝ)≤b k)
    (hK : ∀ᶠ k in l,0≤K k ∧ K k≤D*b k^(1/2:ℝ)*n k)
    (ha : ∀ᶠ k in l,0≤a k ∧ a k≤D*b k^(1/2:ℝ)) :
    ∀ᶠ k in l,
      bvpInverseBound (K k) (a k) (n k)*C*Real.exp (-(3/2:ℝ)*b k^(1/8:ℝ)*n k)≤1/4 ∧
      bvpInverseBound (K k) (a k) (n k)*C*Real.exp (-2*b k^(1/8:ℝ)*n k)≤
        Real.exp (-(3/2:ℝ)*b k^(1/8:ℝ)*n k)/4 := by
  have hz₁ := (bvp_decay (p:=1/8) (q:=1/2) (c:=3/2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hbpos hb hn hfloor hK ha).mul_const C
  have hz₂ := (bvp_decay (p:=1/8) (q:=1/2) (c:=1/2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hbpos hb hn hfloor hK ha).mul_const C
  simp only [zero_mul] at hz₁ hz₂
  have h₁ := hz₁.eventually_le_const (by norm_num : (0:ℝ)<1/4)
  have h₂ := hz₂.eventually_le_const (by norm_num : (0:ℝ)<1/4)
  filter_upwards [h₁,h₂] with k h₁ h₂
  refine ⟨by nlinarith [h₁],?_⟩
  have h := mul_le_mul_of_nonneg_right h₂
    (Real.exp_pos (-(3/2:ℝ)*b k^(1/8:ℝ)*n k)).le
  have he : Real.exp (-(1/2:ℝ)*b k^(1/8:ℝ)*n k)*
      Real.exp (-(3/2:ℝ)*b k^(1/8:ℝ)*n k)=Real.exp (-2*b k^(1/8:ℝ)*n k) := by
    rw [←Real.exp_add]; congr 1; ring
  calc
    _ = (bvpInverseBound (K k) (a k) (n k)*Real.exp (-(1/2:ℝ)*b k^(1/8:ℝ)*n k)*C)*
      Real.exp (-(3/2:ℝ)*b k^(1/8:ℝ)*n k) := by rw [←he]; ring
    _ ≤ _ := by nlinarith [h]
end SmoothObstruction.ShortBin

end

section

namespace SmoothObstruction.ShortBin
open Filter Topology
/-- Polynomial powers of the actual BVP inverse cost remain absorbable. -/
theorem bvp_power_decay {ι : Type*} {l : Filter ι} {b : ι → ℝ} {n : ι → ℕ}
    {K a : ι → ℝ} {p q c D J : ℝ}
    (hp : 0≤p) (hp1 : p≤1) (hpq : p<q) (hc : 0<c)
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto (fun k => (n k:ℝ)) l atTop)
    (hfloor : ∀ᶠ k in l,(n k:ℝ)^(-1/10:ℝ)≤b k)
    (hK : ∀ᶠ k in l,0≤K k ∧ K k≤D*b k^q*n k)
    (ha : ∀ᶠ k in l,0≤a k ∧ a k≤D*b k^q) (m : ℕ) :
    Tendsto (fun k => (bvpInverseBound (K k) (a k) (n k))^m *
      Real.exp (J*b k^q*n k-c*b k^p*n k)) l (𝓝 0) := by
  let c' := c/((m:ℝ)+1)
  have hc' : 0<c' := div_pos hc (by positivity)
  have h₁ := (bvp_decay hp hp1 hpq hc' hbpos hb hn hfloor hK ha).pow m
  have h₂ := ScaleHierarchy.polynomial_decay (C:=J) hp hp1 hpq hc' hbpos hb hn hfloor 0
  simp only [pow_zero,one_mul] at h₂
  have h := h₁.mul h₂
  simp only [mul_zero] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro k
  dsimp only
  rw [mul_pow,←Real.exp_nat_mul,mul_assoc,←Real.exp_add]
  congr 2
  have he : c'*((m:ℝ)+1)=c := by dsimp only [c']; field_simp
  rw [←he]
  ring

/-- The sharp join radius and ideal-cell exchange error at the literal source
spatial scales. The error is measured after applying the inverse product basis. -/
theorem spatial_switch_limits {ι : Type*} {l : Filter ι} {b : ι → ℝ} {n : ι → ℕ}
    {ε : ι → ℝ} (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto (fun k => (n k:ℝ)) l atTop)
    (hfloor : ∀ᶠ k in l,(n k:ℝ)^(-1/10:ℝ)≤b k)
    (hε : ∀ᶠ k in l,0≤ε k ∧ ε k≤Real.exp (-b k^(3/4:ℝ)*n k))
    (Dg A C₀ : ℝ) (hDg : 0≤Dg) (hA : 0≤A) :
    let B (k : ι) := Dg*(b k*n k)
    let g (k : ι) := b k^(1/2:ℝ)
    let r (k : ι) := Real.exp (-2*b k^(1/8:ℝ)*n k)
    let δ (k : ι) := Real.exp (-(3/2:ℝ)*b k^(1/8:ℝ)*n k)
    let V (k : ι) := bvpInverseBound (B k) (A*g k) (n k)
    let ρ (k : ι) := 2*C₀*V k*r k
    let E (k : ι) := 4*Real.exp (2*B k)*(2*Real.exp (2*B k))*
      (ε k+2*Real.exp (2*B k)^2*Real.exp (-2*g k*n k))*(C₀*r k)+V k*C₀*(ρ k)^2
    Tendsto (fun k => ρ k/δ k) l (𝓝 0) ∧
      Tendsto (fun k => ρ k/Real.exp (-b k^(1/8:ℝ)*n k)) l (𝓝 0) ∧
      Tendsto ρ l (𝓝 0) ∧
      Tendsto (fun k => Real.sqrt 2*Real.exp (2*B k)*E k/r k) l (𝓝 0) := by
  intro B g r δ V ρ E
  let D := max Dg A
  have hD : 0≤D := hDg.trans (le_max_left _ _)
  have hK : ∀ᶠ k in l,0≤B k ∧ B k≤D*b k^(1/2:ℝ)*n k := by
    filter_upwards [hbpos,hb.eventually_le_const (by norm_num : (0:ℝ)<1)] with k hk hk1
    have hr : b k≤b k^(1/2:ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hk hk1 (by norm_num : (1/2:ℝ)≤1)
    refine ⟨mul_nonneg hDg (mul_nonneg hk.le (Nat.cast_nonneg _)),?_⟩
    dsimp only [B]
    calc
      Dg*(b k*n k) = Dg*b k*n k := by ring
      _ ≤ D*b k^(1/2:ℝ)*n k := by gcongr; exact le_max_left _ _
  have ha : ∀ᶠ k in l,0≤A*g k ∧ A*g k≤D*b k^(1/2:ℝ) := by
    filter_upwards [hbpos] with k hk
    exact ⟨mul_nonneg hA (Real.rpow_nonneg hk.le _),
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hk.le _)⟩
  have hdec (c : ℝ) (hc : 0<c) := bvp_decay (p:=1/8) (q:=1/2) (c:=c)
    (by norm_num) (by norm_num) (by norm_num) hc hbpos hb hn hfloor hK ha
  have hρδ := (hdec (1/2) (by norm_num)).const_mul (2*C₀)
  have hρh := (hdec 1 (by norm_num)).const_mul (2*C₀)
  have hρ0 := (hdec 2 (by norm_num)).const_mul (2*C₀)
  simp only [mul_zero] at hρδ hρh hρ0
  have hfirst : Tendsto (fun k => Real.exp (6*B k)*ε k) l (𝓝 0) := by
    have hh := ScaleHierarchy.polynomial_decay (p:=3/4) (q:=1) (c:=1) (C:=6*Dg)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbpos hb hn hfloor 0
    simp only [pow_zero,one_mul,Real.rpow_one] at hh
    apply squeeze_zero' _ _ hh
    · filter_upwards [hε] with k hk; exact mul_nonneg (Real.exp_pos _).le hk.1
    · filter_upwards [hε] with k hk
      calc
        _ ≤ Real.exp (6*B k)*Real.exp (-b k^(3/4:ℝ)*n k) := mul_le_mul_of_nonneg_left hk.2 (Real.exp_pos _).le
        _ = _ := by rw [←Real.exp_add]; congr 1; dsimp [B]; ring
  have hsecond := ScaleHierarchy.polynomial_decay (p:=1/2) (q:=1) (c:=2) (C:=10*Dg)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbpos hb hn hfloor 0
  simp only [pow_zero,one_mul,Real.rpow_one] at hsecond
  have hthird : Tendsto (fun k => V k^3*Real.exp (2*B k-2*b k^(1/8:ℝ)*n k)) l (𝓝 0) := by
    have hh := bvp_power_decay (p:=1/8) (q:=1/2) (c:=2) (J:=2*Dg)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbpos hb hn hfloor hK ha 3
    apply squeeze_zero' (Filter.Eventually.of_forall fun k => mul_nonneg (pow_nonneg (bvp_nonneg _ _ _) _) (Real.exp_pos _).le) _ hh
    filter_upwards [hbpos,hb.eventually_le_const (by norm_num : (0:ℝ)<1)] with k hk hk1
    have hr : b k≤b k^(1/2:ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hk hk1 (by norm_num : (1/2:ℝ)≤1)
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (pow_nonneg (bvp_nonneg _ _ _) _)
    dsimp only [B]
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hDg) (Nat.cast_nonneg (n k))
    nlinarith
  refine ⟨?_,?_,?_,?_⟩
  · apply hρδ.congr'; apply Filter.Eventually.of_forall; intro k
    have he : Real.exp (-(1/2:ℝ)*b k^(1/8:ℝ)*n k)=
        Real.exp (-2*b k^(1/8:ℝ)*n k)/Real.exp (-(3/2:ℝ)*b k^(1/8:ℝ)*n k) := by
      rw [←Real.exp_sub]; congr 1; ring
    dsimp only [ρ,δ,r,V]
    rw [he]
    ring
  · apply hρh.congr'; apply Filter.Eventually.of_forall; intro k
    have he : Real.exp (-1*b k^(1/8:ℝ)*n k)=
        Real.exp (-2*b k^(1/8:ℝ)*n k)/Real.exp (-b k^(1/8:ℝ)*n k) := by
      rw [←Real.exp_sub]; congr 1; ring
    dsimp only [ρ,r,V]
    rw [he]
    ring
  · simpa only [ρ,r,V,mul_assoc] using hρ0
  · have hh := ((hfirst.const_mul (8*Real.sqrt 2*C₀)).add
      (hsecond.const_mul (16*Real.sqrt 2*C₀))).add (hthird.const_mul (4*Real.sqrt 2*C₀^3))
    simp only [mul_zero,add_zero] at hh
    apply hh.congr'; apply Filter.Eventually.of_forall; intro k
    have he (m : ℕ) : Real.exp ((m:ℝ)*(2*B k))=Real.exp (2*B k)^m := Real.exp_nat_mul _ _
    have he6 : Real.exp (6*B k)=Real.exp (2*B k)^3 := by convert he 3 using 1; ring_nf
    have he10 : Real.exp (10*Dg*b k*n k)=Real.exp (2*B k)^5 := by
      convert he 5 using 1; dsimp only [B]; ring_nf
    dsimp only [E,ρ,r,g]
    rw [Real.exp_sub,he6,he10, Real.exp_sub]
    simp only [neg_mul,Real.exp_neg]
    field_simp
    ring
end SmoothObstruction.ShortBin

namespace SmoothObstruction.ShortBin
open Filter Topology
/-- Scalar hypotheses of the genuine switch, at the unchanged source scales.
Both grid widths are fixed multiples of the original h0 and r. -/
theorem spatial_ready {ι : Type*} {l : Filter ι} {b : ι → ℝ} {n : ι → ℕ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto (fun k => (n k:ℝ)) l atTop)
    (hfloor : ∀ᶠ k in l,(n k:ℝ)^(-1/10:ℝ)≤b k)
    (Dg A C₀ C₁ Cg K₀F K₀B r₀ rg σ r₁ rμ Ac Ap : ℝ)
    (hDg : 0≤Dg) (hA : 0≤A) (hC₀ : 1≤C₀)
    (hr₀ : 0<r₀) (hrg : 0<rg) (hσ : 0<σ) (hr₁ : 0<r₁) (hrμ : 0<rμ)
    (hAc : 0<Ac) (hAp : 0<Ap) :
    let B (k : ι) := Dg*(b k*n k)
    let g (k : ι) := b k^(1/2:ℝ)
    let ε (k : ι) := Real.exp (-b k^(3/4:ℝ)*n k)
    let h₀ (k : ι) := Real.exp (-b k^(1/8:ℝ)*n k)
    let r (k : ι) := Real.exp (-2*b k^(1/8:ℝ)*n k)
    let δ (k : ι) := Real.exp (-(3/2:ℝ)*b k^(1/8:ℝ)*n k)
    let V (k : ι) := bvpInverseBound (B k) (A*g k) (n k)
    let ρ (k : ι) := 2*C₀*V k*r k
    let E (k : ι) := 4*Real.exp (2*B k)*(2*Real.exp (2*B k))*
      (ε k+2*Real.exp (2*B k)^2*Real.exp (-2*g k*n k))*(C₀*r k)+V k*C₀*(ρ k)^2
    ∀ᶠ k in l,1≤b k*n k ∧ ε k≤1/2 ∧ Real.exp (2*B k)*(2*ε k)≤1/2 ∧
      (2*Real.exp (2*B k))*(2*(2*Real.exp (2*B k)^2*Real.exp (-2*g k*n k)))≤1/2 ∧
      δ k≤r₀ ∧ δ k≤rg ∧ ρ k≤δ k ∧ ρ k≤σ ∧ ρ k≤(h₀ k/Ac)/4 ∧ ρ k≤r₁ ∧
      C₁*ρ k≤δ k ∧ Cg*ρ k<δ k ∧ K₀F*δ k≤1 ∧ K₀B*δ k≤1 ∧
      Real.sqrt 2*Real.exp (2*B k)*E k≤(r k/Ap)/4 ∧
      V k*C₀*δ k≤1/4 ∧ V k*C₀*r k≤δ k/4 ∧ r k<rμ ∧ δ k≤h₀ k := by
  intro B g ε h₀ r δ V ρ E
  have hεenv : ∀ᶠ k in l,0≤ε k ∧ ε k≤Real.exp (-b k^(3/4:ℝ)*n k) :=
    Filter.Eventually.of_forall fun k => ⟨(Real.exp_pos _).le,le_rfl⟩
  obtain ⟨hρδ,hρh,hρ,hE⟩ := spatial_switch_limits hbpos hb hn hfloor hεenv Dg A C₀ hDg hA
  have hdec (p c : ℝ) (hp : 0≤p) (hp1 : p≤1) (hpq : p<1) (hc : 0<c) :
      Tendsto (fun k => Real.exp (-c*b k^p*n k)) l (𝓝 0) := by
    have hh := ScaleHierarchy.polynomial_decay (q:=1) (C:=0) hp hp1 hpq hc hbpos hb hn hfloor 0
    simpa only [pow_zero,one_mul,zero_mul,zero_sub,neg_mul] using hh
  have hδ0 : Tendsto δ l (𝓝 0) := hdec (1/8) (3/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hr0 : Tendsto r l (𝓝 0) := hdec (1/8) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hε0 : Tendsto ε l (𝓝 0) := by
    simpa only [neg_one_mul] using hdec (3/4) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hsmall : Tendsto (fun k => Real.exp (2*B k)*(2*ε k)) l (𝓝 0) := by
    have hh := ScaleHierarchy.polynomial_decay (p:=3/4) (q:=1) (c:=1) (C:=2*Dg)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbpos hb hn hfloor 0
    simp only [pow_zero,one_mul,Real.rpow_one] at hh
    have ht := hh.const_mul 2
    simp only [mul_zero] at ht
    apply ht.congr'; apply Filter.Eventually.of_forall; intro k
    dsimp only [B,ε]
    rw [mul_left_comm,←Real.exp_add]
    congr 2; ring
  have hgap : Tendsto (fun k => (2*Real.exp (2*B k))*(2*(2*Real.exp (2*B k)^2*Real.exp (-2*g k*n k)))) l (𝓝 0) := by
    have hh := ScaleHierarchy.polynomial_decay (p:=1/2) (q:=1) (c:=2) (C:=6*Dg)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbpos hb hn hfloor 0
    simp only [pow_zero,one_mul,Real.rpow_one] at hh
    have ht := hh.const_mul 8
    simp only [mul_zero] at ht
    apply ht.congr'; apply Filter.Eventually.of_forall; intro k
    have he : Real.exp (2*B k)*Real.exp (2*B k)^2*Real.exp (-2*g k*n k)=
        Real.exp (6*Dg*b k*n k-2*b k^(1/2:ℝ)*n k) := by
      rw [←Real.exp_nat_mul,←Real.exp_add,←Real.exp_add]
      congr 1; dsimp only [B,g]; ring
    dsimp only
    rw [show (2*Real.exp (2*B k))*(2*(2*Real.exp (2*B k)^2*Real.exp (-2*g k*n k)))=
      8*(Real.exp (2*B k)*Real.exp (2*B k)^2*Real.exp (-2*g k*n k)) by ring,he]
  have hCρδ : Tendsto (fun k => C₁*(ρ k/δ k)) l (𝓝 0) := by simpa only [mul_zero] using hρδ.const_mul C₁
  have hCgρδ : Tendsto (fun k => Cg*(ρ k/δ k)) l (𝓝 0) := by simpa only [mul_zero] using hρδ.const_mul Cg
  have hKFδ : Tendsto (fun k => K₀F*δ k) l (𝓝 0) := by simpa only [mul_zero] using hδ0.const_mul K₀F
  have hKBδ : Tendsto (fun k => K₀B*δ k) l (𝓝 0) := by simpa only [mul_zero] using hδ0.const_mul K₀B
  filter_upwards [hbpos,hfloor,hn.eventually (eventually_ge_atTop (1:ℝ)),
    hε0.eventually_le_const (by norm_num : (0:ℝ)<1/2),
    hsmall.eventually_le_const (by norm_num : (0:ℝ)<1/2),
    hgap.eventually_le_const (by norm_num : (0:ℝ)<1/2),
    hδ0.eventually_le_const hr₀,hδ0.eventually_le_const hrg,
    hρδ.eventually_le_const (by norm_num : (0:ℝ)<1/2),hρ.eventually_le_const hσ,
    hρh.eventually_le_const (by positivity : (0:ℝ)<1/(4*Ac)),hρ.eventually_le_const hr₁,
    hCρδ.eventually_le_const (by norm_num : (0:ℝ)<1),hCgρδ.eventually_lt_const (by norm_num : (0:ℝ)<1),
    hKFδ.eventually_le_const (by norm_num : (0:ℝ)<1),hKBδ.eventually_le_const (by norm_num : (0:ℝ)<1),
    hE.eventually_le_const (by positivity : (0:ℝ)<1/(4*Ap)),hr0.eventually_lt_const hrμ]
    with k hbpos hf hn1 heps hsmall hgap hδr hδrg hρδ hρσ hρh hρr hCρ hCgρ hKF hKB hE hrμ
  have hδpos : 0<δ k := Real.exp_pos _
  have hrpos : 0<r k := Real.exp_pos _
  have hhpos : 0<h₀ k := Real.exp_pos _
  have hBn : 0≤b k^(1/8:ℝ)*n k := by positivity
  have hδsq : δ k*δ k≤r k := by
    dsimp only [δ,r]; rw [←Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith only [hBn]
  have hρhalf : ρ k≤δ k/2 := by
    have hh := (div_le_iff₀ hδpos).mp hρδ
    linarith
  have hVC₀ : 0≤V k*C₀ := mul_nonneg (bvp_nonneg _ _ _) (by linarith)
  have hdata : V k*C₀*r k≤δ k/4 := by dsimp only [ρ] at hρhalf; nlinarith only [hρhalf]
  have hcontract : V k*C₀*δ k≤1/4 := by
    have hh := mul_le_mul_of_nonneg_left hδsq hVC₀
    have hmul : (V k*C₀*δ k)*δ k≤(1/4:ℝ)*δ k := by nlinarith only [hh,hdata]
    exact (mul_le_mul_iff_left₀ hδpos).mp (by simpa only [mul_comm] using hmul)
  have hbn : 1≤b k*n k := by
    have hs := ScaleHierarchy.lower_bound (p:=1) hn1 (by norm_num) hf
    have hp := Real.one_le_rpow hn1 (by norm_num : (0:ℝ)≤1-(1:ℝ)/10)
    simpa only [Real.rpow_one] using hp.trans hs
  refine ⟨hbn,heps,hsmall,hgap,hδr,hδrg,by linarith,hρσ,?_,hρr,?_,?_,hKF,hKB,?_,hcontract,hdata,hrμ,?_⟩
  · have hh := (div_le_iff₀ hhpos).mp hρh
    calc
      _ ≤ (1/(4*Ac))*h₀ k := hh
      _ = (h₀ k/Ac)/4 := by ring
  · rw [←mul_div_assoc] at hCρ
    exact (div_le_iff₀ hδpos).mp hCρ |>.trans_eq (one_mul _)
  · rw [←mul_div_assoc] at hCgρ
    exact (div_lt_iff₀ hδpos).mp hCgρ |>.trans_eq (one_mul _)
  · have hh := (div_le_iff₀ hrpos).mp hE
    calc
      _ ≤ (1/(4*Ap))*r k := hh
      _ = (r k/Ap)/4 := by ring
  · dsimp only [δ,h₀]; apply Real.exp_le_exp.mpr; nlinarith only [hBn]
end SmoothObstruction.ShortBin

end

end OAI
