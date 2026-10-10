import OAI.Combinatorics.HadwigerCounterexample.FinitePhaseAlternative
import OAI.Combinatorics.HadwigerCounterexample.ConstructionScales

namespace OAI

/-! # Phase Parameters -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators Topology
open Filter
variable {p : Shape} {n N : ℕ}

def mstep (r : ℕ) := 100*r+10
def Bstep (r : ℕ) := 2^(mstep r)*2
def denomStep (r : ℕ) := 10000*(r+1)^2*Bstep r
theorem Bstep_pos (r) : 0<Bstep r := by unfold Bstep; positivity
theorem denom_pos (r) : 0<denomStep r := by unfold denomStep Bstep; positivity

def stage (g r : ℕ) (D : ℝ) := 2*r*num (Comp g)+D+1
def pcoef (g r : ℕ) (D : ℝ) :=
  12*Bstep r+2*(denomStep r:ℝ)*stage g r D
def tinyPhase (g r : ℕ) (D : ℝ) := bp (-(pcoef g r D))
def warn := bp (-10)
def coin : ℝ := 0.0001
def heatloss (r k : ℕ) := 0.001 / (4*(r:ℝ)+k+1 : ℝ)

theorem row_le (p : Shape) (n : ℕ) : num (Row p n) ≤ num (Full p n) := by
  have h' : Fintype.card (Full p n)=Fintype.card (Row p n)+Fintype.card (Fin p.h) := by
    simp only [Full,Fintype.card_sum]
  unfold num; rw [h']; push_cast
  exact le_add_of_nonneg_right (Nat.cast_nonneg _)

theorem tinyPhase_pos (g r : ℕ) (D : ℝ) : 0< tinyPhase g r D := bp_pos _

theorem tinyPhase_le (g r : ℕ) {D : ℝ} (hD : 0 ≤ D) : tinyPhase g r D ≤1 := by
  have ht : 0 ≤ num (Comp g) := Nat.cast_nonneg _
  rw [tinyPhase,←bp_zero]
  apply bp_le; unfold pcoef stage; linarith [Nat.cast_nonneg (α:=ℝ) r,
    show 0≤ (denomStep r:ℝ)*(2*r*num (Comp g)+D+1) from mul_nonneg (Nat.cast_nonneg _) (by positivity)]

theorem heatloss_pos (r k : ℕ) : 0 < heatloss r k := by unfold heatloss; positivity

theorem bp_nat_vanish {c : ℝ} (hc : 0<c) :
    Tendsto (fun n : ℕ => bp (-c*n)) atTop (𝓝 0) :=
  (bp_tendsto_zero hc).comp tendsto_natCast_atTop_atTop

theorem eventually_grid {P : ℕ → Prop} (h : ∀ᶠ N : ℕ in atTop,P N) :
    ∀ᶠ M : ℕ in atTop, ∀ᶠ n : ℕ in atTop, P (M*n) := by
  obtain ⟨k,hk⟩ := eventually_atTop.mp h
  filter_upwards [eventually_ge_atTop 1] with M hM
  filter_upwards [eventually_ge_atTop k] with n hn
  exact hk _ (by nlinarith)

private theorem absorb_pow (p : Shape) {D : ℝ} (hD : 0≤D) (r b N : ℕ)
    (hN : N ≤2*denomStep r*b)
    (hp : 2*pcoef p.g r D ≤ p.h) :
    exponentErr p (mstep r) b (tinyPhase p.g r D)/warn^(2^(mstep r)*(2*b))
      ≤ 2*bp (-(stage p.g r D)*N) := by
  let Z := pcoef p.g r D
  let L := stage p.g r D
  let s := 2^(mstep r)*(2*b)
  have hl : 0 ≤ L := by unfold L stage num; positivity
  have hx : 12*(s:ℝ)+L*N ≤ Z*b := by
    have h : (N:ℝ) ≤ 2*(denomStep r:ℝ)*b := by exact_mod_cast hN
    have hs : (s:ℝ)=(Bstep r:ℝ)*b := by unfold s Bstep; push_cast; ring
    unfold Z pcoef; rw [hs]; change _ ≤ (12*_+2*_ * L)*_
    nlinarith only [mul_le_mul_of_nonneg_left h hl]
  have hz : L*N+10*(s:ℝ) ≤ (p.h:ℝ)*b/2 := by
    have hb : 2*Z*(b:ℝ) ≤ (p.h:ℝ)*b :=
      mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)
    linarith [(Nat.cast_nonneg s : 0≤(s:ℝ))]
  unfold exponentErr tinyPhase warn
  change (((2:ℝ)^s*2^s)*bp (-Z)^b+bp _)/bp (-10)^s≤_
  rw [←bp_nat s,←bp_mul_nat,←bp_mul_nat, ← bp_add,←bp_add,add_div,← bp_sub,← bp_sub,
    two_mul]
  refine add_le_add (bp_le ?_) (bp_le ?_)
  · change _ ≤ -L*N; linarith only [hx]
  change _ ≤ -L*N; linarith only [hz]

private theorem limit_pow (p : Shape) (r : ℕ) {D : ℝ} (hD : 0≤D)
    (hp : 2*pcoef p.g r D ≤ p.h) :
    ∀ᶠ N : ℕ in atTop,warn + noSweepBudget p N (mstep r) (N/denomStep r) r
      (tinyPhase p.g r D) warn (bp (D*N))<0.005 := by
  let C := chanPrice p
  have hw : warn < 0.005 := by
    unfold warn; rw [bp_neg, show (10:ℝ)=↑(10:ℕ) from by norm_num, bp_nat]; norm_num
  have hi : Tendsto (fun N : ℕ => warn+(2*C^2)*bp (-1*N)) atTop (𝓝 warn) := by
    have h := (bp_nat_vanish (by norm_num : 0<(1:ℝ))).const_mul (2*C^2)
    simpa only [neg_mul,mul_zero,add_zero] using h.const_add warn
  filter_upwards [hi.eventually (gt_mem_nhds hw),eventually_ge_atTop (denomStep r)]
    with N h hN
  let b := N / denomStep r
  have he : N≤2*denomStep r*b := by
    have h' : 1≤b := (Nat.le_div_iff_mul_le (denom_pos r)).mpr (by simpa using hN)
    have h2 : b*denomStep r + N%denomStep r=N := Nat.div_add_mod' ..
    have h3 : N%denomStep r < denomStep r := Nat.mod_lt _ (denom_pos r)
    nlinarith
  have hh : noSweepBudget p N (mstep r) b r (tinyPhase p.g r D) warn (bp (D*N))≤
      2*C^2*bp (-1*N) := by
    let A := bp (2*(r:ℝ)*num (Comp p.g)*N)
    unfold noSweepBudget
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (absorb_pow p hD r b N he hp)
      (mul_nonneg (bp_pos _).le (sq_nonneg _)
      )) (bp_pos _).le).trans_eq ?_
    change A * (bp _ * C^2 * _) = _
    have he : A * bp (D*N) * bp (-(stage p.g r D)*N)= bp (-1*N) := by
      unfold A stage; rw [←bp_add,←bp_add]; congr 1; ring
    rw [← he]; ring
  exact (add_le_add_right hh _).trans_lt h

theorem span_stage (b r N : ℕ) (hN : denomStep r*b ≤ N) :
    (↑(maxSpan (mstep r) b r):ℝ) ≤ 0.001*N ∧
    2*(↑(maxSpan (mstep r) b r):ℝ)*r ≤ 0.001*N := by
  have he : maxSpan (mstep r) b r = r*Bstep r*b := by unfold maxSpan Bstep; ring
  rw [he]
  have hb : (Bstep r:ℝ)≥0 := Nat.cast_nonneg _
  have hL : (denomStep r:ℝ)*(b:ℝ) ≤ N := by exact_mod_cast hN
  unfold denomStep at hL
  push_cast at hL ⊢
  have h0 : (0:ℝ)≤r := Nat.cast_nonneg _
  have h1 : 0 ≤ (Bstep r:ℝ)*(b:ℝ) := mul_nonneg hb (Nat.cast_nonneg _)
  constructor <;> nlinarith only [hL,h1,h0,mul_nonneg h0 h1, mul_nonneg (sq_nonneg (r:ℝ)) h1]

private theorem atlas_stage (p : Shape) (r : ℕ) :
    ∀ᶠ N : ℕ in atTop,∀ T : Cov p N,(∀ i,cdSign p T i≤maxSpan (mstep r) (N/denomStep r) r) →
      num (Atlas p r T)≤bp (0.002*N) := by
  let K := num (Wide p r)
  let L := bp (num (Comp p.g)*r*r)
  have he := bp_poly_dom_nat (by norm_num : 0<(0.001:ℝ)) (K*L) 0
  filter_upwards [he] with N h T hT
  apply (atlas_size T _).trans
  let W := maxSpan (mstep r) (N/denomStep r) r
  have hf : (cdim p T:ℝ) ≤2*W := by
    exact_mod_cast (show cdim p T≤ 2*W from (cdim_sign p T).trans_le
      ((add_le_add (hT _) (hT _)).trans_eq (two_mul W).symm))
  have h1 := mul_le_mul_of_nonneg_right hf (show 0≤(r:ℝ) from Nat.cast_nonneg _)
  have hL : (cdim p T:ℝ)*r≤0.001*N := h1.trans
    (span_stage _ r N (Nat.mul_div_le _ _)).2
  have h2 : K*L≤bp (0.001*N) := by simpa using h.le
  have h3 : 0≤K := Nat.cast_nonneg _
  rw [bp_add]
  change K * (_ * L) ≤ _
  rw [mul_comm _ L, ←mul_assoc]
  exact (mul_le_mul h2 (bp_le hL) (bp_pos _).le (bp_pos _).le).trans_eq (by
    rw [←bp_add]; congr 1; ring)

private theorem price_bound {p : Shape} {r n N k : ℕ} {L : ℝ}
    (x y : ℕ) (hx : x≤ 2*r) (hy : y≤ 2*r+k)
    (hf : (2*(r:ℝ))*num (Full p n)+2*p.h*(2*(r:ℝ)+k) ≤ 0.004*N)
    (hl : L ≤ bp (0.004*N)) :
    L*heatRate p n N (heatloss r k) x y≤loseA p N x y := by
  apply (mul_le_mul_of_nonneg_right hl
    (mul_nonneg (bp_pos _).le (bp_pos _).le)
    ).trans
  unfold loseA
  rw [←bp_add,←bp_add]
  refine bp_le ?_
  let ε := heatloss r k
  have he : ε*(4*r+k + (1:ℝ))=0.001 := by
    unfold ε heatloss; field_simp
  have hg : (x:ℝ)≤ 2*r := by exact_mod_cast hx
  have hh : (y:ℝ)≤ 2*r+k := by exact_mod_cast hy
  have ht : ε*(x+y:ℝ) ≤ 0.001 := he ▸ mul_le_mul_of_nonneg_left
    (show _≤_ by linarith) (heatloss_pos r k).le
  have hN := mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg N : 0≤(N:ℝ))
  have hi :
      num (Row p n)*x+2*p.h*(y:ℝ) ≤ 0.004*N := by
    have hu := mul_le_mul (row_le p n) hg
      (Nat.cast_nonneg x : 0≤(x:ℝ)) (Nat.cast_nonneg _ : 0≤num (Full p n))
    have hv := mul_le_mul_of_nonneg_left hh (show 0≤ 2*(p.h:ℝ) by positivity)
    linarith only [hf,hu,hv]
  push_cast
  unfold ε at hN
  linarith [(Nat.cast_nonneg N : 0≤(N:ℝ))]

private theorem early_spend (W : ℝ) :
    ∀ᶠ N : ℕ in atTop,W≤bp (0.004*N) := by
  filter_upwards [bp_poly_dom_nat (by norm_num : 0<(0.004:ℝ)) W 0] with N h
  simpa using h.le

private theorem glimpses_stage (g k r d : ℕ) (D L : ℝ) :
    ∀ᶠ h : ℕ in atTop,∀ p : Shape,p.g=g → p.h=h →
      glimpsesBill p k (rhUp L (tinyPhase g r D)) < coin^(k+1) ∧
      2*glimpsesBill p d (rhUp L (tinyPhase g r D))≤coin/2 := by
  let L' := rhUp L (tinyPhase g r D)
  let f (k h : ℕ) := (num (Comp g×Bool))*(L'*2*bp ((k:ℝ)-h))
  have ht k : Tendsto (f k) atTop (𝓝 0) := by
    let c : ℝ := num (Comp g×Bool)*L'*2*bp k
    have h : f k=fun h : ℕ => c*bp (-1*h) := by
      unfold f c; ext; simp [neg_mul,bp_sub,bp_neg]; ring
    rw [h]
    simpa using (bp_nat_vanish (by norm_num : 0<(1:ℝ))).const_mul c
  have hh : 0<coin := by norm_num [coin]
  filter_upwards [(ht k).eventually (gt_mem_nhds (pow_pos hh (k+1))),
    (ht d).eventually (gt_mem_nhds (show 0<coin/4 by linarith))] with h hA hB p hg hp
  subst g h
  change f k p.h<coin^(k+1) ∧ 2*f d p.h ≤ coin/2
  exact ⟨hA,by linarith only [show f d p.h<coin/4 from hB]⟩

set_option maxHeartbeats 1800000 in
theorem phase_calendar (g r k d : ℕ) (D L : ℝ) (hl : 0≤L) (hd : 0≤D)
    (hk : k ≤ d) (hK : D+1 ≤ 0.49*k) :
    ∀ᶠ h : ℕ in atTop,∀ p : Shape,p.g=g → p.h=h →
    ∀ᶠ M : ℕ in atTop,∀ᶠ n : ℕ in atTop,let N:=M*n;
      ∀ mix : Mixer p n, PhaseReady p n N (mstep r) (N/denomStep r) r k d mix
        (tinyPhase g r D) coin warn (heatloss r k) L (bp (D*N)) := by
  filter_upwards [glimpses_stage g k r d D L,tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (2*pcoef g r D))] with h hstage hH p hg hp
  subst g h
  let ε := heatloss r k
  let t := tinyPhase p.g r D
  let A := rhUp L t
  let B := rhUp A coin
  obtain ⟨hG,hY⟩ := hstage p rfl rfl
  have he :
      ∀ᶠ N : ℕ in atTop,glimpsesBill p k A+bp (-0.1*N)<coin^(k+1) ∧
        5*coin+bp (-0.24*N)<0.005 ∧
        (num (Place p)*2)*(L*2*bp (-0.4*N))≤t/2 := by
    have ht := tinyPhase_pos p.g r D
    let P (N : ℕ) := bp (-0.1*N); let Q (N : ℕ) := bp (-0.24*N)
    let z : ℝ := num (Place p)*2*(L*2)
    have hf1 : ∀ᶠ N in atTop,P N< coin^(k+1)-glimpsesBill p k A :=
      (bp_nat_vanish (by norm_num)).eventually (gt_mem_nhds (sub_pos.mpr hG))
    have hf2 : ∀ᶠ N in atTop,Q N<0.005-5*coin :=
      (bp_nat_vanish (by norm_num)).eventually (gt_mem_nhds (by norm_num [coin]))
    have hf3 : ∀ᶠ N : ℕ in atTop,z*bp (-0.4*N)<t/2 := by
      have hh : Tendsto (fun N : ℕ => z*bp (-0.4*N)) atTop (𝓝 0) := by
        simpa using (bp_nat_vanish (by norm_num : 0<(0.4:ℝ))).const_mul z
      exact hh.eventually (gt_mem_nhds (half_pos ht))
    filter_upwards [hf1,hf2,hf3] with i hi hj hk
    refine ⟨?_,?_,?_⟩
    · unfold P at hi; linarith
    · unfold Q at hj; linarith
    rw [←mul_assoc]
    exact hk.le
  have hε : 0 < ε := heatloss_pos r k
  filter_upwards [columns_budget p (δ:=0.004) (by norm_num)
    (2*(r:ℝ)) (2*p.h*(2*(r:ℝ)+k)) (by positivity) (by positivity),
    columns_budget p (δ:=1) zero_lt_one 2 1 (by norm_num) zero_le_one, raw_ready p hε,
    eventually_grid he,eventually_grid (limit_pow p r hd hH), eventually_grid (atlas_stage p r),
    eventually_grid (early_spend A),eventually_grid (early_spend B),
    eventually_grid (early_spend (t/2)⁻¹),eventually_grid (eventually_ge_atTop (denomStep r))
    ] with M hcols hfull hraw hδ hF hQ ha hb hu hN
  filter_upwards [eventually_ge_atTop 1,hraw,hδ,hF,hQ,ha,hb,hu,hN] with n hn hz hz' hA hZ
    hα hβ hr ht
  dsimp only
  intro mix
  let N := M*n
  have h1 := hcols n hn
  have h2 := hfull n hn
  change 2*num (Full p n)+1≤1*N at h2
  let b := N/denomStep r
  refine ⟨(Nat.le_div_iff_mul_le (denom_pos r)).mpr (by simpa using ht),by unfold mstep; omega,
    hk,tinyPhase_pos ..,tinyPhase_le _ _ hd,by norm_num [coin],by norm_num [coin],
    bp_pos _,hε,hl,(bp_pos _).le,by linarith only [h2],?_,hA,?_,hZ,?_,?_,?_,
      hz'.1,hY,hz'.2.1⟩
  · exact (hz.2 mix).2
  · refine le_trans ?_ hz'.2.2
    unfold scaleBill
    change (num (Place p)*2)*(L*2 * bp (_+(maxSpan (mstep r) b r : ℝ)-N))≤_
    have hi := bp_le (show num (Row p n)+(maxSpan (mstep r) b r:ℝ) - N ≤ -0.4*N by
      have he := (span_stage b r N (Nat.mul_div_le _ _)).1
      linarith only [row_le p n,h2,he,(Nat.cast_nonneg N : 0≤(N:ℝ))])
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi (by positivity))
      (by unfold num; positivity)
  · intro x y hx hy; exact price_bound x y hx (by omega) h1 hα
  · intro x y hx hy; exact price_bound x y hx (by omega) h1 hβ
  intro x hx
  let H := bp (D*N)
  have hh : rhUp H t * heatRate p n N ε x k≤ H * loseA p N x k := by
    unfold rhUp; rw [mul_comm _ H,mul_assoc]
    exact mul_le_mul_of_nonneg_left (price_bound x _ hx (by omega) h1 hr) (bp_pos _).le
  change bp _ * bp _ * _ ≤ _
  refine (mul_le_mul_of_nonneg_left hh
    (mul_nonneg (bp_pos _).le (bp_pos _).le)
    ).trans ?_
  unfold H loseA
  rw [← bp_add,← bp_add,← bp_add]
  apply bp_le
  change _ ≤ -0.2*(N:ℝ)
  have h3 := mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg N : 0≤(N:ℝ))
  linarith only [h3,(Nat.cast_nonneg N : 0≤(N:ℝ))]

end HadwigerCounterexample

end

end OAI
