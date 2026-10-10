import OAI.Geometry.TranslativeCovering.TailComparison

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace SourcePatternTail
open Set Metric Filter MeasureTheory SphericalLaw SourceParameters
open scoped Topology ENNReal Classical
lemma bin_count {A C : ℝ} (hA : 0 < A) (hC : 0 ≤ C) {n : ℕ}
    (hn : 1 ≤ n) (hCn : C ≤ (n:ℝ)^2) :
    (ActivityBins.count (A*C):ℝ) ≤ (A/Real.log 2+1)*(n:ℝ)^2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfloor := Nat.floor_le (div_nonneg (mul_nonneg hA.le hC) hl.le)
  have hn2 : 1 ≤ (n:ℝ)^2 := one_le_pow₀ (by exact_mod_cast hn)
  dsimp [ActivityBins.count]
  push_cast
  calc
    _ ≤ A*C/Real.log 2+1 := by linarith only [hfloor]
    _ ≤ A*(n:ℝ)^2/Real.log 2+1 := by gcongr
    _ = A/Real.log 2*(n:ℝ)^2+1 := by ring
    _ ≤ A/Real.log 2*(n:ℝ)^2+(n:ℝ)^2 := by linarith only [hn2]
    _ = _ := by ring

lemma threshold_limit : ∀ᶠ n : ℕ in atTop,
    0 < RadialShell.low a n ∧
      1/Real.sqrt (1+4*ε) ≤ (1+3*RadialShell.η n)/RadialShell.high a n := by
  have hs : a < Real.sqrt (1+4*ε) := by
    apply (Real.lt_sqrt a_pos.le).mpr
    norm_num [a,ε]
  have ht : 1/Real.sqrt (1+4*ε) < 1/a := one_div_lt_one_div_of_lt a_pos hs
  have hl : Tendsto (fun n => (1+3*RadialShell.η n)/RadialShell.high a n) atTop (𝓝 (1/a)) := by
    convert ((tendsto_const_nhds (x := (1:ℝ))).add (RadialShell.eta_limit.const_mul 3)).div
      (RadialShell.high_limit a) a_pos.ne' using 1
    first | rfl | simp only [mul_zero,add_zero]
  filter_upwards [(RadialShell.low_limit a).eventually (lt_mem_nhds a_pos),hl.eventually_const_le ht] with n hn hh
  exact ⟨hn,hh⟩

theorem uniform : ∃ c : ℝ,0 < c ∧ ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n →
    ∀ [NeZero n] [Fact (2 ≤ n)] (J : Type u_1) [Fintype J] [Nonempty J]
      (e : Sphere n) (p : J → Space n) (R : ℝ),
    0 ≤ R → R ≤ c*(n:ℝ)*Real.log n → R ≤ (n:ℝ)^2 →
    Fintype.card J ≤ N n R →
    volume (closedBall (0 : Space n) D) ≤ 4*volume
      (PatternGeometry.roundedGood p a D (RadialShell.low a n) (RadialShell.high a n) (2*Cloc*R)) →
    (BodyVolume.law e a).real (PatternTail.coverEvent p a D) ≤
      Real.exp (-Real.exp ((1/2:ℝ)*(n:ℝ))) := by
  have ha := a_pos
  let l := 1/(2*a)
  let u₀ := (1/a+1)/2
  let u := (u₀+1)/2
  have hia : 1/a < 1 := (div_lt_one a_pos).mpr a_one
  have hia0 : 0 < 1/a := one_div_pos.mpr a_pos
  have hl : 0 < l := by dsimp [l]; positivity
  have hlt : l < 1/a := by dsimp [l]; exact one_div_lt_one_div_of_lt a_pos (by linarith [a_pos])
  have hu0 : 1/a < u₀ := by dsimp [u₀]; linarith only [hia]
  have hu : u₀ < u := by dsimp [u,u₀]; linarith only [hia]
  have hu1 : u < 1 := by dsimp [u,u₀]; linarith only [hia]
  obtain ⟨K,A,H,hK,hA,hH,n₁,hbound⟩ := PatternTail.bound a_one hl hlt hu0 hu hu1
  let c : ℝ := 1/(256*A*Cloc)
  have hCloc : 0 < Cloc := by norm_num [Cloc,v]
  have hc : 0 < c := by dsimp [c]; positivity
  let B := A/Real.log 2+1
  have hB : 0 < B := by dsimp [B]; have := Real.log_pos (by norm_num : (1:ℝ)<2); positivity
  have hdim : ∀ᶠ n : ℕ in atTop,∀ R : ℝ,0 ≤ R → R ≤ c*(n:ℝ)*Real.log n → 2*Cloc*R ≤ (n:ℝ)^2 := by
    filter_upwards [RadialShell.log_div_limit.eventually_le_const (show 0<1/(2*Cloc*c) by positivity),
      eventually_ge_atTop 1] with n hn hn1 R hR hRb
    have hnp : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
    have hh := (div_le_iff₀ hnp).mp hn
    have h1 := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*Cloc*c*(n:ℝ) by positivity)
    have he : (2*Cloc*c*(n:ℝ))*(1/(2*Cloc*c)*(n:ℝ)) = (n:ℝ)^2 := by field_simp
    rw [he] at h1
    calc
      2*Cloc*R ≤ 2*Cloc*(c*(n:ℝ)*Real.log n) := by gcongr
      _ ≤ _ := by linarith only [h1]
  have hnum := NumericTail.denominator hB
  have hfine := NumericTail.fine_small hH
  have hev : ∀ᶠ n : ℕ in atTop,n₁≤n ∧ 16≤n ∧ 1≤Real.log n ∧
      (∀ R : ℝ,0≤R → R≤c*(n:ℝ)*Real.log n → 2*Cloc*R≤(n:ℝ)^2) ∧
      (∀ R : ℝ,0≤R → R≤(n:ℝ)^2 → (N n R:ℝ)≤Real.exp ((1/100:ℝ)*(n:ℝ))) ∧
      (0<RadialShell.low a n ∧ 1/Real.sqrt (1+4*ε)≤(1+3*RadialShell.η n)/RadialShell.high a n) ∧
      (∀ S : ℝ,0 ≤ S → S ≤ Real.exp ((1/100:ℝ)*(n:ℝ)) →
        (M n:ℝ)^2*(12*((n:ℝ)+1)*S^2*(RadialShell.high a n*(H*Real.sqrt (Real.log n/(n:ℝ)))/D)^(n-1))<1/2) ∧
      (∀ S Q F : ℝ,0≤S → S≤Real.exp ((1/100:ℝ)*(n:ℝ)) → 0≤Q → Q≤B*(n:ℝ)^2 → F≤(n:ℝ)*Real.log n/64 →
        8*(Q*Real.exp F/(M n:ℝ)+10*(n:ℝ)⁻¹^3*Q^2*(12*((n:ℝ)+1)*S^2*(RadialShell.high a n*(4*Real.sqrt ε)/D)^(n-1)))≤Real.exp (-(1/2:ℝ)*(n:ℝ))) := by
    filter_upwards [eventually_ge_atTop n₁,eventually_ge_atTop 16,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1),
      hdim,SourceParameters.length_rate,threshold_limit,hfine,hnum] with n h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hev
  refine ⟨c,hc,n₀,?_⟩
  intro n hn _ _ J _ _ e p R hR hRc hRn hcard hlarge
  obtain ⟨hn₁,hn16,hlog,hCn,hNs,hth,hfine,hden⟩ := hn₀ n hn
  let C := 2*Cloc*R
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hn1 : 1 ≤ n := by omega
  have hCdim : C ≤ (n:ℝ)^2 := hCn R hR hRc
  have hS : (Fintype.card J:ℝ) ≤ Real.exp ((1/100:ℝ)*(n:ℝ)) :=
    (by exact_mod_cast hcard : (Fintype.card J:ℝ)≤(N n R:ℝ)).trans (hNs R hR hRn)
  have hM : 2 ≤ M n := by
    have hnreal : (16:ℝ) ≤ n := by exact_mod_cast hn16
    have he : 1 ≤ (n:ℝ)*Real.log n/16 := by nlinarith only [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) n),hnreal]
    have hm := (Real.exp_one_gt_two.le.trans (Real.exp_le_exp.mpr he)).trans (NumericTail.target_count hn1).1
    exact_mod_cast hm
  have hpc : ((TargetSampling.pairs (M n)).card:ℝ) ≤ (M n:ℝ)^2 := by
    have hh := Finset.card_filter_le (Finset.univ : Finset (Fin (M n)×Fin (M n))) (fun p => p.1 ≠ p.2)
    simpa only [TargetSampling.pairs,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,pow_two] using (Nat.cast_le (α := ℝ)).mpr hh
  have hε : 0 < ε := by norm_num [ε]
  have hhigh : 0 ≤ RadialShell.high a n := by unfold RadialShell.high RadialShell.η; have := a_pos; positivity
  have hsmall := (mul_le_mul_of_nonneg_right hpc (by have := D_pos; positivity)).trans_lt (hfine (Fintype.card J) (Nat.cast_nonneg _) hS)
  have hb := hbound n hn₁ J e p D C ε (M n) D_pos hC hCdim hε (by norm_num [ε]) hM hth.1 hth.2 hlarge hsmall
  have hF : 2*A*C ≤ (n:ℝ)*Real.log n/64 := by
    have hh := mul_le_mul_of_nonneg_left hRc (show 0≤4*A*Cloc by positivity)
    have he : 4*A*Cloc*(c*(n:ℝ)*Real.log n) = (n:ℝ)*Real.log n/64 := by dsimp [c]; field_simp; ring
    rw [he] at hh
    dsimp [C]
    linarith only [hh]
  have hq0 : 0 < (ActivityBins.count (A*C):ℝ) := by dsimp [ActivityBins.count]; positivity
  have hd := hden (Fintype.card J) (ActivityBins.count (A*C)) (2*A*C) (Nat.cast_nonneg _) hS hq0.le (bin_count hA hC hn1 hCdim) hF
  apply hb.trans
  apply Real.exp_le_exp.mpr
  have hMp : 0 < (M n:ℝ) := by exact_mod_cast (by omega : 0<M n)
  have hd0 : 0 < 8*((ActivityBins.count (A*C):ℝ)*Real.exp (2*A*C)/(M n:ℝ)+10*(n:ℝ)⁻¹^3*(ActivityBins.count (A*C):ℝ)^2*(12*((n:ℝ)+1)*(Fintype.card J:ℝ)^2*(RadialShell.high a n*(4*Real.sqrt ε)/D)^(n-1))) := by have := D_pos; positivity
  have hh := neg_le_neg (one_div_le_one_div_of_le hd0 hd)
  have he : Real.exp (-(1/2:ℝ)*(n:ℝ)) = (Real.exp ((1/2:ℝ)*(n:ℝ)))⁻¹ := by rw [show -(1/2:ℝ)*(n:ℝ) = -((1/2:ℝ)*(n:ℝ)) by ring,Real.exp_neg]
  rw [he] at hh
  simpa only [neg_div,one_div,inv_inv] using hh
end SourcePatternTail

end OAI
