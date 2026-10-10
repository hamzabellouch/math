import Mathlib
import OAI.Probability.Ballisticity.Estimates.CellRadiusComparison
import OAI.Probability.Ballisticity.Estimates.StageParameters

namespace OAI

section

open Filter
open scoped Topology
namespace DirectionalTransience

lemma eventually_stage_scale_ratios (j g D : ℝ) (hj : 0 < j) (hg : 0 < g) (hD : 0 < D) :
    ∀ᶠ b : ℝ in atTop, 0 < b ∧
      Real.exp (-(2+Real.log 16*j)*b) ≤ 1/4 ∧
      16*(16:ℝ)^⌊j*b⌋₊*Real.exp (-(2+Real.log 16*j)*b) ≤ D*Real.exp (-b) ∧
      16*(16:ℝ)^⌊j*b⌋₊*Real.exp (g*b) ≤ D*Real.exp ((g+1+Real.log 16*j)*b) ∧
      16*(16:ℝ)^⌊j*b⌋₊*Real.exp (((g+1+Real.log 16*j)+1)*b)+2 ≤ Real.exp (((g+1+Real.log 16*j)+2+Real.log 16*j)*b) := by
  let f := 2+Real.log 16*j
  let χ := g+1+Real.log 16*j
  let E := χ+1+Real.log 16*j
  have hf : 0 < f := by dsimp [f]; positivity
  have hE : 0 < E+1 := by dsimp [E,χ]; positivity
  filter_upwards [eventually_ge_atTop (1:ℝ), eventually_ge_atTop (Real.log 4/f),
    eventually_ge_atTop (-Real.log (D/16)),
    eventually_exp_affine_le (Real.log 16) (-E) (-(E+1)) (by linarith),
    eventually_mul_exp_le 2 0 (-(E+1)) (by linarith)] with b hb hsmall hDsmall hc₁ hc₂
  have hb0 : 0 < b := by linarith
  have hp := radix_floor_bound j b (mul_nonneg hj.le hb0.le)
  have hDb : 16*Real.exp (-b) ≤ D := by
    have hh : Real.exp (-b) ≤ D/16 := by
      rw [← Real.exp_log (by positivity : 0 < D/16)]
      exact Real.exp_le_exp.mpr (by linarith only [hDsmall])
    linarith only [hh]
  refine ⟨hb0,?_,?_,?_,?_⟩
  · have hh := (div_le_iff₀ hf).mp hsmall
    have he : Real.exp (-(2+Real.log 16*j)*b) ≤ Real.exp (-Real.log 4) :=
      Real.exp_le_exp.mpr (by dsimp [f] at hh; nlinarith only [hh])
    simpa only [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ) < 4),one_div] using he
  · calc
      _ ≤ 16*Real.exp (Real.log 16*j*b)*Real.exp (-(2+Real.log 16*j)*b) := by gcongr
      _ = (16*Real.exp (-b))*Real.exp (-b) := by
        simp only [mul_assoc,← Real.exp_add]; congr 2; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hDb (Real.exp_pos _).le
  · calc
      _ ≤ 16*Real.exp (Real.log 16*j*b)*Real.exp (g*b) := by gcongr
      _ = (16*Real.exp (-b))*Real.exp ((g+1+Real.log 16*j)*b) := by
        simp only [mul_assoc,← Real.exp_add]; congr 2; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hDb (Real.exp_pos _).le
  · have h₁ : 16*(16:ℝ)^⌊j*b⌋₊*Real.exp ((χ+1)*b) ≤ Real.exp ((E+1)*b)/2 := by
      calc
        _ ≤ 16*Real.exp (Real.log 16*j*b)*Real.exp ((χ+1)*b) := by gcongr
        _ = Real.exp (Real.log 16-(-E)*b) := by
          rw [show Real.log 16-(-E)*b=Real.log 16+(Real.log 16*j*b+(χ+1)*b) by dsimp [E]; ring,
            Real.exp_add,Real.exp_log (by norm_num : (0:ℝ) < 16),Real.exp_add]; ring
        _ ≤ _ := by convert hc₁ using 1; congr 2; ring
    have h₂ : (2:ℝ) ≤ Real.exp ((E+1)*b)/2 := by simpa using hc₂
    have hh : 16*(16:ℝ)^⌊j*b⌋₊*Real.exp ((χ+1)*b)+2 ≤ Real.exp ((E+1)*b) := by linarith only [h₁,h₂]
    convert hh using 1; dsimp [E,χ]; congr 2; ring

lemma width_target_of_exp_ratio (s D P x y w : ℝ) (hs : 0 ≤ s) (hP : 0 < P)
    (hD : 0 ≤ D) (hw : s*y/P ≤ w) (hr : P*x ≤ D*y) : s*x ≤ D*w := by
  have hh := mul_le_mul_of_nonneg_left hw hD
  have hh' := mul_le_mul_of_nonneg_left hr hs
  apply le_trans _ hh
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hP).mpr
  nlinarith only [hh']

end DirectionalTransience

end

section

open Filter MeasureTheory
open scoped Topology
namespace DirectionalTransience

lemma eventually_inverse_stage_tools {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hI : Integrable S μ) (hne : 0 < μ {x | S x ≠ 0})
    (L : ℕ) (hL : 1 ≤ L) (N T ρ σ : ℝ) (hρ : 0 < ρ) (hρquarter : ρ ≤ 1/4) (hσ : 0 < σ) :
    ∀ᶠ s : ℝ in atTop, 0 < s ∧ 0 < fluctuationRadius μ S s ∧ N ≤ fluctuationRadius μ S s ∧
      T ≤ s*ρ ∧ T ≤ s*σ ∧ fluctuationRadius μ S (s*ρ) ≤ fluctuationRadius μ S s/2 ∧
      s/(16*(L:ℝ)^2) ≤ fluctuationScale μ S (fluctuationRadius μ S s/(4*L)) := by
  obtain ⟨R,hR,hcomp⟩ := fluctuationRadius_scaling_compare μ S hS hI hne
  have hLp : (0:ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  filter_upwards [eventually_gt_atTop (0:ℝ),
    (fluctuationRadius_tendsto μ S hS hI hne).eventually (eventually_ge_atTop N),
    eventually_gt_atTop (fluctuationScale μ S R),
    eventually_gt_atTop ((max T (fluctuationScale μ S R+1))/ρ),
    eventually_ge_atTop (T/σ)] with s hs hN hsR hρT hσT
  obtain ⟨hr,heq⟩ := fluctuationRadius_spec μ S hS hI hne hR hsR
  have hρB : max T (fluctuationScale μ S R+1) < s*ρ := (div_lt_iff₀ hρ).mp hρT
  have ht : fluctuationScale μ S R < s*ρ := by linarith [le_max_right T (fluctuationScale μ S R+1)]
  have hrad := hcomp s (s*ρ) (1/2) ht (by nlinarith only [mul_le_mul_of_nonneg_left hρquarter hs.le]) (by norm_num) (by norm_num)
  refine ⟨hs,hR.trans hr,hN,(le_max_left _ _).trans hρB.le,(div_le_iff₀ hσ).mp hσT,?_,?_⟩
  · simpa only [div_eq_mul_inv,mul_comm,one_mul] using hrad
  · have hc : 0 < (1:ℝ)/(4*L) := by positivity
    have hc1 : (1:ℝ)/(4*L) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < (4:ℝ)*L)).mpr
      have hh : (1:ℝ) ≤ L := by exact_mod_cast hL
      linarith
    have hh := fluctuationScale_scaling μ S hS hne (hR.trans hr) hc hc1
    rw [heq] at hh
    convert hh using 1 <;> ring_nf

lemma short_stage_scale_ratio (s b : ℝ) (L H : ℕ) (n : ℝ)
    (hs : 0 < s) (hL : 0 < L) (hH : (H:ℝ) ≤ s*Real.exp (-b))
    (hn : s/(16*(L:ℝ)^2) ≤ n) : (H:ℝ)/n ≤ 16*(L:ℝ)^2*Real.exp (-b) := by
  have hLp : (0:ℝ) < L := by exact_mod_cast hL
  have hn0 : 0 < n := (div_pos hs (by positivity)).trans_le hn
  apply (div_le_iff₀ hn0).mpr
  have hh := mul_le_mul_of_nonneg_left hn (show 0 ≤ 16*(L:ℝ)^2*Real.exp (-b) by positivity)
  have heq : (16*(L:ℝ)^2*Real.exp (-b))*(s/(16*(L:ℝ)^2)) = s*Real.exp (-b) := by field_simp
  rw [heq] at hh
  exact hH.trans hh

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators Classical
namespace DirectionalTransience

theorem separated_stages_with_gap {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (D₀ : ℝ) (hD₀ : 0 ≤ D₀) :
    ∃ fexp g χ K : ℝ, 0 < fexp ∧ 0 < g ∧ g < χ ∧ 0 < K ∧
      1/g < (1/2:ℝ)/64 ∧ (1+fexp/g)*D₀/K < (1/2:ℝ)/64 ∧
      ∃ k : ℕ, 2 ≤ k ∧ ∀ᶠ b : ℝ in atTop, 0 < b ∧ ∃ sfloor : ℝ, 0 < sfloor ∧
        ∀ s : ℝ, sfloor ≤ s → ∀ a : ℝ,
        let μ := independentConditionedPairLaw ν (realPosition (step e))
        let S := commonIncrementProcess (realPosition (step e)) f 0
        ∀ π : BudgetProfile (k:=k) e f a (fluctuationRadius μ S s),
          environmentLaw ν (stageBadEvent e f ⌊s*Real.exp (χ*b)⌋₊
            (fluctuationRadius μ S (s*Real.exp (-fexp*b)))
            (fluctuationRadius μ S (s*Real.exp (g*b))) π.val
              (ENNReal.ofReal (Real.exp (-(k:ℝ)*b)))) ≤ ENNReal.ofReal (Real.exp (-2*K*b)) := by
  obtain ⟨κ,lam,Cr,lamq,Cq,A,hκ,hrows,hlam,hlam1,hCr,hlamq,hlamq1,hCq,hA,hstage⟩ :=
    actual_finite_stage_estimate ν hue e f hef htrans
  let j : ℝ := 1/(8*A)
  let fexp := 2+Real.log 16*j
  have hA0 : 0 < A := by linarith
  have hj : 0 < j := by dsimp [j]; positivity
  have hfexp : 0 < fexp := by dsimp [fexp]; positivity
  obtain ⟨g,K,hg,hK,hgsmall,hKsmall,k,L,hk,hL,hkr,hkq,hkc,hLk⟩ :=
    stage_parameter_hierarchy A lam lamq D₀ hA hlam hlamq hD₀
  let χ := g+1+Real.log 16*j
  let D := χ+2+Real.log 16*j
  have hχ : 0 < χ := by dsimp [χ]; positivity
  have hgχ : g < χ := by
    dsimp [χ]
    have hh : 0 ≤ Real.log 16*j := by positivity
    linarith
  obtain ⟨C,c,g₀,g₁,hC,hc,hc1,hg₀,hg₁,tseed,htseed,hcb⟩ := hstage k hk
  obtain ⟨T,hT,hTbound⟩ := cell_radius_comparison ν hue e f hef htrans C c hC hc hc1
  let μ := independentConditionedPairLaw ν (realPosition (step e))
  let S := commonIncrementProcess (realPosition (step e)) f 0
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν _
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν _ htrans))
  have hS : Measurable S := measurable_commonIncrementProcess _ _ _
  have hI : Integrable S μ := independent_commonWordIncrement_integrable ν hue _
    (signed_direction_unit e) htrans (signedHeight e) (signedHeight_projection e)
    (signedHeight_step_le e) f
  have hne : 0 < μ {x | S x ≠ 0} := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  have hL0 : 0 < L := by omega
  have hk0 : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hnumeric := eventually_stage_probability_sum lam lamq Cr Cq j D K k L hk hL0 hCr.le
    (by nlinarith only [hkr,mul_pos hlam hk0]) (by linarith only [hLk])
    (by linarith only [hkq]) (by exact lt_trans (by linarith) hkc)
  refine ⟨fexp,g,χ,K,hfexp,hg,hgχ,hK,hgsmall,hKsmall,k,hk,?_⟩
  filter_upwards [hnumeric,stage_budget_parameters A g₀ g₁ κ K k L hA hg₀ hg₁ hk,
    eventually_stage_scale_ratios j g (c^2/(4*C)) hj hg (by positivity)] with b hnum hbgeom hscales
  obtain ⟨hb,hell,hmb,hcoef⟩ := hbgeom
  obtain ⟨_,hquarter,hminus,hplus,hcountExp⟩ := hscales
  have hBstar : 0 < 2*(k:ℝ)*b := by positivity
  obtain ⟨W,N,hW,hbound⟩ := hcb (2*k*b) hBstar
  let m := ⌊j*b⌋₊
  have hm : j*b-1 ≤ (m:ℝ) := by have hh := Nat.lt_floor_add_one (j*b); dsimp [m]; linarith only [hh]
  have hevent : ∀ᶠ s : ℝ in atTop, 0 < s ∧ ∀ a : ℝ,
      ∀ π : BudgetProfile (k:=k) e f a (fluctuationRadius μ S s),
        environmentLaw ν (stageBadEvent e f ⌊s*Real.exp (χ*b)⌋₊
          (fluctuationRadius μ S (s*Real.exp (-fexp*b)))
          (fluctuationRadius μ S (s*Real.exp (g*b))) π.val
            (ENNReal.ofReal (Real.exp (-(k:ℝ)*b)))) ≤ ENNReal.ofReal (Real.exp (-2*K*b)) := by
    filter_upwards [eventually_finest_width (Real.exp (-b)) (Real.exp_pos _) m W,
      eventually_finest_width (Real.exp (χ*b)) (Real.exp_pos _) m W,
      eventually_inverse_stage_tools μ S hS hI hne L hL N T
        (Real.exp (-fexp*b)) (Real.exp (g*b)) (Real.exp_pos _) hquarter (Real.exp_pos _)]
      with s hearly hgrowth hinverse
    obtain ⟨hs,hwidth,hlow⟩ := hearly
    obtain ⟨_,hwidthp,hlowp⟩ := hgrowth
    obtain ⟨_,hrpos,hrN,htminus,htplus,hrhalf,hnscale⟩ := hinverse
    refine ⟨hs,fun a π => ?_⟩
    let He := ⌊s*Real.exp (-b)⌋₊
    let H := ⌊s*Real.exp (χ*b)⌋₊
    let w := finestCellWidth He m
    let wp := finestCellWidth H m
    let n := ((H-He)/w+1)+1
    let v := stageCellStarts He H w
    let ws := stageCellWidths He H w wp
    let Gminus := fluctuationRadius μ S (s*Real.exp (-fexp*b))
    let Gplus := fluctuationRadius μ S (s*Real.exp (g*b))
    let gs := stageCellGaps He H w Gminus Gplus
    obtain ⟨hws,hv,hcover,hgrowth⟩ := stage_cells_geometry He H m W hwidth hwidthp hW Gminus Gplus
    have hgm : ∀ i, i < m → Gminus ≤ c*cellRadius ν e f C w m i/2 := by
      intro i hi
      apply hTbound w m i _ htminus
      exact width_target_of_exp_ratio s _ _ _ _ _ hs.le (by positivity) (by positivity) hlow hminus
    have hgp : ∀ i, i < m → Gplus ≤ c*cellRadius ν e f C wp m i/2 := by
      intro i hi
      apply hTbound wp m i _ htplus
      exact width_target_of_exp_ratio s _ _ _ _ _ hs.le (by positivity) (by positivity) hlowp hplus
    have hgs := stage_cells_gap_bounds ν e f C c Gminus Gplus He H m hgm hgp
    have hqe : Real.exp (-(2*(k:ℝ)*b)) ≤ Real.exp (-(k:ℝ)*b/4) :=
      Real.exp_le_exp.mpr (by nlinarith only [mul_pos hk0 hb])
    have hcoefENN : ENNReal.ofReal (Real.exp (-(k:ℝ)*b)) ≤
        ENNReal.ofReal (Real.exp (-(k:ℝ)*b/4))*(ENNReal.ofReal g₀*ENNReal.ofReal g₁*
          ENNReal.ofReal (Real.exp (-A*k*m))) := by
      have hh := ENNReal.ofReal_le_ofReal hcoef
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le,ENNReal.ofReal_mul (mul_pos hg₀ hg₁).le,
        ENNReal.ofReal_mul hg₀.le] at hh
      exact hh
    have hp := hbound n L He H m a (fluctuationRadius μ S s) (k*b)
      (Real.exp (-(k:ℝ)*b/4)) Gminus Gplus v ws gs hL hrpos hrN
      (mul_pos hk0 hb) (by nlinarith only [mul_pos hk0 hb]) hell hqe hmb
      hws hv hgs hcover hgrowth hrhalf (by simpa only [neg_mul] using hcoefENN) π
    change environmentLaw ν (stageBadEvent e f H Gminus Gplus π.val
      (ENNReal.ofReal (Real.exp (-(k:ℝ)*b)))) ≤ _
    have hn : (n:ℝ) ≤ Real.exp (D*b) :=
      (stage_cell_count_bound b χ s m hs hlow).trans hcountExp
    have hsum := hnum m hm n (Nat.cast_nonneg _) hn
    have hH : (He:ℝ) ≤ s*Real.exp (-b) := Nat.floor_le (by positivity)
    have hrat := short_stage_scale_ratio s b L He _ hs hL0 hH hnscale
    have hshort : (Real.exp (Cr*k-lam*(k*b/2)/L)+Cr*k*Real.exp ((k*b/2)/L)*He /
        fluctuationScale μ S (fluctuationRadius μ S s/(4*L)))^L ≤
        (Real.exp (Cr*k-lam*(k*b/2)/L)+(16*Cr*k*L^2)*Real.exp ((k*b/2)/L-b))^L := by
      have hnnonneg := fluctuationScale_nonneg μ S (fluctuationRadius μ S s/(4*L))
      apply pow_le_pow_left₀ (by positivity) _ L
      apply add_le_add le_rfl
      calc
        _ = (Cr*k*Real.exp ((k*b/2)/L))*((He:ℝ)/fluctuationScale μ S (fluctuationRadius μ S s/(4*L))) := by ring
        _ ≤ (Cr*k*Real.exp ((k*b/2)/L))*(16*(L:ℝ)^2*Real.exp (-b)) :=
          mul_le_mul_of_nonneg_left hrat (by positivity)
        _ = _ := by rw [Real.exp_sub]; rw [Real.exp_neg]; ring
    have hsumENN := ENNReal.ofReal_le_ofReal hsum
    rw [ENNReal.ofReal_add (by positivity : 0 ≤
      (Real.exp (Cr*k-lam*(k*b/2)/L)+(16*Cr*k*L^2)*Real.exp ((k*b/2)/L-b))^L +
        Real.exp (Cq*k)*(Real.exp (-(k:ℝ)*b/4))^lamq) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by positivity : 0 ≤ (n:ℝ)*2^(m-1)),
      ENNReal.ofReal_mul (Nat.cast_nonneg n),ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)] at hsumENN
    simp only [ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat] at hsumENN
    have hp' := hp.trans (add_le_add (add_le_add (ENNReal.ofReal_le_ofReal hshort) le_rfl) le_rfl)
    simp only [mul_assoc,neg_mul] at hp' hsumENN ⊢
    exact hp'.trans hsumENN
  obtain ⟨s₀,hs₀⟩ := eventually_atTop.mp hevent
  refine ⟨hb,max s₀ 1,lt_of_lt_of_le (by norm_num) (le_max_right _ _),fun s hs a => ?_⟩
  exact (hs₀ s ((le_max_left _ _).trans hs)).2 a

theorem separated_stages {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (D₀ : ℝ) (hD₀ : 0 ≤ D₀) :
    ∃ fexp g χ K : ℝ, 0 < fexp ∧ 0 < g ∧ 0 < χ ∧ 0 < K ∧
      1/g < (1/2:ℝ)/64 ∧ (1+fexp/g)*D₀/K < (1/2:ℝ)/64 ∧
      ∃ k : ℕ, 2 ≤ k ∧ ∀ᶠ b : ℝ in atTop, 0 < b ∧ ∃ sfloor : ℝ, 0 < sfloor ∧
        ∀ s : ℝ, sfloor ≤ s → ∀ a : ℝ,
        let μ := independentConditionedPairLaw ν (realPosition (step e))
        let S := commonIncrementProcess (realPosition (step e)) f 0
        ∀ π : BudgetProfile (k:=k) e f a (fluctuationRadius μ S s),
          environmentLaw ν (stageBadEvent e f ⌊s*Real.exp (χ*b)⌋₊
            (fluctuationRadius μ S (s*Real.exp (-fexp*b)))
            (fluctuationRadius μ S (s*Real.exp (g*b))) π.val
              (ENNReal.ofReal (Real.exp (-(k:ℝ)*b)))) ≤ ENNReal.ofReal (Real.exp (-2*K*b)) := by
  obtain ⟨fexp,g,χ,K,hf,hg,hχ,hK,hgs,hKs,k,hk,hb⟩ :=
    separated_stages_with_gap ν hue e f hef htrans D₀ hD₀
  exact ⟨fexp,g,χ,K,hf,hg,hg.trans hχ,hK,hgs,hKs,k,hk,hb⟩

end DirectionalTransience

end

end OAI
