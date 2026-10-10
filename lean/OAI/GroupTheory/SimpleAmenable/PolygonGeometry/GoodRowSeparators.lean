import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FinePatchAtlas
import OAI.GroupTheory.SimpleAmenable.RandomFields.UniformThresholdCDF
import OAI.GroupTheory.SimpleAmenable.Arithmetic.UniformLatticeRiemann
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.DirectionStripCounts

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section GoodRowSeparators
open Classical MeasureTheory ProbabilityTheory

theorem flagSeparates_near_row {a : ℕ} {v : ℝ×ℝ} {j : Fin 4} {c : CutRing}
    {z w : SquareFlag a v} (h : FlagSeparates j c z w) :
    |cutForm a j z.val-ordinary c| ≤ (1+|ordinary (cutTau^a)|)*dist z.val w.val := by
  have hc := flagSeparates_ordinary_bound h
  have hb := abs_le.mp (cutForm_dist_bound a j z.val w.val)
  rcases le_total (cutForm a j z.val) (cutForm a j w.val) with hh|hh
  · rw [min_eq_left hh,max_eq_right hh] at hc
    exact abs_le.mpr ⟨by linarith [hc.1,hc.2],by linarith [hc.1,hc.2]⟩
  · rw [min_eq_right hh,max_eq_left hh] at hc
    exact abs_le.mpr ⟨by linarith [hc.1,hc.2],by linarith [hc.1,hc.2]⟩

theorem directionNoCutProbability_eq_one {a : ℕ} {v : ℝ×ℝ} {s κ : ℝ}
    (hs : 0 < s) (hκ : 0 < κ) (j : Fin 4) (z w : SquareFlag a v)
    (h : ∀c, |conjugate c| ≤ 2*κ/s → ¬ FlagSeparates j c z w) :
    directionNoCutProbability s κ j z w=1 := by
  have hi : κ/s < 2*κ/s := (div_lt_div_iff_of_pos_right hs).mpr (by linarith)
  have hinter : Set.Icc (κ/s) (2*κ/s) ∩ directionNoCut j z w = Set.Icc (κ/s) (2*κ/s) := by
    apply Set.inter_eq_left.mpr
    intro t ht c hc
    exact h c (hc.trans ht.2)
  have he : cond volume (Set.Icc (κ/s) (2*κ/s)) (directionNoCut j z w)=1 := by
    calc
      _ = cond volume (Set.Icc (κ/s) (2*κ/s)) (Set.Icc (κ/s) (2*κ/s)) := by
        rw [cond_apply measurableSet_Icc,cond_apply measurableSet_Icc,hinter,Set.inter_self]
      _ = 1 := cond_apply_self
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hi))
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  exact congrArg ENNReal.toReal he

theorem separatorMatrix_eq_one_on_good_row {a : ℕ} {v : ℝ×ℝ} {s κ : ℝ}
    (hs : 0 < s) (hκ : 0 < κ) (z w : SquareFlag a v) (hw : dist z.val w.val ≤ s)
    (hz : ∀j c, |conjugate c| ≤ 2*κ/s →
      (1+|ordinary (cutTau^a)|)*s < |cutForm a j z.val-ordinary c|) :
    separatorMatrix (thresholdLaw s κ) z w=1 := by
  rw [separatorMatrix_product hs hκ]
  suffices ∀j,directionNoCutProbability s κ j z w=1 by simp [this]
  intro j
  apply directionNoCutProbability_eq_one hs hκ
  intro c hc hsep
  have hb := (flagSeparates_near_row hsep).trans
    (mul_le_mul_of_nonneg_left hw (by positivity))
  exact (not_le_of_gt (hz j c hc)) hb

theorem squareFlag_cutForm_bound {a : ℕ} {v : ℝ×ℝ} (j : Fin 4) (z : SquareFlag a v) :
    |cutForm a j z.val| ≤ 1+|ordinary (cutTau^a)| := by
  have hn : ‖z.val‖ ≤ (1:ℝ) := by
    rw [Prod.norm_def]
    apply max_le
    · rw [Real.norm_eq_abs,abs_of_nonneg z.property.2.1.1]
      exact z.property.2.1.2
    · rw [Real.norm_eq_abs,abs_of_nonneg z.property.2.2.1.1]
      exact z.property.2.2.1.2
  have hz : cutForm a j 0=0 := by fin_cases j <;> simp [cutForm]
  have hh := cutForm_dist_bound a j z.val 0
  rw [hz,sub_zero,dist_zero_right] at hh
  exact hh.trans (by nlinarith [abs_nonneg (ordinary (cutTau^a))])

def flagBadSeparatorRow {a m D : ℕ} {v : ℝ×ℝ} (s κ R : ℝ) : Set (FlagSite a m D v) :=
  {z | z∈flagSiteBox R ∧ ∃j c, |conjugate c| ≤ 2*κ/s ∧
    |cutForm a j z.val.2.val-ordinary c| ≤ (1+|ordinary (cutTau^a)|)*s}

theorem flagBadSeparatorRow_card_bound {a m D : ℕ} {v : ℝ×ℝ} (hD : 0 < D)
    {Q κ s N : ℝ} (hQ : 0 < Q) (hκ : 0 < κ) (hs : 0 < s)
    (hs₁ : s ≤ 1) (hN : 1 ≤ N) (hscale : 1 ≤ s*N)
    (S : Finset (FlagSite a m D v)) (hS : ∀z∈S,z∈flagBadSeparatorRow s κ (Q*N)) :
    (S.card:ℝ) ≤ 4*(m*(4*(D:ℝ)^2*(1+|conjugate (cutTau^a)|)*(1+|ordinary (cutTau^a)|)*Q+2)*
      (2*(D:ℝ)^2*Q+2)*(16*(1+|ordinary (cutTau^a)|)+2))*(κ+s)*N^2 := by
  let L : ℝ := 1+|ordinary (cutTau^a)|
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let row := fun j : Fin 4 => S.filter (fun z => ∃c : CutRing, |conjugate c| ≤ 2*κ/s ∧
    |cutForm a j z.val.2.val-ordinary c| ≤ L*s)
  have hh : S ⊆ Finset.univ.biUnion row := by
    intro z hz
    obtain ⟨j,c,hc,hd⟩ := (hS z hz).2
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hz,c,hc,hd⟩⟩
  have hc j := exceptional_direction_rows hD j (show 0 ≤ 2*L by positivity) hL hQ hκ hs hN hscale
    (row j) (by
      intro z hz
      obtain ⟨hzS,c,hc,hd⟩ := Finset.mem_filter.mp hz
      refine ⟨c,?_,hc,(hS z hzS).1,hd⟩
      have hb := squareFlag_cutForm_bound j z.val.2
      have htri := abs_sub_le (ordinary c) (cutForm a j z.val.2.val) 0
      rw [sub_zero,sub_zero,abs_sub_comm (ordinary c)] at htri
      change |cutForm a j z.val.2.val| ≤ L at hb
      exact htri.trans (by nlinarith))
  have hn : S.card ≤ ∑j : Fin 4,(row j).card :=
    (Finset.card_le_card hh).trans Finset.card_biUnion_le
  have hn' : (S.card:ℝ) ≤ ∑j : Fin 4,((row j).card:ℝ) := by exact_mod_cast hn
  refine hn'.trans ((Finset.sum_le_sum (fun j _ => hc j)).trans_eq ?_)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  dsimp [L]
  ring

end GoodRowSeparators

section NormalizedTentMass
open Classical MeasureTheory

noncomputable def unitTent (x : ℝ) : ℝ := max (1-|x|) 0

theorem unitTent_bounds (x : ℝ) : 0 ≤ unitTent x ∧ unitTent x ≤ 1 := by
  constructor
  · exact le_max_right _ _
  · exact max_le (by linarith [abs_nonneg x]) zero_le_one

theorem unitTent_lipschitz : LipschitzWith 1 unitTent := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,NNReal.coe_one,one_mul]
  calc
    _ ≤ |(1-|x|)-(1-|y|)| := abs_max_sub_max_le_abs _ _ 0
    _ = abs (abs x - abs y) := by rw [show (1-|x|)-(1-|y|)=-(abs x - abs y) by ring,abs_neg]
    _ ≤ |x-y| := abs_abs_sub_abs_le_abs_sub x y

theorem unitTent_zero {x : ℝ} (hx : 1 ≤ |x|) : unitTent x=0 :=
  max_eq_right (by linarith)

theorem unitTent_compact : HasCompactSupport unitTent := by
  apply HasCompactSupport.intro (isCompact_Icc (a:=(-1:ℝ)) (b:=1))
  intro x hx
  by_contra hn
  have hh : |x| < 1 := lt_of_not_ge (fun h => hn (unitTent_zero h))
  exact hx ⟨(abs_lt.mp hh).1.le,(abs_lt.mp hh).2.le⟩

theorem unitTent_integral : ∫x,unitTent x=1 := by
  have hsupp : Function.support unitTent ⊆ Set.Ioc (-1) 1 := by
    intro x hx
    have hh : |x| < 1 := lt_of_not_ge (fun h => hx (unitTent_zero h))
    exact ⟨(abs_lt.mp hh).1,(abs_lt.mp hh).2.le⟩
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupp]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (unitTent_lipschitz.continuous.intervalIntegrable (-1) 0)
    (unitTent_lipschitz.continuous.intervalIntegrable 0 1)]
  have hneg : Set.EqOn unitTent (fun x => 1+x) (Set.uIcc (-1) 0) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    simp only [unitTent,abs_of_nonpos hx.2,sub_neg_eq_add]
    exact max_eq_left (by linarith [hx.1])
  have hpos : Set.EqOn unitTent (fun x => 1-x) (Set.uIcc 0 1) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    simp only [unitTent,abs_of_nonneg hx.1]
    exact max_eq_left (by linarith [hx.2])
  rw [intervalIntegral.integral_congr hneg,intervalIntegral.integral_congr hpos,
    intervalIntegral.integral_add (f:=fun _ : ℝ => (1:ℝ)) (g:=fun x : ℝ => x) (continuous_const.intervalIntegrable _ _)
      (continuous_id.intervalIntegrable _ _),
    intervalIntegral.integral_sub (f:=fun _ : ℝ => (1:ℝ)) (g:=fun x : ℝ => x) (continuous_const.intervalIntegrable _ _)
      (continuous_id.intervalIntegrable _ _)]
  norm_num [intervalIntegral.integral_const,integral_id]

noncomputable def doubleUnitTent (x : Fin 2 → ℝ) : ℝ := ∏i,unitTent (x i)

theorem doubleUnitTent_bounds (x : Fin 2 → ℝ) : 0 ≤ doubleUnitTent x ∧ doubleUnitTent x ≤ 1 := by
  exact ⟨Finset.prod_nonneg (fun i _ => (unitTent_bounds (x i)).1),
    Finset.prod_le_one₀ (fun i _ => (unitTent_bounds (x i)).1) (fun i _ => (unitTent_bounds (x i)).2)⟩

theorem doubleUnitTent_lipschitz : LipschitzWith 2 doubleUnitTent := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have hp := unit_product_sub_bound Finset.univ (fun i => unitTent (x i)) (fun i => unitTent (y i))
    (fun i _ => unitTent_bounds (x i)) (fun i _ => unitTent_bounds (y i))
  calc
    _ ≤ ∑i : Fin 2,|unitTent (x i)-unitTent (y i)| := hp
    _ ≤ ∑i : Fin 2,dist x y := by
      apply Finset.sum_le_sum
      intro i _
      have hh := unitTent_lipschitz.dist_le_mul (x i) (y i)
      rw [Real.dist_eq,NNReal.coe_one,one_mul] at hh
      exact hh.trans (dist_le_pi_dist x y i)
    _ = _ := by simp

theorem doubleUnitTent_zero {x : Fin 2 → ℝ} (hx : 1 < ‖x‖) : doubleUnitTent x=0 := by
  have hh : ∃i,1 < |x i| := by
    by_contra hn
    push Not at hn
    have he : ‖x‖ ≤ (1:ℝ) := by
      rw [← dist_zero_right]
      exact (dist_pi_le_iff zero_le_one).mpr (fun i => by simpa [Real.dist_eq] using hn i)
    exact (not_le_of_gt hx) he
  obtain ⟨i,hi⟩ := hh
  exact Finset.prod_eq_zero (Finset.mem_univ i) (unitTent_zero hi.le)

theorem doubleUnitTent_integral : ∫x,doubleUnitTent x=1 := by
  unfold doubleUnitTent
  rw [integral_fintype_prod_volume_eq_prod]
  simp [unitTent_integral]

noncomputable def pairedUnitTent (x : (Fin 2 → ℝ)×(Fin 2 → ℝ)) : ℝ :=
  doubleUnitTent x.1*doubleUnitTent x.2

theorem pairedUnitTent_bounds (x : (Fin 2 → ℝ)×(Fin 2 → ℝ)) :
    0 ≤ pairedUnitTent x ∧ pairedUnitTent x ≤ 1 := by
  exact ⟨mul_nonneg (doubleUnitTent_bounds x.1).1 (doubleUnitTent_bounds x.2).1,
    (mul_le_of_le_one_left (doubleUnitTent_bounds x.2).1
      (doubleUnitTent_bounds x.1).2).trans (doubleUnitTent_bounds x.2).2⟩

theorem unit_mul_sub_bound {a b c d : ℝ} (ha : a∈Set.Icc (0:ℝ) 1) (hb : b∈Set.Icc (0:ℝ) 1)
    (hc : c∈Set.Icc (0:ℝ) 1) (hd : d∈Set.Icc (0:ℝ) 1) :
    |a*b-c*d| ≤ |a-c|+|b-d| := by
  have h := unit_product_sub_bound (Finset.univ : Finset (Fin 2)) ![a,b] ![c,d]
    (by intro i _; fin_cases i <;> assumption) (by intro i _; fin_cases i <;> assumption)
  simpa [Fin.prod_univ_two,Fin.sum_univ_two] using h

theorem pairedUnitTent_lipschitz : LipschitzWith 4 pairedUnitTent := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have hh := unit_mul_sub_bound (doubleUnitTent_bounds x.1) (doubleUnitTent_bounds x.2)
    (doubleUnitTent_bounds y.1) (doubleUnitTent_bounds y.2)
  have h₁ := doubleUnitTent_lipschitz.dist_le_mul x.1 y.1
  have h₂ := doubleUnitTent_lipschitz.dist_le_mul x.2 y.2
  rw [Real.dist_eq] at h₁ h₂
  change |pairedUnitTent x-pairedUnitTent y| ≤ _ at hh
  have hd₁ : dist x.1 y.1 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hd₂ : dist x.2 y.2 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_right _ _
  norm_num at h₁ h₂ ⊢
  linarith

theorem pairedUnitTent_zero {x : (Fin 2 → ℝ)×(Fin 2 → ℝ)} (hx : 1 < ‖x‖) :
    pairedUnitTent x=0 := by
  rw [Prod.norm_def,lt_max_iff] at hx
  rcases hx with hh|hh
  · simp [pairedUnitTent,doubleUnitTent_zero hh]
  · simp [pairedUnitTent,doubleUnitTent_zero hh]

theorem pairedUnitTent_integrable : Integrable pairedUnitTent := by
  apply pairedUnitTent_lipschitz.continuous.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (isCompact_closedBall (0 : (Fin 2 → ℝ)×(Fin 2 → ℝ)) 1)
  intro x hx
  exact pairedUnitTent_zero (lt_of_not_ge (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx))

theorem pairedUnitTent_integral : ∫x,pairedUnitTent x=1 := by
  change (∫x : (Fin 2 → ℝ)×(Fin 2 → ℝ),doubleUnitTent x.1*doubleUnitTent x.2 ∂
    (volume.prod volume))=1
  rw [integral_prod_mul,doubleUnitTent_integral,mul_one]

theorem pairedQuadratic_tent_mass {d s t : ℝ} (hd : 1 ≤ d) (hs : 0 < s) (ht : 0 < t)
    (hst : 36 ≤ s*t) (q : (Fin 2 → ℝ)×(Fin 2 → ℝ)) :
    ∃S : Finset (CutRing×CutRing),
      (∀z,z∉S → pairedUnitTent (q+pairedQuadraticEmbedding d s t z)=0) ∧
      |(5/(d^4*s^2*t^2))*(∑z∈S,pairedUnitTent (q+pairedQuadraticEmbedding d s t z))-1| ≤
        38880/(d*Real.sqrt (s*t)) := by
  obtain ⟨S,hS,hh⟩ := pairedQuadratic_riemann_uniform hd hs ht hst (show 0 ≤ (1:ℝ) by norm_num)
    pairedUnitTent_integrable pairedUnitTent_lipschitz (fun x hx => pairedUnitTent_zero hx) q
  refine ⟨S,hS,?_⟩
  rw [pairedUnitTent_integral] at hh
  convert hh using 1
  norm_num
  ring

end NormalizedTentMass

end SimpleAmenable
end
end

end OAI
