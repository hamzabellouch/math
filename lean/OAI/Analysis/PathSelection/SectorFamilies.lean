import Mathlib
import OAI.Analysis.PathSelection.LossPullbacks
import OAI.Analysis.PathSelection.SectorLimits

namespace OAI

/-! Countable sector narrowing and common fixed-sector asymptotics. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

/- No uniform angular losses and no uniform original tail thresholds are assumed. -/

open Set Filter Topology
namespace DegeneratingTrees

lemma summable_common_eventual_majorant {a : ℕ → ℕ → ℝ}
    (ha : ∀ i n,0≤a i n) (hs : ∀ i,Summable (a i)) :
    ∃ v : ℕ → ℝ,(∀ n,0≤v n) ∧ Summable v ∧
      ∀ i,∀ᶠ n in atTop,a i n≤v n := by
  let c : ℕ → ℝ := fun i => (1/2:ℝ)^i/(1+∑' n,a i n)
  have hc (i : ℕ) : 0<c i := by
    have ht : 0 ≤ ∑' n,a i n := tsum_nonneg (ha i)
    dsimp [c]
    positivity
  have hc_bound (i : ℕ) : c i*(∑' n,a i n) ≤ (1/2:ℝ)^i := by
    have ht : 0 ≤ ∑' n,a i n := tsum_nonneg (ha i)
    dsimp [c]
    calc
      (1/2:ℝ)^i/(1+∑' n,a i n)*(∑' n,a i n) ≤
          (1/2:ℝ)^i/(1+∑' n,a i n)*(1+∑' n,a i n) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (1/2:ℝ)^i := div_mul_cancel₀ _ (by positivity)
  have hprod : Summable (fun p : ℕ×ℕ => c p.1*a p.1 p.2) := by
    have hn : (0 : ℕ×ℕ → ℝ) ≤ (fun p => c p.1*a p.1 p.2) :=
      fun p => mul_nonneg (hc _).le (ha _ _)
    have hrow (i : ℕ) : Summable (fun n => c i*a i n) := (hs i).mul_left (c i)
    have hsum : Summable (fun i => c i*(∑' n,a i n)) :=
      Summable.of_nonneg_of_le (fun i => mul_nonneg (hc i).le (tsum_nonneg (ha i)))
        hc_bound summable_geometric_two
    have hsum' : Summable (fun i => ∑' n,c i*a i n) := by
      simpa only [tsum_mul_left] using hsum
    exact (summable_prod_of_nonneg hn).mpr ⟨hrow,hsum'⟩
  let w : ℕ → ℝ := fun n => ∑' i,c i*a i n
  have hw (n : ℕ) : 0≤w n := tsum_nonneg (fun i => mul_nonneg (hc i).le (ha i n))
  have hws : Summable w := hprod.prod_symm.prod
  obtain ⟨v,hv,hvs,hvw⟩ := summable_strict_majorant hw hws
  refine ⟨v,hv,hvs,?_⟩
  intro i
  filter_upwards [hvw (c i) (hc i)] with n hn
  have hh : c i*a i n ≤ w n :=
    (hprod.prod_symm.prod_factor n).le_tsum i (fun j _ => mul_nonneg (hc j).le (ha j n))
  exact (mul_le_mul_iff_right₀ (hc i)).mp (hh.trans hn)

 

theorem admissible_countable_majorant {ω : ℕ → ℝ → ℝ}
    (hω : ∀ i,AdmissibleAngularLoss (ω i)) :
    ∃ η : ℝ → ℝ,AdmissibleAngularLoss η ∧
      ∀ i,∀ᶠ r : ℝ in atTop,ω i r≤η r := by
  choose N w hw hws hb using fun i => (hω i).2
  let a : ℕ → ℕ → ℝ := fun i n => w i (n-N i)
  have ha (i n : ℕ) : 0≤a i n := hw i _
  have has (i : ℕ) : Summable (a i) := by
    apply (summable_nat_add_iff (N i)).mp
    simpa only [a,Nat.add_sub_cancel] using hws i
  obtain ⟨v,hv,hvs,hdom⟩ := summable_common_eventual_majorant ha has
  let η : ℝ → ℝ := fun r => max (baseLoss r) (v (dyadicLossIndex 0 r))
  refine ⟨η,admissible_dyadic_step hv hvs 0,?_⟩
  intro i
  filter_upwards [dyadicLossIndex_shell 0,
    (tendsto_dyadicLossIndex 0).eventually (eventually_ge_atTop (N i)),
    (tendsto_dyadicLossIndex 0).eventually (hdom i)] with r hr hN hdom
  have hidx : dyadicLossIndex 0 r-N i+N i=dyadicLossIndex 0 r := Nat.sub_add_cancel hN
  have hbound : ω i r ≤ a i (dyadicLossIndex 0 r) := by
    apply hb i _ r
    · simpa only [hidx,Nat.add_zero] using hr.1
    · simpa only [hidx,Nat.add_zero] using hr.2
  exact hbound.trans (hdom.trans (le_max_right _ _))

 

theorem SectorEventually.countable {P : ℕ → ℂ → Prop}
    (hP : ∀ n,SectorEventually (P n)) :
    ∃ η : ℝ → ℝ,AdmissibleAngularLoss η ∧
      ∀ n,∃ R : ℝ,∀ z∈lossSector η R,P n z := by
  choose ω R hω h using hP
  obtain ⟨η,hη,he⟩ := admissible_countable_majorant hω
  refine ⟨η,hη,?_⟩
  intro n
  obtain ⟨T,hT⟩ := eventually_atTop.mp (he n)
  refine ⟨max (R n) T,?_⟩
  intro z hz
  apply h n z
  refine ⟨(le_max_left _ _).trans_lt hz.1,?_⟩
  have hh := hT ‖z‖ ((le_max_right _ _).trans hz.1.le)
  exact hz.2.trans_le (sub_le_sub_left hh _)

end DegeneratingTrees

 

 

 

open Set Filter Topology
open scoped Asymptotics
namespace DegeneratingTrees

lemma fixed_sector_of_tendsto {E : Type*} [PseudoMetricSpace E]
    {f : ℂ → E} {a : E} (hf : Tendsto f sectorInfinity (𝓝 a)) :
    ∃ η : ℝ → ℝ,AdmissibleAngularLoss η ∧
      ∀ ε : ℝ,0<ε → ∃ R : ℝ,∀ z∈lossSector η R,dist (f z) a<ε := by
  have hp (n : ℕ) : SectorEventually (fun z => dist (f z) a<1/((n:ℝ)+1)) :=
    Metric.tendsto_nhds.mp hf _ (by positivity)
  obtain ⟨η,hη,h⟩ := SectorEventually.countable hp
  refine ⟨η,hη,?_⟩
  intro ε hε
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨R,hR⟩ := h n
  exact ⟨R,fun z hz => (hR z hz).trans hn⟩

lemma fixed_sector_of_littleO {E F : Type*} [Norm E] [SeminormedAddCommGroup F]
    {f : ℂ → E} {g : ℂ → F} (hfg : f =o[sectorInfinity] g) :
    ∃ η : ℝ → ℝ,AdmissibleAngularLoss η ∧
      ∀ ε : ℝ,0<ε → ∃ R : ℝ,∀ z∈lossSector η R,‖f z‖≤ε*‖g z‖ := by
  have hp (n : ℕ) : SectorEventually (fun z => ‖f z‖≤(1/((n:ℝ)+1))*‖g z‖) :=
    hfg.bound (by positivity)
  obtain ⟨η,hη,h⟩ := SectorEventually.countable hp
  refine ⟨η,hη,?_⟩
  intro ε hε
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨R,hR⟩ := h n
  exact ⟨R,fun z hz => (hR z hz).trans (mul_le_mul_of_nonneg_right hn.le (norm_nonneg _))⟩

lemma fixed_sector_realpart {F : ℂ → ℂ}
    (hF : (fun z => (F z).re) =o[sectorInfinity] Complex.re) :
    ∃ η : ℝ → ℝ,AdmissibleAngularLoss η ∧
      ∀ ε : ℝ,0<ε → ∃ R : ℝ,∀ z∈lossSector η R,|(F z).re|≤ε*z.re := by
  have hp (n : ℕ) : SectorEventually (fun z =>
      ‖(F z).re‖≤(1/((n:ℝ)+1))*‖z.re‖ ∧ 0<z.re) :=
    (hF.bound (by positivity)).and SectorEventually.realpart_pos
  obtain ⟨η,hη,h⟩ := SectorEventually.countable hp
  refine ⟨η,hη,?_⟩
  intro ε hε
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨R,hR⟩ := h n
  refine ⟨R,?_⟩
  intro z hz
  obtain ⟨hb,hpos⟩ := hR z hz
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hpos] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right hn.le hpos.le)

end DegeneratingTrees
end

end OAI
