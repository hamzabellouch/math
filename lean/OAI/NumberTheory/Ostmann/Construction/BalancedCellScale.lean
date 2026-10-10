import OAI.NumberTheory.Ostmann.Construction.GiantWindowScale
import OAI.NumberTheory.Ostmann.Construction.GoodLogCellBalance
import OAI.NumberTheory.Ostmann.Construction.LogCellPrimePrior

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter

def cellPrimeCutoff (L : ℝ) : ℕ := ⌈Real.exp (Real.exp L)⌉₊

lemma cellPrimeCutoff_pos (L : ℝ) : 0<cellPrimeCutoff L :=
  Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.one_le_ceil_iff.mpr (Real.exp_pos _)))

lemma cellPrimeCutoff_tendsto : Tendsto cellPrimeCutoff atTop atTop :=
  tendsto_nat_ceil_atTop.comp (Real.tendsto_exp_atTop.comp Real.tendsto_exp_atTop)

lemma cellPrimeCutoff_log_lower (L : ℝ) : Real.exp L≤Real.log (cellPrimeCutoff L:ℝ) := by
  have h := Real.log_le_log (Real.exp_pos (Real.exp L)) (Nat.le_ceil (Real.exp (Real.exp L)))
  simpa only [Real.log_exp,cellPrimeCutoff] using h

lemma cellPrimeCutoff_loglog_upper {L : ℝ} (hL : 0≤L) :
    Real.log (Real.log (cellPrimeCutoff L:ℝ))≤L+1 := by
  have hl := log_ceil_exp_le_add_one (Real.exp L) (Real.exp_pos _).le
  have hpos : 0<Real.log (cellPrimeCutoff L:ℝ) :=
    (Real.exp_pos _).trans_le (cellPrimeCutoff_log_lower L)
  have he1 : 1≤Real.exp L := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hL
  have he2 : (2:ℝ)≤Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hm := mul_le_mul_of_nonneg_left he2 (Real.exp_pos L).le
  rw [← Real.exp_add] at hm
  have hb : Real.log (cellPrimeCutoff L:ℝ)≤Real.exp (L+1) := by
    change Real.log (cellPrimeCutoff L:ℝ)≤Real.exp L+1 at hl
    linarith
  have h := Real.log_le_log hpos hb
  rwa [Real.log_exp] at h

def BalancedCellAfterTwo (d : Decomposition) (c : ℝ) : Prop :=
  ∀ E : Finset ℕ, E.card≤2 → ∃ hZ : 0<logCellMass c E,
    (1/2:ℝ)≤(logCellPrior c E hZ).mean (fun p => balancedPrimeIndicator d p)

theorem balancedCellAfterTwo_eventually (d : Decomposition) {a : ℝ} (ha : 0<a) (b : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ c : ℝ,
      a*favorableBlockWidth L≤c → c≤b*favorableBlockWidth L →
      badLogCellMass d (cellPrimeCutoff L) c≤(1/8:ℝ) → BalancedCellAfterTwo d c := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp logCell_normalization_eventually
  have hlower := ((exp_mul_tendsto (by norm_num : (0:ℝ)<1/100)).const_mul_atTop ha).eventually_ge_atTop
    (max T 2)
  have hrate := (exp_mul_tendsto (by norm_num : (0:ℝ)<99/100)).eventually_ge_atTop (b+1)
  have hwidth := (exp_mul_tendsto (by norm_num : (0:ℝ)<1/100)).eventually_ge_atTop 1
  filter_upwards [hlower,hrate,hwidth] with L hlow hrate hwidth
  intro c hcmin hcmax hbad
  have hcT : T≤c := (le_max_left _ _).trans (hlow.trans hcmin)
  have hc2 : 2≤c := (le_max_right _ _).trans (hlow.trans hcmin)
  have hh : 0<favorableBlockWidth L := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_left hrate hh.le
  have he : favorableBlockWidth L*Real.exp ((99/100:ℝ)*L)=Real.exp L := by
    unfold favorableBlockWidth
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hmul
  have hcover : c+1≤Real.log (cellPrimeCutoff L:ℝ) := by
    apply le_trans _ (cellPrimeCutoff_log_lower L)
    change 1≤favorableBlockWidth L at hwidth
    nlinarith
  intro E hE
  obtain ⟨hZ,hZlo,hZhi⟩ := hT c hcT E hE
  exact ⟨hZ,good_logCell_balanced_probability d c E (cellPrimeCutoff L)
    (cellPrimeCutoff_pos L) hc2 hcover hZ hZhi hbad⟩

theorem badLogCellCenters_linear_bound (d : Decomposition) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ L : ℝ in atTop, ∀ K : Finset ℤ,
      ((badLogCellCenters d (cellPrimeCutoff L) K (1/8)).card:ℝ)≤C*L := by
  obtain ⟨C,hC,hbudget⟩ := eventually_badLogCellCenters_card_le d (by norm_num : (0:ℝ)<1/8)
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [cellPrimeCutoff_tendsto.eventually hbudget,eventually_ge_atTop (1:ℝ)] with L hb hL
  intro K
  have h := hb K
  have hl := cellPrimeCutoff_loglog_upper (show 0≤L by linarith)
  have hm := mul_le_mul_of_nonneg_left hl hC.le
  nlinarith

end Ostmann.Construction

end

end OAI
