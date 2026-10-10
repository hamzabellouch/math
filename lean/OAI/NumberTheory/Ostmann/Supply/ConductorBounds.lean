import OAI.NumberTheory.Ostmann.Supply.RetainedBandScales
import OAI.NumberTheory.Ostmann.Supply.SmoothPrimeWeight
import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalSmoothingAbel
import OAI.NumberTheory.Ostmann.ZeroDensity.SupplyPrimeScales

namespace OAI

noncomputable section
namespace Ostmann.Supply
open Filter
open scoped BigOperators

def supplyPrimeCap (L : ℝ) : ℕ := ⌊Real.exp (Real.exp ((9/10:ℝ)*L))⌋₊
def supplyCharacterCutoff (L : ℝ) : ℕ := (supplyPrimeCap L)^(2*supplyTruncation L)

theorem supplyPrimeCap_pos (L : ℝ) : 0<supplyPrimeCap L := by
  have h : (1:ℝ)≤Real.exp (Real.exp ((9/10:ℝ)*L)) := Real.one_le_exp (Real.exp_pos _).le
  apply Nat.le_floor
  simpa using h

theorem supplyPrimeCap_cast_le (L : ℝ) :
    (supplyPrimeCap L:ℝ)≤Real.exp (Real.exp ((9/10:ℝ)*L)) := Nat.floor_le (Real.exp_pos _).le

theorem supplyCharacterCutoff_pos (L : ℝ) : 0<supplyCharacterCutoff L :=
  pow_pos (supplyPrimeCap_pos L) _

theorem supplyCharacterCutoff_le (L : ℝ) :
    supplyCharacterCutoff L≤Ostmann.ZeroDensity.supplyConductorCutoff L := by
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg (supplyPrimeCap L)) (supplyPrimeCap_cast_le L)
    (2*supplyTruncation L)
  have he : Real.exp (Real.exp ((9/10:ℝ)*L))^(2*supplyTruncation L)=
      Real.exp (2*(supplyTruncation L:ℝ)*Real.exp (9*L/10)) := by
    rw [←Real.exp_nat_mul]
    congr 1
    push_cast
    rw [show (9/10:ℝ)*L=9*L/10 by ring]
  rw [he] at hp
  have hceil := Nat.le_ceil (Real.exp (2*(supplyTruncation L:ℝ)*Real.exp (9*L/10)))
  have hfinal : (supplyCharacterCutoff L:ℝ)≤(Ostmann.ZeroDensity.supplyConductorCutoff L:ℝ) := by
    unfold supplyCharacterCutoff Ostmann.ZeroDensity.supplyConductorCutoff
    rw [Nat.cast_pow]
    exact hp.trans hceil
  exact_mod_cast hfinal

theorem prime_le_supplyPrimeCap {L : ℝ} {p : ℕ} (hp : p.Prime)
    (hband : Real.log (Real.log (p:ℝ))≤(9/10:ℝ)*L) : p≤ supplyPrimeCap L := by
  have hp0 : (0:ℝ)<p := Nat.cast_pos.mpr hp.pos
  have hlog : 0<Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  apply Nat.le_floor
  exact (Real.log_le_iff_le_exp hp0).mp ((Real.log_le_iff_le_exp hlog).mp hband)

theorem primeBand_card_le {L : ℝ} (P : Finset ℕ)
    (hP : ∀p∈P,p.Prime ∧ Real.log (Real.log (p:ℝ))≤(9/10:ℝ)*L) :
    (P.card:ℝ)≤Real.exp (Real.exp ((9/10:ℝ)*L)) := by
  have hsub : P⊆Finset.Icc 1 (supplyPrimeCap L) := fun p hp =>
    Finset.mem_Icc.mpr ⟨(hP p hp).1.one_le,prime_le_supplyPrimeCap (hP p hp).1 (hP p hp).2⟩
  have hc : P.card≤ supplyPrimeCap L := by simpa using Finset.card_le_card hsub
  apply le_trans _ (supplyPrimeCap_cast_le L)
  exact_mod_cast hc

theorem eventually_supplyPrimeCap_le_radius :
    ∀ᶠL:ℝ in atTop,supplyPrimeCap L≤ supplyRadius L ∧ 2≤ supplyRadius L := by
  filter_upwards [eventually_retainedBand_numeric,eventually_ge_atTop (1:ℝ),
    supplyRadius_tendsto.eventually_ge_atTop 2] with L hh hL hR
  have hK : (1:ℝ)≤(2*supplyTruncation L:ℕ) := by
    have hpos : 0<supplyTruncation L := Nat.ceil_pos.mpr (by linarith : 0<10000*L)
    exact_mod_cast (show 1≤2*supplyTruncation L by omega)
  have he : Real.exp ((9/10:ℝ)*L)≤Real.exp L/2 := by
    apply le_trans _ hh.2.1
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hK (Real.exp_pos ((9/10:ℝ)*L)).le
  refine ⟨?_,hR⟩
  have hb := (supplyPrimeCap_cast_le L).trans (Real.exp_le_exp.mpr he)
  have hc := Nat.le_ceil (Real.exp (Real.exp L/2))
  exact_mod_cast hb.trans hc

theorem primeWeight_coprime_local {L : ℝ} (hcap : supplyPrimeCap L≤ supplyRadius L)
    (hR : 2≤ supplyRadius L) {q p : ℕ} (hq : q.Prime) (hp : p.Prime)
    (hpmax : p≤ supplyPrimeCap L)
    (hφ : primeWeight ((q:ℝ)/((supplyRadius L)^2:ℕ))≠0) : Nat.Coprime q p := by
  have hX : (0:ℝ)<((supplyRadius L)^2:ℕ) := by exact_mod_cast pow_pos (supplyRadius_pos L) 2
  have hn := Ostmann.ZeroDensity.principal_weight_nonzero_interval primeWeight_support hX hφ
  have hr : (supplyRadius L:ℝ)≤(((supplyRadius L)^2:ℕ):ℝ)/2 := by
    have hr2 : (2:ℝ)≤ supplyRadius L := by exact_mod_cast hR
    push_cast
    nlinarith
  have hpq : (p:ℝ)<q := by
    apply lt_of_le_of_lt _ (hr.trans_lt hn.1)
    exact_mod_cast hpmax.trans hcap
  apply (Nat.coprime_primes hq hp).mpr
  exact ne_of_gt (by exact_mod_cast hpq)

end Ostmann.Supply

end

end OAI
