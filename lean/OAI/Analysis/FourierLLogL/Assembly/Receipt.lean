import OAI.Analysis.FourierLLogL.Assembly.Series
/-! # The uniform output path -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Paths
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical


namespace Troupe
open Run Streak

def parody (s : Scene M) (i : ℕ) := (rose (tagM i) (0:Grid M)).flag s
def stampAux (s : Scene M) (j : ℕ) :=
    4*parody s (mainIx j+1)+10^20*(fax s+
      (∑ i∈Finset.Ico 0 (mainIx j+1), parody s i / depthRate i))

def stamp (s : Scene M) (j : ℕ) := 512*mutedR s j true + stampAux s j

lemma stamp_nonneg {s : Scene M} (h : Climb s) (j : ℕ) : 0 ≤ stamp s j := by
  unfold stamp stampAux
  have H := surcharge_nonneg s false (priciest s j true)
  have HH (i : ℕ) : 0 ≤ parody s i := flag_nonneg _ _
  have HP : 0 ≤ ∑ i∈Finset.Ico 0 (mainIx j+1), parody s i / depthRate i :=
    Finset.sum_nonneg (fun _ _ => div_nonneg (HH _) (rate_easy _).1.le)
  unfold mutedR
  linarith [(fax_floor h).1,HH (mainIx j+1)]

private lemma chamber_fee (c j) (L : Path M) :
    tokenCost j c L + crumb (lowI j c) (highI j M c) j L =
      rooms c j L+512*subtotal (fun b => mutedR b.post j c) L+
        (if c then 4*(subtotal (special j) L+(billWait (tagM (mainIx j)) j L:ℝ)) else 0) := by
  unfold tokenCost crumb rooms miniStage playsL
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  ring

lemma receipt_main (j : ℕ) (L : Path M) :
    souvenir true j L=rooms true j L+palaces j L + subtotal (fun b => stamp b.post j) L := by
  simp only [souvenir,chamber_fee]
  simp only [↓reduceIte]
  unfold palaces stamp stampAux bigCrumb
  simp_rw [blend _ (f:=fun _ => _) (g:=fun _ => _),subtR]
  let m := Finset.Ico 0 (mainIx j+1)
  let F (b : Beat M) (i : ℕ) := parody b.post i / depthRate i
  have H (i : ℕ) : mainSticker i j L = nakedStage i j L + subtotal (fun b => F b i) L := by
    unfold F mainSticker nakedStage mainRatio parody flagged
    simp_rw [div_eq_mul_inv,mul_comm _ (depthRate i)⁻¹,subtR]
    ring
  simp_rw [H,Finset.sum_add_distrib]
  have HH := cross_subtotal L m F
  unfold F m at HH
  rw [blend L (fun b => fax b.post),HH]; unfold F
  rw [show subtotal (fun b => fax b.post) L=fullFax L from rfl]

  have HV : special j = fun b : Beat M => parody b.post (mainIx j+1) := rfl
  rw [HV]

  linarith
lemma receipt_static (j : ℕ) (L : Path M) :
    souvenir false j L=rooms false j L+512*subtotal (fun b => mutedR b.post j false) L := by
  simp only [souvenir,chamber_fee]; simp

def gateTax (s : Scene M) (j : ℕ) :=
    if s.live then 10^140*height j/Thermal.H j else 10^140*amount s j

lemma tax_pos (s : Scene M) (j : ℕ) : 0 ≤ gateTax s j := by
  have := d_pos j; have := H_pos j; have HA := (amount_limits s j).1
  unfold gateTax; split <;> positivity

lemma receipt_paid :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ s : Scene M, ∀ t : Thread M s, ∀ f : Grid M → ℝ,
      t.Following j J f → Fit s → entry s →
      (s.live=true → exp (-height j) ≤ s.norm) →
      (∀ x, f x ≤ exp (height j)) →
      stats t (souvenir s.live j) ≤ gateTax s j +
        (if s.live then stats t (subtotal (fun b => stamp b.post j)) else 0) := by
  filter_upwards [rooms_fee,palaces_fee,segment_cost,hpoly 1 1] with j hr hp hv hT
    M J s t f h hh hx he hf
  let d := height j
  let k := amount s j; let v := Thermal.H j
  have hV : 1 ≤ v := H_ge _
  have hk : 1 ≤ k := (amount_limits _ _).1
  have hd : 1 ≤ d := one_le_pow₀ (by norm_num)
  have HG := stats_plus t
  have HS := hr M J s f t h hh hx hf
  unfold gateTax
  split
  · rename_i hE
    have Ht := HS true
    have HH := hp M J s f t h hh hx hE (he hE) hf
    have hK : k ≤ 4*d := by
      have H := log_le_log (exp_pos _) (he hE)
      rw [log_exp] at H
      change d+max _ 0+2 ≤ _
      have he' : max (-log s.norm) 0 ≤ d := max_le (by unfold d; linarith) (by linarith)
      linarith
    rw [hE]
    rw [show souvenir (M:=M) true j=
      fun L => rooms true j L+palaces j L+subtotal (fun b => stamp b.post j) L from funext (receipt_main _)]
    rw [HG (f:=fun L => _),HG (f:=fun L => _)]
    have heq : lowI j true=mainIx j := rfl
    rw [heq,depth_at_main] at Ht
    have hi : 0 < v := H_pos j
    have HE : 1/v^8 ≤ 1/v := one_div_le_one_div_of_le hi
      (by simpa using pow_le_pow_right₀ hV (by omega : 1 ≤ 8))
    have HT : 1+10^30*(1/v^8)*k ≤ 10^31*(d/v) := by
      have hΦ : 1 ≤ d/v := (one_le_div hi).mpr (by simpa using hT)
      have hh := mul_le_mul HE hK (by positivity) (by positivity)
      rw [show 1/v*(4*d)=4*(d/v) by ring] at hh; nlinarith
    change stats t _ ≤ 1+10^30*(1/v^8)*k at Ht
    unfold v d at *
    nlinarith [show 0 ≤ height j/Thermal.H j by have := H_pos j; have := d_pos j; positivity,
      show 10^140*height j/Thermal.H j=10^140*(height j/Thermal.H j) by ring,
      show 10^120*height j/Thermal.H j=10^120*(height j/Thermal.H j) by ring]
  · rename_i hE
    have Ht := HS false
    rw [show lowI j false=0 from rfl,show depthRate 0=1 by simp [depthRate,side]] at Ht
    have HM := hv M J s f t h hf (show 0 < s.mass from hx ▸ hh.pos) hh.pos (fun q => priciest q j false) false
    rw [show s.mass/s.norm=1 from entry_share hh hx, one_mul] at HM
    rw [show s.live=false from Bool.eq_false_iff.mpr hE]
    simp only [add_zero]
    rw [show souvenir (M:=M) false j =
      fun L => rooms false j L+512* subtotal (fun b => mutedR b.post j false) L from funext (receipt_static _)]
    change stats t _ ≤ _*k
    rw [HG]
    have HE : stats t (fun L => 512*subtotal (fun b => mutedR b.post j false) L) =
        512* t.fee (fun b => mutedR b.post j false) :=
      Ex_lmul (s.here.dice M) _ 512
    rw [HE]
    change _≤ 1+_*_*k at Ht
    have hp : height j ≤ k := (amount_limits _ _).2
    have hh0 : -log s.mass ≤ k := by unfold entry at hx; rw [← hx]; unfold k amount; linarith [le_max_left (-log s.norm) 0,d_pos j]
    unfold mutedR; linarith

/-- pointwise price comparison for expected flags. -/
lemma parody_fee (s : Scene M) (j : ℕ) (i : ℕ) (h : i ≤ mainIx j+1) :
    parody s i ≤ 10^6*Thermal.H j^32*surcharge s true (i-1) := by
  have hE : 0 < Thermal.H j := H_pos _
  by_cases he : (rose (tagM i) (0:Grid M)).rogue s
  · have hx := he.1
    have hp : 0 < i := hx
    have HH := he.2
    have HC := (bottom_level j)
    have HT : side (mainIx j) ≤ side (i-1) :=
      side_ant _ _ (by omega)
    rw [HC] at HT
    change hazard s true (i-1) at HH
    rw [show parody s i=1 from ite_eq_left he,surcharge,ite_eq_left HH]
    change side (i-1)^2/128 ≤ _ at HH
    let v := Thermal.H j
    have Hb : 1/v^32/128 ≤ edgeW s (i-1) := by
      have Hi : 0 ≤ 1/(Thermal.H j)^16 := by positivity
      apply le_trans _ HH
      have HT := div_le_div_of_nonneg_right (pow_le_pow_left₀ Hi HT 2) (by norm_num : (0:ℝ)≤128)
      rw [show (1/Thermal.H j^16)^2=1/v^32 by unfold v; ring] at HT; exact HT
    have hx' : 0 < v^32 := pow_pos hE _
    change 1 ≤ 10^6*v^32*_
    nlinarith [mul_le_mul_of_nonneg_left Hb hx'.le,
      show v^32*(1/v^32/128)=1/128 by have Hx : 0 < v := hE; field_simp]
  · rw [show parody s i=0 from ite_eq_right he]
    exact mul_nonneg (by positivity) (surcharge_nonneg _ _ _)

lemma depth_rate_fee (i j : ℕ) (h : i ≤ mainIx j) :
    1/depthRate i ≤ Thermal.H j^8 := by
  have H : depthRate (mainIx j) ≤ depthRate i := sqrt_le_sqrt (side_ant i _ h)
  rw [depth_at_main] at H
  apply (div_le_iff₀ (rate_easy _).1).mpr
  have HE := (div_le_iff₀ (show 0 < Thermal.H j^8 by have := H_pos j; positivity)).mp H
  linarith

end Troupe


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
