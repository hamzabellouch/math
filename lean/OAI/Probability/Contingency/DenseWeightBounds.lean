import Mathlib
import OAI.Probability.Contingency.AcceptedChain

namespace OAI

/-! Dense Weight Bounds. -/

noncomputable section

open scoped BigOperators
open scoped BigOperators
namespace Contingency.Dense.BinProblem
noncomputable section
open Contingency.Grid Contingency.Interpolation Contingency.FiniteChain
variable {a c q K : ℕ} (D : BinProblem a c q K)

theorem corner_penalty_bound (hK : (K:ℝ)=4*D.d^8) (v : Vertex q K) :
    penalty (fun i => (D.R i:ℝ)) (fun j => (D.P j:ℝ)) D.widths (D.d^8) D.d
      (fun s => realCorner v (D.e.symm s)) ≤ 4*D.d := by
  have hd : 0<D.d := by linarith [D.hd]
  have hr (i) : 0<(D.R i:ℝ) := by exact_mod_cast D.hR i
  have hp (j) : 0<(D.P j:ℝ) := by exact_mod_cast D.hP j
  have heq : (∑ i,(D.R i:ℝ))=∑ j,(D.P j:ℝ) := by exact_mod_cast D.heq
  have hw (i j) : 0<D.widths i j := by
    change (0:ℝ)<D.w (D.e.symm (i,j))
    exact_mod_cast D.hw (D.e.symm (i,j))
  obtain ⟨u,hu⟩ := interior_point D.d hd _ _ D.widths hr hp heq D.ha D.hc hw
  have hu0 (i j) : 0 ≤ normalized (fun i => (D.R i:ℝ)) (fun j => (D.P j:ℝ)) D.widths u i j :=
    (by positivity : (0:ℝ)≤1/(2*D.d)).trans (hu i j)
  have hb := polytope_bounded _ _ D.widths (D.d^8) (by positivity) hr hp heq D.widthlo u hu0
  have hnorm : ‖(fun s => realCorner v (D.e.symm s))-u‖ ≤ K := by
    apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg K)).mpr
    intro s
    have hv0 : (0:ℝ)≤realCorner v (D.e.symm s) := Nat.cast_nonneg _
    have hvK : realCorner v (D.e.symm s) ≤ K := by
      change ((v (D.e.symm s)).val:ℝ)≤K
      exact_mod_cast (v (D.e.symm s)).isLt.le
    have hbu := hb s
    have hhalf : 2*D.d^8 ≤ (K:ℝ) := by rw [hK]; nlinarith [show 0≤D.d^8 by positivity]
    simp only [Pi.sub_apply,Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> linarith [hbu.1,hbu.2]
  have hz : penalty (fun i => (D.R i:ℝ)) (fun j => (D.P j:ℝ)) D.widths (D.d^8) D.d u=0 :=
    penalty_zero_of_slack _ _ _ _ _ _ (fun i j =>
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd.le) (show 0≤D.d^8 by positivity)).trans (hu0 i j))
  have hdiff := penalty_difference (fun i => (D.R i:ℝ)) (fun j => (D.P j:ℝ)) D.widths (D.d^8) D.d
    (D.d/D.d^8*‖(fun s => realCorner v (D.e.symm s))-u‖) (by positivity)
    (fun s => realCorner v (D.e.symm s)) u
    (fun i j => normalized_lipschitz _ _ _ _ _ (by positivity) D.dim hr hp
      (fun i => by exact_mod_cast D.hRmax i) (fun j => by exact_mod_cast D.hPmax j)
      (fun i j => (hw i j).le) D.widthhi _ _ i j)
  rw [hz,sub_zero,abs_of_nonneg (penalty_nonneg _ _ _ _ _ _)] at hdiff
  calc
    _ ≤ _ := hdiff
    _ ≤ D.d/D.d^8*K := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = 4*D.d := by rw [hK]; field_simp

theorem weight_upper (v : Vertex q K) : D.weight v ≤ 1 := by
  change (2:ℝ)^(-(⌊binExponent D.e _ _ D.widths D.d (realCorner v)⌋:ℝ))≤1
  apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
  apply neg_nonpos.mpr
  exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg (by positivity) (penalty_nonneg _ _ _ _ _ _))

theorem weight_lower (hK : (K:ℝ)=4*D.d^8) (v : Vertex q K) :
    (2:ℝ)^(-(4*D.d^5)) ≤ D.weight v := by
  change _≤(2:ℝ)^(-(⌊binExponent D.e _ _ D.widths D.d (realCorner v)⌋:ℝ))
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hh := Int.floor_le (binExponent D.e (fun i => (D.R i:ℝ)) (fun j => (D.P j:ℝ)) D.widths D.d (realCorner v))
  have hb := mul_le_mul_of_nonneg_left (D.corner_penalty_bound hK v) (show 0≤D.d^4 by positivity)
  unfold binExponent at hh ⊢
  nlinarith only [hh,hb]

theorem normalizer_upper : D.Z ≤ (K:ℝ)^q := by
  calc
    _ ≤ ∑ v : Vertex q K,(1:ℝ) := Finset.sum_le_sum fun v _ => D.weight_upper v
    _ = _ := by simp [Vertex]

theorem stationary_lower (hK : (K:ℝ)=4*D.d^8) (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/(8*D.d))
    (v : Vertex q K) : (2:ℝ)^(-(4*D.d^5))/(K:ℝ)^q ≤ (D.chain p hp0 hp).π v := by
  change _ ≤ D.weight v/D.Z
  exact div_le_div₀ (Real.rpow_nonneg (by norm_num) _) (D.weight_lower hK v) D.Zpos D.normalizer_upper

end
end Contingency.Dense.BinProblem

 

 

open scoped BigOperators
namespace Contingency.Dense.BinProblem
noncomputable section
open Contingency.Grid Contingency.FiniteChain
variable {a c q K : ℕ} (D : BinProblem a c q K)

def inverseGap : ℝ := 2/D.kappa^2

theorem inverseGap_eq (hK : (K:ℝ)=4*D.d^8) : D.inverseGap=320000000000*D.d^20 := by
  have hd : D.d≠0 := by linarith [D.hd]
  unfold inverseGap kappa
  rw [hK]
  field_simp
  ring

theorem inverseGap_bounds (hd : 14 ≤ D.d) (hK : (K:ℝ)=4*D.d^8) :
    1 ≤ D.inverseGap ∧ D.inverseGap ≤ D.d^32 := by
  rw [D.inverseGap_eq hK]
  have h1 : 1 ≤ D.d^20 := one_le_pow₀ (by linarith)
  have h12 : 320000000000 ≤ D.d^12 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤14) hd 12
    norm_num at hh
    linarith only [hh]
  constructor
  · linarith only [h1]
  · have hh := mul_le_mul_of_nonneg_right h12 (show 0 ≤ D.d^20 by positivity)
    calc
      _ ≤ D.d^12*D.d^20 := hh
      _ = _ := by ring

theorem log_stationary_bound (hd : 14 ≤ D.d) (hK : (K:ℝ)=4*D.d^8) :
    4*D.d^5*Real.log 2+(q:ℝ)*Real.log K ≤ 4*D.d^5 := by
  have hd0 : 0<D.d := by linarith
  have h2 : Real.log 2 ≤ (3:ℝ)/4 := by linarith only [Real.log_two_lt_d9]
  have hK0 : (0:ℝ)<K := by exact_mod_cast D.Kpos
  have hK1 : (1:ℝ)≤K := by exact_mod_cast D.Kpos
  have hlogK : Real.log K=2*Real.log 2+8*Real.log D.d := by
    rw [hK,Real.log_mul (by norm_num) (by positivity),Real.log_pow]
    have hh : Real.log (4:ℝ)=2*Real.log 2 := by
      have he : (4:ℝ)=2^2 := by norm_num
      rw [he,Real.log_pow]
      norm_num
    rw [hh]
    norm_num
  have hlogd : Real.log D.d ≤ D.d := (Real.log_le_sub_one_of_pos hd0).trans (by linarith)
  have hlog : Real.log K ≤ 2+8*D.d := by rw [hlogK]; linarith
  have hq := mul_le_mul_of_nonneg_right D.hq (Real.log_nonneg hK1)
  have hh := mul_le_mul_of_nonneg_left hlog hd0.le
  have hc : 4*D.d^5*Real.log 2 ≤ 3*D.d^5 := by
    have hh := mul_le_mul_of_nonneg_left h2 (show 0≤4*D.d^5 by positivity)
    nlinarith only [hh]
  have h3 : 10 ≤ D.d^3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤14) hd 3
    norm_num at hh
    linarith only [hh]
  have hd1 : D.d ≤ D.d^2 := by nlinarith
  have hsmall : 2*D.d+8*D.d^2 ≤ D.d^5 := by
    have hh := mul_le_mul_of_nonneg_right h3 (sq_nonneg D.d)
    nlinarith only [hh,hd1]
  nlinarith only [hc,hq,hh,hsmall]

theorem prefactor_bound (hd : 14 ≤ D.d) (hK : (K:ℝ)=4*D.d^8) :
    ((2:ℝ)^(-(4*D.d^5))/(K:ℝ)^q)⁻¹ ≤ Real.exp (4*D.d^5) := by
  have hK0 : (0:ℝ)<K := by exact_mod_cast D.Kpos
  have he : ((2:ℝ)^(-(4*D.d^5))/(K:ℝ)^q)⁻¹=
      Real.exp (4*D.d^5*Real.log 2+(q:ℝ)*Real.log K) := by
    rw [inv_div,Real.rpow_def_of_pos (by norm_num),div_eq_mul_inv,← Real.exp_neg]
    rw [show (K:ℝ)^q=Real.exp ((q:ℝ)*Real.log K) from by rw [Real.exp_nat_mul,Real.exp_log hK0]]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact Real.exp_le_exp.mpr (D.log_stationary_bound hd hK)

theorem scheduled_mixing (hd : 14 ≤ D.d) (hK : (K:ℝ)=4*D.d^8)
    (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/(8*D.d)) (hplo : 1/(16*D.d) ≤ p)
    (h t : ℕ) (hh : 1 ≤ h) (ht : (t:ℝ)=D.d^50*((h:ℝ)+1)^2) (v : Vertex q K) :
    (D.chain p hp0 hp).tv t v ≤ (2:ℝ)^(-4*((h:ℝ)+D.d)) := by
  have hd0 : 0<D.d := by linarith
  have hg := D.inverseGap_bounds hd hK
  have hk0 : 0<D.inverseGap := by linarith [hg.1]
  have hmix := (D.chain p hp0 hp).mixing_bound_min D.inverseGap hg.1
    (D.chain_poincare p hp0 hp hplo) ((2:ℝ)^(-(4*D.d^5))/(K:ℝ)^q)
    (div_pos (Real.rpow_pos_of_pos (by norm_num) _) (pow_pos (by exact_mod_cast D.Kpos) _))
    (D.stationary_lower hK p hp0 hp) t v
  have hpref := mul_le_mul_of_nonneg_right (D.prefactor_bound hd hK) (Real.exp_pos (-(t:ℝ)/D.inverseGap)).le
  have htime : D.d^18*((h:ℝ)+1)^2 ≤ (t:ℝ)/D.inverseGap := by
    apply (le_div_iff₀ hk0).mpr
    calc
      _ ≤ D.d^18*((h:ℝ)+1)^2*D.d^32 := by gcongr; exact hg.2
      _ = _ := by rw [ht]; ring
  have h18 : 4*D.d^5 ≤ D.d^18 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤14) hd 13
    have hh' : 4 ≤ D.d^13 := by norm_num at hh; linarith only [hh]
    have hm := mul_le_mul_of_nonneg_right hh' (show 0≤D.d^5 by positivity)
    simpa only [← pow_add] using hm
  have h5 : D.d+1 ≤ D.d^5 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤14) hd 4
    have hh' : 2 ≤ D.d^4 := by norm_num at hh; linarith only [hh]
    have hm := mul_le_mul_of_nonneg_right hh' hd0.le
    nlinarith only [hm,hd]
  have hh1 : (1:ℝ)≤h := by exact_mod_cast hh
  have hx : (h:ℝ)+D.d ≤ D.d^5*(h:ℝ)*((h:ℝ)+2) := by
    have hm := mul_le_mul_of_nonneg_right h5 (by positivity : 0≤(h:ℝ))
    have hm2 : (h:ℝ)+D.d ≤ (D.d+1)*(h:ℝ) := by nlinarith
    have hm3 : D.d^5*(h:ℝ) ≤ D.d^5*(h:ℝ)*((h:ℝ)+2) := by nlinarith [show 0≤D.d^5*(h:ℝ) by positivity]
    exact hm2.trans (hm.trans hm3)
  have hlog2 : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
  have hfinal : 4*((h:ℝ)+D.d)*Real.log 2 ≤ (t:ℝ)/D.inverseGap-4*D.d^5 := by
    have hm := mul_le_mul_of_nonneg_right h18 (sq_nonneg ((h:ℝ)+1))
    have hl := mul_le_mul_of_nonneg_left hlog2 (show 0≤4*((h:ℝ)+D.d) by positivity)
    nlinarith only [htime,hm,hx,hl]
  apply hmix.trans (hpref.trans _)
  rw [← Real.exp_add,Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.mpr
  rw [neg_div]
  nlinarith only [hfinal]

end
end Contingency.Dense.BinProblem

 

 

open scoped BigOperators
namespace Contingency.FiniteChain.Chain
noncomputable section
variable {V : Type*} [Fintype V] (C : Chain V)

def invariant : Law V := ⟨C.π,fun x => (C.positive x).le,C.normalized⟩
def transition (x : V) : Law V := ⟨C.P x,C.nonneg x,C.stochastic x⟩
def walk (x : V) : ℕ → Law V
  | 0 => Law.pure x
  | n+1 => (walk x n).bind C.transition

theorem walk_mass [DecidableEq V] (x y : V) (n : ℕ) :
    (C.walk x n).mass y=C.law n x y := by
  induction n generalizing y with
  | zero => by_cases h : x=y <;> simp [walk,Law.pure,law,h]
  | succ n ih =>
    simp only [walk,Law.bind,transition,law]
    apply Finset.sum_congr rfl; intro z _
    rw [ih]

theorem walk_tv [DecidableEq V] (x : V) (n : ℕ) :
    (C.walk x n).tv C.invariant=C.tv n x := by
  simp only [Law.tv,walk_mass,invariant,tv]

end
end Contingency.FiniteChain.Chain

 

 

open scoped BigOperators
namespace Contingency.Dense.BinProblem
noncomputable section
open Contingency.Grid Contingency.FiniteChain
variable {a c q K : ℕ} (D : BinProblem a c q K)

local instance tableFintype (R : Fin (a+1) → ℕ) (P : Fin (c+1) → ℕ) : Fintype (Tables R P) := Fintype.ofFinite _
local instance tableNonempty : Nonempty (Tables D.R D.P) := tables_nonempty D.R D.P D.heq
local instance offsetNonempty : Nonempty (Offsets D.w) := ⟨fun i => ⟨0,D.hw i⟩⟩

def idealSamples : Law (Sample (K:=K) D.w) := ⟨D.sampleMass,D.sampleMass_nonneg,D.sampleMass_total⟩

def decode (s : Sample (K:=K) D.w) : Option (Tables D.R D.P) := by
  classical
  exact if hs : D.good s then some ((acceptedEquiv D.e D.w D.hw D.heq D.bound) ⟨s,hs⟩) else none

theorem decode_eq_some (s : Sample (K:=K) D.w) (X : Tables D.R D.P) :
    D.decode s=some X ↔ s=D.tableSample X := by
  classical
  unfold decode
  split_ifs with hs
  · rw [Option.some.injEq]
    constructor
    · intro h
      have hh := congrArg (acceptedEquiv D.e D.w D.hw D.heq D.bound).symm h
      rw [Equiv.symm_apply_apply] at hh
      exact congrArg Subtype.val hh
    · intro h
      subst s
      exact (acceptedEquiv D.e D.w D.hw D.heq D.bound).apply_symm_apply X
  · simp only [false_iff]
    intro h
    subst s
    exact hs (encodeSample_accepted D.e D.w D.hw D.bound X)

def idealTrial : Law (Option (Tables D.R D.P)) := D.idealSamples.map D.decode

theorem idealTrial_some (X : Tables D.R D.P) :
    D.idealTrial.mass (some X)=D.sampleMass (D.tableSample X) := by
  classical
  simp only [idealTrial,Law.map,Law.bind,Law.pure,mul_ite,mul_one,mul_zero,D.decode_eq_some]
  simp [idealSamples]

theorem idealTrial_none : D.idealTrial.mass none=1-D.success := by
  have ht := D.idealTrial.total
  rw [Fintype.sum_option] at ht
  have he : (∑ X : Tables D.R D.P,D.idealTrial.mass (some X))=D.success := by
    simp only [D.idealTrial_some,D.table_mass,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,D.success_eq_card]
    rw [Nat.card_eq_fintype_card]
    ring
  rw [he] at ht
  linarith

theorem idealTrial_uniform (X : Tables D.R D.P) :
    D.idealTrial.mass (some X)=(1-D.idealTrial.mass none)*(Law.uniform (Tables D.R D.P)).mass X := by
  rw [D.idealTrial_some,D.idealTrial_none]
  have h := D.conditional_uniform X
  have hs : D.success≠0 := ne_of_gt (lt_of_lt_of_le (by norm_num) D.success_lower)
  rw [div_eq_iff hs] at h
  simp only [Law.uniform,Nat.card_eq_fintype_card] at h ⊢
  linarith

 
def implementedOffsets (h d : ℕ) : Law (Offsets D.w) :=
  Law.pi (fun i => (offsetLaw (D.w i) (D.hw i) (Nat.clog 2 (D.w i+1)+4*(h+d))).toLaw)

def uniformOffsets : Law (Offsets D.w) :=
  Law.pi (fun i => @Law.uniform (Fin (D.w i)) inferInstance ⟨⟨0,D.hw i⟩⟩)

theorem offset_tv (h d : ℕ) :
    (D.implementedOffsets h d).tv D.uniformOffsets ≤ (q:ℝ)*(2:ℝ)^(-((4*(h+d):ℕ):ℤ)) := by
  apply (Law.tv_pi _ _).trans
  calc
    _ ≤ ∑ _ : Fin q,(2:ℝ)^(-((4*(h+d):ℕ):ℤ)) :=
      Finset.sum_le_sum fun i _ => rounded_offset_accuracy (D.w i) h d (D.hw i)
    _ = _ := by simp

theorem uniformOffsets_mass (β : Offsets D.w) : D.uniformOffsets.mass β=1/(D.offsetCount:ℝ) := by
  simp only [uniformOffsets,Law.pi,Law.uniform,Fintype.card_fin,one_div]
  have he : (∏ i,(D.w i:ℝ))=(D.offsetCount:ℝ) := by
    simp only [offsetCount,Offsets]
    rw [Fintype.card_pi,Nat.cast_prod]
    simp only [Fintype.card_fin]
  rw [Finset.prod_inv_distrib,he]

theorem idealSamples_prod (p : ℝ) (hp0 : 0≤p) (hp : p≤1/(8*D.d)) :
    D.idealSamples=(D.chain p hp0 hp).invariant.prod D.uniformOffsets := by
  apply Law.ext; funext s
  simp only [idealSamples,sampleMass,Law.prod,D.uniformOffsets_mass,Chain.invariant,chain,
    AcceptedData.chain,Grid.metropolis,AcceptedData.total]
  change D.weight s.1/(D.Z*D.offsetCount)=D.weight s.1/D.Z*(1/D.offsetCount)
  ring

 
def implementedTrial (p : ℝ) (hp0 : 0≤p) (hp : p≤1/(8*D.d)) (h d t : ℕ) : Law (Option (Tables D.R D.P)) :=
  (((D.chain p hp0 hp).walk (fun _ => ⟨0,D.Kpos⟩) t).prod (D.implementedOffsets h d)).map D.decode

end
end Contingency.Dense.BinProblem

 

 

open scoped BigOperators
namespace Contingency.Dense.BinProblem
noncomputable section
open Contingency.Grid Contingency.FiniteChain
variable {a c q K : ℕ} (D : BinProblem a c q K)
attribute [local instance] tableFintype tableNonempty

 
theorem implementedTrial_tv (d : ℕ) (hd : 14≤d) (hD : D.d=d) (hK : (K:ℝ)=4*D.d^8)
    (p : ℝ) (hp0 : 0≤p) (hp : p≤1/(8*D.d)) (hplo : 1/(16*D.d)≤p)
    (h : ℕ) (hh : 1≤h) :
    (D.implementedTrial p hp0 hp h d (d^50*(h+1)^2)).tv D.idealTrial ≤
      (1+(d:ℝ))*(2:ℝ)^(-((4*(h+d):ℕ):ℤ)) := by
  have he : (2:ℝ)^(-4*((h:ℝ)+D.d))=(2:ℝ)^(-((4*(h+d):ℕ):ℤ)) := by
    rw [← Real.rpow_intCast]
    push_cast
    rw [hD]
    congr 1
    ring
  have hc := D.scheduled_mixing (by rw [hD]; exact_mod_cast hd) hK p hp0 hp hplo h
    (d^50*(h+1)^2) hh (by rw [hD]; push_cast; rfl) (fun _ => ⟨0,D.Kpos⟩)
  rw [he,← Chain.walk_tv] at hc
  have ho := D.offset_tv h d
  have hf := Law.tv_prod ((D.chain p hp0 hp).walk (fun _ => ⟨0,D.Kpos⟩) (d^50*(h+1)^2))
    (D.chain p hp0 hp).invariant (D.implementedOffsets h d) D.uniformOffsets
  have hm := Law.tv_map D.decode
    (((D.chain p hp0 hp).walk (fun _ => ⟨0,D.Kpos⟩) (d^50*(h+1)^2)).prod (D.implementedOffsets h d))
    ((D.chain p hp0 hp).invariant.prod D.uniformOffsets)
  rw [← D.idealSamples_prod] at hm hf
  have hq : (q:ℝ)≤d := by simpa only [hD] using D.hq
  change (D.implementedTrial p hp0 hp h d (d^50*(h+1)^2)).tv D.idealTrial ≤ _ at hm
  apply (hm.trans hf).trans
  have hq' := mul_le_mul_of_nonneg_right hq (by positivity : (0:ℝ)≤(2:ℝ)^(-((4*(h+d):ℕ):ℤ)))
  nlinarith only [hc,ho,hq']

end
end Contingency.Dense.BinProblem

 

 

open scoped BigOperators
namespace Contingency

 
theorem square_le_two_pow (d : ℕ) (hd : 4≤d) : d^2≤2^d := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hd
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h : (4+n+1)^2≤2*(4+n)^2 := by nlinarith
    calc
      (4+(n+1))^2 = (4+n+1)^2 := by congr 1
      _ ≤ 2*(4+n)^2 := h
      _ ≤ 2*2^(4+n) := Nat.mul_le_mul_left 2 (ih (by omega))
      _ = 2^(4+(n+1)) := by rw [show 4+(n+1)=4+n+1 by omega,pow_succ]; omega

theorem dense_schedule_offset (d h : ℕ) (hd : 14≤d) :
    ((d^4*(h+1):ℕ):ℝ)*(1+(d:ℝ))*(2:ℝ)^(-((4*(h+d):ℕ):ℤ)) ≤
      (2:ℝ)^(-((h+2:ℕ):ℤ)) := by
  have hd4 : d^4≤2^(2*d) := by
    calc
      d^4 = (d^2)^2 := by ring
      _ ≤ (2^d)^2 := Nat.pow_le_pow_left (square_le_two_pow d (by omega)) 2
      _ = 2^(2*d) := by rw [← pow_mul]; congr 1; omega
  have hh : h+1≤2^h := Nat.lt_two_pow_self (n:=h)
  have hdp : d+1≤2^d := Nat.lt_two_pow_self (n:=d)
  have hn : d^4*(h+1)*(d+1)≤2^(h+3*d) := by
    calc
      _ ≤ 2^(2*d)*2^h*2^d := Nat.mul_le_mul (Nat.mul_le_mul hd4 hh) hdp
      _ = _ := by rw [← pow_add,← pow_add]; congr 1; omega
  have hmul : d^4*(h+1)*(d+1)*2^(h+2)≤2^(4*(h+d)) := by
    calc
      _ ≤ 2^(h+3*d)*2^(h+2) := Nat.mul_le_mul_right _ hn
      _ = 2^((h+3*d)+(h+2)) := by rw [← pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hr : (((d^4*(h+1):ℕ):ℝ)*(1+(d:ℝ)))*(2:ℝ)^(h+2)≤(2:ℝ)^(4*(h+d)) := by
    have hc : ((d^4*(h+1)*(d+1):ℕ):ℝ)*(2:ℝ)^(h+2)≤(2:ℝ)^(4*(h+d)) := by exact_mod_cast hmul
    push_cast at hc ⊢
    nlinarith only [hc]
  rw [zpow_neg,zpow_natCast,zpow_neg,zpow_natCast]
  rw [← div_eq_mul_inv,inv_eq_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simpa only [one_mul] using hr

theorem dense_schedule_failure (d h : ℕ) (hd : 14≤d) :
    (63/64:ℝ)^(d^4*(h+1)) ≤ (2:ℝ)^(-((h+2:ℕ):ℤ)) := by
  have hd4 : 128≤d^4 := by
    have hh := Nat.pow_le_pow_left hd 4
    norm_num at hh
    omega
  have hJ : 64*(h+2)≤d^4*(h+1) := by nlinarith
  calc
    _ ≤ (63/64:ℝ)^(64*(h+2)) := pow_le_pow_of_le_one (by norm_num) (by norm_num) hJ
    _ = ((63/64:ℝ)^64)^(h+2) := by rw [pow_mul]
    _ ≤ (1/2:ℝ)^(h+2) := pow_le_pow_left₀ (by positivity) (by norm_num) (h+2)
    _ = _ := by rw [one_div,inv_pow,zpow_neg,zpow_natCast]

theorem dense_schedule_total (d h : ℕ) (hd : 14≤d) :
    (63/64:ℝ)^(d^4*(h+1))+((d^4*(h+1):ℕ):ℝ)*(1+(d:ℝ))*(2:ℝ)^(-((4*(h+d):ℕ):ℤ)) ≤
      (2:ℝ)^(-(h:ℤ)) := by
  have hf := dense_schedule_failure d h hd
  have ho := dense_schedule_offset d h hd
  have he : (2:ℝ)^(-((h+2:ℕ):ℤ))=(2:ℝ)^(-(h:ℤ))/4 := by
    rw [zpow_neg,zpow_natCast,zpow_neg,zpow_natCast,pow_add]
    norm_num
    ring
  rw [he] at hf ho
  have hn : (0:ℝ)≤(2:ℝ)^(-(h:ℤ)) := by positivity
  linarith

end Contingency

 

 

open scoped BigOperators
namespace Contingency.Dense.BinProblem
noncomputable section
open Contingency.Grid
variable {a c q K : ℕ} (D : BinProblem a c q K)
attribute [local instance] tableFintype tableNonempty

 
def draw (p : ℝ) (hp0 : 0≤p) (hp : p≤1/(8*D.d)) (h d : ℕ)
    (fallback : Tables D.R D.P) : Law (Tables D.R D.P) :=
  Law.first (D.implementedTrial p hp0 hp h d (d^50*(h+1)^2)) fallback (d^4*(h+1))

 
theorem draw_tv (d : ℕ) (hd : 14≤d) (hD : D.d=d) (hK : (K:ℝ)=4*D.d^8)
    (p : ℝ) (hp0 : 0≤p) (hp : p≤1/(8*D.d)) (hplo : 1/(16*D.d)≤p)
    (h : ℕ) (hh : 1≤h) (fallback : Tables D.R D.P) :
    (D.draw p hp0 hp h d fallback).tv (Law.uniform (Tables D.R D.P)) ≤ (2:ℝ)^(-(h:ℤ)) := by
  have ht := D.implementedTrial_tv d hd hD hK p hp0 hp hplo h hh
  have hfirst := Law.first_tv (D.implementedTrial p hp0 hp h d (d^50*(h+1)^2)) D.idealTrial fallback (d^4*(h+1))
  have hideal := Law.first_ideal_tv D.idealTrial fallback (Law.uniform (Tables D.R D.P)) D.idealTrial_uniform (d^4*(h+1))
  have hfail : D.idealTrial.mass none≤63/64 := by rw [D.idealTrial_none]; linarith [D.success_lower]
  have hf := pow_le_pow_left₀ (D.idealTrial.nonneg none) hfail (d^4*(h+1))
  have hm := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (d^4*(h+1)))
  have htri := Law.tv_triangle (D.draw p hp0 hp h d fallback)
    (Law.first D.idealTrial fallback (d^4*(h+1))) (Law.uniform (Tables D.R D.P))
  change (D.draw p hp0 hp h d fallback).tv (Law.first D.idealTrial fallback (d^4*(h+1)))≤_ at hfirst
  have htot := dense_schedule_total d h hd
  nlinarith only [hfirst,hideal,hf,hm,htri,htot]

end
end Contingency.Dense.BinProblem

 

 

open scoped BigOperators
namespace Contingency
noncomputable section

 
def acceptCount (B ex ey : ℕ) : ℕ := 2^(B-(ey-ex))

theorem acceptCount_le (B ex ey : ℕ) : acceptCount B ex ey≤2^B :=
  Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)

def acceptCoin (B ex ey : ℕ) : DyadicLaw Bool where
  bits := B
  count b := if b then acceptCount B ex ey else 2^B-acceptCount B ex ey
  total := by
    simp only [Fintype.sum_bool,Bool.false_eq_true,ite_false,ite_true]
    have := acceptCount_le B ex ey
    omega

theorem acceptCoin_true (B ex ey : ℕ) :
    (acceptCoin B ex ey).toLaw.mass true=(acceptCount B ex ey:ℝ)/(2:ℝ)^B := rfl

 
theorem acceptCount_ratio (B ex ey : ℕ) (hey : ey≤B) :
    (acceptCount B ex ey:ℝ)/(2:ℝ)^B=min (1/(2:ℝ)^ex) (1/(2:ℝ)^ey)/(1/(2:ℝ)^ex) := by
  have he : ey-ex≤B := le_trans (Nat.sub_le _ _) hey
  have hp : (2:ℝ)^B=(2:ℝ)^(B-(ey-ex))*(2:ℝ)^(ey-ex) := by
    rw [← pow_add,Nat.sub_add_cancel he]
  simp only [acceptCount,Nat.cast_pow,Nat.cast_ofNat]
  rw [hp]
  rcases le_total ex ey with h|h
  · have hm : 1/(2:ℝ)^ey≤1/(2:ℝ)^ex :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) h)
    rw [min_eq_right hm]
    have hq : (2:ℝ)^ey=(2:ℝ)^ex*(2:ℝ)^(ey-ex) := by rw [← pow_add,Nat.add_sub_of_le h]
    rw [hq]
    field_simp
  · have hm : 1/(2:ℝ)^ex≤1/(2:ℝ)^ey :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) h)
    rw [min_eq_left hm,Nat.sub_eq_zero_of_le h]
    simp

namespace Law
variable {α : Type*} [Fintype α] [DecidableEq α]

def accept (proposal : Law α) (coin : α → Law Bool) (x : α) : Law α :=
  proposal.bind (fun y => (coin y).map (fun b => if b then y else x))

theorem accept_offdiag (proposal : Law α) (coin : α → Law Bool) (x y : α) (h : x≠y) :
    (proposal.accept coin x).mass y=proposal.mass y*(coin y).mass true := by
  simp only [accept,bind,map,pure,Fintype.sum_bool,Bool.false_eq_true,ite_false,ite_true]
  simp [h]

theorem ext_offdiag (p r : Law α) (x : α) (h : ∀ y,x≠y → p.mass y=r.mass y) : p=r := by
  apply Law.ext; funext y
  by_cases he : x=y
  · subst y
    have hp := Finset.sum_erase_add Finset.univ p.mass (Finset.mem_univ x)
    have hr := Finset.sum_erase_add Finset.univ r.mass (Finset.mem_univ x)
    have hs : (∑ y∈Finset.univ.erase x,p.mass y)=∑ y∈Finset.univ.erase x,r.mass y :=
      Finset.sum_congr rfl fun y hy => h y (Ne.symm (Finset.mem_erase.mp hy).1)
    rw [p.total] at hp
    rw [r.total] at hr
    linarith
  · exact h y he
end Law

namespace DyadicLaw
variable {α : Type*} [Fintype α] [DecidableEq α]

def accept (proposal : DyadicLaw α) (e : α → ℕ) (B : ℕ) (x : α) : DyadicLaw α :=
  proposal.bind (fun y => (acceptCoin B (e x) (e y)).map (fun b => if b then y else x)) B
    (fun y => by rw [map_bits]; rfl)

theorem toLaw_accept (proposal : DyadicLaw α) (e : α → ℕ) (B : ℕ) (x : α) :
    (proposal.accept e B x).toLaw=proposal.toLaw.accept (fun y => (acceptCoin B (e x) (e y)).toLaw) x := by
  unfold accept
  rw [toLaw_bind]
  simp only [toLaw_map,Law.accept]
end DyadicLaw

end
end Contingency

 

 

open scoped BigOperators
namespace Contingency
noncomputable section
namespace DyadicLaw
variable {α : Type*} [Fintype α] [DecidableEq α]

def neighborProposal (E : α → α → Prop) [DecidableRel E] (x : α) (R : ℕ)
    (_hirr : ¬E x x) (hb : (Finset.univ.filter (E x)).card≤2^R) : DyadicLaw α where
  bits := R
  count y := (if x=y then 2^R-(Finset.univ.filter (E x)).card else 0)+(if E x y then 1 else 0)
  total := by
    rw [Finset.sum_add_distrib]
    have hs : (∑ y : α, if E x y then (1:ℕ) else 0) = (Finset.univ.filter (E x)).card := by
      rw [← Finset.sum_filter]
      simp
    rw [hs]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    omega

theorem neighborProposal_offdiag (E : α → α → Prop) [DecidableRel E] (x : α) (R : ℕ)
    (hirr : ¬E x x) (hb : (Finset.univ.filter (E x)).card≤2^R) (y : α) (h : x≠y) :
    (neighborProposal E x R hirr hb).toLaw.mass y=(if E x y then 1 else 0)/(2:ℝ)^R := by
  simp [neighborProposal,toLaw,h]

 
theorem accepted_neighbor_kernel (E : α → α → Prop) [DecidableRel E]
    (e : α → ℕ) (B R : ℕ) (he : ∀ y,e y≤B) (x : α)
    (hirr : ¬E x x) (hb : (Finset.univ.filter (E x)).card≤2^R)
    (P : Law α) (hP : ∀ y,x≠y → P.mass y=
      (1/(2:ℝ)^R)*(if E x y then min (1/(2:ℝ)^e x) (1/(2:ℝ)^e y) else 0)/(1/(2:ℝ)^e x)) :
    ((neighborProposal E x R hirr hb).accept e B x).toLaw=P := by
  rw [toLaw_accept]
  apply Law.ext_offdiag _ _ x
  intro y hxy
  rw [Law.accept_offdiag _ _ _ _ hxy,neighborProposal_offdiag _ _ _ _ _ _ hxy,
    acceptCoin_true,acceptCount_ratio _ _ _ (he y),hP y hxy]
  by_cases h : E x y <;> simp [h]
  ring

end DyadicLaw
end
end Contingency

 

 

namespace Contingency
noncomputable section
 
def proposalRate (M : ℕ) : ℝ := 1/(2:ℝ)^Nat.clog 2 M

theorem proposalRate_bounds (M : ℕ) (hM : 1<M) :
    1/(2*(M:ℝ)) ≤ proposalRate M ∧ proposalRate M ≤ 1/(M:ℝ) := by
  have hM0 : (0:ℝ)<M := by exact_mod_cast (by omega : 0<M)
  have hge : M≤2^Nat.clog 2 M := Nat.le_pow_clog (by norm_num) M
  have hlog : 0<Nat.clog 2 M := by
    by_contra hn
    have hh : Nat.clog 2 M=0 := by omega
    rw [hh,pow_zero] at hge
    omega
  have hlt := Nat.pow_pred_clog_lt_self (by norm_num : 1<2) hM
  change 2^(Nat.clog 2 M-1)<M at hlt
  have he : 2^Nat.clog 2 M = 2*2^(Nat.clog 2 M-1) := by
    conv_lhs => rw [show Nat.clog 2 M=Nat.clog 2 M-1+1 by omega,pow_succ]
    exact Nat.mul_comm _ _
  have hle : 2^Nat.clog 2 M ≤ 2*M := by rw [he]; omega
  unfold proposalRate
  constructor
  · apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast hle
  · apply one_div_le_one_div_of_le hM0
    exact_mod_cast hge

theorem binProposal_bounds (d : ℕ) (hd : 1≤d) :
    1/(16*(d:ℝ)) ≤ proposalRate (8*d) ∧ proposalRate (8*d) ≤ 1/(8*(d:ℝ)) := by
  have hh := proposalRate_bounds (8*d) (by omega)
  push_cast at hh
  simpa only [show (2:ℝ)*(8*d)=16*d by ring] using hh

theorem smallProposal_bounds (d : ℕ) (hd : 1≤d) :
    1/(64*(d:ℝ)^2) ≤ proposalRate (32*d^2) ∧ proposalRate (32*d^2) ≤ 1/(32*(d:ℝ)^2) := by
  have hd2 : 1≤d^2 := one_le_pow₀ hd
  have hh := proposalRate_bounds (32*d^2) (by omega)
  push_cast at hh
  simpa only [show (2:ℝ)*(32*(d:ℝ)^2)=64*(d:ℝ)^2 by ring] using hh

end
end Contingency

end

end OAI
