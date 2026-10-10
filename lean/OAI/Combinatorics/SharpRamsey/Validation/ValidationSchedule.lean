import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.SparseProductSharp
import OAI.Combinatorics.SharpRamsey.Validation.ProducedExclusion

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real Incidence
open scoped Classical BigOperators
noncomputable section

def scheduleLength (q u t : ℝ) : ℕ := ⌈20*q*(log (u/t)+2)⌉₊

def scheduleCutoff (q a : ℝ) (h : ℕ) : ℕ := ⌈2*q*exp ((h:ℝ)*a)⌉₊

lemma scheduleLength_pos {q u t : ℝ} (hq : 0<q) (ht : 0<t) (htu : t≤u) :
    0<scheduleLength q u t := by
  have hd : 0≤log (u/t) := log_nonneg ((le_div_iff₀ ht).mpr (by simpa using htu))
  have hh : 0<20*q*(log (u/t)+2) := by positivity
  exact Nat.ceil_pos.mpr hh

lemma scheduleLength_size {q u t s x Q C : ℝ} (hq : 0<q) (ht : 0<t)
    (htu : t≤u) (hs : 0<s) (hx : 0<x) (hC : 1≤C)
    (hcap : s≤C*x) (hprod : s*t≤2*Q) (hQ : 0≤Q) :
    36*Q/x+u*exp (1-(scheduleLength q u t:ℝ)/(20*q))≤(1000*C*Q/s)/20 := by
  have hu : 0<u := ht.trans_le htu
  have hh := Nat.le_ceil (20*q*(log (u/t)+2))
  have he : 1-(scheduleLength q u t:ℝ)/(20*q)≤ -log (u/t) := by
    have hp : 0<20*q := by positivity
    have hh' : log (u/t)+2≤(scheduleLength q u t:ℝ)/(20*q) := by
      apply (le_div_iff₀ hp).mpr
      simpa only [scheduleLength,mul_comm] using hh
    linarith
  have hrow : u*exp (1-(scheduleLength q u t:ℝ)/(20*q))≤t := by
    apply (mul_le_mul_of_nonneg_left (exp_le_exp.mpr he) hu.le).trans_eq
    rw [exp_neg,exp_log (div_pos hu ht)]
    field_simp
  have hsmall : 36*Q/x≤36*C*Q/s := by
    apply (div_le_div_iff₀ hx hs).mpr
    have hh := mul_le_mul_of_nonneg_left hcap (show 0≤36*Q by positivity)
    nlinarith only [hh]
  have htarget : t≤2*Q/s := (le_div_iff₀ hs).mpr (by nlinarith only [hprod])
  have haux : 2*Q/s≤2*C*Q/s := by
    simpa only [mul_one] using div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hC (by norm_num : (0:ℝ)≤2)) hQ) hs.le
  have hsz := add_le_add hsmall (hrow.trans (htarget.trans haux))
  have hp : 0≤C*Q/s := by positivity
  apply hsz.trans
  convert mul_le_mul_of_nonneg_right (show (38:ℝ) ≤ 50 by norm_num) hp using 1 <;> ring

lemma scheduleCutoff_search {q x w a : ℝ} (hq : 0<q) (hx : 0<x) (hw : 0<w)
    (hratio : w≤exp a*x) (h : ℕ) :
    q≤(scheduleCutoff q a h:ℝ)*((x/w)^h*(9/10)) := by
  have hr : w/x≤exp a := (div_le_iff₀ hx).mpr hratio
  have hp := pow_le_pow_left₀ (div_nonneg hw.le hx.le) hr h
  rw [←exp_nat_mul] at hp
  have hh := Nat.le_ceil (2*q*exp ((h:ℝ)*a))
  have he : (w/x)^h*(x/w)^h=1 := by rw [←mul_pow]; field_simp; simp
  have hs := mul_le_mul_of_nonneg_right hp (show 0≤(x/w)^h by positivity)
  rw [he] at hs
  have hs' := mul_le_mul_of_nonneg_right hh (show 0≤(x/w)^h*(9/10:ℝ) by positivity)
  change q≤(⌈2*q*exp ((h:ℝ)*a)⌉₊:ℝ)*_
  nlinarith [mul_le_mul_of_nonneg_left hs hq.le]

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K (Module.Dual K V))] in
lemma uniform_incidence_sum (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) :
    (∑ y∈T,∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass S x)=
      (incidenceCount S T:ℝ)/S.card := by
  simp_rw [uniform_sum]
  rw [←sum_div]
  congr 1
  unfold incidenceCount
  push_cast
  apply sum_congr rfl
  intro y _
  congr 1
  apply congrArg Finset.card
  ext x
  simp only [mem_inter,mem_filter,mem_univ,true_and]
  tauto

theorem scheduled_validation {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S X W : Finset (Projectivization K V)) (hS : S.Nonempty) (hX : X.Nonempty)
    (hXS : X⊆S) (hXW : X⊆W)
    (T U : Finset (Projectivization K (Module.Dual K V))) (hT : T.Nonempty) (hTU : T⊆U)
    (C a : ℝ) (hC : 1≤C) (hcap : (S.card:ℝ)≤C*X.card)
    (hratio : (W.card:ℝ)≤exp a*X.card)
    (hsparse : (incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(10000*C*Nat.card K)) :
    let q : ℝ := Nat.card K
    let h := scheduleLength q U.card T.card
    let m := scheduleCutoff q a h
    let M := 1000*C*q^(n+3)/S.card
    let accept := implementAccept X (GoodCap SharpLogRamsey.Incidence.Incident q U T M)
    (9/10:ℝ)≤prob (uniformMass X) h (GoodCap SharpLogRamsey.Incidence.Incident q U T M) ∧
    1-PublicTables.integral (rowLaw W (hX.mono hXW) h) accept (fun _ => 1) m≤exp (-q) ∧
    (∀ y,PublicTables.integral (rowLaw W (hX.mono hXW) h) accept
      (fun z => if ¬pass SharpLogRamsey.Incidence.Incident q z y then 1 else 0) m≤
        6*C*q*(∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass S x)) := by
  dsimp only
  let q : ℝ := Nat.card K
  let h := scheduleLength q U.card T.card
  let m := scheduleCutoff q a h
  let M := 1000*C*q^(n+3)/S.card
  have hq : 0<q := by
    change 0 < (Nat.card K:ℝ)
    exact_mod_cast (Nat.card_pos : 0<Nat.card K)
  have hs : (0:ℝ)<S.card := by exact_mod_cast card_pos.mpr hS
  have hx : (0:ℝ)<X.card := by exact_mod_cast card_pos.mpr hX
  have hw : (0:ℝ)<W.card := by exact_mod_cast card_pos.mpr (hX.mono hXW)
  have ht : (0:ℝ)<T.card := by exact_mod_cast card_pos.mpr hT
  have htu : (T.card:ℝ)≤U.card := by exact_mod_cast card_le_card hTU
  have hC0 : 0<C := by linarith
  have hsp : (incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20*Nat.card K) := by
    apply hsparse.trans
    gcongr
    have hqn : (0:ℝ)<Nat.card K := hq
    nlinarith
  have hprod := sparse_product_bound_two hdim S T hsp
  have hsize := scheduleLength_size hq ht htu hs hx hC hcap hprod (pow_nonneg hq.le (n+3))
  have hinc : (incidenceCount X T:ℝ)≤(incidenceCount S T:ℝ) := by
    unfold incidenceCount
    push_cast
    apply sum_le_sum
    intro y _
    exact_mod_cast card_le_card (filter_subset_filter _ hXS)
  have hsp' : (∑ y∈T,∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass X x)≤
      (T.card:ℝ)/(10000*q) := by
    rw [uniform_incidence_sum]
    apply (div_le_iff₀ hx).mpr
    apply hinc.trans (hsparse.trans _)
    apply (div_le_iff₀ (by positivity : 0<10000*C*(Nat.card K:ℝ))).mpr
    have he : (T.card:ℝ)/(10000*q)*X.card*(10000*C*Nat.card K)=C*X.card*T.card := by
      dsimp [q]; field_simp [show (Nat.card K:ℝ) ≠ 0 from hq.ne']
    rw [he]
    nlinarith only [mul_le_mul_of_nonneg_right hcap ht.le]
  have hh : 0<h := scheduleLength_pos hq ht htu
  have hM : 0<M := by dsimp [M]; positivity
  have hg := projective_ideal_acceptance hdim X hX U T hT h hh M hM hsize hsp'
  have hsearch := scheduleCutoff_search hq hx hw hratio h
  have hval := projective_public_validation hdim X W hX (hX.mono hXW) hXW U T hT h hh M hM hsize hsp' m hsearch
  refine ⟨hg,hval.1,?_⟩
  intro y
  have habs := original_exclusion X S W hX hS (hX.mono hXW) hXS hXW
    C⁻¹ (inv_pos.mpr hC0) ((inv_mul_le_iff₀ hC0).mpr hcap)
    h hh (GoodCap SharpLogRamsey.Incidence.Incident q U T M) hg SharpLogRamsey.Incidence.Incident q hq y m
  simpa only [div_inv_eq_mul] using habs

end
end SharpLogRamsey.Validation

end

end OAI
