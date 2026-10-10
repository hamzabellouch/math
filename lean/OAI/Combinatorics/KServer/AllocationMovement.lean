import Mathlib
import OAI.Combinatorics.KServer.OutputRules

namespace OAI

/-! Degree-independent movement algebra, allowing a zero simplex on an empty
active set and using the original fixed universe of star coordinates. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.OutputDynamics
variable {J:Type*} [Fintype J]
attribute [local instance] Classical.propDecidable Classical.decEq

lemma holesI_movement_subprob {R R':ℝ} {a a':J→ℝ} (hR':0≤R')
    (ha:∀ i,0≤a i) (hsa:(∑ i,a i)≤1):
    variation (holesI R' a') (holesI R a)≤|R'-R|+R'*variation a' a:=by
  calc _≤∑ i,(R'*|a' i-a i|+|R'-R| *a i):=by
        apply sum_le_sum
        intro i _
        change |R'*a' i-R*a i|≤_
        calc _=|R'*(a' i-a i)+(R'-R)*a i|:=by congr 1;ring
          _≤|R'*(a' i-a i)|+|(R'-R)*a i|:=abs_add_le _ _
          _=_:=by rw [abs_mul,abs_mul,abs_of_nonneg hR',abs_of_nonneg (ha i)]
      _=R'*variation a' a+|R'-R| *(∑ i,a i):=by
        rw [sum_add_distrib,←mul_sum,←mul_sum];rfl
      _≤_:=by nlinarith [mul_le_mul_of_nonneg_left hsa (abs_nonneg (R'-R))]

lemma outputI_movement_subprob {d d' a a':J→ℝ} {q q':ℝ}
    (ha:∀ i,0≤a i) (hsa:(∑ i,a i)≤1):
    variation (outputI d' q' a') (outputI d q a)≤
      |q'-q|+2*variation d' d+excess d' q'*variation a' a:=by
  have ho:=output_from_holes_movement d d' (holesI (excess d q) a) (holesI (excess d' q') a')
  have hh:=holesI_movement_subprob (R:=excess d q) (a':=a') (excess_nonneg d' q') ha hsa
  have he:=excess_lipschitz d' d q' q
  change variation (outputI d' q' a') (outputI d q a)≤_ at ho
  linarith

lemma variation_divide (o:J) (x y:J→ℝ):
    variation x y=|x o-y o|+∑ i∈univ.erase o,|x i-y i|:=by
  rw [variation,←sum_erase_add _ _ (mem_univ o),add_comm]

lemma restricted_variation_le (o:J) (x y:J→ℝ):
    (∑ i∈univ.erase o,|x i-y i|)≤variation x y:=by
  rw [variation_divide o]
  linarith [abs_nonneg (x o-y o)]

/-- The same residual formula as Rule II on a fixed star universe. -/
def residual (o:J) (d:J→ℝ) (q D:ℝ) (w:J→ℝ):J→ℝ:=
  fun i=>if i=o then min (d o) (q-∑ j∈univ.erase o,(d j-D*w j)) else d i-D*w i

lemma residual_movement (o:J) {d d' w w':J→ℝ} {q q' D D' Cw:ℝ}
    (hD':0≤D') (hw:∀ i,0≤w i) (hws:(∑ i,w i)≤Cw):
    variation (residual o d' q' D' w') (residual o d q D w)≤
      |q'-q|+2*variation d' d+2*D'*variation w' w+2*Cw*|D'-D|:=by
  let s:J→ℝ:=fun i=>d i-D*w i
  let s':J→ℝ:=fun i=>d' i-D'*w' i
  have hscaled:=scaled_movement (D:=D) hD' hw hws (w':=w')
  have hside:=output_from_holes_movement d d' (fun i=>D*w i) (fun i=>D'*w' i)
  change variation s' s≤_ at hside
  have hdom: |min (d' o) (q'-∑ j∈univ.erase o,s' j)-min (d o) (q-∑ j∈univ.erase o,s j)|≤
      |d' o-d o|+|q'-q|+∑ j∈univ.erase o,|s' j-s j|:=by
    have hh: |min (d' o) (q'-∑ j∈univ.erase o,s' j)-min (d o) (q-∑ j∈univ.erase o,s j)|≤
        |d' o-d o|+|(q'-∑ j∈univ.erase o,s' j)-(q-∑ j∈univ.erase o,s j)|:=by
      apply (abs_min_sub_min_le_max _ _ _ _).trans
      exact max_le (by linarith [abs_nonneg ((q'-∑ j∈univ.erase o,s' j)-(q-∑ j∈univ.erase o,s j))])
        (by linarith [abs_nonneg (d' o-d o)])
    have he:|(q'-∑ j∈univ.erase o,s' j)-(q-∑ j∈univ.erase o,s j)|≤
        |q'-q|+∑ j∈univ.erase o,|s' j-s j|:=by
      calc _=|(q'-q)-((∑ j∈univ.erase o,s' j)-∑ j∈univ.erase o,s j)|:=by congr 1;ring
        _≤|q'-q|+|((∑ j∈univ.erase o,s' j)-∑ j∈univ.erase o,s j)|:=abs_sub _ _
        _≤_:=by rw [←sum_sub_distrib]
                exact add_le_add le_rfl (abs_sum_le_sum_abs (fun j:J => s' j-s j) (univ.erase o))
    linarith
  have hs:∑ i∈univ.erase o,|residual o d' q' D' w' i-residual o d q D w i|=
      ∑ i∈univ.erase o,|s' i-s i|:=by
    apply sum_congr rfl
    intro i hi
    simp only [residual,ite_eq_right (mem_erase.mp hi).1,s,s']
  rw [variation_divide o,hs]
  simp only [residual,ite_true]
  change |min (d' o) (q'-∑ j∈univ.erase o,s' j)-min (d o) (q-∑ j∈univ.erase o,s j)|+_≤_
  have hsum: (∑ i∈univ.erase o,|s' i-s i|)≤
      (∑ i∈univ.erase o,|d' i-d i|)+D'*variation w' w+Cw*|D'-D|:=by
    have hp: (∑ i∈univ.erase o,|s' i-s i|)≤
        (∑ i∈univ.erase o,|d' i-d i|)+(∑ i∈univ.erase o,|D'*w' i-D*w i|):=by
      rw [←sum_add_distrib]
      apply sum_le_sum
      intro i _
      dsimp only [s,s']
      calc _=|(d' i-d i)-(D'*w' i-D*w i)|:=by congr 1;ring
        _≤_:=abs_sub _ _
    linarith [restricted_variation_le o (fun i=>D'*w' i) (fun i=>D*w i)]
  rw [variation_divide o d' d]
  linarith [abs_nonneg (d' o-d o)]
end KServer.OutputDynamics

end


/-! Literal residual-hole mass and switch estimates on the fixed star universe.
These bounds also cover empty side sets and zero active masses. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.OutputDynamics
attribute [local instance] Classical.propDecidable Classical.decEq
variable {J:Type*} [Fintype J]

def residualHoles (o:J) (d:J→ℝ) (q D:ℝ) (w:J→ℝ):J→ℝ:=
  fun i=>d i-residual o d q D w i

lemma residualHoles_nonneg (o:J) (d:J→ℝ) (q:ℝ) {D:ℝ} {w:J→ℝ}
    (hD:0≤D) (hw:∀ i,0≤w i):∀ i,0≤residualHoles o d q D w i:=by
  intro i
  by_cases hi:i=o
  · subst i
    simp only [residualHoles,residual,ite_true]
    exact sub_nonneg.mpr (min_le_left _ _)
  · simp only [residualHoles,residual,ite_eq_right hi,sub_sub_cancel]
    exact mul_nonneg hD (hw i)

lemma residualHoles_mass (o:J) (d:J→ℝ) (q:ℝ) {D Cw:ℝ} {w:J→ℝ}
    (hD:0≤D) (hw:∀ i,0≤w i) (hws:(∑ i,w i)≤Cw):
    (∑ i,residualHoles o d q D w i)≤excess d q+Cw*D:=by
  have he: (∑ i,d i)-q≤excess d q:=le_max_left _ _
  have hn:=excess_nonneg d q
  have hside:0≤D*(∑ i∈univ.erase o,w i):=mul_nonneg hD (sum_nonneg fun i _=>hw i)
  have hd:residualHoles o d q D w o≤excess d q:=by
    simp only [residualHoles,residual,ite_true]
    have hs:(∑ i,d i)=(∑ i∈univ.erase o,d i)+d o:=
      (sum_erase_add univ d (mem_univ o)).symm
    rw [hs] at he
    have hx:d o-excess d q≤ min (d o) (q-∑ j∈univ.erase o,(d j-D*w j)):=by
      apply le_min
      · linarith
      · rw [sum_sub_distrib,←mul_sum]
        linarith
    linarith
  have hs:(∑ i∈univ.erase o,residualHoles o d q D w i)=D*(∑ i∈univ.erase o,w i):=by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    simp only [residualHoles,residual,ite_eq_right (mem_erase.mp hi).1,sub_sub_cancel]
  have hsub:(∑ i∈univ.erase o,w i)≤Cw:=by
    apply le_trans _ hws
    exact sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun i _ _=>hw i)
  rw [←sum_erase_add _ _ (mem_univ o),hs]
  nlinarith [mul_le_mul_of_nonneg_left hsub hD]

lemma residual_eq_sub_holes (o:J) (d:J→ℝ) (q D:ℝ) (w:J→ℝ):
    residual o d q D w=(fun i=>d i-residualHoles o d q D w i):=by
  funext i
  dsimp only [residualHoles]
  ring

lemma holesI_mass_subprob {R:ℝ} {a:J→ℝ} (hR:0≤R) (hsa:(∑ i,a i)≤1):
    (∑ i,holesI R a i)≤R:=by
  simp only [holesI,←mul_sum]
  nlinarith [mul_le_mul_of_nonneg_left hsa hR]

lemma downcross_fixed (o:J) {d d' a w':J→ℝ} {q q' D':ℝ}
    (hD':0≤D') (ha:∀ i,0≤a i) (hsa:(∑ i,a i)≤1)
    (hw':∀ i,0≤w' i) (hws:(∑ i,w' i)≤16) (hr:excess d' q'≤10*D'):
    variation (residual o d' q' D' w') (outputI d q a)≤
      |q'-q|+2*variation d' d+36*D':=by
  have hv:=variation_le_mass (holesI_nonneg (excess_nonneg d q) ha)
    (residualHoles_nonneg o d' q' hD' hw')
  have hm:=holesI_mass_subprob (excess_nonneg d q) hsa
  have hm':=residualHoles_mass o d' q' hD' hw' hws
  have he:=excess_lipschitz d' d q' q
  have ho:=output_from_holes_movement d d' (holesI (excess d q) a) (residualHoles o d' q' D' w')
  rw [←residual_eq_sub_holes] at ho
  change variation (residual o d' q' D' w') (outputI d q a)≤_ at ho
  linarith [neg_le_abs (excess d' q'-excess d q)]

lemma upcross_fixed (o:J) {d d' a' w:J→ℝ} {q q' D D' S':ℝ}
    (hD:0≤D) (ha':∀ i,0≤a' i) (hsa:(∑ i,a' i)≤1)
    (hw:∀ i,0≤w i) (hws:(∑ i,w i)≤16)
    (hr:excess d' q'≤10*S') (hreg:D'≤S'/2):
    variation (outputI d' q' a') (residual o d q D w)≤
      |q'-q|+2*variation d' d+28*S'+16*|D'-D|:=by
  have hv:=variation_le_mass (residualHoles_nonneg o d q hD hw)
    (holesI_nonneg (excess_nonneg d' q') ha')
  have hm:=residualHoles_mass o d q hD hw hws
  have hm':=holesI_mass_subprob (excess_nonneg d' q') hsa
  have he:=excess_lipschitz d' d q' q
  have ho:=output_from_holes_movement d d' (residualHoles o d q D w) (holesI (excess d' q') a')
  rw [←residual_eq_sub_holes] at ho
  change variation (outputI d' q' a') (residual o d q D w)≤_ at ho
  linarith [neg_le_abs (excess d' q'-excess d q),neg_le_abs (D'-D)]
end KServer.OutputDynamics

end


/-! Same-rule and full crossing movement bounds for the actual output,
with one unit of parent variation. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
open OutputDynamics
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

lemma alpha_subprob (k:ℝ) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):
    (∑ i,α k P Q t ω i)≤1:=by
  have ha:=(α_mem k P Q t ω).2.1
  split_ifs at ha <;> linarith

lemma error_le_T {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (t:ℕ) (ω:Ω) (hq:size Q t ω≤ k):e k P Q t ω≤ T k P Q t ω:=by
  have hel:1≤ ActualCaps.ell k:=by
    have hh:=Real.log_nonneg (show 1≤ k+1 by linarith)
    unfold ActualCaps.ell
    linarith
  have heb:eb≤ ActualCaps.ell k:=by
    have he:eb≤1:=by norm_num [eb,cb]
    exact he.trans hel
  have he:eb/ActualCaps.ell k≤1:=(div_le_one (ActualCaps.ell_pos hk)).mpr heb
  exact (e_bounds hk P Q t ω hq).2.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he (T_nonneg hk P Q t ω hq))

lemma actual_excess {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q t ω≤ k)
    {q:ℝ} (hp:(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤ q):
    excess (d k P Q t ω) q≤4*S P t ω+T k P Q t ω:=by
  have hb:=beta_range hk Q t ω hq
  have he:=e_bounds hk P Q t ω hq
  have hh:=hole_bound hp (error_sum hk P Q hs t ω hq) (by linarith : 0≤β k Q t ω) he.1
    (fun i=> TrackedCaps.core_nonneg (P i) t ω)
  change excess (d k P Q t ω) q≤β k Q t ω*S P t ω+e k P Q t ω at hh
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_right hb.2 (S_nonneg P t ω))
    (error_le_T hk P Q t ω hq))

lemma excess_ruleI {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q t ω≤ k)
    {q:ℝ} (hp:(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤ q)
    (hr:∀ o,mark P Q t ω=some o→ D P Q t ω/2≤ S P t ω):
    excess (d k P Q t ω) q≤10*S P t ω:=by
  have hh:=actual_excess hk P Q hs t ω hq hp
  have ht:=ruleI_T hk P Q t ω hq hr
  linarith [S_nonneg P t ω]

lemma excess_down {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q t ω≤ k)
    {q:ℝ} (hp:(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤ q)
    (hr:S P t ω≤ D P Q t ω/2):excess (d k P Q t ω) q≤10*D P Q t ω:=by
  linarith [actual_excess hk P Q hs t ω hq hp,(DT_compare hk P Q t ω hq).1,D_nonneg P Q t ω]

lemma outI_movement {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q (t+1) ω≤ k)
    (q q':ℝ) (hp:(∑ i,(n P (t+1) ω i-β k Q (t+1) ω*B P (t+1) ω i+f k P Q (t+1) ω i))≤ q')
    (hr:∀ o,mark P Q (t+1) ω=some o→ D P Q (t+1) ω/2≤ S P (t+1) ω):
    variation (outI k P Q (t+1) ω q') (outI k P Q t ω q)≤
      |q'-q|+2*variation (d k P Q (t+1) ω) (d k P Q t ω)+
      10*S P (t+1) ω*variation (α k P Q (t+1) ω) (α k P Q t ω):=by
  exact (outputI_movement_subprob (α_mem k P Q t ω).1 (alpha_subprob k P Q t ω)).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right (excess_ruleI hk P Q hs (t+1) ω hq hp hr)
      (variation_nonneg _ _)))

lemma outII_movement {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (t:ℕ) (ω:Ω) (q q':ℝ) (o:J):
    variation (outII hk P Q (t+1) ω o q') (outII hk P Q t ω o q)≤
      |q'-q|+2*variation (d k P Q (t+1) ω) (d k P Q t ω)+
      2*D P Q (t+1) ω*variation (side hk P Q (t+1) ω) (side hk P Q t ω)+
      32*|D P Q (t+1) ω-D P Q t ω|:=by
  have hh:=residual_movement o (q:=q) (q':=q') (d:=d k P Q t ω) (d':=d k P Q (t+1) ω)
    (w':=side hk P Q (t+1) ω) (D:=D P Q t ω) (D_nonneg P Q (t+1) ω) (side_mem hk P Q t ω).1 (side_mem hk P Q t ω).2.1
  change variation (outII hk P Q (t+1) ω o q') (outII hk P Q t ω o q)≤_ at hh
  convert hh using 1
  ring

lemma out_downcross {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q (t+1) ω≤ k)
    (q q':ℝ) (o:J)
    (hp:(∑ i,(n P (t+1) ω i-β k Q (t+1) ω*B P (t+1) ω i+f k P Q (t+1) ω i))≤ q')
    (hr:S P (t+1) ω≤ D P Q (t+1) ω/2):
    variation (outII hk P Q (t+1) ω o q') (outI k P Q t ω q)≤
      |q'-q|+2*variation (d k P Q (t+1) ω) (d k P Q t ω)+36*D P Q (t+1) ω:=by
  exact downcross_fixed o (D_nonneg P Q (t+1) ω) (α_mem k P Q t ω).1 (alpha_subprob k P Q t ω)
    (side_mem hk P Q (t+1) ω).1 (side_mem hk P Q (t+1) ω).2.1 (excess_down hk P Q hs (t+1) ω hq hp hr)

lemma out_upcross {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q (t+1) ω≤ k)
    (q q':ℝ) (o:J)
    (hp:(∑ i,(n P (t+1) ω i-β k Q (t+1) ω*B P (t+1) ω i+f k P Q (t+1) ω i))≤ q')
    (hr:2*D P Q (t+1) ω≤ S P (t+1) ω):
    variation (outI k P Q (t+1) ω q') (outII hk P Q t ω o q)≤
      |q'-q|+2*variation (d k P Q (t+1) ω) (d k P Q t ω)+28*S P (t+1) ω+
      16*|D P Q (t+1) ω-D P Q t ω|:=by
  exact upcross_fixed o (D_nonneg P Q t ω) (α_mem k P Q (t+1) ω).1 (alpha_subprob k P Q (t+1) ω)
    (side_mem hk P Q t ω).1 (side_mem hk P Q t ω).2.1
    (excess_ruleI hk P Q hs (t+1) ω hq hp (fun _ _=> by linarith [D_nonneg P Q (t+1) ω]))
    (by linarith)

end KServer.ActualOutput

end


/-! Frozen-history affine payment with bounds on the actual held parameters.
No bound on fictitious off-schedule parameters is needed; the signed edit term
still has to be paid by the concrete coarse schedule. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.AdaptiveMinimization
open KServer.RankTracking
variable {I J Θ : Type*} [Fintype I] [Fintype J]
variable {Ω : Type} [Fintype Ω]

lemma actual_payment_step (F : Family Θ I J) (T : Transport F) {w : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (R : I → FilteredRanks w)
    (θ : ℕ → Ω → Θ) (c : ℕ → Ω → ℝ)
    (H : ℕ → Ω → ℕ) (hH : ∀ i, (R i).history=H)
    (hr : ∀ t ω z, H (t+1) ω=H (t+1) z → H t ω=H t z)
    (hθ : ∀ t ω z, H t ω=H t z → θ t ω=θ t z)
    (hc : ∀ t, Adapted (H t) (c t)) (hcn : ∀ t ω, 0 ≤ c t ω)
    {L : ℝ} (hL : ∀ t ω a, a ∈ F.domain (θ t ω) → ∀ i, |F.coefficient (θ t ω) a i| ≤ L)
    (t : ℕ) :
    avg w (fun ω => c (t+1) ω*movement (state F T θ (rankVector R) c (t+1) ω)
      (state F T θ (rankVector R) c t ω)) ≤
    avg w (fun ω => F.value (θ t ω) (rankVector R t ω) (state F T θ (rankVector R) c t ω))-
    avg w (fun ω => F.value (θ (t+1) ω) (rankVector R (t+1) ω)
      (state F T θ (rankVector R) c (t+1) ω)) +
    L*(∑ i, avg w (fun ω => |(R i).p (t+1) ω-(R i).before (t+1) ω|))+
    avg w (edit F T θ (rankVector R) c t) := by
  let a := state F T θ (rankVector R) c
  have hpoint (ω : Ω) : c (t+1) ω*movement (a (t+1) ω) (a t ω) ≤
      (F.value (θ t ω) (rankVector R t ω) (a t ω)-
        F.value (θ (t+1) ω) (rankVector R (t+1) ω) (a (t+1) ω))+
      (F.value (θ t ω) (beforeVector R (t+1) ω) (a t ω)-
        F.value (θ t ω) (rankVector R t ω) (a t ω))+
      L*(∑ i, |(R i).p (t+1) ω-(R i).before (t+1) ω|)+
      edit F T θ (rankVector R) c t ω := by
    have hm := state_payment F T θ (rankVector R) c t ω (hcn (t+1) ω)
    have hd := (le_abs_self (F.value (θ t ω) (rankVector R (t+1) ω) (a t ω)-
      F.value (θ t ω) (beforeVector R (t+1) ω) (a t ω))).trans
      (F.input_lipschitz (θ t ω) (rankVector R (t+1) ω) (beforeVector R (t+1) ω)
        (a t ω) (hL t ω _ (state_mem F T θ (rankVector R) c t ω)))
    change _ ≤ L*(∑ i, |(R i).p (t+1) ω-(R i).before (t+1) ω|) at hd
    change c (t+1) ω*movement (a (t+1) ω) (a t ω) ≤
      F.value (θ t ω) (rankVector R (t+1) ω) (a t ω)-
      F.value (θ (t+1) ω) (rankVector R (t+1) ω) (a (t+1) ω)+
      edit F T θ (rankVector R) c t ω at hm
    linarith
  have he := avg_mono hw hpoint
  simp only [avg_add,avg_sub,avg_mul,avg_sum_any] at he
  have hf := filtering_zero F T R θ c H hH hr hθ hc t
  rw [avg_sub] at hf
  change avg w (fun ω => F.value (θ t ω) (beforeVector R (t+1) ω) (a t ω))-
    avg w (fun ω => F.value (θ t ω) (rankVector R t ω) (a t ω))=0 at hf
  rw [hf,add_zero] at he
  exact he

/-- The full causal minimizer telescope. The computed signed edit term must be
bounded from the actual coordinate preparation/deletion and coarse schedules;
there is no asserted policy or asserted coarse-budget estimate here. -/
theorem actual_payment (F : Family Θ I J) (T : Transport F) {w : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (R : I → FilteredRanks w)
    (θ : ℕ → Ω → Θ) (c : ℕ → Ω → ℝ)
    (H : ℕ → Ω → ℕ) (hH : ∀ i, (R i).history=H)
    (hr : ∀ t ω z, H (t+1) ω=H (t+1) z → H t ω=H t z)
    (hθ : ∀ t ω z, H t ω=H t z → θ t ω=θ t z)
    (hc : ∀ t, Adapted (H t) (c t)) (hcn : ∀ t ω, 0 ≤ c t ω)
    {L : ℝ} (hL : ∀ t ω a, a ∈ F.domain (θ t ω) → ∀ i, |F.coefficient (θ t ω) a i| ≤ L)
    (n : ℕ) :
    (∑ t ∈ range n, avg w (fun ω => c (t+1) ω*movement
      (state F T θ (rankVector R) c (t+1) ω) (state F T θ (rankVector R) c t ω))) ≤
    avg w (fun ω => F.value (θ 0 ω) (rankVector R 0 ω) (state F T θ (rankVector R) c 0 ω))-
    avg w (fun ω => F.value (θ n ω) (rankVector R n ω) (state F T θ (rankVector R) c n ω))+
    L*(∑ t ∈ range n, ∑ i, avg w (fun ω => |(R i).p (t+1) ω-(R i).before (t+1) ω|))+
    ∑ t ∈ range n, avg w (edit F T θ (rankVector R) c t) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [sum_range_succ]
      have hs := actual_payment_step F T hw R θ c H hH hr hθ hc hcn hL n
      linarith

/-- Uniform endpoint removal: a bound depending only on the fixed finite
family, not on the horizon or its law, contributes at most twice that bound. -/
theorem actual_payment_bounded (F : Family Θ I J) (T : Transport F) {w : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω=1) (R : I → FilteredRanks w)
    (θ : ℕ → Ω → Θ) (c : ℕ → Ω → ℝ)
    (H : ℕ → Ω → ℕ) (hH : ∀ i, (R i).history=H)
    (hr : ∀ t ω z, H (t+1) ω=H (t+1) z → H t ω=H t z)
    (hθ : ∀ t ω z, H t ω=H t z → θ t ω=θ t z)
    (hc : ∀ t, Adapted (H t) (c t)) (hcn : ∀ t ω, 0 ≤ c t ω)
    {L B : ℝ} (hL : ∀ t ω a, a ∈ F.domain (θ t ω) → ∀ i, |F.coefficient (θ t ω) a i| ≤ L)
    (hB : ∀ t ω p a, a ∈ F.domain (θ t ω) → (∀ i, p i ∈ Set.Icc 0 1) → |F.value (θ t ω) p a| ≤ B)
    (n : ℕ) :
    (∑ t ∈ range n, avg w (fun ω => c (t+1) ω*movement
      (state F T θ (rankVector R) c (t+1) ω) (state F T θ (rankVector R) c t ω))) ≤
    L*(∑ t ∈ range n, ∑ i, avg w (fun ω => |(R i).p (t+1) ω-(R i).before (t+1) ω|))+
    (∑ t ∈ range n, avg w (edit F T θ (rankVector R) c t))+2*B := by
  have hb (t : ℕ) (ω : Ω) := hB t ω (rankVector R t ω)
    (state F T θ (rankVector R) c t ω) (state_mem F T θ (rankVector R) c t ω)
    (fun i => (R i).range t ω)
  have htop := avg_mono hw (fun ω => (abs_le.mp (hb 0 ω)).2)
  have hbot := avg_mono hw (fun ω => (abs_le.mp (hb n ω)).1)
  rw [avg_const w hw1] at htop hbot
  have he := actual_payment F T hw R θ c H hH hr hθ hc hcn hL n
  linarith


end KServer.AdaptiveMinimization

end


/-! Dimension-free affine input slope on the actual held simplex parameters. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ScheduledSlope
attribute [local instance] Classical.propDecidable
open AllocationSchedule EpochSchedule SimplexFamilies
variable {J R K : Type} [Fintype J] [DecidableEq J] [Fintype R]

omit [Fintype R] in
lemma coefficient_bound {δ C ell ct : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (hC : 0≤C) (hel : 0<ell) (hct : 0≤ct)
    (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i,0≤x t i)
    (flags : ℕ → J → R → Bool) (t : ℕ)
    (hmax : ∀ i,ct*weight δ x key t i/ell≤1)
    (a : J → ℝ) (ha : a∈ChangingDomains.simplex (activeSet (x t))) (ir : J×R) :
    |coefficient C ell (data hδ hδu C ell ct x key hx flags t) a ir|≤13*C*ell := by
  have heta : ∀ i,ct*weight δ x key t i/ell∈Set.Icc 0 1 := fun i=>
    ⟨div_nonneg (mul_nonneg hct (weight_nonneg δ x key hx t i)) hel.le,hmax i⟩
  have hnn : 0≤13*C*ell := by positivity
  unfold data
  dsimp only
  split
  · split
    · rename_i hn
      have h:=regular_coefficient_bound (activeSet (x t)) (flags t) (weight δ x key t)
        (fun i=>ct*weight δ x key t i/ell)
        (fun i=>weight_regular_one δ x key t i (by simp [hn])) heta hC hel.le ha ir
      exact h.trans (by nlinarith [mul_nonneg hC hel.le])
    · split
      · exact marked_coefficient_bound _ _ _ _ _ _ _ _ heta hC hel.le ha ir
      · simpa only [zeroData,coefficient,ite_true,abs_zero] using hnn
  · simpa only [zeroData,coefficient,ite_true,abs_zero] using hnn

open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile
variable {Ω : Type} [Fintype Ω] {w : Ω → ℝ}

lemma actual_bound {δ C ct k : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (hC : 0≤C) (hct : 0≤ct) (hctu : ct*20002≤1) (hk : 1≤k)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K)
    (hs : ∀ t ω,(∑ i,size (P i) t ω)≤k) (t : ℕ) (ω : Ω)
    (a : J → ℝ) (ha : a∈ChangingDomains.simplex (activeSet (vector cutoff δ P ω t))) (ir : J×R) :
    |coefficient C (1+Real.log (k+1))
      (StarSimplex.input hδ hδu C (1+Real.log (k+1)) ct P key t ω).data a ir|≤
      13*C*(1+Real.log (k+1)) := by
  have hel : 0<1+Real.log (k+1) := by
    have h:=Real.log_nonneg (show 1≤k+1 by linarith)
    linarith
  apply coefficient_bound hδ hδu hC hel hct _ _ (vector_nonneg cutoff δ P ω) _ t _ a ha ir
  intro i
  apply (div_le_iff₀ hel).mpr
  have h:=weight_upper hδ hδu hk (vector cutoff δ P ω) (fun s=>key s ω)
    (vector_nonneg cutoff δ P ω) (fun s=>vector_total hδ hδu P s ω (hs s ω))
    (fun s i hi=>vector_floor hδ hδu P s ω i hi) t i
  have hmul:=mul_le_mul_of_nonneg_left h hct
  have hmul2:=mul_le_mul_of_nonneg_right hctu hel.le
  nlinarith

end KServer.ScheduledSlope

end


/-! Selective parameter charges on the actual size schedule.  In particular a
regular-component edit is charged only to its changed coordinate, and the
marked component is charged to side mass, never to the dominant child. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ScheduleEdits
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseProcess CoarseEpoch AllocationSchedule StarProfile
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w : Ω → ℝ}

omit [DecidableEq J] in
lemma ordinary_reference (x : ℕ→J→ℝ) (key : ℕ→K) (t : ℕ)
    (he : epoch x key t=epoch x key (t+1)) :
    (EpochSchedule.run x key (t+1)).reference=(EpochSchedule.run x key t).reference := by
  have hn:=(epoch_same_iff x key t).mp he
  change ¬EpochSchedule.reset _ _ _ _ _ at hn
  simp only [EpochSchedule.run,EpochSchedule.update,ite_eq_right hn]

omit [DecidableEq J] in
lemma ordinary_mass (x : ℕ→J→ℝ) (key : ℕ→K) (t : ℕ)
    (he : epoch x key t=epoch x key (t+1)) : mass x key (t+1)=mass x key t :=
  congrArg EpochSchedule.total (ordinary_reference x key t he)

omit [DecidableEq J] in
lemma ordinary_mark (x : ℕ→J→ℝ) (key : ℕ→K) (t : ℕ)
    (he : epoch x key t=epoch x key (t+1)) :
    EpochSchedule.dominant (EpochSchedule.run x key (t+1))=
      EpochSchedule.dominant (EpochSchedule.run x key t) :=
  CoarseSide.mark_unchanged ((epoch_same_iff x key t).mp he)

lemma ordinary_weight (δ : ℝ) (x : ℕ→J→ℝ) (key : ℕ→K) (t : ℕ)
    (he : epoch x key t=epoch x key (t+1)) (i : J)
    (hi : EpochSchedule.dominant (EpochSchedule.run x key t)≠some i)
    (hx : x t i=x (t+1) i) : weight δ x key t i=weight δ x key (t+1) i := by
  simp only [weight,ordinary_mark x key t he,ite_eq_right hi,ordinary_mass x key t he,hx]

lemma count_bound {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : R→FilteredRanks w) (t : ℕ) (ω : Ω) :
    TrackedCaps.count P t ω≤40*(active cutoff δ P ω t).value := by
  by_cases hp:0<(active cutoff δ P ω t).value
  · have hc:=(TrackedCaps.domination P (by norm_num : (0:ℝ)∈Set.Icc 0 (1/100:ℝ)) t ω)
    have hn:=TrackedCaps.flex_nonneg P (by norm_num : (0:ℝ)∈Set.Icc 0 (1/100:ℝ)) t ω
    have ha:=(active_accuracy (by norm_num [cutoff] : 0<cutoff) hδ hδu P ω t).1
      ((live_iff hδ hδu P t ω).mp hp)
    linarith
  · have hf:=inactive_flag_false hδ hδu P hp
    have hz:TrackedCaps.count P t ω=0 := by simp [TrackedCaps.count,hf]
    rw [hz]
    exact mul_nonneg (by norm_num) (active_valid cutoff δ P ω t).1

lemma raw_core_bound {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : R→FilteredRanks w) (t : ℕ) (ω : Ω) (p : R→ℝ) (hp:∀ r,p r∈Set.Icc 0 1) :
    (∑ r,if CoreFlags.flag (P r) t ω then p r else 0)≤40*(active cutoff δ P ω t).value := by
  apply le_trans _ (count_bound hδ hδu P t ω)
  apply sum_le_sum
  intro r _
  split_ifs
  · exact (hp r).2
  · rfl

lemma prepared_input_bound {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : J→R→FilteredRanks w) (old : Finset J) (t : ℕ) (ω : Ω)
    (p : J×R→ℝ) (hp:∀ ir,p ir∈Set.Icc 0 1) (i:J) :
    AdaptiveAllocation.preparedInput old (activeSet (vector cutoff δ P ω t))
      (StarSimplex.flags P ω t) p i≤40*vector cutoff δ P ω t i := by
  have hb:=raw_core_bound hδ hδu (P i) t ω (fun r=>p (i,r)) (fun r=>hp (i,r))
  apply le_trans _ hb
  apply sum_le_sum
  intro r _
  simp only [AdaptiveAllocation.preparedFlags,ChangingDomains.syntheticFlags,StarSimplex.flags]
  by_cases hh : i∈old ∧ i∈activeSet (vector cutoff δ P ω t) <;>
    by_cases hf : CoreFlags.flag (P i r) t ω=true <;>
    simp [mem_inter,hh,hf,(hp (i,r)).1]

lemma regular_charge {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : J→R→FilteredRanks w) (key : ℕ→Ω→K) (t : ℕ) (ω : Ω)
    (he : epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1))
    (p : J×R→ℝ) (hp:∀ ir,p ir∈Set.Icc 0 1) (S:Finset J)
    (hS:∀ i∈S,EpochSchedule.dominant (EpochSchedule.run (vector cutoff δ P ω)
      (fun s=>key s ω) t)≠some i) :
    (∑ i∈S,if weight δ (vector cutoff δ P ω) (fun s=>key s ω) t i=
        weight δ (vector cutoff δ P ω) (fun s=>key s ω) (t+1) i then 0 else
      AdaptiveAllocation.preparedInput (activeSet (vector cutoff δ P ω t))
        (activeSet (vector cutoff δ P ω (t+1))) (StarSimplex.flags P ω (t+1)) p i) ≤
    40*(∑ i∈S,CoarseSchedule.charge (active cutoff δ (P i) ω t)
      (active cutoff δ (P i) ω (t+1))) := by
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  split_ifs with hh
  · exact mul_nonneg (by norm_num) (charge_nonneg (active_valid _ _ _ _ _) (active_valid _ _ _ _ _))
  · have hn:(active cutoff δ (P i) ω t).value≠(active cutoff δ (P i) ω (t+1)).value := by
      intro hv
      exact hh (ordinary_weight δ _ _ t he i (hS i hi) hv)
    rw [CoarseSchedule.charge,ite_eq_right hn]
    have hb:=prepared_input_bound hδ hδu P (activeSet (vector cutoff δ P ω t)) (t+1) ω p hp i
    change _≤40*((active cutoff δ (P i) ω t).value+(active cutoff δ (P i) ω (t+1)).value)
    change _≤40*(active cutoff δ (P i) ω (t+1)).value at hb
    linarith [(active_valid cutoff δ (P i) ω t).1]

lemma side_ratio_charge {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (x:ℕ→J→ℝ) (key:ℕ→K) (hx:∀ t i,0≤x t i) (t:ℕ)
    (he:epoch x key t=epoch x key (t+1)) (o:J)
    (ho:EpochSchedule.dominant (EpochSchedule.run x key t)=some o)
    (B:J→ℝ) (hb:∀ i,B i≤40*x (t+1) i) :
    (if sideRatio δ x key t=sideRatio δ x key (t+1) then 0 else
      (∑ i∈univ.erase o,B i)+(sideRatio δ x key t+sideRatio δ x key (t+1))*(∑ i,B i)) ≤
    124*CoarseSide.charge δ (CoarseSide.sideInput x key) (CoarseSide.epochReset x key) t := by
  have hn:=(epoch_same_iff x key t).mp he
  have hm:=ordinary_mass x key t he
  have ho':EpochSchedule.dominant (EpochSchedule.run x key (t+1))=some o :=
    (ordinary_mark x key t he).trans ho
  have hA : 0 < mass x key t :=dominant_mass_pos ho
  have hs:0≤CoarseSide.sideInput x key t:=CoarseSide.side_nonneg (hx t) _
  have hs':0≤CoarseSide.sideInput x key (t+1):=CoarseSide.side_nonneg (hx (t+1)) _
  have hch:0≤CoarseSide.charge δ (CoarseSide.sideInput x key) (CoarseSide.epochReset x key) t := by
    unfold CoarseSide.charge
    split_ifs
    · exact add_nonneg hs hs'
    · rfl
  split_ifs with hu
  · exact mul_nonneg (by norm_num) hch
  · have hU:sideHeld δ x key t≠sideHeld δ x key (t+1) := by
      intro hh
      exact hu (by simp only [sideRatio,hm,hh])
    have ht:factorTest id δ (CoarseSide.sideInput x key (t+1)) (sideHeld δ x key t) := by
      by_contra hh
      apply hU
      symm
      change CoarseSide.held δ _ _ (t+1)=CoarseSide.held δ _ _ t
      change ¬factorTest id δ (CoarseSide.sideInput x key (t+1))
        (CoarseSide.held δ _ _ t) at hh
      rw [CoarseSide.held,ite_eq_right (not_or.mpr ⟨hn,hh⟩)]
    rw [CoarseSide.charge,ite_eq_left ⟨hn,ht⟩]
    have hsn: (∑ i∈univ.erase o,B i)≤40*CoarseSide.sideInput x key (t+1) := by
      change _≤40*CoarseSide.side (x (t+1)) (EpochSchedule.run x key (t+1))
      rw [side_eq_erase _ _ ho',mul_sum]
      exact sum_le_sum fun i _=>hb i
    have htot:(∑ i,B i)≤41*mass x key t := by
      have h:=sum_le_sum (s:=univ) (fun i _=>hb i)
      rw [←mul_sum] at h
      have ha:=(mass_accuracy x key hx (t+1)).2
      rw [hm] at ha
      change EpochSchedule.total (x (t+1))≤_ at ha
      change (∑ i,B i)≤40*EpochSchedule.total (x (t+1)) at h
      linarith
    have hrat : 0 ≤ sideRatio δ x key t+sideRatio δ x key (t+1) :=
      add_nonneg (side_ratio_nonneg δ x key hx t) (side_ratio_nonneg δ x key hx (t+1))
    have hprod:=mul_le_mul_of_nonneg_left htot hrat
    have heq:(sideRatio δ x key t+sideRatio δ x key (t+1))*(41*mass x key t)=
        41*(sideHeld δ x key t+sideHeld δ x key (t+1)) := by
      simp only [sideRatio,hm]
      field_simp [hA.ne']
    rw [heq] at hprod
    have hu0:=(side_held_accuracy hδ x key hx t).2
    have hu1:=(side_held_accuracy hδ x key hx (t+1)).2
    have hUbound:sideHeld δ x key t+sideHeld δ x key (t+1)≤
        2*(CoarseSide.sideInput x key t+CoarseSide.sideInput x key (t+1)) := by
      have hmul:=mul_le_mul_of_nonneg_right (show 1+δ≤2 by linarith) (add_nonneg hs hs')
      nlinarith
    linarith

end KServer.ScheduleEdits

end


/-! Literal all-case pointwise movement, preserving the coefficient one of
parent movement. No probabilistic movement endpoint is assumed here. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar OutputDynamics
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def switchCharge (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=
  RuleSchedule.charge (marked P Q (t+1) ω) (reset P Q (t+1) ω)
    (rule P Q t ω) (S P (t+1) ω) (D P Q (t+1) ω)

lemma switchCharge_nonneg (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):
    0≤ switchCharge P Q t ω:=
  RuleSchedule.charge_nonneg (S_nonneg P (t+1) ω) (D_nonneg P Q (t+1) ω) _ _ _

lemma reset_iff (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):
    reset P Q (t+1) ω=false ↔
      epoch (vector cutoff ds P ω) (fun s=> key Q s ω) t=
      epoch (vector cutoff ds P ω) (fun s=> key Q s ω) (t+1):=by
  simp only [reset,Nat.add_sub_cancel,decide_eq_false_iff_not]
  exact (epoch_same_iff (vector cutoff ds P ω) (fun s=> key Q s ω) t).symm

lemma ordinary_mark (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω)
    (he:reset P Q (t+1) ω=false):mark P Q (t+1) ω=mark P Q t ω:=by
  exact ScheduleEdits.ordinary_mark _ _ t ((reset_iff P Q t ω).mp he)

lemma ordinary_movement {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω)
    (hq:size Q (t+1) ω≤ k) (q q':ℝ)
    (hp:(∑ i,(n P (t+1) ω i-β k Q (t+1) ω*B P (t+1) ω i+f k P Q (t+1) ω i))≤ q')
    (he:reset P Q (t+1) ω=false):
    variation (out hk P Q (t+1) ω q') (out hk P Q t ω q)≤
      |q'-q|+2*variation (d k P Q (t+1) ω) (d k P Q t ω)+
      40*(S P (t+1) ω*variation (α k P Q (t+1) ω) (α k P Q t ω)+
        D P Q (t+1) ω*variation (side hk P Q (t+1) ω) (side hk P Q t ω)+
        |D P Q (t+1) ω-D P Q t ω|+switchCharge P Q t ω):=by
  have hm:=ordinary_mark P Q t ω he
  have hSa:0≤ S P (t+1) ω*variation (α k P Q (t+1) ω) (α k P Q t ω):=
    mul_nonneg (S_nonneg P (t+1) ω) (variation_nonneg _ _)
  have hDw:0≤ D P Q (t+1) ω*variation (side hk P Q (t+1) ω) (side hk P Q t ω):=
    mul_nonneg (D_nonneg P Q (t+1) ω) (variation_nonneg _ _)
  have hJ:=switchCharge_nonneg P Q t ω
  have hD:=abs_nonneg (D P Q (t+1) ω-D P Q t ω)
  cases ho:mark P Q t ω with
  | none=>
    have ho':mark P Q (t+1) ω=none:=hm.trans ho
    have hh:=outI_movement hk P Q hs t ω hq q q' hp (fun _ h=> by rw [ho'] at h; cases h)
    simp only [out,ho,ho']
    linarith
  | some o=>
    have ho':mark P Q (t+1) ω=some o:=hm.trans ho
    have hmarked:marked P Q (t+1) ω=true:=by simp [marked,ho']
    have hu:rule P Q (t+1) ω=RuleSchedule.update (S P (t+1) ω) (D P Q (t+1) ω) (rule P Q t ω):=by
      simp only [rule,RuleSchedule.run,RuleSchedule.step,hmarked,he,ite_true,Bool.false_eq_true,ite_false]
    have hj:switchCharge P Q t ω=
        (if rule P Q (t+1) ω=rule P Q t ω then 0 else
          if rule P Q (t+1) ω then D P Q (t+1) ω else S P (t+1) ω):=by
      simp only [switchCharge,RuleSchedule.charge,hmarked,he,Bool.false_eq_true,ite_false,ite_true,←hu]
    cases hold:rule P Q t ω <;> cases hnew:rule P Q (t+1) ω
    · have hr: D P Q (t+1) ω/2≤ S P (t+1) ω:=by
        have h:=(rule_allowed P Q (t+1) ω).2 hmarked
        simpa only [hnew,Bool.false_eq_true,ite_false] using h
      have hh:=outI_movement hk P Q hs t ω hq q q' hp (fun _ _=> hr)
      simp only [out,ho,ho',hold,hnew,Bool.false_eq_true,ite_false]
      linarith
    · have hr:S P (t+1) ω≤ D P Q (t+1) ω/2:=by
        rw [hold,RuleSchedule.update,RuleSchedule.choose] at hu
        simp only [hnew,Bool.false_eq_true,ite_false] at hu
        exact (of_decide_eq_true hu.symm).le
      have hh:=out_downcross hk P Q hs t ω hq q q' o hp hr
      have hj':switchCharge P Q t ω=D P Q (t+1) ω:=by simpa only [hold,hnew,Bool.true_eq_false,ite_false,ite_true] using hj
      simp only [out,ho,ho',hold,hnew,Bool.false_eq_true,ite_false,ite_true]
      rw [hj']
      linarith [D_nonneg P Q (t+1) ω]
    · have hr:2*D P Q (t+1) ω≤ S P (t+1) ω:=by
        rw [hold,RuleSchedule.update] at hu
        simp only [hnew,ite_true] at hu
        exact (lt_of_not_ge (of_decide_eq_false hu.symm)).le
      have hh:=out_upcross hk P Q hs t ω hq q q' o hp hr
      have hj':switchCharge P Q t ω=S P (t+1) ω:=by simpa only [hold,hnew,Bool.false_eq_true,ite_false] using hj
      simp only [out,ho,ho',hold,hnew,Bool.false_eq_true,ite_false,ite_true]
      rw [hj']
      linarith [S_nonneg P (t+1) ω]
    · have hh:=outII_movement hk P Q t ω q q' o
      simp only [out,ho,ho',hold,hnew,ite_true]
      linarith

end KServer.ActualOutput

end

end OAI
