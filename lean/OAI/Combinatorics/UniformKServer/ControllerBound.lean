import Mathlib
import OAI.Combinatorics.UniformKServer.OffsetSuffix
import OAI.Combinatorics.UniformKServer.EpochTape
import OAI.Combinatorics.UniformKServer.ControllerGroups

namespace OAI

noncomputable section
                                      
section

namespace UniformKServer.ControllerBound
open EpochShadow EpochExpectation EpochPartition TapeController
variable {n k b M R : ℕ} [NeZero k] (hk2 : 2≤k) (d : RationalMetric n)
  (u : Configuration n k) (hu : Function.Injective u)
  (N : BState n k→Fin n→Fin k→ℕ) (hN : ∀s r,∑j,N s r j=2^b)
  (hLazy : ∀s r j,(∃i,s.2 i=r)→s.2 j≠r→N s r j=0)
  (D δ A E : ℝ) (hD : 0≤D) (hδ : 0≤δ) (hA : 0≤A)
  (hdiam : ∀x y,(d.distance x y:ℝ)≤D)
  (hsep : ∀x y,x≠y→δ≤(d.distance x y:ℝ))
  (hcap : R*(k+1)*D≤(M+1)*δ)
  (hTable : ∀w : List (Fin n),w.length≤horizon k M→
    BitSampling.mean (BitSampling.runCost N hN next (charge d) ([],u) w)≤
      A*offlineCost d u w+E+D)

include hk2 hu hLazy hD hδ hA hdiam hsep hcap hTable in
theorem epoch (raw : List (Fin n)) (hR : blockCount (k:=k) ∅ raw≤R)
    (s c : Configuration n k) (g : History n k) (hg : g.map Prod.fst=raw) :
    BitSampling.mean (fun coins : Tape k M b=>costAlong d s
      (EpochControl.runTrace (NeZero.pos k) M (selector N hN (extend coins)) (EpochControl.initial u) raw))≤
      2*A*costAlong d c g+(2*A+1)*k*D+2*E+2*D := by
  simp_rw [EpochControl.initial_trace]
  change BitSampling.mean (fun coins : Tape k M b=>
    costAlong d s (EpochTape.fullTrace (NeZero.pos k) M N hN u raw coins))≤_
  rw [EpochTape.full_mean]
  exact (OffsetComparison.comparison (NeZero.pos k) hk2 d N hN hLazy u s c hu M R
    D δ A E hD hδ hA hdiam hsep hcap hTable raw hR g hg).2

include hk2 hu hLazy hD hδ hA hdiam hsep hcap hTable in
theorem groups (es : List (List (Fin n))) (hR : ∀e∈es,blockCount (k:=k) ∅ e≤R)
    (s c : Configuration n k) (g : History n k) (hg : g.map Prod.fst=es.flatten) :
    groupExpected (M:=M) (NeZero.pos k) d u N hN s es≤
      2*A*costAlong d c g+((2*A+1)*k*D+2*E+2*D)*es.length := by
  induction es generalizing s c g with
  | nil=>
    have hgn : g=[] := List.map_eq_nil_iff.mp hg
    simp [groupExpected,hgn,costAlong]
  | cons e es ih=>
    obtain ⟨g₁,g₂,rfl,hg₁,hg₂⟩:=RawBlockCharge.split_history g e es.flatten hg
    have htail:=ih (fun e he=>hR e (by simp [he]))
    have hep:=epoch hk2 d u hu N hN hLazy D δ A E hD hδ hA hdiam hsep hcap hTable
      e (hR e (by simp)) s c g₁ hg₁
    let trace := fun coins : Tape k M b=>
      EpochControl.runTrace (NeZero.pos k) M (selector N hN (extend coins)) (EpochControl.initial u) e
    have hm:=EpochExpectation.mean_mono
      (fun coins : Tape k M b=>costAlong d s (trace coins)+
        groupExpected (M:=M) (NeZero.pos k) d u N hN (finish s (trace coins)) es)
      (fun coins : Tape k M b=>costAlong d s (trace coins)+
        (2*A*costAlong d (finish c g₁) g₂+((2*A+1)*k*D+2*E+2*D)*es.length))
      (fun coins=>add_le_add (le_refl _) (htail _ (finish c g₁) g₂ hg₂))
    simp only [BitSampling.mean_add,BitSampling.mean_const] at hm
    change BitSampling.mean _≤_
    change BitSampling.mean (fun coins=>costAlong d s (trace coins))≤_ at hep
    rw [BitSampling.mean_add,RawBlockCharge.cost_append]
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith

include hk2 hu hLazy hD hδ hA hdiam hsep hcap hTable in
theorem suffix (hR : 0<R) (hE : 0≤E)
    (hpay : (2*A+1)*k*D+2*E+2*D≤(2*A+4)*R*δ)
    (pre w : List (Fin n)) (original actual : Configuration n k) :
    TapeController.expected (NeZero.pos k) hR d u N hN (TapeController.initial (M:=M) hR u) actual w≤
      (4*A+4)*offlineCost d original (pre++w)+((2*A+1)*k*D+2*E+2*D) := by
  rw [expected_epochs]
  let K : ℝ := (2*A+1)*k*D+2*E+2*D
  have hK : 0≤K := by dsimp [K];positivity
  obtain ⟨g,hg,hcost⟩:=OfflineDynamic.optRat_attained d original (pre++w)
  rw [←OfflineDynamic.offline_eq_optRat] at hcost
  obtain ⟨gp,gw,rfl,hgp,hgw⟩:=RawBlockCharge.split_history g pre w hg
  have hcostw : costAlong d (finish original gp) gw≤offlineCost d original (pre++w) := by
    rw [←hcost,RawBlockCharge.cost_append]
    exact le_add_of_nonneg_left (OffsetSuffix.cost_nonneg d original gp)
  have he:=groups hk2 d u hu N hN hLazy D δ A E hD hδ hA hdiam hsep hcap hTable
    (epochs k R hR w) (epoch_blocks k R hR w) actual (finish original gp) gw
    (by rw [epochs_flatten];exact hgw)
  have hc:=epoch_charge (NeZero.pos k) d R hR δ hδ hsep pre w original
  have hc' : (((epochs k R hR w).length-1:ℕ):ℝ)*K≤(2*A+4)*offlineCost d original (pre++w) := by
    have hh:=mul_le_mul_of_nonneg_left hpay
      (show (0:ℝ)≤(((epochs k R hR w).length-1:ℕ):ℝ) by positivity)
    have ht:=mul_le_mul_of_nonneg_left hc (show 0≤2*A+4 by positivity)
    dsimp [K]
    nlinarith only [hh,ht]
  have hn : (epochs k R hR w).length≤(epochs k R hR w).length-1+1 := by omega
  have hn' : ((epochs k R hR w).length:ℝ)≤(((epochs k R hR w).length-1:ℕ):ℝ)+1 := by exact_mod_cast hn
  have hcount:=mul_le_mul_of_nonneg_left hn' hK
  have hcompare:=mul_le_mul_of_nonneg_left hcostw (show 0≤2*A by positivity)
  change groupExpected (M:=M) (NeZero.pos k) d u N hN actual _≤(4*A+4)*offlineCost d original (pre++w)+K
  change groupExpected (M:=M) (NeZero.pos k) d u N hN actual _≤
    2*A*costAlong d (finish original gp) gw+K*(epochs k R hR w).length at he
  nlinarith only [he,hcount,hc',hcompare]

end UniformKServer.ControllerBound

end


end

end OAI
