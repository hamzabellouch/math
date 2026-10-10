import Mathlib
import OAI.Combinatorics.UniformKServer.RawSound
import OAI.Combinatorics.UniformKServer.ControllerBound
import OAI.Combinatorics.UniformKServer.RawAccepted
import OAI.Combinatorics.UniformKServer.OffsetInstance

namespace OAI

noncomputable section
                                        
section

namespace UniformKServer.RawControllerCost
open RawArithmetic RawCertificate EpochExpectation
variable {n k mult : ℕ} [NeZero k] (hk : 2≤k) (hkn : k≤n)
  (hm : PartitionTree.absoluteRate≤(mult:ℝ)) (d : RationalMetric n) (draw : List Q)
  (hd : ∀x y : Fin n,value (RawTable.dist n draw x.val y.val)=d.distance x y)
  (v : Certificate) (hv : verify mult (n,k,draw) v=true)

abbrev u : Configuration n k := fun j=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩

omit [NeZero k] in
theorem u_injective : Function.Injective (u hkn) := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin n=>x.val) h)

noncomputable def N : BState n k→Fin n→Fin k→ℕ :=
  RawRows.complete (NeZero.pos k) (horizon k (cap v)) (bits v) (table v)

include hd hv in
theorem total : ∀s r,∑j,N (n:=n) (k:=k) v s r j=2^(bits v) :=
  RawRows.total (NeZero.pos k) (RawAccepted.spec d draw hd hv).rows

include hd hv in
theorem lazy : ∀s r j,(∃i,s.2 i=r)→s.2 j≠r→N (n:=n) (k:=k) v s r j=0 :=
  RawRows.forbidden (NeZero.pos k) (RawAccepted.spec d draw hd hv).rows

noncomputable def expected (s : Configuration n k) (w : List (Fin n)) : ℝ :=
  TapeController.expected (NeZero.pos k) (RawAccepted.spec d draw hd hv).numbers.restart_pos
    d (u hkn) (N v) (total d draw hd v hv)
    (TapeController.initial (M:=cap v) (RawAccepted.spec d draw hd hv).numbers.restart_pos (u hkn)) s w

def slope : ℝ := (mult:ℝ)*(ell v)^2

def endpoint : ℝ := (2*slope (mult:=mult) v+1)*k*(value (diam v):ℝ)+
  2*(restart v)*(value (sep v):ℝ)+2*(value (diam v):ℝ)

omit [NeZero k] in
theorem endpoint_nonneg : 0≤endpoint (k:=k) (mult:=mult) v := by
  have hD : (0:ℝ)≤(value (diam v):ℝ) := by exact_mod_cast value_nonneg (diam v)
  have hδ : (0:ℝ)≤(value (sep v):ℝ) := by exact_mod_cast value_nonneg (sep v)
  unfold endpoint slope
  positivity

include hk hd hv in
theorem suffix (pre w : List (Fin n)) (original actual : Configuration n k) :
    expected hkn d draw hd v hv actual w≤
      (4*slope (mult:=mult) v+4)*offlineCost d original (pre++w)+endpoint (k:=k) (mult:=mult) v := by
  have hp:=RawAccepted.spec d draw hd hv
  let D : ℝ := value (diam v)
  let δ : ℝ := value (sep v)
  let A : ℝ := slope (mult:=mult) v
  let E : ℝ := (restart v)*δ
  have hD : 0≤D := by dsimp [D];exact_mod_cast value_nonneg (diam v)
  have hδ : 0≤δ := by dsimp [δ];exact_mod_cast hp.numbers.sep_pos.le
  have hA : 0≤A := by dsimp [A,slope];positivity
  have hE : 0≤E := by dsimp [E];positivity
  have hdiam : ∀x y,(d.distance x y:ℝ)≤D := by intro x y;dsimp [D];exact_mod_cast hp.diam_bound x y
  have hsep : ∀x y,x≠y→δ≤(d.distance x y:ℝ) := by intro x y h;dsimp [δ];exact_mod_cast hp.sep_bound x y h
  have hcap : (restart v:ℝ)*(k+1)*D≤(cap v+1:ℝ)*δ := by dsimp [D,δ];exact_mod_cast hp.numbers.cap_bound
  have hrestart : (k:ℝ)*D≤(restart v:ℝ)*δ := by dsimp [D,δ];exact_mod_cast hp.numbers.restart_bound
  have hpay : (2*A+1)*k*D+2*E+2*D≤(2*A+4)*(restart v)*δ := by
    have hk' : (2:ℝ)≤k := by exact_mod_cast hk
    have hb:=mul_le_mul_of_nonneg_left hrestart (by positivity : 0≤2*A+1)
    dsimp [E]
    nlinarith [mul_le_mul_of_nonneg_right hk' hD]
  have ht : ∀w : List (Fin n),w.length≤horizon k (cap v)→
      BitSampling.mean (BitSampling.runCost (N v) (total d draw hd v hv)
        EpochExpectation.next (EpochExpectation.charge d) ([],u hkn) w)≤
        A*offlineCost d (u hkn) w+E+D := by
    intro w hw
    rw [BitSampling.bit_path_mean]
    have hh:=RawSound.table_bound hkn d draw hd (diam v) (sep v) (table v) hp.rows hp.budget w hw
    have hn : @RawExpansion.next n k = @EpochExpectation.next n k := rfl
    have hc : @RawExpansion.charge n k d = @EpochExpectation.charge n k d := rfl
    rw [hn,hc] at hh
    simpa only [A,slope,E,D,δ,N,u,Nat.cast_mul,Nat.cast_pow,add_assoc] using hh
  have hh:=ControllerBound.suffix hk d (u hkn) (u_injective hkn) (N v)
    (total d draw hd v hv) (lazy d draw hd v hv) D δ A E hD hδ hA hdiam hsep hcap ht
    hp.numbers.restart_pos hE hpay pre w original actual
  simpa only [expected,endpoint,A,D,δ,E,mul_assoc] using hh

include hm hk hd hv in
omit [NeZero k] in
theorem coefficient_bound : 4*slope (mult:=mult) v+4≤
    OffsetInstance.coefficient mult*(Real.log (k+1))^2 := by
  have he:=(RawAccepted.spec d draw hd hv).numbers.ell_eq
  have hh:=OffsetInstance.coefficient_bound mult hm hk
  simpa only [OffsetInstance.slope,OffsetLP.slope,slope,he,Rat.cast_mul,Rat.cast_natCast,Rat.cast_pow] using hh

noncomputable def delayed (s : Configuration n k) (delay : ℕ) (w : List (Fin n)) : ℝ :=
  let gp:=ComputedInstance.prefixTrace (w.take delay)
  costAlong d s gp+expected hkn d draw hd v hv (UniformKServer.finish s gp) (w.drop delay)

include hk hm hd hv in
theorem delayed_bound (s : Configuration n k) (delay : ℕ) :
    ∃B : ℝ,0≤B ∧ ∀w : List (Fin n),delayed hkn d draw hd v hv s delay w≤
      OffsetInstance.coefficient mult*(Real.log (k+1))^2*offlineCost d s w+B := by
  let B : ℝ := (delay:ℝ)*(value (diam v):ℝ)+endpoint (k:=k) (mult:=mult) v
  have hp:=RawAccepted.spec d draw hd hv
  have hD : (0:ℝ)≤(value (diam v):ℝ) := by exact_mod_cast value_nonneg (diam v)
  refine ⟨B,add_nonneg (mul_nonneg (Nat.cast_nonneg _) hD) (endpoint_nonneg v),?_⟩
  intro w
  have he:=suffix hk hkn d draw hd v hv (w.take delay) (w.drop delay) s
    (UniformKServer.finish s (ComputedInstance.prefixTrace (w.take delay)))
  rw [List.take_append_drop] at he
  have ht:=OffsetInstance.history_diameter d s (ComputedInstance.prefixTrace (w.take delay))
    (value (diam v):ℝ) (fun x y=>by exact_mod_cast hp.diam_bound x y)
  have hl : (ComputedInstance.prefixTrace (k:=k) (w.take delay)).length≤delay := by
    simp [ComputedInstance.prefixTrace,List.length_take]
  have hb:=mul_le_mul_of_nonneg_right (show ((ComputedInstance.prefixTrace (k:=k) (w.take delay)).length:ℝ)≤delay by exact_mod_cast hl) hD
  have ho : 0≤offlineCost d s w := by
    rw [OfflineDynamic.offline_eq_optRat]
    exact_mod_cast EffectiveLP.opt_nonneg d s w
  have hc:=mul_le_mul_of_nonneg_right (coefficient_bound hk hm d draw hd v hv) ho
  unfold delayed
  dsimp [B]
  linarith

end UniformKServer.RawControllerCost

end


end

end OAI
