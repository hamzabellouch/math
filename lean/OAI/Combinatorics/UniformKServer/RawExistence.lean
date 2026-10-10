import Mathlib
import OAI.Combinatorics.UniformKServer.RawMetric
import OAI.Combinatorics.UniformKServer.OffsetInstance
import OAI.Combinatorics.UniformKServer.RawTableWitness

namespace OAI

noncomputable section
                                   
section

namespace UniformKServer.RawExistence
open RawArithmetic RawWords RawTable RawTyped RawCertificate ComputedInstance EffectiveLP

theorem row_bound {n k : ℕ} [NeZero k] (hn : 2≤n) (hk : 2≤k) (hkn : k≤n)
    (mult : ℕ) (hm : PartitionTree.absoluteRate≤(mult:ℝ)) (d : RationalMetric n)
    (w : List (Fin n)) (hw : w.length≤horizon k (OffsetInstance.cap mult hm hn hk hkn d)) :
    BitSampling.rowCost (b:=OffsetTable.bitWidth k (horizon k (OffsetInstance.cap mult hm hn hk hkn d)))
      (OffsetEpoch.counts d (canonical hkn) (OffsetInstance.slope mult k)
        (horizon k (OffsetInstance.cap mult hm hn hk hkn d)))
      RawExpansion.next (RawExpansion.charge d) ([],(canonical hkn).val) w ≤
      (OffsetInstance.slope mult k:ℝ)*offlineCost d (canonical hkn).val w+
        (OffsetInstance.restart mult hm hn hk hkn d:ℝ)*(separation hn d:ℝ)+(diameter hn d:ℝ) := by
  let H:=horizon k (OffsetInstance.cap mult hm hn hk hkn d)
  have hv:=OffsetInstance.valid mult hm hk hkn d H
  obtain ⟨_,_,hN,hlegal,hcost⟩:=OffsetTable.construct d (canonical hkn) (OffsetInstance.slope mult k)
    H hv (diameter hn d:ℝ) (parameters hn (NeZero.pos k) d).1 (parameters hn (NeZero.pos k) d).2.2.1
  have htotal:=OffsetEpoch.total d (canonical hkn) (OffsetInstance.slope mult k) H hv
  have he : BitSampling.rowCost (b:=OffsetTable.bitWidth k H) (OffsetEpoch.counts d (canonical hkn) (OffsetInstance.slope mult k) H)
      RawExpansion.next (RawExpansion.charge d) ([],(canonical hkn).val) w=
      BitSampling.mean (BitSampling.runCost (OffsetTable.counts d (canonical hkn) (OffsetInstance.slope mult k) H)
        hN OffsetTable.next (fun s r j=>(OffsetTable.charge d s r j:ℝ)) ([],canonical hkn) w) := by
    rw [←BitSampling.bit_path_mean _ htotal]
    congr 1
    funext coins
    exact OffsetEpoch.runCost_eq d (canonical hkn) (OffsetInstance.slope mult k) H hv hN hlegal [] (canonical hkn) w coins
  rw [he]
  have hc:=hcost w hw
  have hr:= (OffsetParameters.restart_spec hn hk d (canonical hkn) (OffsetInstance.slope mult k)
    (OffsetInstance.rate_bound mult hm hk)).2.2
  have hr' : (OffsetTable.offset d (canonical hkn) (OffsetInstance.slope mult k) H : ℝ) ≤
    (OffsetInstance.restart mult hm hn hk hkn d:ℝ)*(separation hn d:ℝ) := by exact_mod_cast hr
  exact hc.trans (by linarith)

theorem exists_certificate {n k : ℕ} [NeZero k] (hn : 2≤n) (hk : 2≤k) (hkn : k≤n)
    (mult : ℕ) (hm : PartitionTree.absoluteRate≤(mult:ℝ)) (d : RationalMetric n)
    (draw : List Q) (hd : ∀x y : Fin n,value (dist n draw x.val y.val)=d.distance x y) :
    ∃v : Certificate,verify mult (n,k,draw) v=true := by
  let ell:=Nat.clog 2 (k+1)
  let M:=OffsetInstance.cap mult hm hn hk hkn d
  let H:=UniformKServer.horizon k M
  let R:=OffsetInstance.restart mult hm hn hk hkn d
  let b:=OffsetTable.bitWidth k H
  let A:=OffsetInstance.slope mult k
  let N:=OffsetEpoch.counts d (canonical hkn) A H
  let D:=RawMetric.present (diameter hn d)
  let δ:=RawMetric.present (separation hn d)
  have hp:=parameters hn (NeZero.pos k) d
  have hD : 0≤diameter hn d := by exact_mod_cast hp.1
  have hδ : 0<separation hn d := by exact_mod_cast hp.2.1
  have hDe : value D=diameter hn d := RawMetric.present_eq _ hD
  have hδe : value δ=separation hn d := RawMetric.present_eq _ hδ.le
  have hv:=OffsetInstance.valid mult hm hk hkn d H
  have htotal:=OffsetEpoch.total d (canonical hkn) A H hv
  have hforbid:=OffsetEpoch.forbidden d (canonical hkn) A H hv
  obtain ⟨T,hT⟩:=RawRepresentation.represents H N
  let v : Certificate:=((ell,b,M,R),(D,δ),T)
  refine ⟨v,?_⟩
  have hnums : numbersOK k v=true := by
    have hr:=OffsetParameters.restart_spec hn hk d (canonical hkn) A (OffsetInstance.rate_bound mult hm hk)
    have hc:=OffsetParameters.cap_bound (k:=k) hn d R
    have hend : (R*(k+1):ℚ)*value D≤(M+1:ℚ)*value δ := by
      rw [hDe,hδe]
      exact_mod_cast hc
    simp only [numbersOK,RawCertificate.ell,RawCertificate.cap,RawCertificate.restart,diam,sep,v,
      Bool.and_eq_true_iff]
    refine ⟨⟨⟨⟨⟨⟨decide_eq_true (Nat.clog_pos (by decide : 1<2) (by omega : 1<k+1)),
      decide_eq_true (Nat.pow_pred_clog_lt_self (by decide : 1<2) (by omega : 1<k+1))⟩,
      decide_eq_true (Nat.le_pow_clog (by decide : 1<2) (k+1))⟩,decide_eq_true hr.1⟩,decide_eq_true (RawMetric.present_pos _ hδ)⟩,?_⟩,?_⟩
    · apply decide_eq_true
      apply (le_iff _ _).mpr
      simpa only [value_mul,value_natural,hDe,hδe,R,A,OffsetInstance.restart] using hr.2.1
    · apply decide_eq_true
      apply (le_iff _ _).mpr
      simpa only [value_mul,value_natural,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using hend
  have hbounds : boundsOK n draw D δ=true := by
    apply RawMetric.bounds_ok d draw hd D δ
    · intro x y;rw [hDe];exact_mod_cast hp.2.2.1 x y
    · intro x y h;rw [hδe];exact_mod_cast hp.2.2.2.1 x y h
  have hrows:=RawCompleteness.rows_ok T N hT htotal hforbid
  have htable : tableOK n k H b (mult*ell^2) R draw D δ T=true := by
    apply RawTableWitness.table_ok hkn d draw hd D δ T N hT htotal hforbid
    intro w hw
    have hcanon : (canonical hkn).val=(fun j : Fin k=>(⟨j.val,lt_of_lt_of_le j.isLt hkn⟩:Fin n)) := by
      funext j;exact Fin.ext rfl
    rw [←hcanon]
    have hb:=row_bound hn hk hkn mult hm d w hw
    dsimp [N,A,H,M,R,ell]
    simpa only [hDe,hδe,OffsetInstance.slope,OffsetLP.slope,Rat.cast_mul,Rat.cast_natCast,
      Rat.cast_pow,Nat.cast_mul,Nat.cast_pow,canonical] using hb
  change (numbersOK k v && boundsOK n draw D δ &&
    rowsOK n k (RawCertificate.horizon k M) b T &&
    tableOK n k (RawCertificate.horizon k M) b (mult*ell^2) R draw D δ T)=true
  rw [RawMetric.horizon_eq]
  change (numbersOK k v && boundsOK n draw D δ && rowsOK n k H b T &&
    tableOK n k H b (mult*ell^2) R draw D δ T)=true
  rw [hnums,hbounds,hrows,htable]
  rfl

end UniformKServer.RawExistence

end


end

end OAI
