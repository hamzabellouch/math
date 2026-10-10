import Mathlib
import OAI.Combinatorics.UniformKServer.RawMetric

namespace OAI

noncomputable section
                                  
section

namespace UniformKServer.RawAccepted
open RawArithmetic RawTable RawCertificate

structure Numbers (k : ℕ) (v : Certificate) : Prop where
  ell_eq : ell v=Nat.clog 2 (k+1)
  restart_pos : 0<restart v
  sep_pos : 0<value (sep v)
  restart_bound : (k:ℚ)*value (diam v)≤(restart v:ℚ)*value (sep v)
  cap_bound : (restart v:ℚ)*(k+1)*value (diam v)≤(cap v+1:ℚ)*value (sep v)

theorem numbers_spec {k : ℕ} {v : Certificate} (h : numbersOK k v=true) : Numbers k v := by
  simp only [numbersOK,Bool.and_eq_true_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨h0,hlo⟩,hhi⟩,hr⟩,hδ⟩,hc⟩,hm⟩:=h
  have h0:=of_decide_eq_true h0
  have hlo:=of_decide_eq_true hlo
  have hhi:=of_decide_eq_true hhi
  have hl := (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).mpr hlo
  have hu := (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr hhi
  refine ⟨by omega,of_decide_eq_true hr,?_,?_,?_⟩
  · unfold value
    have hp : 0<(sep v).1 := of_decide_eq_true hδ
    positivity
  · have hh:=(le_iff _ _).mp (of_decide_eq_true hc)
    simpa only [value_mul,value_natural] using hh
  · have hh:=(le_iff _ _).mp (of_decide_eq_true hm)
    simpa only [value_mul,value_natural,Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_assoc] using hh

theorem bounds_spec {n : ℕ} (d : RationalMetric n) (draw : List Q)
    (hd : ∀x y : Fin n,value (dist n draw x.val y.val)=d.distance x y)
    {D δ : Q} (h : boundsOK n draw D δ=true) :
    (∀x y,d.distance x y≤value D) ∧ (∀x y,x≠y→value δ≤d.distance x y) := by
  have hxy : ∀x y : Fin n,le (dist n draw x.val y.val) D ∧
      (x.val=y.val ∨ le δ (dist n draw x.val y.val)) := by
    intro x y
    have hh:=List.all_eq_true.mp (List.all_eq_true.mp h x.val (List.mem_range.mpr x.isLt)) y.val (List.mem_range.mpr y.isLt)
    have ha:=Bool.and_eq_true_iff.mp hh
    refine ⟨of_decide_eq_true ha.1,?_⟩
    rcases Bool.or_eq_true_iff.mp ha.2 with he|he
    · exact Or.inl (of_decide_eq_true he)
    · exact Or.inr (of_decide_eq_true he)
  constructor
  · intro x y;rw [←hd];exact (le_iff _ _).mp (hxy x y).1
  · intro x y hxy'
    have hn : x.val≠y.val := fun h=>hxy' (Fin.ext h)
    rw [←hd]
    exact (le_iff _ _).mp ((hxy x y).2.resolve_left hn)

structure Params {n k : ℕ} (mult : ℕ) (d : RationalMetric n) (draw : List Q)
    (v : Certificate) : Prop where
  numbers : Numbers k v
  diam_bound : ∀x y,d.distance x y≤value (diam v)
  sep_bound : ∀x y,x≠y→value (sep v)≤d.distance x y
  rows : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true
  budget : tableOK n k (UniformKServer.horizon k (cap v)) (bits v) (mult*(ell v)^2)
    (restart v) draw (diam v) (sep v) (table v)=true

theorem spec {n k mult : ℕ} (d : RationalMetric n) (draw : List Q)
    (hd : ∀x y : Fin n,value (dist n draw x.val y.val)=d.distance x y)
    {v : Certificate} (h : verify mult (n,k,draw) v=true) : Params (k:=k) mult d draw v := by
  simp only [verify,Bool.and_eq_true_iff,RawMetric.horizon_eq] at h
  obtain ⟨⟨⟨hn,hb⟩,hr⟩,ht⟩:=h
  exact ⟨numbers_spec hn,(bounds_spec d draw hd hb).1,(bounds_spec d draw hd hb).2,hr,ht⟩

end UniformKServer.RawAccepted

end


end

end OAI
