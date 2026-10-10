import Mathlib
import OAI.Combinatorics.UniformKServer.OfflineDynamic
import OAI.Combinatorics.UniformKServer.RawBounded

namespace OAI

noncomputable section
                               
section

namespace UniformKServer.RawSound
open RawArithmetic RawWords RawTable RawPath RawTyped RawExpansion RawCertificate RawRows

theorem extracted_cost {n k : ℕ} (d : RationalMetric n) (draw : List Q)
    (hd : ∀x y : Fin n,value (dist n draw x.val y.val)=d.distance x y)
    (c : Configuration n k) (h : History n k) :
    (value (cost n draw (config c) (requests (h.map Prod.fst))
      (requests (h.map Prod.snd))):ℝ)=costAlong d c h := by
  rw [cost_value,history_zip (h.map Prod.fst) (h.map Prod.snd) (by simp)]
  have hz : (h.map Prod.fst).zip (h.map Prod.snd)=h := by
    induction h <;> simp_all
  simpa only [hz] using movement_eq d draw hd c h

theorem config_canonical {n k : ℕ} (hkn : k≤n) :
    config (fun j : Fin k=>(⟨j.val,lt_of_lt_of_le j.isLt hkn⟩:Fin n))=List.range k := by
  exact (range_eq_ofFn k).symm

theorem table_bound {n k H b A R : ℕ} [NeZero k] (hkn : k≤n)
    (d : RationalMetric n) (draw : List Q)
    (hd : ∀x y : Fin n,value (dist n draw x.val y.val)=d.distance x y)
    (D δ : Q) (T : List ℕ) (hrows : rowsOK n k H b T=true)
    (htable : tableOK n k H b A R draw D δ T=true)
    (w : List (Fin n)) (hw : w.length≤H) :
    BitSampling.rowCost (b:=b) (complete (NeZero.pos k) H b T) next (charge d)
      ([],fun j : Fin k=>(⟨j.val,lt_of_lt_of_le j.isLt hkn⟩:Fin n)) w ≤
      (A:ℝ)*offlineCost d (fun j : Fin k=>(⟨j.val,lt_of_lt_of_le j.isLt hkn⟩:Fin n)) w+
        R*(value δ:ℝ)+(value D:ℝ) := by
  let u : Configuration n k := fun j=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩
  obtain ⟨h,hh,hcost⟩:=OfflineDynamic.optRat_attained d u w
  have hg : requests (h.map Prod.snd)∈words k (requests w).length := by
    apply (mem_words _ _ _).mpr
    refine ⟨?_,?_⟩
    · simp only [requests,List.length_map]
      simpa only [List.length_map] using congrArg List.length hh
    · intro j hj
      obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hj
      exact x.isLt
  have ht:=of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp htable (requests w) (requests_mem w H hw))
      (requests (h.map Prod.snd)) hg)
  have ht':=(le_iff _ _).mp ht
  have htR : (value (expected n k b draw T [] (List.range k) (requests w)):ℝ) ≤
      A*(value (cost n draw (List.range k) (requests w) (requests (h.map Prod.snd))):ℝ)+
        (R*(value δ:ℝ)+(value D:ℝ)) := by
    exact_mod_cast (by simpa only [value_add,value_mul,value_natural] using ht')
  have he:=RawBounded.expected_eq (NeZero.pos k) d draw hd T hrows [] u w (by simpa using hw)
  have hu : config u=List.range k := config_canonical hkn
  simp only [requests,List.map_nil,hu] at he
  rw [←he]
  have hc:=extracted_cost d draw hd u h
  rw [hh,hu,hcost,←OfflineDynamic.offline_eq_optRat] at hc
  rw [hc] at htR
  simpa only [add_assoc,requests,u] using htR

end UniformKServer.RawSound

end


end

end OAI
