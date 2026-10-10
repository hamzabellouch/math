import Mathlib
import OAI.Combinatorics.UniformKServer.RawSound
import OAI.Combinatorics.UniformKServer.RawCompleteness

namespace OAI

noncomputable section
                                      
section

namespace UniformKServer.RawTableWitness
open RawArithmetic RawWords RawTable RawPath RawTyped RawExpansion RawCertificate RawRows RawRepresentation

theorem table_ok {n k H b A R : ℕ} [NeZero k] (hkn : k≤n)
    (d : RationalMetric n) (draw : List Q)
    (hd : ∀x y : Fin n,value (dist n draw x.val y.val)=d.distance x y)
    (D δ : Q) (T : List ℕ) (N : State n k→Fin n→Fin k→ℕ)
    (hrep : ∀p c r j,p.length≤H→entry T (requests p) (config c) r.val j.val=N (p,c) r j)
    (hN : ∀s r,∑j,N s r j=2^b)
    (hlazy : ∀s r j,(∃i,s.2 i=r)→s.2 j≠r→N s r j=0)
    (hbound : ∀w : List (Fin n),w.length≤H→
      BitSampling.rowCost (b:=b) N next (charge d)
        ([],fun j : Fin k=>(⟨j.val,lt_of_lt_of_le j.isLt hkn⟩:Fin n)) w ≤
        (A:ℝ)*offlineCost d (fun j : Fin k=>(⟨j.val,lt_of_lt_of_le j.isLt hkn⟩:Fin n)) w+
          R*(value δ:ℝ)+(value D:ℝ)) :
    tableOK n k H b A R draw D δ T=true := by
  have hr:=RawCompleteness.rows_ok T N hrep hN hlazy
  let u : Configuration n k := fun j=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩
  have hu : config u=List.range k := RawSound.config_canonical hkn
  apply List.all_eq_true.mpr
  intro w hw
  obtain ⟨hlen,hmem⟩:=(mem_upto n H w).mp hw
  obtain ⟨w',rfl⟩:=lift_list w hmem
  have hw' : w'.length≤H := by simpa [requests] using hlen
  apply List.all_eq_true.mpr
  intro g hg
  obtain ⟨hglen,hgmem⟩:= (mem_words k (requests w').length g).mp hg
  obtain ⟨g',rfl⟩:=lift_list g hgmem
  have hlen' : w'.length=g'.length := by simpa [requests] using hglen.symm
  apply decide_eq_true
  apply (le_iff _ _).mpr
  have he:=RawBounded.expected_eq (NeZero.pos k) d draw hd T hr [] u w' (by simpa using hw')
  rw [RawCompleteness.rowCost_eq (NeZero.pos k) T N hrep d [] u w' (by simpa using hw')] at he
  have hl := OfflineDynamic.optRat_lower d u (w'.zip g')
  have hzip : (w'.zip g').map Prod.fst=w' := List.map_fst_zip (by omega)
  rw [hzip,←OfflineDynamic.offline_eq_optRat] at hl
  have hb:=hbound w' hw'
  have hc : (value (cost n draw (config u) (requests w') (requests g')):ℝ)=
      costAlong d u (w'.zip g') := by
    rw [cost_value,history_zip w' g' hlen']
    exact movement_eq d draw hd u (w'.zip g')
  have ha : (0:ℝ)≤A := by positivity
  have hm:=mul_le_mul_of_nonneg_left hl ha
  have hfinal : (value (expected n k b draw T [] (List.range k) (requests w')):ℝ) ≤
      A*(value (cost n draw (List.range k) (requests w') (requests g')):ℝ)+
        R*(value δ:ℝ)+(value D:ℝ) := by
    change (value (expected n k b draw T [] (config u) (requests w')):ℝ)=_ at he
    rw [hu] at he
    rw [hu] at hc
    rw [he,hc]
    exact hb.trans (by dsimp [u] at *;linarith only [hm])
  simp only [value_add,value_mul,value_natural]
  have hfinal' : (value (expected n k b draw T [] (List.range k) (requests w')):ℝ) ≤
      (A:ℝ)*(value (cost n draw (List.range k) (requests w') (requests g')):ℝ)+
        ((R:ℝ)*(value δ:ℝ)+(value D:ℝ)) := by simpa only [add_assoc] using hfinal
  exact_mod_cast hfinal'

end UniformKServer.RawTableWitness

end


end

end OAI
