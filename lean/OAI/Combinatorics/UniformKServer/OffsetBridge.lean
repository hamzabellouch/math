import Mathlib
import OAI.Combinatorics.UniformKServer.OffsetLP
import OAI.Combinatorics.UniformKServer.PublicFlow
import OAI.Combinatorics.UniformKServer.RealFlowBounds
import OAI.Combinatorics.UniformKServer.RealFlowConvex

namespace OAI

noncomputable section

/-! Restrict the law-independent strongly-lazy real flow to exactly the source
injective configuration and admissible-label LP, with no support assumption. -/
namespace UniformKServer.OffsetLP
open Finset EffectiveLP TreeRounding RealFlow
open scoped Classical
variable {n k H : ℕ} [NeZero k]
local instance configEqOB : DecidableEq (Configuration n k) :=
  fun first second => Classical.propDecidable (first = second)

omit [NeZero k] in
 theorem mem_labels_iff (c : Config n k) (r : Fin n) (j : Fin k) :
    j∈labels c r ↔ PublicInput.allowed c.val r j := by
  simp only [labels,PublicInput.allowed]
  split_ifs with h <;> simp [h]

omit [NeZero k] in
 theorem mass_injective (u : Config n k) (F : Data (Fin n) (Configuration n k) (Fin k))
    (hF : RealFlow.Valid F serve PublicInput.allowed u.val H)
    (w : List (Fin n)) (hw : w.length≤H) (c : Configuration n k)
    (hc : ¬Function.Injective c) : F.mass w c=0 := by
  induction w using List.reverseRecOn generalizing c with
  | nil =>
    rw [hF.initial]
    have he : c≠u.val := by intro he;exact hc (he ▸ u.property)
    simp [he]
  | append_singleton w r ih =>
    have hlen : w.length<H := by simp only [List.length_append,List.length_singleton] at hw;omega
    rw [←hF.inflow w hlen r]
    apply sum_eq_zero
    intro a ha
    apply sum_eq_zero
    intro j hj
    by_cases hai : Function.Injective a
    · by_cases hjl : PublicInput.allowed a r j
      · have hinj := EffectiveLP.label_injective (⟨a,hai⟩ : Config n k) r
          ⟨j,(mem_labels_iff ⟨a,hai⟩ r j).mpr hjl⟩
        have hne : serve a r j≠c := by intro he;exact hc (he ▸ hinj)
        simp [hne]
      · rw [hF.support w hlen r a j hjl]
        simp
    · rw [RealFlow.zero_flow F serve PublicInput.allowed u.val H hF w hlen r a
        (ih hlen.le a hai) j]
      simp

 theorem sum_restrict {A : Type*} [Fintype A] (P : A→Prop)
    [Fintype {a//P a}] (f : A→ℝ)
    (hz : ∀a,¬P a→f a=0) : (∑a,f a)=∑a : {a//P a},f a.val := by
  classical
  calc
    _ = ∑a ∈ univ.filter P,f a := by
      symm
      apply sum_subset (filter_subset _ _)
      intro a ha hp
      exact hz a (by simpa using hp)
    _ = _ := Finset.sum_subtype _ (by simp) _

 def restrict (F : Data (Fin n) (Configuration n k) (Fin k)) : BoundedFlow n k H ℝ where
  mass w c := F.mass w.val c.val
  flow w r c j := F.flow w.val.val r c.val j.val

omit [NeZero k] in
 theorem labels_sum (F : Data (Fin n) (Configuration n k) (Fin k))
    (u : Configuration n k) (hF : RealFlow.Valid F serve PublicInput.allowed u H)
    (w : List (Fin n)) (hw : w.length<H) (r : Fin n) (c : Config n k)
    (v : Fin k→ℝ) :
    (∑j,F.flow w r c.val j*v j)=∑j : Label c r,F.flow w r c.val j.val*v j.val := by
  simpa only [Label] using (@sum_restrict (Fin k) _ (fun j=>j∈labels c r) (instFintypeLabel c r)
    (fun j=>F.flow w r c.val j*v j) (fun j hj=>by
      rw [hF.support w hw r c.val j (mt (mem_labels_iff c r j).mpr hj),zero_mul]))

omit [NeZero k] in
theorem joint_sum (u : Config n k) (F : Data (Fin n) (Configuration n k) (Fin k))
    (hF : RealFlow.Valid F serve PublicInput.allowed u.val H)
    (w : List (Fin n)) (hw : w.length<H) (r : Fin n)
    (v : Configuration n k→Fin k→ℝ) :
    (∑c,∑j,F.flow w r c j*v c j)=
      ∑c : Config n k,∑j : Label c r,F.flow w r c.val j.val*v c.val j.val := by
  calc
    _ = ∑c : Config n k,∑j,F.flow w r c.val j*v c.val j := by
      simpa only [Config] using (@sum_restrict (Configuration n k) _ Function.Injective (instFintypeConfig n k)
        (fun c=>∑j,F.flow w r c j*v c j) (fun c hc=>by
          apply sum_eq_zero
          intro j _
          rw [RealFlow.zero_flow F serve PublicInput.allowed u.val H hF w hw r c
            (mass_injective u F hF w hw.le c hc) j,zero_mul]))
    _ = _ := sum_congr rfl fun c _=>labels_sum F u.val hF w hw r c (v c.val)

 theorem flowCost_prefix {R C J : Type*} [Fintype C] [Fintype J]
    (F : Data R C J) (d : C→R→J→ℝ) (pre w : List R) :
    flowCost F d pre w =
      ∑i : Fin w.length,∑c,∑j,F.flow (pre++w.take i) w[i] c j*d c w[i] j := by
  induction w generalizing pre with
  | nil => simp [flowCost]
  | cons r w ih =>
    simp only [flowCost,List.length_cons]
    rw [Fin.sum_univ_succ,ih]
    simp [Fin.getElem_fin,List.append_assoc]

 theorem restriction_valid (d : RationalMetric n) (u : Config n k) (A : ℚ)
    (F : Data (Fin n) (Configuration n k) (Fin k)) (a : ℝ)
    (hF : RealFlow.Valid F serve PublicInput.allowed u.val H) (ha : 0≤a)
    (hcost : ∀w : List (Fin n),w.length≤H→
      flowCost F (fun c r j=>(d.distance (c j) r : ℝ)) [] w≤
        (A : ℝ)*offlineCost d u.val w+a) : Valid d u A (restrict (H:=H) F) a := by
  refine ⟨ha,?_,?_,?_,?_,?_,?_,?_⟩
  · intro w c
    exact hF.mass_nonneg w.val ((mem_words _).mp w.property) c.val
  · intro w
    have hs := @sum_restrict (Configuration n k) _ Function.Injective (instFintypeConfig n k) (F.mass w.val)
      (fun c hc=>mass_injective u F hF w.val ((mem_words _).mp w.property) c hc)
    change (∑c : Config n k,F.mass w.val c.val)=1
    exact hs.symm.trans (hF.mass_total w.val ((mem_words _).mp w.property))
  · intro c
    change F.mass [] c.val=_
    rw [hF.initial]
    congr 1
    exact propext ⟨fun h=>Subtype.ext h,fun h=>congrArg Subtype.val h⟩
  · intro w r c j
    exact hF.flow_nonneg w.val.val w.property r c.val j.val
  · intro w r c
    change (∑j : Label c r,F.flow w.val.val r c.val j.val)=F.mass w.val.val c.val
    have hs := labels_sum F u.val hF w.val.val w.property r c (fun _=>1)
    simp only [mul_one] at hs
    rw [←hs,hF.outflow w.val.val w.property r c.val]
  · intro w r c'
    have hs := joint_sum u F hF w.val.val w.property r
      (fun c j=>if serve c r j=c'.val then 1 else 0)
    simp only [mul_ite,mul_one,mul_zero] at hs
    have hh := hF.inflow w.val.val w.property r c'.val
    rw [hs] at hh
    change (∑c : Config n k,∑j : Label c r,
      if EffectiveLP.step c r j=c' then F.flow w.val.val r c.val j.val else 0)=_
    have he (c : Config n k) (j : Label c r) :
        EffectiveLP.step c r j=c' ↔ serve c.val r j.val=c'.val :=
      ⟨fun h=>congrArg Subtype.val h,fun h=>Subtype.ext h⟩
    simpa only [he,extend,restrict] using hh
  · intro w
    have hh := hcost w.val ((mem_words _).mp w.property)
    rw [OfflineDynamic.offline_eq_optRat] at hh
    apply le_trans (le_of_eq ?_) hh
    rw [flowCost_prefix]
    apply sum_congr rfl
    intro i _
    simpa only [List.nil_append,restrict,prefixNode] using
      (joint_sum u F hF (w.val.take i) (prefixNode w i).property w.val[i]
        (fun c j=>(d.distance (c j) w.val[i] : ℝ))).symm

end UniformKServer.OffsetLP

end

end OAI
