import Mathlib
import OAI.Combinatorics.UniformKServer.HeavyRecordGeometry
import OAI.Combinatorics.UniformKServer.HeavyRadius
import OAI.Combinatorics.UniformKServer.FinitePiLaw

namespace OAI

                                      
section

/-! Physical separation by the actual disjoint heavy balls. No factor equal
to the number of records is lost: for a short edge there is at most one
possible boundary ball, and its single birth-coordinate marginal is uniform. -/
noncomputable section
namespace UniformKServer.HeavyRecords
open Finset FiniteProbability
open scoped Classical
variable {X Λ I : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] [Fintype I] {r : ℝ}
local instance pairDecEq : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
local instance indexDecEq : DecidableEq I := fun a b => Classical.propDecidable (a=b)

omit [Fintype X] in
theorem key_eq_iff (S : State X Λ r) (hr : 0 ≤ r) (x y : X) :
    key S x=key S y ↔ ∀ l, covers S l x ↔ covers S l y := by
  constructor
  · intro he l
    rw [←key_some S hr x l,←key_some S hr y l,he]
  · intro he
    cases hx : key S x with
    | none =>
      symm
      apply (key_none S y).mpr
      rintro ⟨l,hl⟩
      have := (key_some S hr x l).mpr ((he l).mpr hl)
      rw [hx] at this
      cases this
    | some l =>
      symm
      exact (key_some S hr y l).mpr ((he l).mp ((key_some S hr x l).mp hx))

omit [Fintype X] in
theorem key_ne_witness (S : State X Λ r) (hr : 0 ≤ r) (x y : X)
    (hne : key S x ≠ key S y) : ∃ l ∈ S.present, ¬(covers S l x ↔ covers S l y) := by
  have hh : ¬∀ l, covers S l x ↔ covers S l y := fun h => hne ((key_eq_iff S hr x y).mpr h)
  push Not at hh
  obtain ⟨l,hl⟩ := hh
  have hnot : ¬(covers S l x ↔ covers S l y) := by tauto
  refine ⟨l,?_,hnot⟩
  by_contra hn
  exact hnot (by simp only [covers,hn,false_and])

omit [Fintype X] [Fintype Λ] in
theorem near_boundary (S : State X Λ r) (hr : 0 ≤ r) (x y : X) (hd : dist x y < r)
    (l : Λ) (hl : l ∈ S.present) (hm : ¬(covers S l x ↔ covers S l y)) :
    dist (S.center l) x ≤ 21*r := by
  by_cases hx : covers S l x
  · linarith [hx.2,(S.radius_bounds l hl).2]
  · have hy : covers S l y := by tauto
    have ht := dist_triangle (S.center l) y x
    rw [dist_comm y x] at ht
    linarith [hy.2,(S.radius_bounds l hl).2]

theorem static_separation (hr : 0 < r) (H : Finset X) (hH : HeavySchedule.Separated r H)
    (birth : X → I) (S : (I → HeavyRadius.Sample (X:=X) r) → State X Λ r)
    (hcenters : ∀ ω, centers (S ω)=H)
    (hrad : ∀ ω l, l ∈ (S ω).present →
      (S ω).radius l=HeavyRadius.radius r (ω (birth ((S ω).center l)))) (x y : X) :
    (Law.pi (fun _ : I => HeavyRadius.law (X:=X) r)).expect
      (fun ω => if key (S ω) x ≠ key (S ω) y then (1:ℝ) else 0) ≤ dist x y/r := by
  let P := Law.pi (fun _ : I => HeavyRadius.law (X:=X) r)
  by_cases hd : dist x y < r
  · by_cases he : ∃ c ∈ H, dist c x ≤ 21*r
    · obtain ⟨c,hc,hcx⟩ := he
      have hb : ∀ ω, (if key (S ω) x ≠ key (S ω) y then (1:ℝ) else 0) ≤
          if (ω (birth c)).val (c,x) != (ω (birth c)).val (c,y) then 1 else 0 := by
        intro ω
        by_cases hk : key (S ω) x ≠ key (S ω) y
        · obtain ⟨l,hl,hm⟩ := key_ne_witness (S ω) hr.le x y hk
          have hc' : (S ω).center l ∈ H := by rw [←hcenters ω]; exact mem_image.mpr ⟨l,hl,rfl⟩
          have hnear := near_boundary (S ω) hr.le x y hd l hl hm
          have hcen : (S ω).center l=c := by
            apply HeavySchedule.intersect_unique r hr.le H hH x _ _ hc' hc <;>
              rw [dist_comm] <;> linarith
          have hcov (z : X) : covers (S ω) l z ↔ (ω (birth c)).val (c,z)=true := by
            rw [HeavyRadius.covers r hr]
            simp only [covers,hl,true_and,hrad ω l hl,hcen]
          have hbits : (ω (birth c)).val (c,x) ≠ (ω (birth c)).val (c,y) := by
            intro heq
            apply hm
            rw [hcov x,hcov y,heq]
          simp only [ite_eq_left hk]
          cases hx : (ω (birth c)).val (c,x) <;> cases hy : (ω (birth c)).val (c,y) <;> simp_all
        · simp only [ite_eq_right hk]
          split_ifs <;> norm_num
      have hh := P.expect_mono _ _ hb
      have hmarg := Law.expect_pi_coordinate (fun _ : I => HeavyRadius.law (X:=X) r) (birth c)
        (fun ω => if ω.val (c,x) != ω.val (c,y) then (1:ℝ) else 0)
      change P.expect _ = _ at hmarg
      rw [hmarg] at hh
      apply (hh.trans (HeavyRadius.separation r hr c x y)).trans
      exact div_le_div_of_nonneg_left dist_nonneg hr (by linarith)
    · have hz : ∀ ω, key (S ω) x=key (S ω) y := by
        intro ω
        by_contra hk
        obtain ⟨l,hl,hm⟩ := key_ne_witness (S ω) hr.le x y hk
        apply he
        refine ⟨(S ω).center l,?_,near_boundary (S ω) hr.le x y hd l hl hm⟩
        rw [←hcenters ω]
        exact mem_image.mpr ⟨l,hl,rfl⟩
      have heq : P.expect (fun ω => if key (S ω) x ≠ key (S ω) y then (1:ℝ) else 0)=0 := by
        simp only [hz,ne_eq,not_true_eq_false,ite_false,P.expect_const]
      change P.expect _ ≤ _
      rw [heq]
      positivity
  · have hb : ∀ ω, (if key (S ω) x ≠ key (S ω) y then (1:ℝ) else 0) ≤ 1 := by
      intro ω; split_ifs <;> norm_num
    have hh := P.expect_mono _ _ hb
    rw [P.expect_const] at hh
    exact hh.trans ((le_div_iff₀ hr).mpr (by linarith))

end UniformKServer.HeavyRecords

end


end

end OAI
