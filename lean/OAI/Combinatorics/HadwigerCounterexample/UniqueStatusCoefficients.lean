import OAI.Combinatorics.HadwigerCounterexample.BinaryStatusComparison

namespace OAI

/-! # Unique Status Coefficients -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Function Matrix Submodule Module LinearMap
open scoped BigOperators
namespace StatusAnalysis
namespace DualAnalysis
variable {p:Shape} {r:ℕ} {d:Rates}
    {u:Terrain p r} {s:Gazette p r d} {β δ:ℝ}

private theorem loose_coeff {n:ℕ} (a b:RhymeSet n) (h:a.coal≠b.coal∨a.headBit≠b.headBit)
    (Q S T:F) :
    ∃ x:Par n,dotProduct a.coal x.2+a.headBit*x.1+a.gamma*Q+S ≠
      dotProduct b.coal x.2+b.headBit*x.1+b.gamma*Q+T := by
  classical
  by_contra! he
  have h0 := he (0,0)
  simp only [dotProduct_zero,mul_zero,add_zero,zero_add] at h0
  obtain ⟨ha,hb⟩ : a.coal=b.coal∧a.headBit=b.headBit :=by
    constructor
    · funext i
      have hh:=he (0,Pi.single i 1)
      simp only [dotProduct_single,mul_one,mul_zero,add_zero,add_assoc,h0] at hh
      exact add_right_cancel hh
    have hh:=he (1,0); simp only [dotProduct_zero,mul_one,zero_add,add_assoc,h0] at hh
    exact add_right_cancel hh
  simp [ha,hb] at h

theorem shot_switch (u:Terrain p r) (s:Gazette p r d) (i) (z:Appearance p)
    (a:RhymeSet (d i)) (f g:Pulsar p r)
    (hw:IsLaw (u z.l z.q)) (hs:∀ j, IsLaw (s i z j)) :
    shot u s i z a g ≤ shot u s i z a f+pr (u z.l z.q) (fun j=>f z.l z.q j≠ g z.l z.q j) := by
  unfold shot pr; rw [←avg_add]
  refine avg_mono hw.nz (fun j=>?_); let T:=s i z j
  have hh := disagreement_bound (s i z j) (hs j).nz (a.soot z)
    (fun _=>f z.l z.q j) (fun _=>g z.l z.q j)
  unfold pr at hh; rw [(hs j).avg_const] at hh; exact hh
set_option maxHeartbeats 1000000 in
theorem unison (hp:3≤p.g) (hu:origami p r u δ) (hs:reports p r u s β δ)
    (i : Nodes) {ε e:ℝ}
    (a b:RhymeSet (d i))
    (f g:Pulsar p r) (A B : Finset (Label p.b)) (h:(A∪B).card < Fintype.card (Label p.b))
    (hA:praise u s i A a f ε) (hB:praise u s i B b g e)
    (hC:a.bit=b.bit) (ht:ε+e<1/2*β) (hβ:0≤β) :
    a.coal=b.coal ∧ a.headBit=b.headBit ∧ ∀ l q, pr (u l q)
      (fun k=>f l q k+a.gamma*q≠g l q k+b.gamma*q) ≤ ε+e := by
  classical
  obtain ⟨x,hx⟩:= any_label _ h
  let X:= amazes p x
  let P l q k (w:Magazine p (d i)) :=
    a.read q w.2≠ f l q k ∨ b.read q w.2 ≠g l q k
  have hX l q : (X l q).apt:=generic_apt p hp _ rfl
  have hi l q :
      avg (u l q) (fun k=>pr (s i (X l q) k) (P l q k)) ≤ ε+e := by
    have h1:=hA (X l q) (fun h=>hx (mem_union_left _ h)) (hX l q)
    have h2:=hB (X l q) (fun h=>hx (mem_union_right _ h)) (hX l q)
    let t k:=s i (X l q) k
    let q1 (k:Fin r) (w:Magazine p (d i)):= a.read q w.2≠ f l q k
    let q2 (k:Fin r) (w:Magazine p (d i)):= b.read q w.2≠g l q k
    apply (avg_mono (hu.1 l q).nz (fun j=> pr_or_le (p:=q1 j) (q:=q2 j)
      (hs.law _ _ (hX ..) j).nz)).trans
    rw [avg_add]
    exact add_le_add h1 h2
  have ht' (l q k) (w:Magazine p (d i)) (h:¬P l q k w) :
      let x:=(w.2.1)
      dotProduct a.coal x.2+a.headBit*x.1+a.gamma*q + f l q k =
        dotProduct b.coal x.2+b.headBit*x.1+b.gamma*q+g l q k := by
    have ha : a.read q w.2=f l q k := not_not.mp (mt Or.inl h)
    have hb : b.read q w.2=g l q k := not_not.mp (mt Or.inr h)
    let x:=w.2.1
    let V (s:RhymeSet (d i)) := dotProduct s.coal x.2+s.headBit*x.1+s.gamma*q
    have hh (s:RhymeSet (d i)) : V s + s.read q w.2=s.bit*(w.2.2+x.1) := by
      have hh : s.read q w.2=s.bit*(w.2.2+x.1)+V s := by unfold RhymeSet.read V x; ring
      rw [hh,add_left_comm,char_two,add_zero]
    change V a+_= V b+_
    rw [←ha, ←hb,hh,hh,hC]
  have he : a.coal=b.coal∧a.headBit=b.headBit := by
    let l:Tag p.g:= ⟨0,by omega⟩; let Q:=show F from 0
    let R:=X l Q; let S(k:Fin r):= δ≤u l Q k
    by_contra! hf
    have hb (k) (hk:S k): β ≤ pr (s i R k) (P l Q k) := by
      obtain ⟨z,hz⟩:= loose_coeff a b (by tauto) Q (f l Q k)
        (g l Q k)
      · exact le_trans (hs.generous i _ rfl (hX _ _) k hk z)
          (pr_mono (hs.law _ R (hX _ _) k).nz (fun x hx=> not_not.mp
          (fun ht=>hz (hx ▸ ht' l Q k x ht))))

    have hh : 1/2*β ≤ avg (u l Q) (fun k=>pr (s i R k) (P l Q k)) := by
      refine (mul_le_mul_of_nonneg_right (hu.2 l Q) hβ).trans ?_
      unfold pr; rw [←avg_mul]; refine avg_mono (hu.1 l Q).nz fun i=> ?_
      change ind (S i) * _ ≤ _
      by_cases h:S i
      · rw [ind_one h,one_mul]; exact hb i h
      rw [ind_zero h,zero_mul]; exact pr_nonneg (hs.law _ _ (hX _ _) i).nz
    exact ht.not_ge (hh.trans (hi l Q))
  refine ⟨he.1,he.2,fun l q=> le_trans ?_ (hi l q)⟩
  refine avg_mono (hu.1 l q).nz fun k=> ?_
  let W:=s i (X l q) k
  have hw:=hs.law i _ (hX l q) k
  let C:=f l q k+a.gamma*q≠g l q k+b.gamma*q
  change ind C ≤ pr W _
  by_cases h:C
  · have hh w : P l q k w := by
      by_contra hy
      have hm:=ht' l q k w hy; dsimp only at hm
      rw [he.1,he.2,add_assoc _ (a.gamma*q),add_assoc _ (b.gamma*q)] at hm
      exact h (by rw [add_comm _ (a.gamma*q),add_comm _ (b.gamma*q)]; exact add_left_cancel hm)
    rw [ind_one h]; simp_rw [funext fun w=>eq_true (hh w),pr_true,show tot W=1 from hw.total]; exact le_rfl
  rw [ind_zero h]
  exact pr_nonneg hw.nz
end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
