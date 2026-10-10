import OAI.Analysis.PlanarPacking.TailSplit

namespace OAI

namespace SharpPlanar
open scoped BigOperators
def shortNode : Fin 21 → Node := ![⟨1,by norm_num [residues]⟩,⟨3,by norm_num [residues]⟩,⟨4,by norm_num [residues]⟩,⟨7,by norm_num [residues]⟩,⟨9,by norm_num [residues]⟩,⟨12,by norm_num [residues]⟩,⟨13,by norm_num [residues]⟩,⟨15,by norm_num [residues]⟩,⟨16,by norm_num [residues]⟩,⟨19,by norm_num [residues]⟩,⟨21,by norm_num [residues]⟩,⟨24,by norm_num [residues]⟩,⟨25,by norm_num [residues]⟩,⟨27,by norm_num [residues]⟩,⟨28,by norm_num [residues]⟩,⟨31,by norm_num [residues]⟩,⟨33,by norm_num [residues]⟩,⟨36,by norm_num [residues]⟩,⟨37,by norm_num [residues]⟩,⟨39,by norm_num [residues]⟩,⟨40,by norm_num [residues]⟩]
lemma shortNode_inj : Function.Injective shortNode := by decide +kernel
lemma shortNode_le (i : Fin 21) : (shortNode i).val ≤ 40 := by revert i; decide +kernel
lemma shortNode_cover_check : ∀ n : Fin 41,0<n.val ∧ n.val%12∈residues →
    ∃ i : Fin 21,(shortNode i).val=n.val := by decide +kernel
lemma shortNode_range (n : Node) : (∃ i,shortNode i=n) ↔ n.val≤40 := by
  constructor
  · rintro ⟨i,rfl⟩; exact shortNode_le i
  · intro hn
    obtain ⟨i,hi⟩:=shortNode_cover_check ⟨n.val,Nat.lt_succ_of_le hn⟩ n.prop
    exact ⟨i,Subtype.ext hi⟩
abbrev HeadNodeIndex := Option (Fin 21)
def headNodeNat : HeadNodeIndex → ℕ
  | none => 0
  | some i => (shortNode i).val
noncomputable def headC (p : CardinalData) : HeadNodeIndex → ℝ
  | none => p.c₀
  | some i => p.x (shortNode i,false)
noncomputable def headD (p : CardinalData) : HeadNodeIndex → ℝ
  | none => p.d₀
  | some i => p.x (shortNode i,true)
noncomputable def headRational (p : CardinalData) (s : ℝ) : ℝ :=
  p.C+∑ i,(headC p i/(s-headNodeNat i)^2+headD p i/(s-headNodeNat i))
lemma headNodeNat_le (i : HeadNodeIndex) : headNodeNat i≤40 := by
  cases i with
  | none => norm_num [headNodeNat]
  | some i => exact shortNode_le i
lemma headData_low (a : Bool) (n : Node) (hn : n.val≤40) (d : Bool) :
    (headData a).x (n,d)=(exactData a).x (n,d) := by
  simp only [headData,lp.coeFn_sub,Pi.sub_apply,tailList_apply,not_lt.mpr hn,ite_false,sub_zero]
lemma head_series_finite (a : Bool) (s : ℝ) :
    cardinalSeries (headData a) 0 s =
      (exactData a).C*P s+(exactData a).c₀*basisMoment false 0 0 s+
        (exactData a).d₀*basisMoment true 0 0 s+
        ∑ i : Fin 21,((exactData a).x (shortNode i,false)*basisMoment false (shortNode i).val 0 s+
          (exactData a).x (shortNode i,true)*basisMoment true (shortNode i).val 0 s) := by
  have ht:=shortNode_inj.tsum_eq (f:=fun n => (headData a).x (n,false)*basisMoment false n.val 0 s+
      (headData a).x (n,true)*basisMoment true n.val 0 s) (by
    intro n hn
    apply (shortNode_range n).mpr
    by_contra hh
    have hgt : 40<n.val := by omega
    exact hn (by simp only [headData_zero a n hgt false,headData_zero a n hgt true,zero_mul,add_zero]))
  simp only [tsum_fintype,headData_low a _ (shortNode_le _)] at ht
  simp only [cardinalSeries,Pmoment_zero]
  rw [← ht]
  rfl
lemma head_rational_factor (a : Bool) {s : ℝ} (hs : (83:ℝ)/2 ≤ s) :
    cardinalSeries (headData a) 0 s=P s*headRational (exactData a) s := by
  have he (n : ℕ) (hn : n≤40) (hr : n%12∈residues) (d : Bool) :
      basisMoment d n 0 s=P s/(s-n)^(if d then 1 else 2) := by
    have hns : (n:ℝ)≤40 := by exact_mod_cast hn
    have hne : s-(n:ℝ)≠0 := by linarith
    cases d
    · simp only [Bool.false_eq_true,ite_false]
      exact (eq_div_iff (pow_ne_zero 2 hne)).mpr (by nlinarith [basisU_factor n hr s])
    · simp only [ite_true,pow_one]
      exact (eq_div_iff hne).mpr (by nlinarith [basisV_factor n hr s])
  rw [head_series_finite]
  simp only [he 0 (by omega) (by norm_num [residues]),Nat.cast_zero,sub_zero,
    Bool.false_eq_true,ite_false,ite_true,pow_one,
    headRational,Fintype.sum_option,headC,headD,headNodeNat,Nat.cast_zero,sub_zero]
  simp_rw [he _ (shortNode_le _) (shortNode _).prop.2 false,
    he _ (shortNode_le _) (shortNode _).prop.2 true]
  simp only [ite_true,Bool.false_eq_true,ite_false,pow_one,
    Finset.mul_sum,Finset.sum_add_distrib,mul_add]
  ring_nf
end SharpPlanar

end OAI
