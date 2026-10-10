import OAI.Combinatorics.PolynomialVacuum.Cylinder.SystemMerge

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra
variable {M H : ℕ} [NeZero M]

theorem codedWeight_factor (inp out : ZMod M → Spin) (s : Bool × ZMod M → ArcChoice M)
    (hH : 2*arcChoiceLength s<H) :
    codedWeight H inp out s=codedWeight H inp (fun _=>.zero) (cutCode false s)*
      codedWeight H (fun _=>.zero) out (cutCode true s) := by
  by_cases he : ∃S : ArcSystem (bandSites M H),S.code=s
  · obtain ⟨S,rfl⟩:=he
    rw [← S.part_code_eq false,← S.part_code_eq true,codedWeight_code,codedWeight_code,codedWeight_code]
    have hs : arcChoiceLength S.code<H := by omega
    rw [S.parts_matches hs inp out,S.parts_weight]
    split_ifs <;> simp_all
  · rw [codedWeight_zero inp out s he]
    have hh : ¬((∃S : ArcSystem (bandSites M H),S.code=cutCode false s) ∧
        (∃S : ArcSystem (bandSites M H),S.code=cutCode true s)) := by
      intro hh; exact he ((ArcSystem.exists_code_cut_iff s hH).mpr hh)
    rcases not_and_or.mp hh with hh | hh
    · rw [codedWeight_zero _ _ _ hh,zero_mul]
    · rw [codedWeight_zero _ _ _ hh,mul_zero]

theorem limitingCodedWeight_factor (inp out : ZMod M → Spin) (s : Bool × ZMod M → ArcChoice M) :
    limitingCodedWeight inp out s=limitingCodedWeight inp (fun _=>.zero) (cutCode false s)*
      limitingCodedWeight (fun _=>.zero) out (cutCode true s) := by
  unfold limitingCodedWeight
  rw [codedWeight_factor inp out s (by omega)]
  have h (b : Bool) : 2*arcChoiceLength (cutCode b s)<2*arcChoiceLength s+1 := by
    have := cutCode_length s b; omega
  rw [codedWeight_stable _ (2*arcChoiceLength (cutCode false s)+1) _ _ _ (h false) (by omega),
    codedWeight_stable (2*arcChoiceLength s+1) (2*arcChoiceLength (cutCode true s)+1) _ _ _ (h true) (by omega)]

noncomputable def joinCode (a b : ZMod M → ArcChoice M) (p : Bool × ZMod M) : ArcChoice M :=
  if p.1 then b p.2 else a p.2
noncomputable def halfCodeEquiv : ((ZMod M → ArcChoice M) × (ZMod M → ArcChoice M)) ≃
    (Bool × ZMod M → ArcChoice M) where
  toFun ab:=joinCode ab.1 ab.2
  invFun s:=(fun i=>s (false,i),fun i=>s (true,i))
  left_inv ab:=by apply Prod.ext <;> funext i <;> rfl
  right_inv s:=by funext p; rcases p with ⟨b,i⟩; cases b <;> rfl

omit [NeZero M] in
@[simp] theorem cut_join_false [NeZero M] (a b : ZMod M → ArcChoice M) :
    cutCode false (joinCode a b)=joinCode a (fun _=>.inl ()) := by
  funext p; rcases p with ⟨c,i⟩; cases c <;> rfl
omit [NeZero M] in
@[simp] theorem cut_join_true [NeZero M] (a b : ZMod M → ArcChoice M) :
    cutCode true (joinCode a b)=joinCode (fun _=>.inl ()) b := by
  funext p; rcases p with ⟨c,i⟩; cases c <;> rfl

noncomputable def lowerAmplitude (inp : ZMod M → Spin) : ℂ :=
  ∑'a : ZMod M → ArcChoice M,limitingCodedWeight inp (fun _=>.zero) (joinCode a (fun _=>.inl ()))
noncomputable def upperAmplitude (out : ZMod M → Spin) : ℂ :=
  ∑'b : ZMod M → ArcChoice M,limitingCodedWeight (fun _=>.zero) out (joinCode (fun _=>.inl ()) b)

theorem limitingCodedWeight_norm_summable (inp out : ZMod M → Spin) :
    Summable (fun s => ‖limitingCodedWeight inp out s‖) := by
  apply (arcChoice_summable M).of_nonneg_of_le (fun _=>norm_nonneg _)
  intro s
  exact codedWeight_norm _ _ _ _

theorem arcLimit_factor (inp out : ZMod M → Spin) : arcLimit inp out=lowerAmplitude inp*upperAmplitude out := by
  unfold arcLimit lowerAmplitude upperAmplitude
  rw [← halfCodeEquiv.tsum_eq]
  have hi0 : Function.Injective (fun a : ZMod M → ArcChoice M => joinCode a (fun _=>.inl ())) := by
    intro a b h; funext i; exact congrFun h (false,i)
  have hi1 : Function.Injective (fun b : ZMod M → ArcChoice M => joinCode (fun _=>.inl ()) b) := by
    intro a b h; funext i; exact congrFun h (true,i)
  rw [tsum_mul_tsum_of_summable_norm
    ((limitingCodedWeight_norm_summable inp (fun _=>.zero)).comp_injective hi0)
    ((limitingCodedWeight_norm_summable (fun _=>.zero) out).comp_injective hi1)]
  apply tsum_congr
  intro ab
  exact (limitingCodedWeight_factor inp out (joinCode ab.1 ab.2)).trans (by rw [cut_join_false,cut_join_true])
end PolynomialVacuumCylinder

end OAI
