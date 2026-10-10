import OAI.Probability.DilutedSpin.RegularScheduleShift

namespace OAI

section
section
namespace DilutedSpinGlass
open scoped BigOperators
noncomputable local instance simultaneousShiftPropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

lemma real_telescope_sq_le (F : ℕ → ℝ) (n : ℕ) :
    (F 0-F n)^2 ≤ (n:ℝ)*∑ i : Fin n, (F i.val-F (i.val+1))^2 := by
  have h := @sq_sum_le_card_mul_sum_sq ℕ ℝ _ _ _ _ (Finset.range n)
    (fun i => F i-F (i+1))
  rw [Finset.sum_range_sub',Finset.card_range] at h
  rw [Fin.sum_univ_eq_sum_range (fun i => (F i-F (i+1))^2) n]
  exact h

namespace DepthAverage
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

noncomputable def shiftPathFlag (s : α → Bool) (t : ℕ) (v : α) : Bool :=
  if (Fintype.equivFin α v).val < t then s v else false

noncomputable def shiftPath (s : α → Bool) (t : ℕ) (q : α → Fin L) : α → Fin L :=
  coordinateProjection id (fun v => shiftPerm (shiftPathFlag s t v)) q

omit [DecidableEq α] [NeZero L] in
lemma shiftPath_zero (s : α → Bool) (q : α → Fin L) : shiftPath s 0 q=q := by
  funext v
  simp only [shiftPath,coordinateProjection,id_eq,shiftPathFlag,Nat.not_lt_zero,ite_false,
    shiftPerm,Bool.false_eq_true,Equiv.refl_apply]

omit [DecidableEq α] [NeZero L] in
lemma shiftPath_full (s : α → Bool) (q : α → Fin L) :
    shiftPath s (Fintype.card α) q=coordinateProjection id (fun v => shiftPerm (s v)) q := by
  funext v
  simp only [shiftPath,coordinateProjection,id_eq,shiftPathFlag,
    (Fintype.equivFin α v).isLt,ite_true]

omit [DecidableEq α] [NeZero L] in
lemma shiftPath_step_false (s : α → Bool) (q : α → Fin L) (i : Fin (Fintype.card α))
    (hs : s ((Fintype.equivFin α).symm i)=false) :
    shiftPath s (i.val+1) q=shiftPath s i.val q := by
  funext v
  by_cases hvi : Fintype.equivFin α v=i
  · have hv : v=(Fintype.equivFin α).symm i := (Equiv.eq_symm_apply _).mpr hvi
    subst v
    simp only [shiftPath,coordinateProjection,shiftPathFlag,Equiv.apply_symm_apply,
      Nat.lt_succ_self,ite_true,lt_self_iff_false,ite_false,id_eq,hs]
  · have hvn : (Fintype.equivFin α v).val ≠ i.val := by intro h; exact hvi (Fin.ext h)
    have he : ((Fintype.equivFin α v).val < i.val+1) ↔
        ((Fintype.equivFin α v).val < i.val) := by omega
    simp only [shiftPath,coordinateProjection,shiftPathFlag,he]

lemma shiftPath_step_values {η : ℝ} (hlarge : 1<η*(L:ℝ))
    (s : α → Bool) (q : α → Fin L) (hr : Regular η q) (i : Fin (Fintype.card α))
    (hs : s ((Fintype.equivFin α).symm i)=true) :
    (fun v => (shiftPath s (i.val+1) q v).val)=
      updateCoordinate (fun v => (shiftPath s i.val q v).val)
        ((Fintype.equivFin α).symm i) ((shiftPath s i.val q ((Fintype.equivFin α).symm i)).val+1) := by
  funext v
  by_cases hv : v=(Fintype.equivFin α).symm i
  · subst v
    rw [updateCoordinate_self]
    simp only [shiftPath,coordinateProjection,shiftPathFlag,Equiv.apply_symm_apply,
      Nat.lt_succ_self,ite_true,lt_self_iff_false,ite_false,id_eq,hs,
      shiftPerm,Bool.false_eq_true,Equiv.refl_apply]
    exact rotate_val_of_room _ (regular_room hlarge hr _)
  · rw [updateCoordinate_of_ne hv]
    have hvn : (Fintype.equivFin α v).val ≠ i.val := by
      intro h
      exact hv ((Equiv.eq_symm_apply _).mpr (Fin.ext h))
    have he : ((Fintype.equivFin α v).val < i.val+1) ↔
        ((Fintype.equivFin α v).val < i.val) := by omega
    simp only [shiftPath,coordinateProjection,shiftPathFlag,he]

end DepthAverage
namespace ReducedTopology
variable {Ω : Type} [Fintype Ω] {L : ℕ} [NeZero L]

 
theorem averaged_simultaneous_shift_le (H d : ℕ) (hheight : d+H=L)
    (S : ReducedTopology) (η : ℝ)
    (hlarge : 1<η*(L:ℝ)) (s : S.Vertex → Bool)
    (D : (S.Vertex → Fin L) → Prop)
    (hD : ∀ q, D q → Admissible S (fun v => (q v).val) d L ∧ DepthAverage.Regular η q)
    (T : KernelTower Ω H) (f : FinitePath Ω H → ℝ) (hf : ∀ x, |f x|≤1) :
    DepthAverage.average D (fun q =>
      (PrescribedTree.treeMean (realize H d S (fun v => (q v).val)) T f-
       PrescribedTree.treeMean (realize H d S
         (fun v => (DepthAverage.shiftPerm (s v) (q v)).val)) T f)^2) ≤
      (Fintype.card S.Vertex:ℝ)*(∑ v : S.Vertex, (vertexArity S v:ℝ)^2)/(L:ℝ) := by
  classical
  let b := Fintype.card S.Vertex
  let idx : Fin b → S.Vertex := (Fintype.equivFin S.Vertex).symm
  let G : ℕ → (S.Vertex → Fin L) → ℝ := fun t q =>
    PrescribedTree.treeMean (realize H d S (fun v => (DepthAverage.shiftPath s t q v).val)) T f
  have hg0 (q) : G 0 q=PrescribedTree.treeMean (realize H d S (fun v => (q v).val)) T f := by
    simp only [G,DepthAverage.shiftPath_zero]
  have hgb (q) : G b q=PrescribedTree.treeMean (realize H d S
        (fun v => (DepthAverage.shiftPerm (s v) (q v)).val)) T f := by
    simp only [G,b,DepthAverage.shiftPath_full,DepthAverage.coordinateProjection,id_eq]
  have ha (q) (hq : D q) (t : ℕ) :
      Admissible S (fun v => (DepthAverage.shiftPath s t q v).val) d L :=
    admissible_regular_shift S hlarge q (hD q hq).1 (hD q hq).2
      (DepthAverage.shiftPathFlag s t)
  have hstep (i : Fin b) : DepthAverage.average D (fun q => (G i.val q-G (i.val+1) q)^2) ≤
      (vertexArity S (idx i):ℝ)^2/(L:ℝ) := by
    by_cases hs : s (idx i)=false
    · have he (q) : G (i.val+1) q=G i.val q := by
        simp only [G,DepthAverage.shiftPath_step_false s q i hs]
      simp only [he,sub_self,zero_pow (by decide : 2≠0),DepthAverage.average,ite_self,
        FiniteLaw.expect_const]
      exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
    · have hs' : s (idx i)=true := Bool.eq_true_of_not_eq_false hs
      let E : (S.Vertex → Fin L) → Prop := fun q =>
        Admissible S (fun v => (q v).val) d L ∧
        Admissible S (updateCoordinate (fun v => (q v).val) (idx i) ((q (idx i)).val+1)) d L
      have hm (q) (hq : D q) : E (DepthAverage.shiftPath s i.val q) := by
        constructor
        · exact ha q hq i.val
        · rw [← DepthAverage.shiftPath_step_values hlarge s q (hD q hq).2 i hs']
          exact ha q hq (i.val+1)
      have he (q) (hq : D q) : (G i.val q-G (i.val+1) q)^2=
          vertexChangeSq H d S (idx i) T f (DepthAverage.shiftPath s i.val q) := by
        unfold G vertexChangeSq
        rw [DepthAverage.shiftPath_step_values hlarge s q (hD q hq).2 i hs']
      have he' : DepthAverage.average D (fun q => (G i.val q-G (i.val+1) q)^2)=
          DepthAverage.average D (fun q => vertexChangeSq H d S (idx i) T f
            (DepthAverage.shiftPath s i.val q)) := by
        apply FiniteLaw.expect_congr
        intro q
        split_ifs with hq
        · exact he q hq
        · rfl
      rw [he']
      exact (DepthAverage.fiber_bound id Function.injective_id
        (fun v => DepthAverage.shiftPerm (DepthAverage.shiftPathFlag s i.val v)) D E hm
        (vertexChangeSq H d S (idx i) T f) (vertexChangeSq_nonneg H d S (idx i) T f)).trans
        (averaged_vertexChangeSq_le H d S (idx i) E (by simpa only [hheight] using
          (fun q (hq : E q) => hq)) T f hf)
  have hp (q) : (if D q then (G 0 q-G b q)^2 else 0) ≤
      (b:ℝ)*∑ i : Fin b, if D q then (G i.val q-G (i.val+1) q)^2 else 0 := by
    split_ifs with hq
    · exact real_telescope_sq_le (fun t => G t q) b
    · simp
  have hh := (DepthAverage.depthLaw S.Vertex L).expect_mono hp
  rw [FiniteLaw.expect_mul_left,FiniteLaw.expect_fintype_sum] at hh
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hstep i)
  have hind : (∑ i : Fin b, (vertexArity S (idx i):ℝ)^2)=
      ∑ v : S.Vertex, (vertexArity S v:ℝ)^2 :=
    by
      simpa only [idx,b] using Equiv.sum_comp (Fintype.equivFin S.Vertex).symm
        (fun v : S.Vertex => (vertexArity S v:ℝ)^2)
  rw [← Finset.sum_div,hind] at hsum
  have hb : (0:ℝ)≤b := Nat.cast_nonneg _
  have hfin := hh.trans (mul_le_mul_of_nonneg_left hsum hb)
  simpa only [DepthAverage.average,b,hg0,hgb,← mul_div_assoc] using hfin

end ReducedTopology
end DilutedSpinGlass
end

end

end OAI
