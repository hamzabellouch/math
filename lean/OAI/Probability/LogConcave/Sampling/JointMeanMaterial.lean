import Mathlib
import OAI.Probability.LogConcave.JetEstimates.JetMaterial

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma joint_mean_material {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (i : Fin d) (y : Point d) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (jointMean F x r i) (ρ,y)=
      JetCalculus.gadj jointSpace (jointScore F x r) (fun k => jointU F x r ((lam:ℝ)*r)
        (fun _ : Unit => JetCalculus.spaceBasis d k) [()] i) (ρ,y) := by
  have hm := jointMean_timeSmooth hF x hr.le hl i (ρ,y) (by dsimp; linarith) h1
  have ht := joint_mdir_eq_material F x r (hm.differentiableAt (by simp))
  change JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (jointMean F x r i) (ρ,y)=_ at ht
  rw [ht]
  change materialScalar F x r (fun t y => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
    (conditionalFieldMean F x r t y)) ρ y=_
  rw [material_conditionalFieldMean hF x hr hlam hl h0 h1]
  rw [joint_gadj_slice hF x hr.le hl h0 h1 (fun k =>
    (jointU_timeSmooth hF x hr hlam hl (fun _ : Unit => JetCalculus.spaceBasis d k) [()]
      (by simp) i (ρ,y) (by dsimp; linarith) h1).differentiableAt (by simp))]
  rfl

lemma joint_mean_outer {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (i : Fin d) (y : Point d) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (jointMean F x r i) (ρ,y)=
      ((lam:ℝ)*r)*(TensorSum.pure TensorAtom.one).outer F x r ((lam:ℝ)*r) (fun _ => i) (ρ,y) := by
  rw [joint_mean_material hF x hr hlam hl h0 h1]
  have hL : (lam:ℝ)*r≠0 := ne_of_gt (mul_pos (by exact_mod_cast hlam) hr)
  have he : (fun k => jointU F x r ((lam:ℝ)*r)
      (fun _ : Unit => JetCalculus.spaceBasis d k) [()] i)=
      fun k p => ((lam:ℝ)*r)*(TensorSum.pure TensorAtom.one).eval F x r ((lam:ℝ)*r)
        (Sum.elim (fun _ => i) (fun _ => k)) p := by
    funext k p
    rw [TensorSum.pure_eval,TensorAtom.one_eval]
    dsimp only [Sum.elim_inl,Sum.elim_inr]
    field_simp
  rw [he,JetCalculus.gadj_scalar_at _ _ (fun k =>
    ((TensorSum.pure TensorAtom.one).timeSmooth hF x hr hlam hl _ (ρ,y)
      (by dsimp; linarith) h1).differentiableAt (by simp))]
  rfl

theorem mean_material_representation (n : ℕ) :
    ∃A : TensorSum (Unit ⊕ Unit), A.weightLE (2*n) ∧
      ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}, Primitive F lam →
        ∀(x : Point d) {r ρ : ℝ},0 < r → 0 < lam → (lam:ℝ)*r^2≤1/2 → 0≤ρ → ρ<1 →
          ∀(i : Fin d) (y : Point d),
            JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) (n+1) (jointMean F x r i) (ρ,y)=
              ((lam:ℝ)*r)*A.outer F x r ((lam:ℝ)*r) (fun _ => i) (ρ,y) := by
  induction n with
  | zero =>
    refine ⟨TensorSum.pure TensorAtom.one,TensorSum.weightLE_pure _ (by rfl),?_⟩
    intro d F lam hF x r ρ hr hlam hl h0 h1 i y
    exact joint_mean_outer hF x hr hlam hl h0 h1 i y
  | succ n ih =>
    obtain ⟨A,hA,he⟩ := ih
    obtain ⟨B,hB,hAB⟩ := A.hasMaterial hA
    refine ⟨B.add (A.insertOne.scale 1 Polynomial.X),?_,?_⟩
    · apply TensorSum.weightLE_add
      · convert hB using 1
      · exact TensorSum.weightLE_mono (TensorSum.weightLE_scale
          (TensorSum.weightLE_insertOne hA) _ _) (by omega)
    · intro d F lam hF x r ρ hr hlam hl h0 h1 i y
      have ho := A.outer_timeSmooth hF x hr hlam hl (fun _ : Unit => i)
      have hs : JetCalculus.TimeSmooth (fun p => ((lam:ℝ)*r)*A.outer F x r ((lam:ℝ)*r) (fun _ => i) p) :=
        fun p hp0 hp1 => contDiffAt_const.mul (ho p hp0 hp1)
      change JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
        (JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) (n+1) (jointMean F x r i)) (ρ,y)=_
      rw [JetCalculus.mdir_congr_nonneg_time (1,0) jointSpace r (jointMean F x r)
        (JetCalculus.materialIter_timeSmooth _ _ _ (jointMean_timeSmooth hF x hr.le hl)
          (jointMean_timeSmooth hF x hr.le hl i) (n+1)) hs
        (fun ht0 ht1 z => he hF x hr hlam hl ht0 ht1 i z) h0 h1 y,
        JetCalculus.mdir_const_mul_at _ _ _ _ ((ho (ρ,y) (by dsimp; linarith) h1).differentiableAt (by simp)),
        TensorSum.outer_material hF x hr hlam hl h0 h1 hAB]
end LogConcaveSampling

end

end

end

end OAI
