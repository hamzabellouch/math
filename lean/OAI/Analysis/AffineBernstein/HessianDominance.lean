import Mathlib
import OAI.Analysis.AffineBernstein.SimultaneousMinima
import OAI.Analysis.AffineBernstein.MatrixDetRigidity
import OAI.Analysis.AffineBernstein.HessianCompactness

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section HessianDominance
open Matrix

/-- The simultaneous near-minimum principle produces one limiting Hessian
which dominates every actual Hessian in quadratic-form order. -/
theorem balanced_dominating_hessian {n : ℕ} (hn : 1 ≤ n)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hbal : SectionBalance univ u ρ)
    (hD : ∀ x y, (hessian u x).det=(hessian u y).det) :
    ∃ A ∈ closure (range (hessian u)), ∀ x, (A-hessian u x).PosSemidef := by
  classical
  let f := fun e : Space n => dirDeriv e (dirDeriv e u)
  let m := fun e : Space n => sSup (range (f e))
  have hbd (e : Space n) : BddAbove (range (f e)) :=
    balanced_global_directional_bddAbove hn hu hp hm hρ hρ1 hbal e
  have hfm (e x : Space n) : f e x ≤ m e := le_csSup (hbd e) ⟨x,rfl⟩
  have hfc (e : Space n) : ContDiff ℝ ∞ (f e) := contDiff_dirDeriv (contDiff_dirDeriv hu e) e
  let I := Space n × {r : ℝ // 0 < r}
  let Q := fun (A : Matrix (Fin n) (Fin n) ℝ) (e : Space n) =>
    (fun i => e i) ⬝ᵥ (A*ᵥ (fun i => e i))
  have hQ (e : Space n) : Continuous (fun A => Q A e) := by
    dsimp only [Q,dotProduct,Matrix.mulVec]
    fun_prop
  let T := fun i : I => {A : Matrix (Fin n) (Fin n) ℝ | m i.1-i.2.val ≤ Q A i.1}
  have hT (i : I) : IsClosed (T i) := isClosed_le continuous_const (hQ i.1)
  have hfinite (s : Finset I) : (closure (range (hessian u)) ∩ ⋂ i∈s, T i).Nonempty := by
    have htol : ∃ ε : ℝ, 0 < ε ∧ ∀ i∈s, ε ≤ i.2.val := by
      induction s using Finset.induction_on with
      | empty => exact ⟨1,by norm_num,by simp⟩
      | @insert a s _ ih =>
        obtain ⟨ε,hε,Hε⟩ := ih
        refine ⟨min a.2.val ε,lt_min a.2.property hε,?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact min_le_left _ _
        · exact (min_le_right _ _).trans (Hε i hi)
    obtain ⟨ε,hε,Hε⟩ := htol
    let F := fun i : s => fun x => m i.val.1-f i.val.1 x
    have hF (i : s) : ContDiff ℝ ∞ (F i) := contDiff_const.sub (hfc i.val.1)
    have hFp (i : s) (x : Space n) : 0 ≤ F i x := sub_nonneg.mpr (hfm _ _)
    have hFL (i : s) (x : Space n) : inverseHessianTrace u (F i) x ≤ 0 := by
      change inverseHessianTrace u (fun y => m i.val.1-f i.val.1 y) x ≤ 0
      rw [inverseHessianTrace_sub isOpen_univ contDiffOn_const (hfc _).contDiffOn (mem_univ x),
        inverseHessianTrace_constant,zero_sub]
      exact neg_nonpos.mpr (constant_det_directional_subsolution hn hu hp hD _ x)
    have hsmall (i : s) (δ : ℝ) (hδ : 0 < δ) : ∃ x, F i x < δ := by
      obtain ⟨r,⟨x,rfl⟩,hx⟩ := exists_lt_of_lt_csSup (range_nonempty (f i.val.1))
        (show m i.val.1-δ < m i.val.1 by linarith)
      exact ⟨x,by dsimp [F]; linarith⟩
    obtain ⟨x,hx⟩ := balanced_simultaneous_minima hn hu hp hm hρ hρ1 hbal F hF hFp hFL hsmall hε
    refine ⟨hessian u x,subset_closure ⟨x,rfl⟩,?_⟩
    simp only [mem_iInter]
    intro i hi
    have H := hx ⟨i,hi⟩
    change m i.1-i.2.val ≤ Q (hessian u x) i.1
    have he : Q (hessian u x) i.1=f i.1 x := (second_directional_eq_quadratic hu _ _).symm
    rw [he]
    have hεi := Hε i hi
    dsimp only [F] at H
    linarith
  obtain ⟨A,hA,HA⟩ := (balanced_hessian_range_compact hn hu hp hm hρ hρ1 hbal).inter_iInter_nonempty T hT hfinite
  have hq (e x : Space n) : Q (hessian u x) e ≤ Q A e := by
    have hmA : m e ≤ Q A e := by
      apply le_of_forall_pos_le_add
      intro ε hε
      have H := mem_iInter.mp HA (e,⟨ε,hε⟩)
      change m e-ε ≤ Q A e at H
      linarith
    rw [show Q (hessian u x) e=f e x from (second_directional_eq_quadratic hu e x).symm]
    exact (hfm e x).trans hmA
  refine ⟨A,hA,fun x => ?_⟩
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((Matrix.isHermitian_iff_isSymm.mpr (hessian_closure_isSymm hu hA)).sub (hp x).isHermitian)
  intro p
  have H := hq (WithLp.toLp 2 p) x
  change p ⬝ᵥ ((hessian u x)*ᵥ p) ≤ p ⬝ᵥ (A*ᵥ p) at H
  simpa only [star_trivial,Matrix.sub_mulVec,dotProduct_sub] using sub_nonneg.mpr H

 theorem balanced_constant_hessian {n : ℕ} (hn : 1 ≤ n)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hbal : SectionBalance univ u ρ) : ∀ x y, hessian u x=hessian u y := by
  have hD := balanced_affineMaximal_constant_det hn hu hp hm hρ hρ1 hbal
  obtain ⟨A,hA,HA⟩ := balanced_dominating_hessian hn hu hp hm hρ hρ1 hbal hD
  have he (x : Space n) : A=hessian u x :=
    posDef_eq_of_posSemidef_sub_det_eq (hp x) (HA x) ((hessian_closure_det hD hA).trans (hD _ _))
  exact fun x y => (he x).symm.trans (he y)

end HessianDominance


end
end AffineBernstein
end

end OAI
