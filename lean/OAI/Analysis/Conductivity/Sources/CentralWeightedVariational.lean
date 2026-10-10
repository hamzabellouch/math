import Mathlib
import OAI.Analysis.Conductivity.Variational.CentralVariational

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

variable {V G : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

def centralWeightedForm {ι : Type*} (κ : ℝ) (w : ι → ℝ) (D : V →L[ℝ] G)
    (T : Fin 3 → V →L[ℝ] spectralTraceGraph w) : V →L[ℝ] V →L[ℝ] ℝ :=
  (((innerSL ℝ).comp D).flip.comp D).flip + κ • ∑ i : Fin 3,
    (((innerSL ℝ).comp ((spectralGraphWeight w).comp (T i))).flip.comp
      ((spectralGraphWeight w).comp (T i))).flip

lemma centralWeightedForm_apply {ι : Type*} (κ : ℝ) (w : ι → ℝ) (D : V →L[ℝ] G)
    (T : Fin 3 → V →L[ℝ] spectralTraceGraph w) (u v : V) :
    centralWeightedForm κ w D T u v=inner ℝ (D u) (D v)+
      κ*(∑ i : Fin 3,inner ℝ (spectralGraphWeight w (T i u)) (spectralGraphWeight w (T i v))) := by
  simp [centralWeightedForm,smul_eq_mul]

theorem central_variational_exists_graph_weighted [CompleteSpace V] {ι : Type*} [Zero ι]
    (κ : ℝ) (hκ : 1≤κ) (w : ι → ℝ) (D : V →L[ℝ] G)
    (T : Fin 3 → V →L[ℝ] spectralTraceGraph w)
    (M : V →L[ℝ] ℝ) (oneV : V) (hM : M oneV=1) (hD : D oneV=0)
    (hT : ∀ i,spectralGraphWeight w (T i oneV)=0)
    (havg : ∀ i,spectralGraphMean w (T i oneV)=1)
    {C : ℝ} (hC : 0<C)
    (hP : ∀ u : M.ker,‖u‖^2≤C*(‖D u.val‖^2+
      ∑ i : Fin 3,‖spectralGraphWeight w (T i u.val)‖^2))
    (s : Fin 3 → ℝ) (hs : ∑ i,s i=0) :
    ∃ p : V,M p=0 ∧
      (∀ v : V,inner ℝ (D p) (D v)+
        κ*(∑ i : Fin 3,inner ℝ (spectralGraphWeight w (T i p))
          (spectralGraphWeight w (T i v)))=
        κ*(∑ i : Fin 3,s i*spectralGraphMean w (T i v))) ∧
      (∀ q : V,(∀ v : V,inner ℝ (D q) (D v)+
        κ*(∑ i : Fin 3,inner ℝ (spectralGraphWeight w (T i q))
          (spectralGraphWeight w (T i v)))=
        κ*(∑ i : Fin 3,s i*spectralGraphMean w (T i v))) → q-p=M q • oneV) := by
  let B := centralWeightedForm κ w D T
  let F : V →L[ℝ] ℝ := κ • ∑ i : Fin 3,s i • (spectralGraphMean w).comp (T i)
  have hFa (v : V) : F v=κ*(∑ i : Fin 3,s i*spectralGraphMean w (T i v)) := by
    simp [F,smul_eq_mul]
  have hF : F oneV=0 := by rw [hFa]; simp only [havg,mul_one,hs,mul_zero]
  have hB (u : V) : B u oneV=0 := by
    simp only [B,centralWeightedForm_apply,hD,inner_zero_right,hT,Finset.sum_const_zero,mul_zero,add_zero]
  have hB' (v : V) : B oneV v=0 := by
    simp only [B,centralWeightedForm_apply,hD,inner_zero_left,hT,Finset.sum_const_zero,mul_zero,zero_add]
  have hcoer : IsCoercive (((B.comp M.ker.subtypeL).flip.comp M.ker.subtypeL).flip) := by
    refine ⟨C⁻¹,inv_pos.mpr hC,?_⟩
    intro u
    change C⁻¹*‖u‖*‖u‖≤B u.val u.val
    have hn : 0≤∑ i : Fin 3,‖spectralGraphWeight w (T i u.val)‖^2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hb : ‖D u.val‖^2+∑ i : Fin 3,‖spectralGraphWeight w (T i u.val)‖^2≤B u.val u.val := by
      simp only [B,centralWeightedForm_apply,real_inner_self_eq_norm_sq]
      nlinarith [mul_le_mul_of_nonneg_right hκ hn]
    have hh := (hP u).trans (mul_le_mul_of_nonneg_left hb hC.le)
    calc
      _=‖u‖^2/C := by ring
      _≤B u.val u.val := (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hh)
  obtain ⟨p,hp,hfull,huniq⟩ := solve_form_mod_constants B M F oneV hM hF hB hB' hcoer
  refine ⟨p,hp,?_,?_⟩
  · intro v
    exact (centralWeightedForm_apply κ w D T p v).symm.trans ((hfull v).trans (hFa v))
  · intro q hq
    apply huniq q
    intro v
    exact (centralWeightedForm_apply κ w D T q v).trans ((hq v).trans (hFa v).symm)

end ScalarConductivity

end

end OAI
