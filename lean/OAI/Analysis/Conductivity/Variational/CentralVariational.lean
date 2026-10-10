import Mathlib
import OAI.Analysis.Conductivity.Sources.WeightedSpectralSpace

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

def spectralGraphWeight {ι : Type*} (w : ι → ℝ) :
    spectralTraceGraph w →L[ℝ] SpectralL2 ι :=
  ((PiLp.proj 2 (fun _ : Fin 2 => SpectralL2 ι) 1).comp
    (spectralTraceGraph w).subtypeL).restrictScalars ℝ

def spectralGraphMean {ι : Type*} [Zero ι] (w : ι → ℝ) :
    spectralTraceGraph w →L[ℝ] ℝ :=
  Complex.reCLM.comp (((lp.evalCLM ℂ (fun _ : ι => ℂ) 2 0).comp
    ((PiLp.proj 2 (fun _ : Fin 2 => SpectralL2 ι) 0).comp
      (spectralTraceGraph w).subtypeL)).restrictScalars ℝ)

variable {V G : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

def centralForm {ι : Type*} (w : ι → ℝ) (D : V →L[ℝ] G)
    (T : Fin 3 → V →L[ℝ] spectralTraceGraph w) : V →L[ℝ] V →L[ℝ] ℝ :=
  (((innerSL ℝ).comp D).flip.comp D).flip + ∑ i : Fin 3,
    (((innerSL ℝ).comp ((spectralGraphWeight w).comp (T i))).flip.comp
      ((spectralGraphWeight w).comp (T i))).flip

lemma centralForm_apply {ι : Type*} (w : ι → ℝ) (D : V →L[ℝ] G)
    (T : Fin 3 → V →L[ℝ] spectralTraceGraph w) (u v : V) :
    centralForm w D T u v=inner ℝ (D u) (D v)+
      ∑ i : Fin 3,inner ℝ (spectralGraphWeight w (T i u)) (spectralGraphWeight w (T i v)) := by
  simp [centralForm]

lemma centralForm_lower {ι : Type*} (w : ι → ℝ) (D : V →L[ℝ] G)
    (T : Fin 3 → V →L[ℝ] spectralTraceGraph w) (u : V) :
    ‖D u‖^2≤centralForm w D T u u := by
  rw [centralForm_apply,real_inner_self_eq_norm_sq]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => real_inner_self_nonneg)

theorem solve_form_mod_constants [CompleteSpace V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (M F : V →L[ℝ] ℝ) (oneV : V)
    (hM : M oneV=1) (hF : F oneV=0)
    (hB : ∀ u : V,B u oneV=0) (hB' : ∀ v : V,B oneV v=0)
    (hcoer : IsCoercive (((B.comp M.ker.subtypeL).flip.comp M.ker.subtypeL).flip)) :
    ∃ p : V, M p=0 ∧ (∀ v : V,B p v=F v) ∧
      (∀ q : V,(∀ v : V,B q v=F v) → q-p=M q • oneV) := by
  let K := M.ker
  have hclosed : IsClosed (K : Set V) := M.isClosed_ker
  let : CompleteSpace K := hclosed.completeSpace_coe
  let A : K →L[ℝ] K →L[ℝ] ℝ := ((B.comp K.subtypeL).flip.comp K.subtypeL).flip
  let L : K →L[ℝ] ℝ := F.comp K.subtypeL
  let p : K := hcoer.continuousLinearEquivOfBilin.symm ((InnerProductSpace.toDual ℝ K).symm L)
  have hp (v : K) : B p.val v.val=F v.val := by
    change A p v=L v
    rw [←hcoer.continuousLinearEquivOfBilin_apply]
    dsimp only [p]
    rw [hcoer.continuousLinearEquivOfBilin.apply_symm_apply]
    exact congrArg (fun f : K →L[ℝ] ℝ => f v) ((InnerProductSpace.toDual ℝ K).apply_symm_apply L)
  have hpM : M p.val=0 := p.property
  have hfull (v : V) : B p.val v=F v := by
    have hv : v-M v • oneV∈K := by
      change M (v-M v • oneV)=0
      simp [hM]
    have hh := hp ⟨_,hv⟩
    change B p.val (v-M v • oneV)=F (v-M v • oneV) at hh
    simpa only [map_sub,map_smul,hB,hF,smul_zero,sub_zero] using hh
  refine ⟨p.val,hpM,hfull,?_⟩
  intro q hq
  let d : V := q-p.val-M q • oneV
  have hdK : d∈K := by
    change M (q-p.val-M q • oneV)=0
    simp [hpM,hM]
  have hd : B d d=0 := by
    dsimp only [d]
    simp only [map_sub,map_smul,sub_apply,smul_apply,
      hq,hfull,hB',smul_zero,sub_self]
  have hz : (⟨d,hdK⟩ : K)=0 := by
    apply hcoer.continuousLinearEquivOfBilin.injective
    apply ext_inner_right ℝ
    intro v
    rw [map_zero,inner_zero_left,hcoer.continuousLinearEquivOfBilin_apply]
    change B d v.val=0
    dsimp only [d]
    simp only [map_sub,map_smul,sub_apply,smul_apply,
      hq,hfull,hB',smul_zero,sub_self]
  have he : d=0 := congrArg (fun z : K => z.val) hz
  exact sub_eq_zero.mp he

theorem central_variational_exists [CompleteSpace V] {ι : Type*} [Zero ι]
    (w : ι → ℝ) (D : V →L[ℝ] G) (T : Fin 3 → V →L[ℝ] spectralTraceGraph w)
    (M : V →L[ℝ] ℝ) (oneV : V) (hM : M oneV=1) (hD : D oneV=0)
    (hT : ∀ i,spectralGraphWeight w (T i oneV)=0)
    (havg : ∀ i,spectralGraphMean w (T i oneV)=1)
    {C : ℝ} (hC : 0<C) (hP : ∀ u : M.ker,‖u‖≤C*‖D u.val‖)
    (s : Fin 3 → ℝ) (hs : ∑ i,s i=0) :
    ∃ p : V,M p=0 ∧
      (∀ v : V,inner ℝ (D p) (D v)+
        (∑ i : Fin 3,inner ℝ (spectralGraphWeight w (T i p))
          (spectralGraphWeight w (T i v)))=
        ∑ i : Fin 3,s i*spectralGraphMean w (T i v)) ∧
      (∀ q : V,(∀ v : V,centralForm w D T q v=
        ∑ i : Fin 3,s i*spectralGraphMean w (T i v)) → q-p=M q • oneV) := by
  let B := centralForm w D T
  let F : V →L[ℝ] ℝ := ∑ i : Fin 3,s i • (spectralGraphMean w).comp (T i)
  have hFa (v : V) : F v=∑ i : Fin 3,s i*spectralGraphMean w (T i v) := by
    simp [F,smul_eq_mul]
  have hF : F oneV=0 := by rw [hFa]; simpa only [havg,mul_one] using hs
  have hB (u : V) : B u oneV=0 := by
    simp only [B,centralForm_apply,hD,inner_zero_right,hT,Finset.sum_const_zero,add_zero]
  have hB' (v : V) : B oneV v=0 := by
    simp only [B,centralForm_apply,hD,inner_zero_left,hT,Finset.sum_const_zero,zero_add]
  have hcoer : IsCoercive (((B.comp M.ker.subtypeL).flip.comp M.ker.subtypeL).flip) := by
    refine ⟨C⁻¹^2,sq_pos_of_pos (inv_pos.mpr hC),?_⟩
    intro u
    change C⁻¹^2*‖u‖*‖u‖≤B u.val u.val
    have hh := mul_self_le_mul_self (norm_nonneg u) (hP u)
    have hlo := centralForm_lower w D T u.val
    have hCC : 0<C^2 := sq_pos_of_pos hC
    have hb : ‖u‖^2/C^2≤‖D u.val‖^2 := by
      apply (div_le_iff₀ hCC).mpr
      nlinarith [hh]
    calc
      _=‖u‖^2/C^2 := by simp only [div_eq_mul_inv,inv_pow]; ring
      _≤‖D u.val‖^2 := hb
      _≤B u.val u.val := hlo
  obtain ⟨p,hp,hfull,huniq⟩ := solve_form_mod_constants B M F oneV hM hF hB hB' hcoer
  refine ⟨p,hp,?_,?_⟩
  · intro v
    exact (centralForm_apply w D T p v).symm.trans ((hfull v).trans (hFa v))
  · intro q hq
    apply huniq q
    intro v
    exact (hq v).trans (hFa v).symm

theorem central_variational_exists_graph [CompleteSpace V] {ι : Type*} [Zero ι]
    (w : ι → ℝ) (D : V →L[ℝ] G) (T : Fin 3 → V →L[ℝ] spectralTraceGraph w)
    (M : V →L[ℝ] ℝ) (oneV : V) (hM : M oneV=1) (hD : D oneV=0)
    (hT : ∀ i,spectralGraphWeight w (T i oneV)=0)
    (havg : ∀ i,spectralGraphMean w (T i oneV)=1)
    {C : ℝ} (hC : 0<C)
    (hP : ∀ u : M.ker,‖u‖^2≤C*(‖D u.val‖^2+
      ∑ i : Fin 3,‖spectralGraphWeight w (T i u.val)‖^2))
    (s : Fin 3 → ℝ) (hs : ∑ i,s i=0) :
    ∃ p : V,M p=0 ∧
      (∀ v : V,inner ℝ (D p) (D v)+
        (∑ i : Fin 3,inner ℝ (spectralGraphWeight w (T i p))
          (spectralGraphWeight w (T i v)))=
        ∑ i : Fin 3,s i*spectralGraphMean w (T i v)) ∧
      (∀ q : V,(∀ v : V,inner ℝ (D q) (D v)+
        (∑ i : Fin 3,inner ℝ (spectralGraphWeight w (T i q))
          (spectralGraphWeight w (T i v)))=
        ∑ i : Fin 3,s i*spectralGraphMean w (T i v)) → q-p=M q • oneV) := by
  let B := centralForm w D T
  let F : V →L[ℝ] ℝ := ∑ i : Fin 3,s i • (spectralGraphMean w).comp (T i)
  have hFa (v : V) : F v=∑ i : Fin 3,s i*spectralGraphMean w (T i v) := by
    simp [F,smul_eq_mul]
  have hF : F oneV=0 := by rw [hFa]; simpa only [havg,mul_one] using hs
  have hB (u : V) : B u oneV=0 := by
    simp only [B,centralForm_apply,hD,inner_zero_right,hT,Finset.sum_const_zero,add_zero]
  have hB' (v : V) : B oneV v=0 := by
    simp only [B,centralForm_apply,hD,inner_zero_left,hT,Finset.sum_const_zero,zero_add]
  have hcoer : IsCoercive (((B.comp M.ker.subtypeL).flip.comp M.ker.subtypeL).flip) := by
    refine ⟨C⁻¹,inv_pos.mpr hC,?_⟩
    intro u
    change C⁻¹*‖u‖*‖u‖≤B u.val u.val
    have hh := hP u
    have he : B u.val u.val=‖D u.val‖^2+
        ∑ i : Fin 3,‖spectralGraphWeight w (T i u.val)‖^2 := by
      simp only [B,centralForm_apply,real_inner_self_eq_norm_sq]
    rw [←he] at hh
    calc
      _=‖u‖^2/C := by ring
      _≤B u.val u.val := (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hh)
  obtain ⟨p,hp,hfull,huniq⟩ := solve_form_mod_constants B M F oneV hM hF hB hB' hcoer
  refine ⟨p,hp,?_,?_⟩
  · intro v
    exact (centralForm_apply w D T p v).symm.trans ((hfull v).trans (hFa v))
  · intro q hq
    apply huniq q
    intro v
    exact (centralForm_apply w D T q v).trans ((hq v).trans (hFa v).symm)

end ScalarConductivity

end

end OAI
