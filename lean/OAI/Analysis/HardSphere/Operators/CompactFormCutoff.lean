import Mathlib
import OAI.Analysis.HardSphere.Geometry.HeatScalar

namespace OAI

noncomputable section
open Set MeasureTheory Filter ContinuousLinearMap
open scoped Topology ComplexOrder
namespace HardSphere.CompactForm

def cutoff (δ x : ℝ) : ℝ := Real.smoothTransition (((2 : ℕ) : ℝ)*x/δ-1)
lemma cutoff_smooth (δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (cutoff δ) := by
  exact Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).div_const δ |>.sub contDiff_const)
lemma cutoff_nonneg (δ x : ℝ) : 0≤cutoff δ x := Real.smoothTransition.nonneg _
lemma cutoff_le_one (δ x : ℝ) : cutoff δ x≤1 := Real.smoothTransition.le_one _
lemma cutoff_zero {δ x : ℝ} (hδ : 0<δ) (hx : x≤δ/2) : cutoff δ x=0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hh : 2*x/δ≤1 := (div_le_one hδ).mpr (by linarith)
  linarith
lemma cutoff_one {δ x : ℝ} (hδ : 0<δ) (hx : δ≤x) : cutoff δ x=1 := by
  apply Real.smoothTransition.one_of_one_le
  have hh : 2≤2*x/δ := (le_div_iff₀ hδ).mpr (by linarith)
  linarith
lemma cutoff_error {δ x : ℝ} (hδ : 0<δ) (hx : 0≤x) :
    ‖(1-cutoff δ x)^2*x‖≤δ := by
  have hq := cutoff_nonneg δ x
  have hq' := cutoff_le_one δ x
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) hx)]
  by_cases hh : δ≤x
  · rw [cutoff_one hδ hh]; simpa using hδ.le
  · have hx' : x≤δ := (lt_of_not_ge hh).le
    have hs : (1-cutoff δ x)^2≤1 := by nlinarith
    exact (mul_le_mul_of_nonneg_right hs hx).trans (by simpa using hx')

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma finite_range_compact (F : H →L[ℂ] H) (W : Submodule ℂ H)
    [FiniteDimensional ℂ W] (hW : ∀x,F x∈W) : IsCompactOperator F := by
  have hh := isCompactOperator_of_locallyCompactSpace_dom (F.codRestrict W hW)
  exact hh.clm_comp W.subtypeL

lemma cutoff_compact {ι : Type*} (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (v : ι→H) (r : ι→ℝ)
    (hdense : (Submodule.span ℂ (range v)).topologicalClosure=⊤)
    (heigen : ∀i,T (v i)=r i • v i)
    (hfinite : ∀ε : ℝ,0<ε → {i | ε≤r i}.Finite)
    {δ : ℝ} (hδ : 0<δ) :
    IsCompactOperator (cfc (p:=IsSelfAdjoint) (cutoff δ) T : H →L[ℂ] H) := by
  let S : Set ι := {i | δ/2≤r i}
  have hS : S.Finite := hfinite _ (by positivity)
  let W : Submodule ℂ H := Submodule.span ℂ (v '' S)
  have : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (hS.image v)
  apply finite_range_compact _ W
  have hgen : Submodule.span ℂ (range v) ≤
      W.comap (cfc (p:=IsSelfAdjoint) (cutoff δ) T).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change cfc (p:=IsSelfAdjoint) (cutoff δ) T (v i)∈W
    rw [cfc_eigen_apply T hT _ (cutoff_smooth δ).continuous _
      ((cutoff_smooth δ).differentiable (by norm_num)).differentiableAt _ (heigen i)]
    by_cases hi : i∈S
    · exact W.smul_mem _ (Submodule.subset_span ⟨i,hi,rfl⟩)
    · have hr : r i≤δ/2 := (lt_of_not_ge hi).le
      rw [cutoff_zero hδ hr,zero_smul]
      exact W.zero_mem
  have hclosed : IsClosed (W.comap (cfc (p:=IsSelfAdjoint) (cutoff δ) T).toLinearMap : Set H) :=
    W.closed_of_finiteDimensional.preimage (cfc (p:=IsSelfAdjoint) (cutoff δ) T).continuous
  have hh := (Submodule.span ℂ (range v)).topologicalClosure_minimal hgen hclosed
  rw [hdense] at hh
  intro x
  exact hh (Submodule.mem_top : x∈(⊤ : Submodule ℂ H))

end HardSphere.CompactForm

namespace HardSphere.CompactForm
variable {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma cutoff_embedding_error (J : G →L[ℂ] H) (T : H →L[ℂ] H)
    (hJT : J ∘L J.adjoint=T) (hT : T.IsPositive) (hTn : ‖T‖≤1)
    {δ : ℝ} (hδ : 0<δ) :
    ‖((1-cfc (p:=IsSelfAdjoint) (cutoff δ) T) : H →L[ℂ] H) ∘L J‖^2≤δ := by
  let q : ℝ→ℝ := fun x ↦ 1-cutoff δ x
  have hq : Continuous q := continuous_const.sub (cutoff_smooth δ).continuous
  let Q : H →L[ℂ] H := cfc (p:=IsSelfAdjoint) q T
  have hQ : Q=1-cfc (p:=IsSelfAdjoint) (cutoff δ) T := by
    dsimp only [Q,q]
    rw [cfc_sub _ _ T continuousOn_const (cutoff_smooth δ).continuous.continuousOn,
      cfc_const 1 T hT.isSelfAdjoint,map_one]
  have hQadj : Q.adjoint=Q := cfc_predicate q T
  let E : G →L[ℂ] H := Q ∘L J
  have hEE : E ∘L E.adjoint=Q*T*Q := by
    change (Q ∘L J) ∘L (Q ∘L J).adjoint=Q*T*Q
    rw [adjoint_comp,hQadj]
    calc
      _ = Q ∘L ((J ∘L J.adjoint) ∘L Q) := by simp only [comp_assoc]
      _ = Q*T*Q := by rw [hJT]; rfl
  have hcalc : Q*T*Q=cfc (p:=IsSelfAdjoint) (fun x : ℝ ↦ (1-cutoff δ x)^2*x) T := by
    have hf : (fun x : ℝ ↦ (1-cutoff δ x)^2*x)=(fun x ↦ (q x*x)*q x) := by
      funext x; dsimp only [q]; ring
    rw [hf]
    symm
    calc
      _ = cfc (p:=IsSelfAdjoint) (fun x : ℝ ↦ q x*x) T * cfc q T :=
        cfc_mul (fun x : ℝ ↦ q x*x) q T (hq.mul continuous_id).continuousOn hq.continuousOn
      _ = (cfc q T * cfc (p:=IsSelfAdjoint) id T) * cfc q T := by
        congr 1
        exact cfc_mul q id T hq.continuousOn continuous_id.continuousOn
      _ = Q*T*Q := by
        change cfc q T * cfc (p:=IsSelfAdjoint) (fun x : ℝ ↦ x) T * cfc q T = _
        rw [cfc_id' ℝ T hT.isSelfAdjoint]
  have hb : ‖E ∘L E.adjoint‖≤δ := by
    rw [hEE,hcalc]
    apply norm_cfc_le hδ.le
    intro spectralValue hmem
    have hnonneg := spectrum_nonneg_of_nonneg
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr hT) hmem
    by_cases hlarge : 1 ≤ δ
    · have hbound : spectralValue ≤ 1 := (le_abs_self _).trans
        ((spectrum.norm_le_norm_mul_of_mem hmem).trans
          ((mul_le_of_le_one_right (norm_nonneg T) norm_id_le).trans hTn))
      have hcutoff : (1-cutoff δ spectralValue)^2 ≤ 1 := by
        nlinarith [cutoff_nonneg δ spectralValue, cutoff_le_one δ spectralValue]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hnonneg)]
      exact (mul_le_of_le_one_left hnonneg hcutoff).trans (hbound.trans hlarge)
    · exact cutoff_error hδ hnonneg
  have hn := norm_adjoint_comp_self E.adjoint
  rw [adjoint_adjoint,LinearIsometryEquiv.norm_map] at hn
  rw [hn] at hb
  change ‖Q ∘L J‖*‖Q ∘L J‖≤δ at hb
  rw [hQ] at hb
  simpa only [sq] using hb

lemma compact_embedding {ι : Type*} (J : G →L[ℂ] H) (T : H →L[ℂ] H)
    (hJT : J ∘L J.adjoint=T) (hT : T.IsPositive) (hTn : ‖T‖≤1)
    (v : ι→H) (r : ι→ℝ)
    (hdense : (Submodule.span ℂ (range v)).topologicalClosure=⊤)
    (heigen : ∀i,T (v i)=r i • v i)
    (hfinite : ∀ε : ℝ,0<ε → {i | ε≤r i}.Finite) : IsCompactOperator J := by
  have hclosed : IsClosed {F : G →L[ℂ] H | IsCompactOperator F} := isClosed_setOfPred_isCompactOperator
  apply hclosed.closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  let δ : ℝ := ε^2/4
  have hδ : 0<δ := by dsimp only [δ]; positivity
  let F : H →L[ℂ] H := cfc (p:=IsSelfAdjoint) (cutoff δ) T
  have hF : IsCompactOperator F := cutoff_compact T hT.isSelfAdjoint v r hdense heigen hfinite hδ
  refine ⟨F ∘L J,hF.comp_clm J,?_⟩
  rw [dist_eq_norm]
  have heq : J-F ∘L J=(1-F) ∘L J := by ext x; simp
  rw [heq]
  have hh := cutoff_embedding_error J T hJT hT hTn hδ
  change ‖(1-F) ∘L J‖^2≤δ at hh
  have hn := norm_nonneg ((1-F) ∘L J)
  dsimp only [δ] at hh
  nlinarith

end HardSphere.CompactForm
end

end OAI
