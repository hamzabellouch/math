import Mathlib
import OAI.Probability.LogConcave.Sampling.JointSpace

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace JetCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

lemma gadj_scalar (b : ι → E) (s : ι → E → ℝ) {V : ι → E → ℝ}
    (hV : ∀i,Differentiable ℝ (V i)) (c : ℝ) :
    gadj b s (fun i y => c*V i y)=fun y => c*gadj b s V y := by
  unfold gadj cadj
  simp_rw [dir_const_mul (hV _)]
  funext y
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end JetCalculus

lemma conditionalU_eq_scaled_jet {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    {κ : Type*} (v : κ → Point d) (l : List κ) (u : Point d) :
    (fun y => conditionalU F x r ρ y u ((lam:ℝ)*r) v l)=
      fun y => (ρ^l.length)⁻¹*JetCalculus.jet v l
        (fun z => inner ℝ u (conditionalFieldMean F x r ρ z)) y := by
  funext y
  have hh := conditionalFieldMean_jet_U hF x hr hlam hl hρ0.le hρ1 u y v l
  have hm : conditionalMeanScalar F x r ρ (fun z => inner ℝ u (primitiveField F x r z))=
      fun y => inner ℝ u (conditionalFieldMean F x r ρ y) :=
    (funext (conditionalFieldMean_inner hF x hr.le hl hρ0.le hρ1 u)).symm
  rw [hm] at hh
  rw [hh]
  field_simp [hρ0.ne']

lemma conditionalU_smooth_pos {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    {κ : Type*} (v : κ → Point d) (l : List κ) (u : Point d) :
    ContDiff ℝ (⊤:ℕ∞) (fun y => conditionalU F x r ρ y u ((lam:ℝ)*r) v l) := by
  rw [conditionalU_eq_scaled_jet hF x hr hlam hl hρ0 hρ1]
  exact contDiff_const.mul (JetCalculus.smooth_jet
    ((innerSL ℝ u).contDiff.comp (conditionalFieldMean_smooth hF x hr.le hl hρ0.le hρ1)) v l)

lemma mean_jet_eq_scaled_U {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {κ : Type*} (v : κ → Point d) (l : List κ) (i : Fin d) :
    JetCalculus.jet v l (fun z => jointMean F x r i (ρ,z))=
      fun y => ρ^l.length*conditionalU F x r ρ y (EuclideanSpace.basisFun (Fin d) ℝ i)
        ((lam:ℝ)*r) v l := by
  funext y
  have hm : conditionalMeanScalar F x r ρ
      (fun z => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i) (primitiveField F x r z))=
      fun y => jointMean F x r i (ρ,y) :=
    (funext (conditionalFieldMean_inner hF x hr.le hl hρ0 hρ1 _)).symm
  rw [←hm]
  exact conditionalFieldMean_jet_U hF x hr hlam hl hρ0 hρ1 _ y v l

lemma dir_mean_jet_eq_scaled_U {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {κ : Type*} (v : κ → Point d) (l : List κ) (i k : Fin d) :
    JetCalculus.dir (JetCalculus.spaceBasis d k)
      (JetCalculus.jet v l (fun z => jointMean F x r i (ρ,z)))=
      fun y => ρ^(l.length+1)*conditionalU F x r ρ y (EuclideanSpace.basisFun (Fin d) ℝ i)
        ((lam:ℝ)*r) (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k))
          (Sum.inr ()::l.map Sum.inl) := by
  have hh := mean_jet_eq_scaled_U hF x hr hlam hl hρ0 hρ1
    (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k)) (Sum.inr ()::l.map Sum.inl) i
  simpa only [JetCalculus.jet,JetCalculus.jet_map,Function.comp_def,Sum.elim_inl,Sum.elim_inr,
    List.length_cons,List.length_map] using hh

end LogConcaveSampling

end

end

end

end OAI
