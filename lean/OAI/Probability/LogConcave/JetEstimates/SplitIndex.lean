import Mathlib
import OAI.Probability.LogConcave.Sampling.SpatialTensor

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal

namespace JetCalculus
lemma gadj_scalar_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (b : ι → E) (s : ι → E → ℝ) {V : ι → E → ℝ} {p : E}
    (hV : ∀i,DifferentiableAt ℝ (V i) p) (c : ℝ) :
    gadj b s (fun i y => c*V i y) p=c*gadj b s V p := by
  unfold gadj cadj
  simp_rw [dir_const_mul_at (hV _)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
end JetCalculus

namespace TensorAtom
variable {S : Type} [Fintype S]

lemma jetCard (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) (hne : l≠[]) :
    2≤Fintype.card (S ⊕ Unit) := by
  have he := Fintype.card_congr (List.Nodup.getEquivOfForallMemList l hN hall)
  have hp := List.length_pos_iff.mpr hne
  simp only [Fintype.card_fin] at he
  simp only [Fintype.card_sum,Fintype.card_unit]
  omega

abbrev SplitIndex (l : List S) := ↥(l.toFinset.powerset.erase ∅)

omit [Fintype S] in
lemma splitIndex_nonempty {l : List S} (a : SplitIndex l) : a.val.Nonempty :=
  Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp a.property).1

def splitAtom (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) (a : SplitIndex l) : TensorAtom (S ⊕ Unit) :=
  splitProduct l hN hall a.val (splitIndex_nonempty a)

lemma splitAtom_weight (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) (a : SplitIndex l) :
    (splitAtom l hN hall a).expression.weight=l.length-1 := splitProduct_weight _ _ _ _ _

lemma material_jetList {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) (hne : l≠[])
    (c : S ⊕ Unit → Fin d) (y : Point d) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
      ((jetList l hN hall hne).eval F x r ((lam:ℝ)*r) c) (ρ,y)=
      ((extendedU l hN hall).adjoint (jetCard l hN hall hne)).eval F x r ((lam:ℝ)*r) c (ρ,y)+
      2*(r*((lam:ℝ)*r))*ρ*∑a : SplitIndex l,(splitAtom l hN hall a).eval F x r ((lam:ℝ)*r) c (ρ,y) := by
  let L : ℝ := (lam:ℝ)*r
  have hL : L≠0 := ne_of_gt (mul_pos (by exact_mod_cast hlam) hr)
  let v : S → Point d := fun s => JetCalculus.spaceBasis d (c (Sum.inl s))
  let U := jointU F x r L v l (c (Sum.inr ()))
  let V := fun k => jointU F x r L (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k))
    (Sum.inr ()::l.map Sum.inl) (c (Sum.inr ()))
  have hU := jointU_timeSmooth hF x hr hlam hl v l hN (c (Sum.inr ()))
  have hV (k : Fin d) := jointU_timeSmooth hF x hr hlam hl
    (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k)) _ (extra_list_nodup hN) (c (Sum.inr ()))
  have hA : ((extendedU l hN hall).adjoint (jetCard l hN hall hne)).eval F x r L c (ρ,y)=
      L⁻¹*JetCalculus.gadj jointSpace (jointScore F x r) V (ρ,y) := by
    rw [adjoint_eval]
    have he : (fun k => (extendedU l hN hall).eval F x r L (Sum.elim c (fun _ => k)))=
        fun k p => L⁻¹*V k p := by
      funext k
      rw [extendedU_eval]
      rfl
    rw [he]
    exact JetCalculus.gadj_scalar_at _ _ (fun k =>
      (hV k (ρ,y) (by dsimp; linarith) hρ1).differentiableAt (by simp)) _
  change JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
      ((jetList l hN hall hne).eval F x r L c) (ρ,y)=_
  rw [jetList_eval,JetCalculus.mdir_const_mul_at _ _ _ _
    ((hU (ρ,y) (by dsimp; linarith) hρ1).differentiableAt (by simp)),
    material_jointU hF x hr hlam hl hρ0 hρ1 v l hN,hA]
  rw [mul_add]
  congr 1
  simp only [splitAtom,splitProduct_eval]
  rw [←Finset.sum_coe_sort]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [L,v]
  field_simp [hL]

end TensorAtom
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

namespace JetCalculus

lemma dir_time {d : ℕ} (P : Polynomial ℝ) (v : ℝ × Point d) (p : ℝ × Point d) :
    dir v (fun q : ℝ × Point d => P.eval q.1) p=P.derivative.eval p.1*v.1 := by
  have hh := (P.hasDerivAt p.1).comp_hasFDerivAt p (hasFDerivAt_fst (𝕜:=ℝ) (p:=p))
  simp only [Function.comp_def] at hh
  change (fderiv ℝ (fun q : ℝ × Point d => P.eval q.1) p) v=_
  rw [hh.fderiv]
  rfl

lemma mdir_time {d : ℕ} (P : Polynomial ℝ) (r : ℝ) (M : Fin d → ℝ × Point d → ℝ)
    (p : ℝ × Point d) :
    mdir (1,0) jointSpace r M (fun q : ℝ × Point d => P.eval q.1) p=P.derivative.eval p.1 := by
  unfold mdir
  simp only [dir_time,jointSpace,mul_zero,Finset.sum_const_zero,sub_zero,mul_one]

lemma gadj_time_at {d : ℕ} (P : Polynomial ℝ) (s : Fin d → ℝ × Point d → ℝ)
    {V : Fin d → ℝ × Point d → ℝ} {p : ℝ × Point d}
    (hV : ∀i,DifferentiableAt ℝ (V i) p) :
    gadj jointSpace s (fun i q => P.eval q.1*V i q) p=P.eval p.1*gadj jointSpace s V p := by
  have hP : DifferentiableAt ℝ (fun q : ℝ × Point d => P.eval q.1) p :=
    P.differentiable.differentiableAt.comp p differentiableAt_fst
  unfold gadj cadj
  simp_rw [dir_mul_at hP (hV _),dir_time]
  simp only [jointSpace,mul_zero,zero_mul,zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end JetCalculus
end LogConcaveSampling

end

end

end

end OAI
