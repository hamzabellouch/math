import Mathlib
import OAI.Probability.LogConcave.Analysis.InterpolationPotential
import OAI.Probability.LogConcave.Sampling.DirectionalBasisSum

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators

lemma allSplitBound_pair {d : ℕ} {B : Fin d → Fin d → ℝ} {M : ℝ}
    (hB : Bound B (M^2)) :
    AllSplitBound (fun c : Unit ⊕ Unit → Fin d => B (c (Sum.inl ())) (c (Sum.inr ()))) M := by
  intro I O _ _ _ _ _ _ e
  have hc := Fintype.card_congr e
  simp only [Fintype.card_sum,Fintype.card_unique] at hc
  have hi := Fintype.card_pos (α:=I)
  have ho := Fintype.card_pos (α:=O)
  obtain ⟨uI⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp (show Fintype.card I=1 by omega)
  obtain ⟨uO⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp (show Fintype.card O=1 by omega)
  let : Unique I := uI
  let : Unique O := uO
  cases he0 : e (Sum.inl ()) with
  | inl i =>
    cases he1 : e (Sum.inr ()) with
    | inl j =>
      have hh := e.injective (he0.trans ((congrArg Sum.inl (Subsingleton.elim i j)).trans he1.symm))
      cases hh
    | inr o =>
      have hh := (hB.transpose (sq_nonneg M)).reindex
        (Equiv.funUnique O (Fin d)) (Equiv.funUnique I (Fin d))
      simpa only [he0,he1,Sum.elim_inl,Sum.elim_inr,Equiv.funUnique_apply,
        Subsingleton.elim i (default:I),Subsingleton.elim o (default:O)] using hh
  | inr o =>
    cases he1 : e (Sum.inr ()) with
    | inl i =>
      have hh := hB.reindex (Equiv.funUnique O (Fin d)) (Equiv.funUnique I (Fin d))
      simpa only [he0,he1,Sum.elim_inl,Sum.elim_inr,Equiv.funUnique_apply,
        Subsingleton.elim i (default:I),Subsingleton.elim o (default:O)] using hh
    | inr p =>
      have hh := e.injective (he0.trans ((congrArg Sum.inr (Subsingleton.elim o p)).trans he1.symm))
      cases hh

end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace TensorEnergy
open scoped Matrix.Norms.L2Operator in
lemma Bound.add_norm {I O : Type*} [Fintype I] [Fintype O]
    {A B : O → I → ℝ} {M N : ℝ} (hA : Bound A (M^2)) (hB : Bound B (N^2))
    (hM : 0≤M) (hN : 0≤N) : Bound (fun o i => A o i+B o i) ((M+N)^2) := by
  change Bound (A+B) ((M+N)^2)
  apply (bound_iff_norm_le (add_nonneg hM hN)).mpr
  exact (norm_add_le _ _).trans (add_le_add (hA.norm_le hM) (hB.norm_le hN))

lemma AllSplitBound.add {S : Type} [Fintype S] {d : ℕ}
    {A B : (S → Fin d) → ℝ} {M N : ℝ}
    (hA : AllSplitBound A M) (hB : AllSplitBound B N) (hM : 0≤M) (hN : 0≤N) :
    AllSplitBound (fun c => A c+B c) (M+N) := by
  intro I O _ _ _ _ _ _ e
  exact (hA I O e).add_norm (hB I O e) hM hN

lemma allSplitBound_delta {d : ℕ} : AllSplitBound
    (fun c : Unit ⊕ Unit → Fin d => if c (Sum.inl ())=c (Sum.inr ()) then (1:ℝ) else 0) 1 := by
  have hB : Bound (fun i j : Fin d => if i=j then (1:ℝ) else 0) ((1:ℝ)^2) := by
    intro v
    simp only [one_pow,one_mul,ite_mul,zero_mul]
    simp
  exact @allSplitBound_pair d (fun i j : Fin d => if i=j then (1:ℝ) else 0) 1 hB

lemma allSplitBound_spatial_delta {d : ℕ} {K : Type} [Fintype K]
    (l : List K) (hall : ∀k,k∈l) : AllSplitBound
    (fun c : (K ⊕ Unit) ⊕ Unit → Fin d => if l=[] then
      (if c (Sum.inl (Sum.inr ()))=c (Sum.inr ()) then (1:ℝ) else 0) else 0)
    (if l=[] then 1 else 0) := by
  by_cases hl : l=[]
  · let : IsEmpty K := ⟨fun k => by simpa only [hl,List.not_mem_nil] using hall k⟩
    have hh := (allSplitBound_delta (d:=d)).reindex
      ((Equiv.emptySum K Unit).sumCongr (Equiv.refl Unit)).symm
    simpa only [hl,↓reduceIte,Function.comp_def,Equiv.sumCongr_symm,
      Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,Equiv.refl_symm,Equiv.refl_apply,
      Equiv.emptySum_symm_apply] using hh
  · intro I O _ _ _ _ _ _ e v
    simp [hl]
end TensorEnergy

def scoreAugmented {d : ℕ} {K : Type} (H : Point d → ℝ) (l : List K)
    (y : Point d) (c : (K ⊕ Unit) ⊕ Unit → Fin d) : ℝ :=
  JetCalculus.jet (fun k => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl (Sum.inl k)))) l
    (directional (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl (Sum.inr ()))))
      (directional (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr ()))) H)) y

lemma scoreAugmented_eq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {K : Type} [Fintype K] (l : List K) (hlen : l.length=Fintype.card K)
    (y : Point d) (c : (K ⊕ Unit) ⊕ Unit → Fin d) :
    scoreAugmented (interpolationPotential F x r ρ) l y c =
      (if l=[] then (if c (Sum.inl (Sum.inr ()))=c (Sum.inr ()) then 1 else 0) else 0) +
      (r*ρ)*(ρ^(Fintype.card K+1)*((lam:ℝ)*r))*
        normalizedTensor F x r ρ ((lam:ℝ)*r) y
          (Sum.elim (fun _ => false) (fun _ => true))
          ((l.map Sum.inl++[Sum.inr ()]).map Sum.inl++[Sum.inr ()]) c := by
  let v := EuclideanSpace.basisFun (Fin d) ℝ
  let w := v (c (Sum.inr ()))
  let k := l.map Sum.inl++[Sum.inr ()]
  have hg : directional w (interpolationPotential F x r ρ)=fun y =>
      inner ℝ w y+(r*ρ)*inner ℝ w (conditionalFieldMean F x r ρ y) := by
    funext y
    rw [directional_gradient,interpolationPotential_gradient hF x hr.le hl hρ0 hρ1,
      real_inner_comm,inner_add_right,inner_smul_right]
  have hm := (conditionalFieldMean_component_polySmooth hF x hr hlam hl hρ0 hρ1 (c (Sum.inr ()))).smooth
  have hlin : ContDiff ℝ (⊤:ℕ∞) (fun y => inner ℝ w y) := (innerSL ℝ w).contDiff
  have hklen : k.length=Fintype.card (K ⊕ Unit) := by simp [k,hlen]
  have he : scoreAugmented (interpolationPotential F x r ρ) l y c =
      JetCalculus.jet (fun s => v (c (Sum.inl s))) k
        (directional w (interpolationPotential F x r ρ)) y := by
    simp only [k,JetCalculus.jet_append,JetCalculus.jet_map,JetCalculus.jet]
    rfl
  rw [he,hg,JetCalculus.jet_add hlin (contDiff_const.mul hm),JetCalculus.jet_const_mul hm]
  have hlinear : JetCalculus.jet (fun s => v (c (Sum.inl s))) k
      (fun y => inner ℝ w y) y =
      if l=[] then (if c (Sum.inl (Sum.inr ()))=c (Sum.inr ()) then 1 else 0) else 0 := by
    simp only [k,JetCalculus.jet_append,JetCalculus.jet_map,JetCalculus.jet]
    have hd : JetCalculus.dir (v (c (Sum.inl (Sum.inr ())))) (fun y => inner ℝ w y)=
        fun _ => inner ℝ w (v (c (Sum.inl (Sum.inr ())))) := by
      funext z
      exact congrArg (fun A : Point d →L[ℝ] ℝ => A (v (c (Sum.inl (Sum.inr ())))))
        (innerSL ℝ w).hasFDerivAt.fderiv
    rw [hd,JetCalculus.jet_const]
    by_cases hl : l=[]
    · simp only [hl,↓reduceIte]
      change inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ _) (EuclideanSpace.basisFun (Fin d) ℝ _)=_
      rw [EuclideanSpace.basisFun_inner]
      simp [EuclideanSpace.basisFun_apply,eq_comm]
    · simp only [hl,↓reduceIte]
  dsimp only []
  rw [hlinear]
  have hmean := conditionalFieldMean_jet_normalized hF x hr hlam hl hρ0 hρ1 y k hklen c
  change JetCalculus.jet (fun s => v (c (Sum.inl s))) k
    (fun y => inner ℝ w (conditionalFieldMean F x r ρ y)) y=_ at hmean
  rw [hmean]
  simp only [Fintype.card_sum,Fintype.card_unique]
  ring

end LogConcaveSampling

end

end

end

end OAI
