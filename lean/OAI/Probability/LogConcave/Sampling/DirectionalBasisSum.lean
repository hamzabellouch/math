import Mathlib
import OAI.Probability.LogConcave.JetEstimates.PolySmooth
import OAI.Probability.LogConcave.Sampling.NormalizedTensor
import OAI.Probability.LogConcave.JetEstimates.ContractLeftSplit

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators RealInnerProductSpace

lemma directional_basis_sum {d : ℕ} (v : Point d) (f : Point d → ℝ) :
    directional v f=fun x => ∑i : Fin d,
      (EuclideanSpace.basisFun (Fin d) ℝ).repr v i *
        directional (EuclideanSpace.basisFun (Fin d) ℝ i) f x := by
  funext x
  unfold directional
  conv_lhs => arg 2; rw [←(EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v]
  simp only [map_sum,map_smul,smul_eq_mul]

lemma basis_jet_growth_all {d : ℕ} {f : Point d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ∀l : List (Fin d),HasPolynomialGrowth
      (JetCalculus.jet (EuclideanSpace.basisFun (Fin d) ℝ) l f))
    (l : List (Point d)) : HasPolynomialGrowth (JetCalculus.jet id l f) := by
  induction l generalizing f with
  | nil => exact hg []
  | cons v l ih =>
    change HasPolynomialGrowth (directional v (JetCalculus.jet id l f))
    rw [←jet_directional hf,directional_basis_sum,
      JetCalculus.jet_sum Finset.univ (fun i _ =>
        contDiff_const.mul (directional_smooth hf _))]
    apply Appell.HasGrowth.sum
    intro i _
    rw [JetCalculus.jet_const_mul (directional_smooth hf _)]
    apply Appell.HasGrowth.mul (growth_const _)
    apply ih (directional_smooth hf _)
    intro k
    have hh := hg (k++[i])
    have he : JetCalculus.jet (EuclideanSpace.basisFun (Fin d) ℝ) [i] f=
        directional (EuclideanSpace.basisFun (Fin d) ℝ i) f := rfl
    rw [JetCalculus.jet_append,he] at hh
    exact hh

lemma PolySmooth.of_basis_growth {d : ℕ} {f : Point d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ∀l : List (Fin d),HasPolynomialGrowth
      (JetCalculus.jet (EuclideanSpace.basisFun (Fin d) ℝ) l f)) : PolySmooth f :=
  ⟨hf,basis_jet_growth_all hf hg⟩

lemma growth_of_bounded {d : ℕ} {f : Point d → ℝ} {B : ℝ}
    (hB : 0≤B) (h : ∀x,|f x|≤B) : HasPolynomialGrowth f := by
  refine ⟨B,hB,0,fun x => ?_⟩
  simp only [pow_zero,Real.norm_eq_abs]
  exact (h x).trans (by linarith)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

universe u

lemma normalizedTensor_spatial_allSplit {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (y : Point d) {S K : Type u} [Fintype S] [Fintype K]
    (mask : S → Bool) (l : List S) (hlne : l≠[])
    (hlN : l.Nodup) (hlall : ∀s,s∈l) (k : List K) (hkN : k.Nodup) (hkall : ∀i,i∈k) :
    TensorEnergy.AllSplitBound (fun c : K ⊕ S → Fin d =>
      JetCalculus.jet (fun i => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl i))) k
        (fun y => normalizedTensor F x r ρ ((lam:ℝ)*r) y mask l (fun s => c (Sum.inr s))) y)
      (normalizedTensorMajorant (Fintype.card K+Fintype.card S) (1-ρ^2)) := by
  have hS : 0<Fintype.card S := by
    rw [←list_length_full l hlN hlall]
    exact List.length_pos_iff.mpr hlne
  have he := normalizedTensor_spatial_jet hF x hr hlam hl hρ0 hρ1 y mask l hlne hS
    k (list_length_full k hkN hkall)
  simp_rw [he]
  have hN : (k.map Sum.inl++l.map Sum.inr).Nodup := JetCalculus.nodup_sum_append hkN hlN
  have hall : ∀t : K ⊕ S,t∈k.map Sum.inl++l.map Sum.inr := by
    intro t
    cases t <;> simp [hkall,hlall]
  have hh := (normalizedTensor_allSplit hF x hr hlam hl hρ0 hρ1 y
    (Sum.elim (fun _ => false) mask) (k.map Sum.inl++l.map Sum.inr) hN hall).const_mul
    (ρ^(Fintype.card K))
  simp only [Fintype.card_sum] at hh
  apply hh.mono (mul_nonneg (pow_nonneg hρ0 _) (normalizedTensorMajorant_nonneg _ _))
  exact mul_le_of_le_one_left (normalizedTensorMajorant_nonneg _ _)
    (pow_le_one₀ hρ0 hρ1.le)

lemma normalizedTensor_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {S : Type} [Fintype S] (mask : S → Bool) (l : List S)
    (hlN : l.Nodup) (hlall : ∀s,s∈l) (hS : 2≤Fintype.card S) (c : S → Fin d) :
    PolySmooth (fun y => normalizedTensor F x r ρ ((lam:ℝ)*r) y mask l c) := by
  have hlne : l≠[] := by
    intro he
    have hh := list_length_full l hlN hlall
    simp [he] at hh
    omega
  apply PolySmooth.of_basis_growth (normalizedTensor_smooth hF x hr hlam hl hρ0 hρ1 mask l hlne c)
  intro k
  apply growth_of_bounded (normalizedTensorMajorant_nonneg (k.length+Fintype.card S) (1-ρ^2))
  intro y
  have hh := (normalizedTensor_spatial_allSplit hF x hr hlam hl hρ0 hρ1 y mask l hlne hlN hlall
    (List.finRange k.length) (List.nodup_finRange _) (by simp)).entry_le
      (normalizedTensorMajorant_nonneg _ _) (by simp only [Fintype.card_sum,Fintype.card_fin]; omega)
      (Sum.elim k.get c)
  simp only [Sum.elim_inl,Sum.elim_inr,Fintype.card_fin] at hh
  change |JetCalculus.jet ((EuclideanSpace.basisFun (Fin d) ℝ) ∘ k.get)
    (List.finRange k.length) (fun y => normalizedTensor F x r ρ ((lam:ℝ)*r) y mask l c) y|≤_ at hh
  rw [←JetCalculus.jet_map, List.map_get_finRange] at hh
  exact hh

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma conditionalFieldMean_jet_normalized {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (y : Point d) {S : Type} [Fintype S] (l : List S) (hlen : l.length=Fintype.card S)
    (c : S ⊕ Unit → Fin d) :
    JetCalculus.jet (fun s => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl s))) l
      (fun y => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr ())))
        (conditionalFieldMean F x r ρ y)) y=
      ρ^(Fintype.card S)*((lam:ℝ)*r)*normalizedTensor F x r ρ ((lam:ℝ)*r) y
        (Sum.elim (fun _ => false) (fun _ => true)) (l.map Sum.inl++[Sum.inr ()]) c := by
  have hi : (fun y => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr ())))
      (conditionalFieldMean F x r ρ y))=
      conditionalMeanScalar F x r ρ (fun z => inner ℝ
        (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr ()))) (primitiveField F x r z)) :=
    funext (conditionalFieldMean_inner hF x hr.le hl hρ0 hρ1 _)
  rw [hi,conditionalFieldMean_jet_U hF x hr hlam hl hρ0 hρ1]
  unfold conditionalU normalizedTensor
  rw [JetCalculus.jet_append,JetCalculus.jet_map]
  simp only [Fintype.card_sum,Fintype.card_unique,add_tsub_cancel_right,hlen,
    Function.comp_def]
  have hv : (fun s => jointPosition d (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl s))))=
      (fun s => EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ
        (conditionalSlotEmbedding d (Sum.elim (fun _ => false) (fun _ => true)) c (Sum.inl s))) := by
    funext s
    exact jointPosition_basis _
  rw [hv,jointField_basis]
  have he : conditionalSlotEmbedding d (Sum.elim (fun _ : S => false) (fun _ : Unit => true)) c
      (Sum.inr ())=Sum.inr (c (Sum.inr ())) := rfl
  simp only [JetCalculus.jet,he]
  ring

lemma conditionalFieldMean_component_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (i : Fin d) : PolySmooth (fun y => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
      (conditionalFieldMean F x r ρ y)) := by
  let v := EuclideanSpace.basisFun (Fin d) ℝ i
  have hs := (innerSL ℝ v).contDiff.comp (conditionalFieldMean_smooth hF x hr.le hl hρ0 hρ1)
  apply PolySmooth.of_basis_growth hs
  intro k
  by_cases hk : k=[]
  · subst k
    exact growth_of_lipschitz ((innerSL ℝ v).lipschitzWith.comp
      (conditionalFieldMean_lipschitz hF x hr.le hl hρ0 hρ1))
  · let c : Fin k.length ⊕ Unit → Fin d := Sum.elim k.get (fun _ => i)
    have he : JetCalculus.jet (EuclideanSpace.basisFun (Fin d) ℝ) k
        (fun y => inner ℝ v (conditionalFieldMean F x r ρ y))=
        fun y => ρ^k.length*((lam:ℝ)*r)*normalizedTensor F x r ρ ((lam:ℝ)*r) y
          (Sum.elim (fun _ => false) (fun _ => true))
          ((List.finRange k.length).map Sum.inl++[Sum.inr ()]) c := by
      funext y
      have hh := conditionalFieldMean_jet_normalized hF x hr hlam hl hρ0 hρ1 y
        (List.finRange k.length) (by simp) c
      simp only [c,Sum.elim_inl,Sum.elim_inr,Fintype.card_fin] at hh
      change JetCalculus.jet ((EuclideanSpace.basisFun (Fin d) ℝ) ∘ k.get)
        (List.finRange k.length) _ y=_ at hh
      rw [←JetCalculus.jet_map,List.map_get_finRange] at hh
      exact hh
    change HasPolynomialGrowth (JetCalculus.jet (EuclideanSpace.basisFun (Fin d) ℝ) k
      (fun y => inner ℝ v (conditionalFieldMean F x r ρ y)))
    rw [he]
    apply Appell.HasGrowth.mul (growth_const _)
    have hN : ((List.finRange k.length).map (Sum.inl : Fin k.length → Fin k.length ⊕ Unit)++
        [Sum.inr ()]).Nodup := by
      simpa using JetCalculus.nodup_sum_append (List.nodup_finRange k.length)
        (by simp : ([()] : List Unit).Nodup)
    have hall : ∀t : Fin k.length ⊕ Unit,t∈(List.finRange k.length).map Sum.inl++[Sum.inr ()] := by
      intro t; cases t <;> simp
    exact (normalizedTensor_polySmooth hF x hr hlam hl hρ0 hρ1 _ _ hN hall
      (by simp; exact List.length_pos_iff.mpr hk) c).growth []

end LogConcaveSampling

end

end

end

end OAI
