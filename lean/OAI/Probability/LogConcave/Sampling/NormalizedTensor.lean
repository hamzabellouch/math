import Mathlib
import OAI.Probability.LogConcave.Sampling.ConditionalSlotEmbedding
import OAI.Probability.LogConcave.JetEstimates.AllSplitBound

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators RealInnerProductSpace NNReal

universe u

lemma list_split_perm {S I O : Type u} [Fintype I] [Fintype O]
    (l : List S) (hl : l.Nodup) (hall : ∀s,s∈l) (e : S ≃ I ⊕ O) :
    (l.map e).Perm ((Finset.univ.toList : List I).map Sum.inl ++
      (Finset.univ.toList : List O).map Sum.inr) := by
  apply (List.perm_ext_iff_of_nodup (hl.map e.injective) ?_).mpr
  · intro s
    constructor
    · intro _
      cases s <;> simp
    · intro _
      exact List.mem_map.mpr ⟨e.symm s,hall _,e.apply_symm_apply _⟩
  · simp only [List.nodup_append]
    refine ⟨(Finset.nodup_toList _).map Sum.inl_injective,
      (Finset.nodup_toList _).map Sum.inr_injective,?_⟩
    intro a ha b hb
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    obtain ⟨o,ho,rfl⟩ := List.mem_map.mp hb
    exact Sum.inl_ne_inr

def normalizedTensor {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ L : ℝ)
    (y : Point d) {S : Type u} [Fintype S] (mask : S → Bool) (l : List S)
    (c : S → Fin d) : ℝ :=
  ((1-ρ^2)^(Fintype.card S-1))⁻¹ * JetCalculus.jet
    (fun s => EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ
      (conditionalSlotEmbedding d mask c s)) l
    (fun z => Real.log (Appell.laplace (jointConditionalLaw F x r ρ y L)
      (fun _ => (1:ℝ)) z)) 0

def normalizedTensorMajorant (n : ℕ) (a : ℝ) : ℝ :=
  Real.sqrt (((n+1:ℕ):ℝ)^(2*(n+1))*(2*Real.pi^2)^n*
    ((n.factorial:ℝ)^2)^2/a^(n-2))

lemma normalizedTensorMajorant_nonneg (n : ℕ) (a : ℝ) :
    0≤normalizedTensorMajorant n a := Real.sqrt_nonneg _

lemma normalizedTensor_allSplit {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (y : Point d) {S : Type u} [Fintype S] (mask : S → Bool) (l : List S)
    (hlN : l.Nodup) (hlall : ∀s,s∈l) :
    TensorEnergy.AllSplitBound (normalizedTensor F x r ρ ((lam:ℝ)*r) y mask l)
      (normalizedTensorMajorant (Fintype.card S) (1-ρ^2)) := by
  intro I O _ _ _ _ _ _ e
  let f : S ≃ O ⊕ I := e.trans (Equiv.sumComm I O)
  let lo : List O := Finset.univ.toList
  let li : List I := Finset.univ.toList
  have hlo : lo≠[] := by
    intro h
    obtain ⟨o⟩ := ‹Nonempty O›
    have : o∈lo := by simp [lo]
    simp [h] at this
  have hli : li≠[] := by
    intro h
    obtain ⟨i⟩ := ‹Nonempty I›
    have : i∈li := by simp [li]
    simp [h] at this
  have h := conditional_normalized_tensor_energy hF x hr hlam hl hρ0 hρ1 y
    (fun o => mask (f.symm (Sum.inl o))) (fun i => mask (f.symm (Sum.inr i))) lo li
    (Finset.nodup_toList _) (by simp [lo]) (Finset.nodup_toList _) (by simp [li]) hlo hli
    (l.map f) (list_split_perm l hlN hlall f)
  have hc : Fintype.card S=Fintype.card O+Fintype.card I := by
    simpa using Fintype.card_congr f
  have ha : 0<1-ρ^2 := (probability_time hρ0 hρ1).1
  have hbound :
      (((Fintype.card O+Fintype.card I+1:ℕ):ℝ)^(2*(Fintype.card O+Fintype.card I+1)) *
        (2*Real.pi^2)^(Fintype.card O+Fintype.card I) *
        (((Fintype.card O).factorial:ℝ)*((Fintype.card I).factorial:ℝ))^2 /
        (1-ρ^2)^(Fintype.card O+Fintype.card I-2)) ≤
        (normalizedTensorMajorant (Fintype.card S) (1-ρ^2))^2 := by
    dsimp only [normalizedTensorMajorant]
    rw [Real.sq_sqrt (by positivity),hc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    rw [pow_two]
    apply mul_le_mul
    · exact_mod_cast Nat.factorial_le (Nat.le_add_right (Fintype.card O) (Fintype.card I))
    · exact_mod_cast Nat.factorial_le (Nat.le_add_left (Fintype.card I) (Fintype.card O))
    · positivity
    · positivity
  have hh := h.mono hbound
  convert hh using 1
  funext o i
  dsimp only [normalizedTensor]
  rw [hc,JetCalculus.jet_map]
  congr 2
  funext s
  have hs := f.symm_apply_apply s
  cases he : f s with
  | inl z =>
    have hse : s=f.symm (Sum.inl z) := by rw [←he,hs]
    subst s
    simp [f,conditionalSlotEmbedding,Function.comp_def]
    congr 1
    change (if mask _ then Sum.inr _ else Sum.inl _) = _
    simp
  | inr z =>
    have hse : s=f.symm (Sum.inr z) := by rw [←he,hs]
    subst s
    simp [f,conditionalSlotEmbedding,Function.comp_def]
    congr 1
    change (if mask _ then Sum.inr _ else Sum.inl _) = _
    simp

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace NNReal Topology

lemma joint_laplace_as_conditional {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (r ρ L : ℝ) (y : Point d) (θ : JointPoint d) :
    Appell.laplace (jointConditionalLaw F x r ρ y L) (fun _ => (1:ℝ)) θ=
      conditionalMeanScalar F x r ρ (fun z => Real.exp (inner ℝ θ
        (jointImage (primitiveField F x r) L z))) y := by
  have hs := (jointImage_contDiff (primitiveField_contDiff hF x r) L).continuous
  rw [Appell.laplace,jointConditionalLaw,integral_map hs.aemeasurable (by fun_prop)]
  simp only [smul_eq_mul,mul_one,conditionalMeanScalar]

lemma joint_laplace_shift {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (L : ℝ) (y h : Point d) (θ : JointPoint d) :
    Appell.laplace (jointConditionalLaw F x r ρ (y+h) L) (fun _ => (1:ℝ)) θ=
      Appell.laplace (jointConditionalLaw F x r ρ y L) (fun _ => (1:ℝ))
        (θ+jointPosition d ((ρ/(1-ρ^2)) • h)) /
      Appell.laplace (jointConditionalLaw F x r ρ y L) (fun _ => (1:ℝ))
        (jointPosition d ((ρ/(1-ρ^2)) • h)) := by
  rw [joint_laplace_as_conditional hF,conditionalMeanScalar_shift hF x hr hl hρ0 hρ1]
  simp only [Appell.normalizedLaplace,div_eq_mul_inv]
  rw [mul_comm]
  congr 1
  · rw [joint_laplace_as_conditional hF]
    unfold Appell.laplace conditionalMeanScalar
    congr 1
    funext z
    dsimp only
    rw [inner_add_left,Real.exp_add,jointPosition_inner]
    simp only [smul_eq_mul]
    ring
  · congr 1
    symm
    exact joint_laplace_one (primitiveField_contDiff hF x r).continuous L _

lemma joint_log_laplace_shift {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (y h : Point d) (θ : JointPoint d) :
    Real.log (Appell.laplace (jointConditionalLaw F x r ρ (y+h) ((lam:ℝ)*r))
      (fun _ => (1:ℝ)) θ)=
      Real.log (Appell.laplace (jointConditionalLaw F x r ρ y ((lam:ℝ)*r))
        (fun _ => (1:ℝ)) (θ+jointPosition d ((ρ/(1-ρ^2)) • h)))-
      Real.log (Appell.laplace (jointConditionalLaw F x r ρ y ((lam:ℝ)*r))
        (fun _ => (1:ℝ)) (jointPosition d ((ρ/(1-ρ^2)) • h))) := by
  obtain ⟨hp,hm,_⟩ := jointConditionalLaw_properties hF x hr hlam hl hρ0 hρ1 y
  let := hp
  rw [joint_laplace_shift hF x hr.le hl hρ0 hρ1]
  exact Real.log_div (Appell.laplace_one_pos hm _).ne' (Appell.laplace_one_pos hm _).ne'

lemma joint_log_laplace_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (y : Point d) : ContDiff ℝ (⊤ : ℕ∞) (fun θ => Real.log
      (Appell.laplace (jointConditionalLaw F x r ρ y ((lam:ℝ)*r))
        (fun _ => (1:ℝ)) θ)) := by
  obtain ⟨hp,hm,_⟩ := jointConditionalLaw_properties hF x hr hlam hl hρ0 hρ1 y
  let := hp
  exact (Appell.contDiff_laplace hm continuous_const (Appell.HasGrowth.const _)).log
    (fun θ => (Appell.laplace_one_pos hm θ).ne')

def jointCumulant {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ L : ℝ)
    {ι : Type*} (v : ι → JointPoint d) (l : List ι) (y : Point d) : ℝ :=
  JetCalculus.jet v l (fun θ => Real.log
    (Appell.laplace (jointConditionalLaw F x r ρ y L) (fun _ => (1:ℝ)) θ)) 0

lemma jointCumulant_shift {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (y h : Point d) {ι : Type*} (v : ι → JointPoint d) (l : List ι) (hlne : l≠[]) :
    jointCumulant F x r ρ ((lam:ℝ)*r) v l (y+h)=
      JetCalculus.jet v l (fun θ => Real.log
        (Appell.laplace (jointConditionalLaw F x r ρ y ((lam:ℝ)*r))
          (fun _ => (1:ℝ)) θ)) (jointPosition d ((ρ/(1-ρ^2)) • h)) := by
  let g := fun θ => Real.log (Appell.laplace
    (jointConditionalLaw F x r ρ y ((lam:ℝ)*r)) (fun _ => (1:ℝ)) θ)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := joint_log_laplace_smooth hF x hr hlam hl hρ0 hρ1 y
  have he : (fun θ => Real.log (Appell.laplace
      (jointConditionalLaw F x r ρ (y+h) ((lam:ℝ)*r)) (fun _ => (1:ℝ)) θ))=
      fun θ => g (θ+jointPosition d ((ρ/(1-ρ^2)) • h))-
        g (jointPosition d ((ρ/(1-ρ^2)) • h)) := by
    funext θ
    exact joint_log_laplace_shift hF x hr hlam hl hρ0 hρ1 y h θ
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun θ => g (θ+jointPosition d ((ρ/(1-ρ^2)) • h))) :=
    hg.comp (contDiff_id.add contDiff_const)
  unfold jointCumulant
  rw [he,JetCalculus.jet_sub hcomp (contDiff_const (c:=g (jointPosition d ((ρ/(1-ρ^2)) • h)))),
    JetCalculus.jet_const]
  simp only [hlne,↓reduceIte,sub_zero]
  have hh := congrFun (JetCalculus.jet_comp_affine hg
    (ContinuousLinearMap.id ℝ (JointPoint d)) (jointPosition d ((ρ/(1-ρ^2)) • h)) v l) 0
  simpa only [ContinuousLinearMap.id_apply,zero_add] using hh

lemma jointCumulant_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {ι : Type*} (v : ι → JointPoint d) (l : List ι) (hlne : l≠[]) :
    ContDiff ℝ (⊤ : ℕ∞) (jointCumulant F x r ρ ((lam:ℝ)*r) v l) := by
  have hg := JetCalculus.smooth_jet (joint_log_laplace_smooth hF x hr hlam hl hρ0 hρ1 0) v l
  have he : jointCumulant F x r ρ ((lam:ℝ)*r) v l =
      fun y => JetCalculus.jet v l (fun θ => Real.log (Appell.laplace
        (jointConditionalLaw F x r ρ 0 ((lam:ℝ)*r)) (fun _ => (1:ℝ)) θ))
        (jointPosition d ((ρ/(1-ρ^2)) • y)) := by
    funext y
    simpa only [zero_add] using jointCumulant_shift hF x hr hlam hl hρ0 hρ1 0 y v l hlne
  rw [he]
  exact hg.comp (by fun_prop)

lemma jointCumulant_spatial_jet {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (y : Point d) {ι κ : Type*} (v : ι → JointPoint d) (l : List ι) (hlne : l≠[])
    (w : κ → Point d) (k : List κ) :
    JetCalculus.jet w k (jointCumulant F x r ρ ((lam:ℝ)*r) v l) y=
      (ρ/(1-ρ^2))^k.length * JetCalculus.jet (fun i => jointPosition d (w i)) k
        (JetCalculus.jet v l (fun θ => Real.log (Appell.laplace
          (jointConditionalLaw F x r ρ y ((lam:ℝ)*r)) (fun _ => (1:ℝ)) θ))) 0 := by
  let g := fun θ => Real.log (Appell.laplace
    (jointConditionalLaw F x r ρ y ((lam:ℝ)*r)) (fun _ => (1:ℝ)) θ)
  have hg := JetCalculus.smooth_jet (joint_log_laplace_smooth hF x hr hlam hl hρ0 hρ1 y) v l
  let B : Point d →L[ℝ] JointPoint d := (ρ/(1-ρ^2)) • jointPosition d
  have hs := jointCumulant_smooth hF x hr hlam hl hρ0 hρ1 v l hlne
  have htrans := congrFun (JetCalculus.jet_comp_affine hs
    (ContinuousLinearMap.id ℝ (Point d)) y w k) 0
  have he : (fun h => jointCumulant F x r ρ ((lam:ℝ)*r) v l (h+y))=
      fun h => JetCalculus.jet v l g (B h+0) := by
    funext h
    simpa only [add_comm h y,B,smul_apply,map_smul,add_zero]
      using jointCumulant_shift hF x hr hlam hl hρ0 hρ1 y h v l hlne
  simp only [ContinuousLinearMap.id_apply,zero_add] at htrans
  rw [←htrans,he,JetCalculus.jet_comp_affine hg B 0]
  simp only [map_zero,zero_add]
  have hB : (fun i => B (w i))=fun i => (ρ/(1-ρ^2)) • jointPosition d (w i) := rfl
  rw [hB,JetCalculus.jet_smul hg]

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

universe u

lemma list_length_full {S : Type u} [Fintype S] (l : List S)
    (hl : l.Nodup) (hall : ∀s,s∈l) : l.length=Fintype.card S := by
  have he : l.toFinset=Finset.univ := Finset.eq_univ_of_forall (fun s => List.mem_toFinset.mpr (hall s))
  rw [←List.toFinset_card_of_nodup hl,he,Finset.card_univ]

lemma normalizedTensor_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {S : Type u} [Fintype S] (mask : S → Bool) (l : List S) (hlne : l≠[])
    (c : S → Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => normalizedTensor F x r ρ ((lam:ℝ)*r) y mask l c) :=
  contDiff_const.mul (jointCumulant_smooth hF x hr hlam hl hρ0 hρ1 _ l hlne)

lemma normalizedTensor_spatial_jet {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (y : Point d) {S K : Type u} [Fintype S] [Fintype K]
    (mask : S → Bool) (l : List S) (hlne : l≠[]) (hS : 0<Fintype.card S)
    (k : List K) (hklen : k.length=Fintype.card K) (c : K ⊕ S → Fin d) :
    JetCalculus.jet (fun i => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl i))) k
      (fun y => normalizedTensor F x r ρ ((lam:ℝ)*r) y mask l (fun s => c (Sum.inr s))) y=
      ρ^(Fintype.card K)*normalizedTensor F x r ρ ((lam:ℝ)*r) y
        (Sum.elim (fun _ => false) mask) (k.map Sum.inl++l.map Sum.inr) c := by
  let g := fun θ => Real.log (Appell.laplace
    (jointConditionalLaw F x r ρ y ((lam:ℝ)*r)) (fun _ => (1:ℝ)) θ)
  let v := fun s => EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ
    (conditionalSlotEmbedding d mask (fun s => c (Sum.inr s)) s)
  let w := fun i => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl i))
  have hs := jointCumulant_smooth hF x hr hlam hl hρ0 hρ1 v l hlne
  change JetCalculus.jet w k (fun y => ((1-ρ^2)^(Fintype.card S-1))⁻¹*
    jointCumulant F x r ρ ((lam:ℝ)*r) v l y) y=_
  rw [JetCalculus.jet_const_mul hs]
  dsimp only
  rw [jointCumulant_spatial_jet hF x hr hlam hl hρ0 hρ1 y v l hlne w k]
  have he : (fun t : K ⊕ S => EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ
      (conditionalSlotEmbedding d (Sum.elim (fun _ => false) mask) c t))=
      Sum.elim (fun i => jointPosition d (w i)) v := by
    funext t
    cases t with
    | inl i =>
      change EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ (Sum.inl (c (Sum.inl i)))=_
      exact (jointPosition_basis _).symm
    | inr s => rfl
  unfold normalizedTensor
  rw [he,JetCalculus.jet_append,JetCalculus.jet_map,JetCalculus.jet_map]
  simp only [Function.comp_def,Sum.elim_inl,Sum.elim_inr,Fintype.card_sum,hklen]
  have ha : 1-ρ^2≠0 := (probability_time hρ0 hρ1).1.ne'
  have hn : Fintype.card K+Fintype.card S-1=(Fintype.card S-1)+Fintype.card K := by omega
  rw [hn,pow_add,div_pow]
  field_simp

end LogConcaveSampling

end

end

end

end OAI
