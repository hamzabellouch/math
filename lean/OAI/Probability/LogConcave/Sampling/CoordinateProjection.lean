import Mathlib
import OAI.Probability.LogConcave.JetEstimates.Squared
import OAI.Probability.LogConcave.JetEstimates.Extend

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Function
open scoped Classical BigOperators
open TensorEnergy

def coordinateProjection {d D : ℕ} (e : Fin d ↪ Fin D) : Point D →L[ℝ] Point d :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => PiLp.proj 2 (fun _ : Fin D => ℝ) (e i)))

@[simp] lemma coordinateProjection_apply {d D : ℕ} (e : Fin d ↪ Fin D)
    (y : Point D) (i : Fin d) : coordinateProjection e y i=y (e i) := rfl

lemma coordinateProjection_basis_in {d D : ℕ} (e : Fin d ↪ Fin D) (i : Fin d) :
    coordinateProjection e (EuclideanSpace.basisFun (Fin D) ℝ (e i))=
      EuclideanSpace.basisFun (Fin d) ℝ i := by
  ext j
  simp only [coordinateProjection_apply,EuclideanSpace.basisFun_apply,PiLp.single_apply]
  simp only [e.injective.eq_iff]

lemma coordinateProjection_basis_out {d D : ℕ} (e : Fin d ↪ Fin D) {i : Fin D}
    (hi : i∉Set.range e) : coordinateProjection e (EuclideanSpace.basisFun (Fin D) ℝ i)=0 := by
  ext j
  simp only [coordinateProjection_apply,EuclideanSpace.basisFun_apply,PiLp.single_apply,PiLp.zero_apply]
  exact ite_eq_right (fun h => hi ⟨j,h⟩)

lemma slotEmbedding_mem_range {S : Type*} {d D : ℕ} (e : S → Fin d ↪ Fin D) (c : S → Fin D) :
    c∈Set.range (slotEmbedding e) ↔ ∀s,c s∈Set.range (e s) := by
  constructor
  · rintro ⟨a,rfl⟩ s
    exact ⟨a s,rfl⟩
  · intro h
    choose a ha using h
    exact ⟨a,funext ha⟩

namespace JetCalculus
lemma jet_eq_zero_of_direction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Type*} (v : S → E) (l : List S) (f : E → ℝ) {s : S} (hs : s∈l) (hv : v s=0) :
    jet v l f=fun _ => 0 := by
  induction l with
  | nil => simp at hs
  | cons i l ih =>
    rcases List.mem_cons.mp hs with rfl|hs
    · simp only [jet,hv,dir_zero]
    · rw [jet,ih hs]
      funext x
      simp [dir]
end JetCalculus

def arrayCoordinateLift {S : Type} {d D : ℕ} (e : Fin d ↪ Fin D)
    (ι : S → Fin d ↪ Fin D) (F : (S → Fin d) → Point d → ℝ) :
    (S → Fin D) → Point D → ℝ :=
  fun c y => TensorEnergy.zeroExtend (slotEmbedding ι) (fun a => F a (coordinateProjection e y)) c

lemma arrayCoordinateLift_smooth {S : Type} {d D : ℕ} (e : Fin d ↪ Fin D)
    (ι : S → Fin d ↪ Fin D) (F : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) (c : S → Fin D) :
    ContDiff ℝ (⊤:ℕ∞) (arrayCoordinateLift e ι F c) := by
  by_cases hc : c∈Set.range (slotEmbedding ι)
  · obtain ⟨a,rfl⟩ := hc
    change ContDiff ℝ (⊤:ℕ∞) (fun y => TensorEnergy.zeroExtend (slotEmbedding ι) (fun a => F a (coordinateProjection e y)) (slotEmbedding ι a))
    simp only [zeroExtend_apply]
    exact (hF a).comp (coordinateProjection e).contDiff
  · have he : arrayCoordinateLift e ι F c=fun _ => 0 := by
      funext y; exact zeroExtend_out _ _ hc
    rw [he]; exact contDiff_const

lemma spatialTensor_coordinateLift {S J : Type} [Fintype J] {d D : ℕ}
    (e : Fin d ↪ Fin D) (ι : S → Fin d ↪ Fin D) (F : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) (l : List J) (hl : ∀j,j∈l) (y : Point D) :
    spatialTensor (arrayCoordinateLift e ι F) l y=
      TensorEnergy.zeroExtend (slotEmbedding (Sum.elim (fun _ : J => e) ι))
        (spatialTensor F l (coordinateProjection e y)) := by
  funext c
  by_cases hc : c∈Set.range (slotEmbedding (Sum.elim (fun _ : J => e) ι))
  · obtain ⟨a,rfl⟩ := hc
    rw [zeroExtend_apply]
    unfold spatialTensor arrayCoordinateLift
    have hc : (fun s => slotEmbedding (Sum.elim (fun _ : J => e) ι) a (.inr s))=
        slotEmbedding ι (fun s => a (.inr s)) := rfl
    rw [hc]
    simp only [zeroExtend_apply,slotEmbedding_apply,Sum.elim_inl]
    have hh := JetCalculus.jet_comp_affine (hF (fun s => a (.inr s))) (coordinateProjection e) 0
      (fun j => EuclideanSpace.basisFun (Fin D) ℝ (e (a (.inl j)))) l
    simp only [add_zero,coordinateProjection_basis_in] at hh
    exact congrFun hh y
  · rw [zeroExtend_out _ _ hc]
    by_cases hs : (fun s => c (.inr s))∈Set.range (slotEmbedding ι)
    · obtain ⟨a,ha⟩ := hs
      have hj : ∃j : J,c (.inl j)∉Set.range e := by
        by_contra! hj
        apply hc
        rw [slotEmbedding_mem_range]
        rintro (j|s)
        · exact hj j
        · exact ⟨a s,congrFun ha s⟩
      obtain ⟨j,hj⟩ := hj
      unfold spatialTensor arrayCoordinateLift
      rw [←ha]
      simp only [zeroExtend_apply]
      have hh := JetCalculus.jet_comp_affine (hF a) (coordinateProjection e) 0
        (fun j => EuclideanSpace.basisFun (Fin D) ℝ (c (.inl j))) l
      simp only [add_zero] at hh
      rw [hh,JetCalculus.jet_eq_zero_of_direction _ l _ (hl j) (coordinateProjection_basis_out e hj)]
    · have he : arrayCoordinateLift e ι F (fun s => c (.inr s))=fun _ => 0 := by
        funext z; exact zeroExtend_out _ _ hs
      change JetCalculus.jet _ l (arrayCoordinateLift e ι F _) y=0
      rw [he,JetCalculus.jet_const]
      split_ifs <;> rfl

lemma AllSplitBound.coordinateLift {S : Type} [Fintype S] {d D j : ℕ}
    (e : Fin d ↪ Fin D) (ι : S → Fin d ↪ Fin D) (F : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) {M : ℝ}
    (hb : ∀x,AllSplitBound (spatialTensor F (List.finRange j) x) M) (y : Point D) :
    AllSplitBound (spatialTensor (arrayCoordinateLift e ι F) (List.finRange j) y) M := by
  rw [spatialTensor_coordinateLift e ι F hF _ (fun k => List.mem_finRange k) y]
  exact (hb _).zeroExtend _
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators
open TensorEnergy

lemma squared_zeroExtend {S : Type} [Fintype S] {d D : ℕ}
    (e : (S → Fin d) ↪ (S → Fin D)) (F : (S → Fin d) → ℝ) :
    squared (zeroExtend e F)=squared F := by
  exact (congrArg (fun f : (S → Fin D) → ℝ => ∑c,f c) (zeroExtend_sq e F)).trans
    (zeroExtend_sum e (fun a => (F a)^2))
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators RealInnerProductSpace

def productPointEquiv (d e : ℕ) : Point (d+e) ≃L[ℝ] Point d × Point e :=
  EuclideanSpace.finAddEquivProd

lemma productPointEquiv_volume (d e : ℕ) :
    MeasurePreserving (productPointEquiv d e) := by
  have h₁ := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (finSumFinEquiv.symm : Fin (d+e) ≃ Fin d ⊕ Fin e)).measurePreserving
  have h₂ := (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin d ⊕ Fin e => ℝ)).measurePreserving
  have h₃ := WithLp.volume_preserving_ofLp (Point d) (Point e)
  exact h₃.comp (h₂.comp h₁)

lemma productPointEquiv_norm_sq {d e : ℕ} (y : Point (d+e)) :
    ‖y‖^2=‖(productPointEquiv d e y).1‖^2+‖(productPointEquiv d e y).2‖^2 := by
  let T := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (finSumFinEquiv.symm : Fin (d+e) ≃ Fin d ⊕ Fin e)
  have hh := PiLp.norm_sq_eq_of_L2 (fun _ : Fin d ⊕ Fin e => ℝ) (T y)
  simp only [Real.norm_eq_abs,sq_abs,Fintype.sum_sum_type] at hh
  rw [T.norm_map] at hh
  simpa [productPointEquiv,T,EuclideanSpace.finAddEquivProd,EuclideanSpace.sumEquivProd,EuclideanSpace.real_norm_sq_eq] using hh

def productPotential {d e : ℕ} (H : Point d → ℝ) (G : Point e → ℝ)
    (y : Point (d+e)) : ℝ := H (productPointEquiv d e y).1+G (productPointEquiv d e y).2

lemma productPotential_density {d e : ℕ} (H : Point d → ℝ) (G : Point e → ℝ)
    (y : Point (d+e)) : gibbsDensity (productPotential H G) y=
      gibbsDensity H (productPointEquiv d e y).1*gibbsDensity G (productPointEquiv d e y).2 := by
  simp only [gibbsDensity,productPotential,neg_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _)]
end LogConcaveSampling

end

end

end

end OAI
