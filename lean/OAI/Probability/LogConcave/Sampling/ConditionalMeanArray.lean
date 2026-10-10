import Mathlib
import OAI.Probability.LogConcave.Sampling.TensorVector

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace NNReal
open TensorEnergy

lemma scoreAugmented_gaussian {d : ℕ} {K : Type} (l : List K)
    (y : Point d) (c : (K ⊕ Unit) ⊕ Unit → Fin d) :
    scoreAugmented (fun z : Point d => ‖z‖^2/2) l y c=
      if l=[] then (if c (.inl (.inr ()))=c (.inr ()) then 1 else 0) else 0 := by
  let v := EuclideanSpace.basisFun (Fin d) ℝ
  have hg : directional (v (c (.inr ()))) (fun z : Point d => ‖z‖^2/2)=
      fun z => inner ℝ (v (c (.inr ()))) z := by
    funext z
    rw [directional_gaussianPotential,real_inner_comm]
  have hd : directional (v (c (.inl (.inr ()))))
      (fun z => inner ℝ (v (c (.inr ()))) z)=fun _ =>
      inner ℝ (v (c (.inr ()))) (v (c (.inl (.inr ())))) := by
    funext z
    exact congrArg (fun A : Point d →L[ℝ] ℝ => A (v (c (.inl (.inr ())))))
      (innerSL ℝ (v (c (.inr ())))).hasFDerivAt.fderiv
  unfold scoreAugmented
  change JetCalculus.jet _ l (directional _ (directional (v (c (.inr ()))) _)) y=_
  rw [hg,hd,JetCalculus.jet_const]
  by_cases hl : l=[]
  · simp only [hl,↓reduceIte]
    rw [EuclideanSpace.basisFun_inner]
    simp [EuclideanSpace.basisFun_apply,v,eq_comm]
  · simp only [hl,↓reduceIte]

lemma scoreField_gaussian_allSplit {d n : ℕ} (hn : 0<n) (y : Point d) :
    AllSplitBound (spatialTensor (scoreField (fun z : Point d => ‖z‖^2/2))
      (List.finRange n) y) 1 := by
  obtain ⟨h,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hh := (allSplitBound_spatial_delta (d:=d) (List.finRange h) (by simp)).reindex (scoreSpatialSlots h)
  have he : (fun c => (if List.finRange h=[] then
        (if (c ∘ scoreSpatialSlots h) (.inl (.inr ()))=(c ∘ scoreSpatialSlots h) (.inr ()) then (1:ℝ) else 0) else 0))=
      spatialTensor (scoreField (fun z : Point d => ‖z‖^2/2)) (List.finRange (h+1)) y := by
    funext c
    rw [←scoreAugmented_gaussian,scoreSpatial_eq]
  change AllSplitBound (fun c => (if List.finRange h=[] then
        (if (c ∘ scoreSpatialSlots h) (.inl (.inr ()))=(c ∘ scoreSpatialSlots h) (.inr ()) then (1:ℝ) else 0) else 0)) _ at hh
  rw [he] at hh
  apply hh.mono
  · split_ifs <;> norm_num
  · split_ifs <;> norm_num

lemma centeringScore_allSplit {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (hn : 0<n) (y : Point (d+d)) :
    AllSplitBound (spatialTensor (scoreField (productPotential
      (interpolationPotential F x r T) (fun z : Point d => ‖z‖^2/2)))
      (List.finRange n) y) (2+normalizedTensorMajorant (n+1) (1-T^2)) := by
  convert scoreField_product_allSplit
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
    (add_nonneg (by norm_num : (0:ℝ)≤1) (normalizedTensorMajorant_nonneg _ _))
    (by norm_num : (0:ℝ)≤1) (scoreField_spatial_allSplit hF x hr hlam hl hT0 hT1 n hn)
    (scoreField_gaussian_allSplit hn) y using 1
  ring
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy

lemma probability_gibbs_of_gaussianTail {d : ℕ} {H : Point d → ℝ}
    (hH : Continuous H) (ht : HasGaussianLowerTail H) : IsProbabilityMeasure (gibbs H) := by
  have hi : Integrable (fun z => Real.exp (-H z)) := by
    simpa only [inner_zero_left,zero_sub,smul_eq_mul,mul_one] using
      integrable_tilted H hH continuous_const ht (growth_const (1:ℝ)) 0
  exact probability_gibbs_of_partition (partition_pos_of_continuous hH).ne'
    (partition_ne_top_of_integrable hi)

def conditionalMeanArray {d : ℕ} (F : Point d → ℝ) (x : Point d) (r T : ℝ)
    (c : Unit → Fin d) (y : Point d) : ℝ :=
  inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c ())) (conditionalFieldMean F x r T y)

lemma conditionalMeanArray_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (c : Unit → Fin d) : PolySmooth (conditionalMeanArray F x r T c) :=
  conditionalFieldMean_component_polySmooth hF x hr hlam hl hT0 hT1 (c ())

lemma conditionalMeanArray_allSplit {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (y : Point d) :
    AllSplitBound (spatialTensor (conditionalMeanArray F x r T) (List.finRange n) y)
      ((lam:ℝ)*r*normalizedTensorMajorant (n+1) (1-T^2)) := by
  let mask : Fin n ⊕ Unit → Bool := Sum.elim (fun _ => false) (fun _ => true)
  let l : List (Fin n ⊕ Unit) := (List.finRange n).map Sum.inl++[Sum.inr ()]
  have hnodup : l.Nodup := by
    simpa [l] using JetCalculus.nodup_sum_append (List.nodup_finRange n)
      (by simp : ([()] : List Unit).Nodup)
  have hall : ∀s,s∈l := by intro s; cases s <;> simp [l]
  have hh := (normalizedTensor_allSplit hF x hr hlam hl hT0 hT1 y mask l hnodup hall).const_mul
    (T^n*((lam:ℝ)*r))
  have he : spatialTensor (conditionalMeanArray F x r T) (List.finRange n) y=
      fun c => T^n*((lam:ℝ)*r)*normalizedTensor F x r T ((lam:ℝ)*r) y mask l c := by
    funext c
    unfold spatialTensor
    have hf : conditionalMeanArray F x r T (fun s => c (Sum.inr s))=
        (fun z => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr ())))
          (conditionalFieldMean F x r T z)) := rfl
    rw [hf]
    simpa only [Fintype.card_fin,mask,l] using
      conditionalFieldMean_jet_normalized hF x hr hlam hl hT0 hT1 y
        (List.finRange n) (by simp) c
  rw [he]
  simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_unique] at hh
  apply hh.mono
  · exact mul_nonneg (mul_nonneg (pow_nonneg hT0 _) (mul_nonneg lam.2 hr.le))
      (normalizedTensorMajorant_nonneg _ _)
  ·
    have ht : T^n≤1 := pow_le_one₀ hT0 hT1.le
    have ht' : T^n*((lam:ℝ)*r)≤(lam:ℝ)*r := by
      calc
        _ ≤ 1*((lam:ℝ)*r) := mul_le_mul_of_nonneg_right ht (mul_nonneg lam.2 hr.le)
        _ = _ := one_mul _
    exact mul_le_mul_of_nonneg_right ht' (normalizedTensorMajorant_nonneg _ _)

lemma conditionalMeanArray_energy {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (hn : 0<n) :
    spatialEnergy (conditionalMeanArray F x r T) n (gibbs (interpolationPotential F x r T))≤
      d*((lam:ℝ)*r)^2*(normalizedTensorMajorant (n+1) (1-T^2))^2 := by
  have hH := interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1
  have ht := interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1
  let := probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  exact (spatialEnergy_from_split hH.smooth.continuous ht _
    (conditionalMeanArray_polySmooth hF x hr hlam hl hT0 hT1) hn
    (conditionalMeanArray_allSplit hF x hr hlam hl hT0 hT1)).trans_eq (by ring)
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma directional_basis_gradient {d : ℕ} (H : Point d → ℝ) (y : Point d) (i : Fin d) :
    directional (EuclideanSpace.basisFun (Fin d) ℝ i) H y=gradient H y i := by
  rw [directional_gradient]
  have hh (v : Point d) : inner ℝ v (EuclideanSpace.basisFun (Fin d) ℝ i)=v i := by
    simp [EuclideanSpace.basisFun_apply,PiLp.inner_apply]
  exact hh (gradient H y)

lemma gradient_productPotential {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : Differentiable ℝ H) (hG : Differentiable ℝ G) (y : Point (d+e)) :
    productPointEquiv d e (gradient (productPotential H G) y)=
      (gradient H (productPointEquiv d e y).1,gradient G (productPointEquiv d e y).2) := by
  apply Prod.ext
  · ext i
    change gradient (productPotential H G) y (Fin.castAdd e i)=_
    rw [←directional_basis_gradient,productPotential_directional_left hH hG,directional_basis_gradient]
  · ext i
    change gradient (productPotential H G) y (Fin.natAdd d i)=_
    rw [←directional_basis_gradient,productPotential_directional_right hH hG,directional_basis_gradient]

lemma productPointEquiv_fst_norm_le {d e : ℕ} (y : Point (d+e)) :
    ‖(productPointEquiv d e y).1‖≤‖y‖ := by
  nlinarith [productPointEquiv_norm_sq y,sq_nonneg ‖(productPointEquiv d e y).2‖,
    norm_nonneg y,norm_nonneg (productPointEquiv d e y).1]
lemma productPointEquiv_snd_norm_le {d e : ℕ} (y : Point (d+e)) :
    ‖(productPointEquiv d e y).2‖≤‖y‖ := by
  nlinarith [productPointEquiv_norm_sq y,sq_nonneg ‖(productPointEquiv d e y).1‖,
    norm_nonneg y,norm_nonneg (productPointEquiv d e y).2]

lemma productPotential_gradient_lipschitz {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : Differentiable ℝ H) (hG : Differentiable ℝ G) {K L : ℝ≥0}
    (hK : LipschitzWith K (gradient H)) (hL : LipschitzWith L (gradient G)) :
    LipschitzWith (K+L) (gradient (productPotential H G)) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  simp only [dist_eq_norm,NNReal.coe_add]
  have h1 := hK.dist_le_mul (productPointEquiv d e y).1 (productPointEquiv d e z).1
  have h2 := hL.dist_le_mul (productPointEquiv d e y).2 (productPointEquiv d e z).2
  simp only [dist_eq_norm] at h1 h2
  have hp := productPointEquiv_norm_sq (gradient (productPotential H G) y-gradient (productPotential H G) z)
  rw [map_sub,gradient_productPotential hH hG,gradient_productPotential hH hG] at hp
  simp only [Prod.fst_sub,Prod.snd_sub] at hp
  have h1' := productPointEquiv_fst_norm_le (y-z)
  have h2' := productPointEquiv_snd_norm_le (y-z)
  simp only [map_sub,Prod.fst_sub,Prod.snd_sub] at h1' h2'
  have h1'' := h1.trans (mul_le_mul_of_nonneg_left h1' K.2)
  have h2'' := h2.trans (mul_le_mul_of_nonneg_left h2' L.2)
  have hn : ‖gradient (productPotential H G) y-gradient (productPotential H G) z‖≤
      ‖gradient H (productPointEquiv d e y).1-gradient H (productPointEquiv d e z).1‖+
      ‖gradient G (productPointEquiv d e y).2-gradient G (productPointEquiv d e z).2‖ := by
    nlinarith [norm_nonneg (gradient (productPotential H G) y-gradient (productPotential H G) z),
      norm_nonneg (gradient H (productPointEquiv d e y).1-gradient H (productPointEquiv d e z).1),
      norm_nonneg (gradient G (productPointEquiv d e y).2-gradient G (productPointEquiv d e z).2),
      mul_nonneg (norm_nonneg (gradient H (productPointEquiv d e y).1-gradient H (productPointEquiv d e z).1))
        (norm_nonneg (gradient G (productPointEquiv d e y).2-gradient G (productPointEquiv d e z).2))]
  exact hn.trans ((add_le_add h1'' h2'').trans_eq (by ring))
end LogConcaveSampling

end

end

end

end OAI
