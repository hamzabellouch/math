import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.MatrixAlgebras.MatrixSmallPacking

namespace OAI

section

noncomputable section
namespace DirectPacking
open Pureness CurrentMain
open scoped ComplexOrder

variable {D : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [TraceFamily D]

omit [PartialOrder D] [StarOrderedRing D] [TraceFamily D] in
lemma hom_maps_projection {B : Type*} [CStarAlgebra B]
    (φ : B →⋆ₙₐ[ℂ] D) {P : B} (hP : IsStarProjection P) : IsStarProjection (φ P) where
  isIdempotentElem := by change φ P*φ P=φ P; rw [←map_mul,hP.isIdempotentElem.eq]
  isSelfAdjoint := by change star (φ P)=φ P; rw [←map_star,hP.isSelfAdjoint.star_eq]

omit [TraceFamily D] in
lemma projection_overlap_gap (τ : TracialState D) {t a y : D}
    (ht : IsStarProjection t) (ha : IsStarProjection a) (hy : y*a=a) :
    (τ.functional (a*(1-t))).re≤traceTwoNorm τ (t-y)^2 := by
  have he : (1-t)*a=((1-t)*(y-t))*a := by
    noncomm_ring [ht.isIdempotentElem.eq,hy]
  have hn : traceTwoNorm τ ((1-t)*a)≤traceTwoNorm τ (t-y) := by
    rw [he]
    apply (twoNorm_mul_right_contraction τ ha.norm_le _).trans
    exact (twoNorm_mul_left_contraction τ ht.one_sub.norm_le _).trans_eq (traceTwoNorm_sub_swap τ _ _)
  have hh := projection_overlap_identity τ ht.one_sub ha (1:D)
  simp only [one_mul,mul_one,star_one] at hh
  rw [τ.tracial (1-t) a] at hh
  rw [hh]
  exact (sq_le_sq₀ (traceTwoNorm_nonneg τ _) (traceTwoNorm_nonneg τ _)).mpr hn

namespace MatrixPackingCertificate
variable {z : D} {m : ℕ} (C : MatrixPackingCertificate z m)

lemma compress_projection_energy (hinsert : InsertionSupply (D := D))
    {P : CStarMatrix (Fin m) (Fin m) ℂ} (hP : IsStarProjection P)
    {x : D} (hx : ‖x‖≤1) (τ : RestrictedTracialState D) :
    traceTwoNorm τ (x*C.compress P-C.compress P*x)^2≤4*C.energy τ x P+120*C.gap τ := by
  classical
  have hp (i : C.Index) : IsStarProjection (C.hom i P) := hom_maps_projection (C.hom i) hP
  choose a ha hat hab using fun i => hinsert (1-C.piece i) (C.hom i P) (C.projection i).one_sub (hp i)
  have hle (i : C.Index) : a i≤C.piece i := by simpa only [sub_sub_cancel] using hat i
  have hal (i : C.Index) : C.piece i*a i=a i := ((ha i).le_iff_mul_eq_right (C.projection i)).mp (hle i)
  have har (i : C.Index) : a i*C.piece i=a i := ((ha i).le_iff_mul_eq_left (C.projection i)).mp (hle i)
  have hoa : Pairwise (fun i j => a i*a j=0) := by
    intro i j hij
    calc
      a i*a j=(a i*C.piece i)*(C.piece j*a j) := by rw [har,hal]
      _=0 := by rw [mul_assoc,←mul_assoc (C.piece i),C.orthogonal hij,zero_mul,mul_zero]
  have hd (i : C.Index) : traceTwoNorm τ (a i-C.hom i P)^2≤5*traceTwoNorm τ (C.piece i-C.hom i 1)^2 := by
    apply ((hab i τ).2.1).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact projection_overlap_gap τ (C.projection i) (hp i) (by rw [←map_mul,one_mul])
  have hs := orthogonal_sum_energy_le Finset.univ a (fun i _ => ha i) (fun i _ j _ hij => hoa hij) τ x
  have he : traceTwoNorm τ (x*(∑ i,a i)-(∑ i,a i)*x)^2≤2*C.energy τ x P+40*C.gap τ := by
    apply hs.2.trans
    have hh := Finset.sum_le_sum fun i (_ : i∈Finset.univ) => commutator_perturb_sq τ hx (a i) (C.hom i P)
    apply hh.trans
    have hh' := Finset.sum_le_sum fun i (_ : i∈Finset.univ) => hd i
    simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hh' ⊢
    dsimp [energy,gap]
    linarith
  have hd' : traceTwoNorm τ (C.compress P-∑ i,a i)^2≤5*C.gap τ := by
    have hid : C.compress P-∑ i,a i=∑ i,C.piece i*(C.hom i P-a i)*C.piece i := by
      simp only [compress,←Finset.sum_sub_distrib,mul_sub,sub_mul,hal,har]
    rw [hid,orthogonal_sum_twoNorm_sq τ _ (supported_orthogonal C.projection C.orthogonal (by
      intro i; simp only [←mul_assoc,(C.projection i).isIdempotentElem.eq]))]
    have hc (i : C.Index) : traceTwoNorm τ (C.piece i*(C.hom i P-a i)*C.piece i)^2≤traceTwoNorm τ (C.hom i P-a i)^2 :=
      (sq_le_sq₀ (traceTwoNorm_nonneg (τ : TracialState D) (C.piece i*(C.hom i P-a i)*C.piece i)) (traceTwoNorm_nonneg (τ : TracialState D) (C.hom i P-a i))).mpr (twoNorm_compress_le (τ : TracialState D) (C.projection i) (C.hom i P-a i))
    apply le_trans (Finset.sum_le_sum fun i (_ : i∈Finset.univ) => hc i)
    simp_rw [traceTwoNorm_sub_swap τ (C.hom _ P)]
    exact (Finset.sum_le_sum fun i _ => hd i).trans_eq (by rw [←Finset.mul_sum]; rfl)
  have hh := commutator_perturb_sq τ hx (C.compress P) (∑ i,a i)
  linarith

end MatrixPackingCertificate
end DirectPacking

end
end

end OAI
