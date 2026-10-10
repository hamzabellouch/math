import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.MatrixEmbedding

namespace OAI


noncomputable section
open scoped NNReal Topology

namespace TraceCone
variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma starHom_continuous (f : A →⋆ₙₐ[ℂ] B) : Continuous f := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simpa only [dist_eq_norm,← map_sub,NNReal.coe_one,one_mul] using
    NonUnitalStarAlgHom.norm_apply_le f (a-b)

@[simp] theorem Positive.map_cut (f : A →⋆ₙₐ[ℂ] B) (ε : ℝ≥0) (a : Positive A) :
    Positive.map f (Positive.cut ε a) = Positive.cut ε (Positive.map f a) := by
  apply Subtype.ext
  exact f.map_cfcₙ (fun t : ℝ => max (t-ε) 0) a.1
    (by fun_prop) (by simp) (starHom_continuous f) (IsSelfAdjoint.of_nonneg a.2)
    (IsSelfAdjoint.of_nonneg (Positive.map f a).2)

theorem cuntzClass_maps_eq_of_dense (f g : A →⋆ₙₐ[ℂ] B) (S : Set (Positive A))
    (hdense : ∀ (a : Positive A) (ε : ℝ), 0 < ε → ∃ b ∈ S, ‖a.1-b.1‖ < ε)
    (hcut : ∀ b ∈ S, ∀ ε : ℝ≥0, Positive.cut ε b ∈ S)
    (hfg : ∀ b ∈ S, CuntzClass.mk (Positive.map f b) = CuntzClass.mk (Positive.map g b))
    (a : Positive A) : CuntzClass.mk (Positive.map f a) = CuntzClass.mk (Positive.map g a) := by
  have oneWay (f g : A →⋆ₙₐ[ℂ] B)
      (hfg : ∀ b ∈ S, CuntzClass.mk (Positive.map f b) = CuntzClass.mk (Positive.map g b)) :
      CuntzBelow (Positive.map f a) (Positive.map g a) := by
    intro ε hε
    obtain ⟨b,hb,hab⟩ := hdense a (ε/4) (by linarith)
    let δ : ℝ≥0 := ⟨ε/4,by linarith⟩
    have hδ : 0 < δ := by change (0 : ℝ) < ε/4; linarith
    have hba : CuntzBelow (Positive.cut δ b) a :=
      cut_cuntzBelow_of_norm_sub_lt b a δ hδ (by change ‖b.1-a.1‖ < ε/4; rwa [norm_sub_rev])
    have hcb := ((CuntzClass.mk_eq_mk_iff _ _).mp (hfg _ (hcut b hb δ))).1.trans (hba.map g)
    obtain ⟨v,hv⟩ := hcb (ε/2) (by linarith)
    refine ⟨v,?_⟩
    have hd : ‖f (Positive.cut δ b).1-f a.1‖ < ε/2 := by
      rw [← map_sub]
      apply (NonUnitalStarAlgHom.norm_apply_le f _).trans_lt
      have hc := Positive.norm_sub_cut_le δ b
      have ht := norm_sub_le_norm_sub_add_norm_sub (Positive.cut δ b).1 b.1 a.1
      rw [norm_sub_rev (Positive.cut δ b).1 b.1,norm_sub_rev b.1 a.1] at ht
      change ‖b.1-(Positive.cut δ b).1‖ ≤ ε/4 at hc
      linarith
    have ht := norm_sub_le_norm_sub_add_norm_sub (star v * g a.1 * v) (f (Positive.cut δ b).1) (f a.1)
    change ‖star v*g a.1*v-f (Positive.cut δ b).1‖ < ε/2 at hv
    exact ht.trans_lt (by linarith)
  exact (CuntzClass.mk_eq_mk_iff _ _).mpr ⟨oneWay f g hfg,
    oneWay g f (fun b hb => (hfg b hb).symm)⟩
end TraceCone
end


noncomputable section
open scoped CStarAlgebra NNReal

namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def matrixParityEmbedding (n : ℕ) (r : Fin 2) : Fin n ↪ Fin (n*2) where
  toFun i := finProdFinEquiv (i,r)
  inj' := by intro i j h; exact (Prod.mk.inj (finProdFinEquiv.injective h)).1

def matrixParity (r : Fin 2) : MatrixLimit A →⋆ₙₐ[ℂ] MatrixLimit A :=
  if r = 0 then matrixEven else matrixOdd

lemma matrixParity_embedding (n : ℕ) (r : Fin 2) (M : FinMatrix A n) :
    matrixEmbedding (matrixParityEmbedding n r) M =
      matrixInterleave n (if r = 0 then (M,0) else (0,M)) := by
  apply matrixEmbedding_ext
  · intro i j
    change matrixInterleave n _ (finProdFinEquiv (i,r)) (finProdFinEquiv (j,r)) = _
    rw [matrixInterleave_entry]
    fin_cases r <;> simp
  · intro i j h
    obtain ⟨⟨p,s⟩,rfl⟩ := finProdFinEquiv.surjective i
    obtain ⟨⟨q,t⟩,rfl⟩ := finProdFinEquiv.surjective j
    have hs : s ≠ r ∨ t ≠ r := by
      rcases h with h | h
      · exact Or.inl (fun he => h ⟨p,by subst s; rw [matrixParityEmbedding.eq_1]; rfl⟩)
      · exact Or.inr (fun he => h ⟨q,by subst t; rfl⟩)
    rw [matrixInterleave_entry]
    fin_cases r <;> fin_cases s <;> fin_cases t <;> simp_all

lemma matrixParity_stage (n : ℕ) (r : Fin 2) (M : FinMatrix A n) :
    matrixParity r (matrixLimitStage n M) =
      matrixLimitStage (n*2) (matrixEmbedding (matrixParityEmbedding n r) M) := by
  rw [matrixParity_embedding]
  fin_cases r <;> simp [matrixParity,matrixLimitBlock]

theorem matrixLimit_maps_eq (f g : MatrixLimit A →⋆ₙₐ[ℂ] MatrixLimit A)
    (hfg : ∀ n (M : Positive (FinMatrix A n)),
      CuntzClass.mk (Positive.map f (Positive.map (matrixLimitStage n) M)) =
      CuntzClass.mk (Positive.map g (Positive.map (matrixLimitStage n) M)))
    (a : Positive (MatrixLimit A)) :
    CuntzClass.mk (Positive.map f a) = CuntzClass.mk (Positive.map g a) := by
  let S : Set (Positive (MatrixLimit A)) :=
    {a | ∃ (n : ℕ) (M : Positive (FinMatrix A n)), Positive.map (matrixLimitStage n) M = a}
  apply cuntzClass_maps_eq_of_dense f g S ?_ ?_ ?_ a
  · intro b ε hε
    obtain ⟨n,M,hM⟩ := matrixLimit_positive_approximation b hε
    exact ⟨_,⟨n,M,rfl⟩,hM⟩
  · rintro _ ⟨n,M,rfl⟩ ε
    exact ⟨n,Positive.cut ε M,Positive.map_cut _ _ _⟩
  · rintro _ ⟨n,M,rfl⟩
    exact hfg n M

theorem matrixParity_cuntzClass (r : Fin 2) (a : Positive (MatrixLimit A)) :
    CuntzClass.mk (Positive.map (matrixParity r) a) = CuntzClass.mk a := by
  apply matrixLimit_maps_eq (matrixParity r) (NonUnitalStarAlgHom.id ℂ (MatrixLimit A)) ?_ a
  intro n M
  have he : Positive.map (matrixParity r) (Positive.map (matrixLimitStage n) M) =
      Positive.map (matrixLimitStage (n*2)) (Positive.map (matrixEmbedding (matrixParityEmbedding n r)) M) :=
    Subtype.ext (matrixParity_stage n r M.1)
  rw [he]
  exact matrixEmbedding_cuntzClass _ M

namespace CuntzClass
instance : Zero (CuntzClass A) := ⟨mk Positive.zero⟩
@[simp] lemma zero_mk : mk (Positive.zero (A := A)) = (0 : CuntzClass A) := rfl

theorem matrixAdd_zero (x : CuntzClass (MatrixLimit A)) : matrixAdd x 0 = x := by
  induction x using Quotient.inductionOn with | h a =>
  change mk (matrixBlockPositive a Positive.zero) = mk a
  have he : matrixBlockPositive a Positive.zero = Positive.map (matrixParity 0) a := by
    apply Subtype.ext
    simp [matrixBlockPositive,Positive.map,positiveProduct,Positive.zero,matrixBlockHom,matrixParity]
  rw [he]
  exact matrixParity_cuntzClass 0 a

theorem zero_matrixAdd (x : CuntzClass (MatrixLimit A)) : matrixAdd 0 x = x := by
  induction x using Quotient.inductionOn with | h a =>
  change mk (matrixBlockPositive Positive.zero a) = mk a
  have he : matrixBlockPositive Positive.zero a = Positive.map (matrixParity 1) a := by
    apply Subtype.ext
    simp [matrixBlockPositive,Positive.map,positiveProduct,Positive.zero,matrixBlockHom,matrixParity]
  rw [he]
  exact matrixParity_cuntzClass 1 a
end CuntzClass
end TraceCone
end


noncomputable section
open scoped NNReal CStarAlgebra

namespace TraceCone
variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

structure PositiveCore where
  carrier : Set (Positive A)
  approximate : ∀ (a : Positive A) (ε : ℝ), 0 < ε → ∃ b ∈ carrier, ‖a.1-b.1‖ < ε
  cut_mem : ∀ b ∈ carrier, ∀ ε : ℝ≥0, Positive.cut ε b ∈ carrier

variable {A}
def matrixPositiveCore : PositiveCore (MatrixLimit A) where
  carrier := {a | ∃ (n : ℕ) (M : Positive (FinMatrix A n)), Positive.map (matrixLimitStage n) M = a}
  approximate a ε hε := by
    obtain ⟨n,M,hM⟩ := matrixLimit_positive_approximation a hε
    exact ⟨_,⟨n,M,rfl⟩,hM⟩
  cut_mem := by
    rintro _ ⟨n,M,rfl⟩ ε
    exact ⟨n,Positive.cut ε M,Positive.map_cut _ _ _⟩

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def PositiveCore.prod (S : PositiveCore A) (T : PositiveCore B) : PositiveCore (A × B) where
  carrier := {a | Positive.map (NonUnitalStarAlgHom.fst ℂ A B) a ∈ S.carrier ∧
    Positive.map (NonUnitalStarAlgHom.snd ℂ A B) a ∈ T.carrier}
  approximate a ε hε := by
    obtain ⟨b,hb,hab⟩ := S.approximate (Positive.map (NonUnitalStarAlgHom.fst ℂ A B) a) ε hε
    obtain ⟨c,hc,hac⟩ := T.approximate (Positive.map (NonUnitalStarAlgHom.snd ℂ A B) a) ε hε
    refine ⟨⟨(b.1,c.1),b.2,c.2⟩,⟨hb,hc⟩,?_⟩
    exact max_lt hab hac
  cut_mem a ha ε := by
    change Positive.map _ _ ∈ _ ∧ Positive.map _ _ ∈ _
    rw [Positive.map_cut,Positive.map_cut]
    exact ⟨S.cut_mem _ ha.1 ε,T.cut_mem _ ha.2 ε⟩

theorem PositiveCore.maps_eq (S : PositiveCore A) (f g : A →⋆ₙₐ[ℂ] B)
    (h : ∀ a ∈ S.carrier, CuntzClass.mk (Positive.map f a) = CuntzClass.mk (Positive.map g a))
    (a : Positive A) : CuntzClass.mk (Positive.map f a) = CuntzClass.mk (Positive.map g a) :=
  cuntzClass_maps_eq_of_dense f g S.carrier S.approximate S.cut_mem h a

theorem matrixPositiveCore_common (a b : Positive (MatrixLimit A))
    (ha : a ∈ matrixPositiveCore.carrier) (hb : b ∈ matrixPositiveCore.carrier) :
    ∃ (n : ℕ) (M N : Positive (FinMatrix A n)),
      Positive.map (matrixLimitStage n) M = a ∧ Positive.map (matrixLimitStage n) N = b := by
  obtain ⟨n,M,rfl⟩ := ha
  obtain ⟨m,N,rfl⟩ := hb
  refine ⟨max n m,Positive.map (matrixInclusion (le_max_left n m)) M,
    Positive.map (matrixInclusion (le_max_right n m)) N,?_,?_⟩ <;>
    apply Subtype.ext <;> exact matrixLimitStage_compatible _ _
end TraceCone
end

end OAI
