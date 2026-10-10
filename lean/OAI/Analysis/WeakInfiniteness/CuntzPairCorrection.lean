import Mathlib
import OAI.Analysis.WeakInfiniteness.RectangularPolar

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

universe u

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma rectangular_norm_le_sum_entries {m n : Type*} [Fintype m] [Fintype n]
    (M : CStarMatrix m n A) : ‖M‖ ≤ ∑ j,∑ i,‖M i j‖ := by
  rw [CStarMatrix.norm_def]
  refine (CStarMatrix.toCLM M).opNorm_le_bound (by positivity) fun v => ?_
  simp only [CStarMatrix.toCLM_apply_eq_sum,Finset.sum_mul]
  apply WithCStarModule.pi_norm_le_sum_norm _ |>.trans
  gcongr with i _
  apply norm_sum_le _ _ |>.trans
  gcongr with j _
  apply norm_mul_le _ _ |>.trans
  rw [mul_comm]
  gcongr
  exact WithCStarModule.norm_apply_le_norm v j

lemma exists_inverse_sqrt_tolerance (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ g : A,0≤g → ‖g-1‖<δ →
      IsStrictlyPositive g ∧ ‖g^(-(1/2):ℝ)-1‖<ε := by
  have h1 : IsStrictlyPositive (1:A) := isUnit_one.isStrictlyPositive zero_le_one
  have hc := (CFC.continuousOn_rpow (A := A) (-(1/2):ℝ)) (1:A) h1
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousWithinAt_iff.mp hc ε hε
  refine ⟨min δ 1,lt_min hδ zero_lt_one,?_⟩
  intro g hg hgn
  have hn : ‖1-g‖<1 := by rw [norm_sub_rev]; exact lt_of_lt_of_le hgn (min_le_right _ _)
  have hu : IsUnit g := by
    have hh := isUnit_one_sub_of_norm_lt_one hn
    simpa only [sub_sub_cancel] using hh
  have hp := hu.isStrictlyPositive hg
  refine ⟨hp,?_⟩
  have hh := hclose hp (show dist g 1<δ by simpa only [dist_eq_norm] using lt_of_lt_of_le hgn (min_le_left _ _))
  simpa only [CFC.one_rpow,dist_eq_norm] using hh

local instance correctionMatrixReal {n : Type*} [Fintype n] :
    Module ℝ (CStarMatrix n n A) := Module.complexToReal _

local instance correctionMatrixRealAlgebra {n : Type*} [Fintype n] [DecidableEq n] :
    Algebra ℝ (CStarMatrix n n A) := Algebra.complexToReal

lemma exists_rectangular_isometry_near {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M ε : ℝ) (hM : 0≤M) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ u : CStarMatrix m n A,‖u‖≤M → ‖u.conjTranspose*u-1‖<δ →
      ∃ v : CStarMatrix m n A,v.conjTranspose*v=1 ∧ ‖v-u‖<ε := by
  classical
  obtain ⟨δ,hδ,hcorr⟩ := exists_inverse_sqrt_tolerance (A := CStarMatrix n n A)
    (ε/(M+1)) (div_pos hε (by linarith))
  refine ⟨δ,hδ,?_⟩
  intro u hu hug
  let g : CStarMatrix n n A := u.conjTranspose*u
  obtain ⟨hgp,hgn⟩ := hcorr g (rectangular_initial_nonneg u) hug
  let k : CStarMatrix n n A := g^(-(1/2):ℝ)
  have hk : star k=k := (CFC.rpow_nonneg (a := g)).star_eq
  refine ⟨u*k,?_,?_⟩
  · calc
      (u*k).conjTranspose*(u*k) = k*(u.conjTranspose*u)*k := by
        rw [rectangular_star_mul]
        change (star k*u.conjTranspose)*(u*k)=_
        rw [hk]
        simp only [rectangular_mul_assoc]
      _ = 1 := CFC.conjugate_rpow_neg_one_half g hgp
  · have hu1 : u*(1:CStarMatrix n n A)=u := by
      ext i j
      change (∑ l,u i l*(if l=j then 1 else 0))=u i j
      simp
    have hsub : u*(k-1)=u*k-u*(1:CStarMatrix n n A) := by
      ext i j
      change (∑ l,u i l*(k l j-(1:CStarMatrix n n A) l j))=
        (∑ l,u i l*k l j)-(∑ l,u i l*(1:CStarMatrix n n A) l j)
      simp only [mul_sub,Finset.sum_sub_distrib]
    have he : u*k-u=u*(k-1) := by rw [hsub,hu1]
    rw [he]
    calc
      _ ≤ ‖u‖*‖k-1‖ := rectangular_norm_mul_le _ _
      _ ≤ M*‖k-1‖ := mul_le_mul_of_nonneg_right hu (norm_nonneg _)
      _ < (M+1)*(ε/(M+1)) := by
        change ‖k-1‖<ε/(M+1) at hgn
        have hn := norm_nonneg (k-1)
        have hp : 0 < ε/(M+1) := div_pos hε (by linarith)
        nlinarith
      _ = ε := mul_div_cancel₀ _ (by linarith : M+1≠0)

def cuntzPairRow (s t : A) : CStarMatrix (Fin 1) (Fin 2) A :=
  CStarMatrix.ofMatrix (fun _ => ![s,t])

omit [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma cuntzPairRow_apply (s t : A) (i : Fin 1) (j : Fin 2) :
    cuntzPairRow s t i j=![s,t] j := rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma cuntzPairRow_initial_entry (s t : A) (i j : Fin 2) :
    ((cuntzPairRow s t).conjTranspose*cuntzPairRow s t) i j =
      star (![s,t] i)*(![s,t] j) := by
  change (∑ k : Fin 1,star ((cuntzPairRow s t) k i)*(cuntzPairRow s t) k j)=_
  simp only [Fin.sum_univ_one,cuntzPairRow_apply]

lemma norm_cuntzPairRow_le (s t : A) : ‖cuntzPairRow s t‖≤‖s‖+‖t‖ := by
  have h := rectangular_norm_le_sum_entries (cuntzPairRow s t)
  simpa only [Fin.sum_univ_two,Fin.sum_univ_one,cuntzPairRow_apply,Matrix.cons_val_zero,Matrix.cons_val_one] using h

lemma norm_cuntzPairRow_initial_sub_one_le (s t : A) :
    ‖(cuntzPairRow s t).conjTranspose*cuntzPairRow s t-1‖ ≤
      ‖star s*s-1‖+‖star t*t-1‖+2*‖star s*t‖ := by
  have h := rectangular_norm_le_sum_entries
    ((cuntzPairRow s t).conjTranspose*cuntzPairRow s t-1)
  have hnorm : ‖star t*s‖=‖star s*t‖ := by
    rw [← norm_star (star s*t),star_mul,star_star]
  simp only [Fin.sum_univ_two,CStarMatrix.sub_apply,cuntzPairRow_initial_entry,
    Matrix.cons_val_zero,Matrix.cons_val_one,
    CStarMatrix.one_apply_eq,CStarMatrix.one_apply_ne (by decide : (0:Fin 2)≠1),
    CStarMatrix.one_apply_ne (by decide : (1:Fin 2)≠0),sub_zero,hnorm] at h
  linarith

lemma exists_cuntzPair_near (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ s t : A,‖s‖≤1 → ‖t‖≤1 →
      ‖star s*s-1‖<δ → ‖star t*t-1‖<δ → ‖star s*t‖<δ →
      ∃ r q : A,star r*r=1 ∧ star q*q=1 ∧ star r*q=0 ∧ ‖r-s‖<ε ∧ ‖q-t‖<ε := by
  obtain ⟨δ,hδ,hcorr⟩ := exists_rectangular_isometry_near (A := A)
    (m := Fin 1) (n := Fin 2) 2 ε (by norm_num) hε
  refine ⟨δ/4,by positivity,?_⟩
  intro s t hs ht hss htt hst
  have hu : ‖cuntzPairRow s t‖≤2 := (norm_cuntzPairRow_le s t).trans (by linarith)
  have hg : ‖(cuntzPairRow s t).conjTranspose*cuntzPairRow s t-1‖<δ := by
    have h := norm_cuntzPairRow_initial_sub_one_le s t
    linarith
  obtain ⟨v,hv,hvn⟩ := hcorr (cuntzPairRow s t) hu hg
  refine ⟨v 0 0,v 0 1,?_,?_,?_,?_,?_⟩
  · have h := congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) A => M 0 0) hv
    change (∑ k : Fin 1,star (v k 0)*v k 0)=(1:CStarMatrix (Fin 2) (Fin 2) A) 0 0 at h
    simpa using h
  · have h := congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) A => M 1 1) hv
    change (∑ k : Fin 1,star (v k 1)*v k 1)=(1:CStarMatrix (Fin 2) (Fin 2) A) 1 1 at h
    simpa using h
  · have h := congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) A => M 0 1) hv
    change (∑ k : Fin 1,star (v k 0)*v k 1)=(1:CStarMatrix (Fin 2) (Fin 2) A) 0 1 at h
    simpa [CStarMatrix.one_apply_ne (by decide : (0:Fin 2)≠1)] using h
  · have h := (CStarMatrix.norm_entry_le_norm (M := v-cuntzPairRow s t) (i := 0) (j := 0)).trans_lt hvn
    simpa only [CStarMatrix.sub_apply,cuntzPairRow_apply,Matrix.cons_val_zero,Matrix.cons_val_one] using h
  · have h := (CStarMatrix.norm_entry_le_norm (M := v-cuntzPairRow s t) (i := 0) (j := 1)).trans_lt hvn
    simpa only [CStarMatrix.sub_apply,cuntzPairRow_apply,Matrix.cons_val_zero,Matrix.cons_val_one] using h

end

end WeakPureInfiniteness
end

end OAI
