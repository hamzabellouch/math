import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.HNPolynomial
import OAI.Combinatorics.Chromatic.Walls.HNMatrixTriangular

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]
variable (c η : I → ℝ)
lemma hnKeyLT_irrefl (d : I → ℕ) : ¬hnKeyLT c η d d := by
  simp [hnKeyLT]
lemma hnKeyLT_trans {d e f : I → ℕ} (h : hnKeyLT c η d e) (k : hnKeyLT c η e f) :
    hnKeyLT c η d f := by
  rcases h with h|⟨h,hm⟩ <;> rcases k with k|⟨k,km⟩
  · exact Or.inl (h.trans k)
  · exact Or.inl (k ▸ h)
  · exact Or.inl (h ▸ k)
  · exact Or.inr ⟨h.trans k,hm.trans km⟩
instance hnKeyLT_strict : IsStrictOrder (I → ℕ) (hnKeyLT c η) where
  irrefl := hnKeyLT_irrefl c η
  trans := fun _ _ _=>hnKeyLT_trans c η
lemma hnKeyLT_bounds {d e : I → ℕ} (h : ¬hnKeyLT c η d e) :
    slope c η e ≤ slope c η d ∧ (slope c η d=slope c η e → mass c e ≤ mass c d) := by
  exact ⟨le_of_not_gt (fun hs=>h (Or.inl hs)),fun hs=>le_of_not_gt (fun hm=>h (Or.inr ⟨hs,hm⟩))⟩
lemma ordered_tail {d : I → ℕ} {l : List (I → ℕ)} (h : HNOrdered c η (d::l)) : HNOrdered c η l :=
  ⟨fun e he=>h.1 e (by simp [he]),h.2.tail⟩
lemma ordered_total_lt_head (hc : ∀ i,0<c i) {d : I → ℕ} {l : List (I → ℕ)}
    (h : HNOrdered c η (d::l)) (hl : l≠[]) : slope c η (d::l).sum < slope c η d := by
  have hn:=list_sum_ne_zero h.1 (by simp)
  have ht:=list_sum_ne_zero (ordered_tail c η h).1 hl
  have H:=ordered_tail_lt_head c η hc h hl
  apply (div_lt_iff₀ (mass_pos c hc _ hn)).mpr
  simp only [List.sum_cons,mass_add]
  rw [mass_eq c η hc d,mass_eq c η hc l.sum,mul_add]
  exact add_lt_add_right (mul_lt_mul_of_pos_right H (mass_pos c hc _ ht)) _
end ElementaryPositivity.SlopeArithmetic

namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)

lemma castS_shuffle_right {d e f : I → ℕ} (h : e=f) (x : S d) (y : S e) :
    castS (congrArg (d+·) h) (shufflePolynomial a x y)=shufflePolynomial a x (castS h y) := by
  subst f; rfl
lemma quotient_clipped_zero {κ : ℝ} {d : I → ℕ} {f : S d}
    (hf : f∈destabilizingSpace a (clippedSlope c η κ) d) :
    quotientAlg a (slope c η) d f=0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (clipped_destabilizingSpace_le a c η κ d hf)

noncomputable def singletonDetector (d : I → ℕ) : S ([d].sum) →ₗ[ℚ] HNTensor a c η [d] :=
  (((TensorProduct.mk ℚ (B a (slope c η) d) (S (0 : I → ℕ))).flip 1).comp
    (quotientAlg a (slope c η) d).toLinearMap).comp (dimensionCast (add_zero d))
lemma singletonDetector_apply (d : I → ℕ) (f : S [d].sum) :
    singletonDetector a c η d f=quotientAlg a (slope c η) d (castS (add_zero d) f)⊗ₜ[ℚ]1 := rfl
lemma singletonDetector_diagonal (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (hσ : ∀ d,Function.RightInverse (σ d) (destabilizingSpace a (slope c η) d).mkQ)
    (d : I → ℕ) : (singletonDetector a c η d).comp (hnPolynomial a c η σ [d])=LinearMap.id := by
  apply TensorProduct.ext'
  intro x y
  change B a (slope c η) d at x
  change S (0 : I → ℕ) at y
  change singletonDetector a c η d (shufflePolynomial a (σ d x) y)=x⊗ₜ[ℚ]y
  erw [S_zero_eq_scalar y,shufflePolynomial_smul_right,shufflePolynomial_unit_right,map_smul,
    singletonDetector_apply,castS_trans,castS_rfl]
  change _=x⊗ₜ[ℚ](_ • (1 : S (0 : I → ℕ)))
  rw [TensorProduct.tmul_smul]
  exact congrArg (fun z=>MvPolynomial.constantCoeff y.val • (z⊗ₜ[ℚ](1 : S (0 : I → ℕ)))) (hσ d x)
lemma singletonDetector_ideal (d : I → ℕ) (θ : ℝ) (f : S [d].sum)
    (hf : f∈destabilizingSpace a (clippedSlope c η θ) [d].sum) : singletonDetector a c η d f=0 := by
  change quotientAlg a (slope c η) d (castS (add_zero d) f)⊗ₜ[ℚ](1 : S (0 : I → ℕ))=0
  exact (congrArg (fun z=>z⊗ₜ[ℚ](1 : S (0 : I → ℕ)))
    (quotient_clipped_zero a c η (castS_mem_destabilizing a _ (add_zero d) hf))).trans (TensorProduct.zero_tmul _ _)

lemma singletonDetector_off (hc : ∀ i,0<c i) (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (d : I → ℕ) (hd : d≠0) (r : List (I → ℕ)) (hr : HNOrdered c η r) (h : r.sum=[d].sum) (hne : r≠[d])
    (x : HNTensor a c η r) : singletonDetector a c η d (castS h (hnPolynomial a c η σ r x))=0 := by
  cases r with
  | nil =>
    exact (hd (by simpa using h.symm)).elim
  | cons e r =>
    have hn : r≠[] := by
      intro he; subst r
      have : e=d := by simpa using h
      exact hne (by simp [this])
    have H : (singletonDetector a c η d).comp ((dimensionCast h).comp (hnPolynomial a c η σ (e::r)))=0 := by
      apply TensorProduct.ext'
      intro x y
      have hz : quotientAlg a (slope c η) d
          (castS (h.trans (add_zero d)) (shufflePolynomial a (σ e x) (hnPolynomial a c η σ r y)))=0 := by
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        apply Submodule.subset_span
        refine ⟨e,r.sum,h.trans (add_zero d),σ e x,hnPolynomial a c η σ r y,
          hr.1 e (by simp),list_sum_ne_zero (ordered_tail c η hr).1 hn,?_,?_⟩
        · have H:=ordered_total_lt_head c η hc hr hn
          simpa only [h,List.sum_cons,List.sum_nil,add_zero] using H
        · exact (dimensionCast_eq_castS (h.trans (add_zero d)) (shufflePolynomial a (σ e x) (hnPolynomial a c η σ r y))).symm
      have Hcast : castS (add_zero d) (dimensionCast h
          (shufflePolynomial a (σ e x) (hnPolynomial a c η σ r y)))=
          castS (h.trans (add_zero d)) (shufflePolynomial a (σ e x) (hnPolynomial a c η σ r y)) :=
        (congrArg (castS (add_zero d)) (dimensionCast_eq_castS h _)).trans (castS_trans _ _ _)
      exact (singletonDetector_apply a c η d _).trans
        ((congrArg (fun f=>quotientAlg a (slope c η) d f⊗ₜ[ℚ](1 : S (0 : I → ℕ))) Hcast).trans
          ((congrArg (fun z=>z⊗ₜ[ℚ](1 : S (0 : I → ℕ))) hz).trans (TensorProduct.zero_tmul _ _)))
    simpa only [LinearMap.comp_apply,dimensionCast_eq_castS,LinearMap.zero_apply] using LinearMap.congr_fun H x
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)

structure IsHNDetector (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (l : List (I → ℕ)) (D : S l.sum →ₗ[ℚ] HNTensor a c η l) : Prop where
  ideal : ∀ θ : ℝ,(∀ d∈l,slope c η d ≤ θ) → ∀ f : S l.sum,
    f∈destabilizingSpace a (clippedSlope c η θ) l.sum → D f=0
  diagonal : D.comp (hnPolynomial a c η σ l)=LinearMap.id
  off : ∀ (r : List (I → ℕ)),HNOrdered c η r → ∀ h : r.sum=l.sum,
    ¬List.Lex (hnKeyLT c η) r l → r≠l → ∀ x : HNTensor a c η r,
    D (castS h (hnPolynomial a c η σ r x))=0

noncomputable def quotientDetector (l : List (I → ℕ)) (D : S l.sum →ₗ[ℚ] HNTensor a c η l)
    (κ : ℝ) (hk : ∀ f : S l.sum,f∈destabilizingSpace a (clippedSlope c η κ) l.sum → D f=0) :
    B a (clippedSlope c η κ) l.sum →ₗ[ℚ] HNTensor a c η l :=
  (destabilizingSpace a (clippedSlope c η κ) l.sum).liftQ D (fun f hf=>hk f hf)
lemma quotientDetector_mk (l : List (I → ℕ)) (D : S l.sum →ₗ[ℚ] HNTensor a c η l)
    (κ : ℝ) (hk : ∀ f : S l.sum,f∈destabilizingSpace a (clippedSlope c η κ) l.sum → D f=0)
    (f : S l.sum) : quotientDetector a c η l D κ hk (quotientAlg a (clippedSlope c η κ) l.sum f)=D f := rfl

noncomputable def consDetector (d : I → ℕ) (l : List (I → ℕ)) (D : S l.sum →ₗ[ℚ] HNTensor a c η l)
    (κ : ℝ) (hk : ∀ f : S l.sum,f∈destabilizingSpace a (clippedSlope c η κ) l.sum → D f=0) :
    S (d::l).sum →ₗ[ℚ] HNTensor a c η (d::l) :=
  (TensorProduct.map (clippedToOriginal a c η κ d) (quotientDetector a c η l D κ hk)).comp
    (headRestriction a (clippedSlope c η κ) d l.sum)

lemma consDetector_shuffle (hc : ∀ i,0<c i) (d : I → ℕ) (l : List (I → ℕ))
    (D : S l.sum →ₗ[ℚ] HNTensor a c η l) (κ : ℝ)
    (hk : ∀ f : S l.sum,f∈destabilizingSpace a (clippedSlope c η κ) l.sum → D f=0)
    (hd : d≠0) (hk' : κ<slope c η d) (ht : slope c η l.sum≤κ) (f : S d) (g : S l.sum) :
    consDetector a c η d l D κ hk (shufflePolynomial a f g)=quotientAlg a (slope c η) d f⊗ₜ[ℚ]D g := by
  change TensorProduct.map _ _ (headRestriction a (clippedSlope c η κ) d l.sum (shufflePolynomial a f g))=_
  rw [headRestriction_shuffle_head a c η hc κ f g hd hk' ht]
  rfl

lemma consDetector_apply (d : I → ℕ) (l : List (I → ℕ))
    (D : S l.sum →ₗ[ℚ] HNTensor a c η l) (κ : ℝ)
    (hk : ∀ f : S l.sum,f∈destabilizingSpace a (clippedSlope c η κ) l.sum → D f=0)
    (f : S (d+l.sum)) : consDetector a c η d l D κ hk f=
    TensorProduct.map (clippedToOriginal a c η κ d) (quotientDetector a c η l D κ hk)
      (headRestriction a (clippedSlope c η κ) d l.sum f) := rfl

lemma consDetector_ideal (hc : ∀ i,0<c i) (d : I → ℕ) (l : List (I → ℕ))
    (D : S l.sum →ₗ[ℚ] HNTensor a c η l) (κ : ℝ)
    (hk : ∀ f : S l.sum,f∈destabilizingSpace a (clippedSlope c η κ) l.sum → D f=0)
    (θ : ℝ) (hs : slope c η (d+l.sum)≤θ) (hd : clippedSlope c η κ d≤θ)
    (ht : clippedSlope c η κ l.sum≤θ) (f : S (d+l.sum))
    (hf : f∈destabilizingSpace a (clippedSlope c η θ) (d+l.sum)) :
    consDetector a c η d l D κ hk f=0 := by
  exact (consDetector_apply a c η d l D κ hk f).trans
    ((congrArg (TensorProduct.map (clippedToOriginal a c η κ d) (quotientDetector a c η l D κ hk))
      (headRestriction_ideal a c η hc κ θ d l.sum hs hd ht f hf)).trans (map_zero _))

lemma consDetector_diagonal (hc : ∀ i,0<c i)
    (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (hσ : ∀ d,Function.RightInverse (σ d) (destabilizingSpace a (slope c η) d).mkQ)
    (d : I → ℕ) (l : List (I → ℕ)) (D : S l.sum →ₗ[ℚ] HNTensor a c η l) (κ : ℝ)
    (hk : ∀ f : S l.sum,f∈destabilizingSpace a (clippedSlope c η κ) l.sum → D f=0)
    (hd : d≠0) (hk' : κ<slope c η d) (ht : slope c η l.sum≤κ)
    (hD : D.comp (hnPolynomial a c η σ l)=LinearMap.id) :
    (consDetector a c η d l D κ hk).comp (hnPolynomial a c η σ (d::l))=LinearMap.id := by
  apply TensorProduct.ext'
  intro x y
  change consDetector a c η d l D κ hk (shufflePolynomial a (σ d x) (hnPolynomial a c η σ l y))=x⊗ₜ[ℚ]y
  rw [consDetector_shuffle a c η hc d l D κ hk hd hk' ht]
  change (destabilizingSpace a (slope c η) d).mkQ (σ d x)⊗ₜ[ℚ]D (hnPolynomial a c η σ l y)=_
  rw [hσ d x,show D (hnPolynomial a c η σ l y)=y from LinearMap.congr_fun hD y]

lemma consDetector_same_head (hc : ∀ i,0<c i)
    (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (d : I → ℕ) (l : List (I → ℕ)) (D : S l.sum →ₗ[ℚ] HNTensor a c η l) (κ : ℝ)
    (hk : ∀ f : S l.sum,f∈destabilizingSpace a (clippedSlope c η κ) l.sum → D f=0)
    (hd : d≠0) (hk' : κ<slope c η d) (ht : slope c η l.sum≤κ)
    (r : List (I → ℕ)) (h : r.sum=l.sum)
    (hD : ∀ x,D (castS h (hnPolynomial a c η σ r x))=0) (x : HNTensor a c η (d::r)) :
    consDetector a c η d l D κ hk (castS (congrArg (d+·) h) (hnPolynomial a c η σ (d::r) x))=0 := by
  have Hzero : (consDetector a c η d l D κ hk).comp ((dimensionCast (congrArg (d+·) h)).comp
      (hnPolynomial a c η σ (d::r)))=0 := by
    apply TensorProduct.ext'
    intro v w
    have Hcast := dimensionCast_eq_castS (congrArg (d+·) h)
      (shufflePolynomial a (σ d v) (hnPolynomial a c η σ r w))
    exact (congrArg (consDetector a c η d l D κ hk) Hcast).trans
      ((congrArg (consDetector a c η d l D κ hk) (castS_shuffle_right a h _ _)).trans
        ((consDetector_shuffle a c η hc d l D κ hk hd hk' ht _ _).trans
          ((congrArg (fun z=>quotientAlg a (slope c η) d (σ d v)⊗ₜ[ℚ]z) (hD w)).trans
            (TensorProduct.tmul_zero _ _))))
  exact (congrArg (consDetector a c η d l D κ hk) (dimensionCast_eq_castS _ _)).symm.trans
    (LinearMap.congr_fun Hzero x)

lemma consDetector_wrong_head (hc : ∀ i,0<c i)
    (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (d : I → ℕ) (l : List (I → ℕ)) (D : S l.sum →ₗ[ℚ] HNTensor a c η l) (κ : ℝ)
    (hk : ∀ f : S l.sum,f∈destabilizingSpace a (clippedSlope c η κ) l.sum → D f=0)
    (hk' : κ<slope c η d) (ht : slope c η l.sum≤κ)
    (b : I → ℕ) (r : List (I → ℕ)) (h : b+r.sum=d+l.sum) (hb : b≠0)
    (hs : slope c η d ≤ slope c η b) (hm : slope c η b=slope c η d → mass c d ≤ mass c b)
    (hne : b≠d) (x : HNTensor a c η (b::r)) :
    consDetector a c η d l D κ hk (castS h (hnPolynomial a c η σ (b::r) x))=0 := by
  have Hzero : (consDetector a c η d l D κ hk).comp ((dimensionCast h).comp
      (hnPolynomial a c η σ (b::r)))=0 := by
    apply TensorProduct.ext'
    intro v w
    have Hcast := dimensionCast_eq_castS h (shufflePolynomial a (σ b v) (hnPolynomial a c η σ r w))
    exact (congrArg (consDetector a c η d l D κ hk) Hcast).trans
      ((consDetector_apply a c η d l D κ hk _).trans
        ((congrArg (TensorProduct.map (clippedToOriginal a c η κ d) (quotientDetector a c η l D κ hk))
          (headRestriction_wrong_head a c η hc κ h (σ b v) (hnPolynomial a c η σ r w) hb hk' ht hs hm hne)).trans (map_zero _)))
  exact (congrArg (consDetector a c η d l D κ hk) (dimensionCast_eq_castS _ _)).symm.trans
    (LinearMap.congr_fun Hzero x)

theorem hn_detector_exists (hc : ∀ i,0<c i)
    (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (hσ : ∀ d,Function.RightInverse (σ d) (destabilizingSpace a (slope c η) d).mkQ)
    (l : List (I → ℕ)) (hl : HNOrdered c η l) :
    ∃ D : S l.sum →ₗ[ℚ] HNTensor a c η l,IsHNDetector a c η σ l D := by
  classical
  induction l with
  | nil =>
    refine ⟨LinearMap.id,?_,rfl,?_⟩
    · intro θ h f hf
      change f∈destabilizingSpace a (clippedSlope c η θ) 0 at hf
      rw [destabilizingSpace_zero] at hf
      exact hf
    · intro r hr h hn he x
      exact (list_sum_ne_zero hr.1 he h).elim
  | cons d l ih =>
    have hd : d≠0:=hl.1 d (by simp)
    cases l with
    | nil =>
      refine ⟨singletonDetector a c η d,?_,singletonDetector_diagonal a c η σ hσ d,?_⟩
      · intro θ h f hf; exact singletonDetector_ideal a c η d θ f hf
      · intro r hr h hn he x; exact singletonDetector_off a c η hc σ d hd r hr h he x
    | cons e l =>
      let t:=e::l
      have ho : HNOrdered c η t := ordered_tail c η hl
      obtain ⟨D,hD⟩:=ih ho
      obtain ⟨κ,hκ,hkb⟩:=exists_uniform_cutoff c η (d+t.sum) (slope c η d)
      have hb : ∀ x∈t,slope c η x ≤ κ := by
        intro x hx
        apply hkb x _ (ho.1 x hx) ((List.pairwise_cons.mp hl.2).1 x hx)
        exact (List.le_sum_of_mem hx).trans (le_add_of_nonneg_left zero_le)
      have ht : slope c η t.sum ≤ κ := list_slope_le c η hc κ t
        (list_sum_ne_zero ho.1 (by simp [t])) hb
      let hk := hD.ideal κ hb
      refine ⟨consDetector a c η d t D κ hk,?_,?_,?_⟩
      · intro θ h f hf
        apply consDetector_ideal a c η hc d t D κ hk θ ?_ ?_ ?_ f hf
        · exact (ordered_sum_le_head c η hc hl).trans (h d (by simp))
        · exact max_le (h d (by simp)) (hκ.le.trans (h d (by simp)))
        · exact max_le (ht.trans (hκ.le.trans (h d (by simp)))) (hκ.le.trans (h d (by simp)))
      · exact consDetector_diagonal a c η hc σ hσ d t D κ hk hd hκ ht hD.diagonal
      · intro r hr h hn he x
        cases r with
        | nil => exact (list_sum_ne_zero hl.1 (by simp) h.symm).elim
        | cons b r =>
          have hb0:=hr.1 b (by simp)
          have hbd : ¬hnKeyLT c η b d := fun H=>hn (List.Lex.rel H)
          obtain ⟨hs,hm⟩:=hnKeyLT_bounds c η hbd
          by_cases hbd' : b=d
          · subst b
            have hr' : r.sum=t.sum := add_left_cancel h
            have hne : r≠t := fun H=>he (congrArg (d::·) H)
            have hn' : ¬List.Lex (hnKeyLT c η) r t := fun H=>hn (List.Lex.cons H)
            exact consDetector_same_head a c η hc σ d t D κ hk hd hκ ht r hr'
              (hD.off r (ordered_tail c η hr) hr' hn' hne) x
          · exact consDetector_wrong_head a c η hc σ d t D κ hk hκ ht b r h hb0 hs hm hbd' x
end ElementaryPositivity.RawShuffle

end

end OAI
