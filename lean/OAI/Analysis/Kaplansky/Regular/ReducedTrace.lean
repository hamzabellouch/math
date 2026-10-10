import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Quotient.MatrixKernel

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped InnerProductSpace ComplexOrder BigOperators ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance 2200] Complex.partialOrder
variable {G : Type*}

def delta (g : G) : HilbertSum G ℂ := lp.single 2 g 1
@[simp] lemma delta_apply (g h : G) : delta g h = if h=g then 1 else 0 := by
  simp [delta,lp.single_apply,Pi.single_apply]
@[simp] lemma inner_delta (g : G) (x : HilbertSum G ℂ) : inner ℂ (delta g) x = x g := by
  simp [delta,lp.inner_single_left,RCLike.inner_apply]

@[simp] lemma inner_delta_right (g : G) (x : HilbertSum G ℂ) : inner ℂ x (delta g) = star (x g) := by
  simp [delta,lp.inner_single_right,RCLike.inner_apply]

variable [Group G]

def right (g : G) : HilbertSum G ℂ →L[ℂ] HilbertSum G ℂ :=
  (reindex (Equiv.mulRight g⁻¹)).toLinearIsometry.toContinuousLinearMap
@[simp] lemma right_apply (g h : G) (x : HilbertSum G ℂ) : right g x h = x (h*g) := by
  simp [right,reindex_apply]
lemma right_star (g : G) : star (right g) = right g⁻¹ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro x y
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  simpa [right_apply,mul_assoc] using
    ((Equiv.mulRight g).tsum_eq (fun i => inner ℂ (x (i*g⁻¹)) (y i))).symm

lemma left_commute_right (g h : G) : Commute (left g) (right h) := by
  apply ContinuousLinearMap.ext; intro x; ext k
  simp [mul_assoc]

lemma algebra_commute_right (T : Algebra G) (g : G) : Commute T.val (right g) := by
  have hs : Algebra G ≤ StarSubalgebra.centralizer ℂ (Set.range (right (G:=G))) := by
    apply StarSubalgebra.topologicalClosure_minimal
    · apply StarAlgebra.adjoin_le
      rintro _ ⟨h,rfl⟩
      change left h ∈ StarSubalgebra.centralizer ℂ (Set.range (right (G:=G)))
      rw [StarSubalgebra.mem_centralizer_iff ℂ]
      rintro _ ⟨k,rfl⟩
      exact ⟨(left_commute_right h k).eq.symm, by rw [right_star]; exact (left_commute_right h k⁻¹).eq.symm⟩
    · exact Set.isClosed_centralizer _
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp (hs T.property)) _ ⟨g,rfl⟩).1.symm

lemma right_delta (g : G) : right g (delta 1) = delta g⁻¹ := by
  ext k
  simp only [right_apply,delta_apply]
  simp only [mul_eq_one_iff_eq_inv]

lemma algebra_delta (T : Algebra G) (g h : G) :
    T.val (delta g) h = T.val (delta 1) (h*g⁻¹) := by
  have he : delta g = right g⁻¹ (delta 1) := by simp [right_delta]
  rw [he]
  have hc := congrArg (fun S : HilbertSum G ℂ →L[ℂ] HilbertSum G ℂ => S (delta 1) h)
    (algebra_commute_right T g⁻¹).eq
  simpa only [mul_apply_eq_comp,right_apply] using hc

lemma algebra_star_delta (T : Algebra G) (g : G) :
    (star T).val (delta 1) g = star (T.val (delta 1) g⁻¹) := by
  rw [← inner_delta]
  change inner ℂ (delta g) (T.val.adjoint (delta 1)) = _
  rw [ContinuousLinearMap.adjoint_inner_right,inner_delta_right,algebra_delta,one_mul]

def coefficient (T : Algebra G) : ℂ := T.val (delta 1) 1
lemma coefficient_square (T : Algebra G) :
    coefficient (star T*T) = inner ℂ (T.val (delta 1)) (T.val (delta 1)) := by
  calc
    coefficient (star T*T) = inner ℂ (delta 1) (T.val.adjoint (T.val (delta 1))) :=
      (inner_delta 1 _).symm
    _ = _ := T.val.adjoint_inner_right (delta 1) (T.val (delta 1))

lemma coefficient_tracial (S T : Algebra G) : coefficient (S*T) = coefficient (T*S) := by
  have he (X Y : Algebra G) : coefficient (X*Y) = ∑' g, X.val (delta 1) g⁻¹ * Y.val (delta 1) g := by
    rw [coefficient,← inner_delta]
    change inner ℂ (delta 1) (X.val (Y.val (delta 1))) = _
    rw [← ContinuousLinearMap.adjoint_inner_left,lp.inner_eq_tsum]
    apply tsum_congr; intro g
    change inner ℂ ((star X).val (delta 1) g) (Y.val (delta 1) g) = _
    rw [algebra_star_delta]
    simp [RCLike.inner_apply,mul_comm]
  rw [he,he]
  simpa [mul_comm] using ((Equiv.inv G).tsum_eq (fun g => S.val (delta 1) g⁻¹ * T.val (delta 1) g)).symm

lemma delta_cyclic (T : Algebra G) (h : T.val (delta 1) = 0) : T = 0 := by
  have hd (g : G) : T.val (delta g) = 0 := by
    ext k
    rw [algebra_delta,h]; rfl
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  change T.val x = 0
  have hs := (T.val.hasSum (lp.hasSum_single (by norm_num : (2:ℝ≥0∞) ≠ ⊤) x))
  have hz (g : G) : T.val (lp.single 2 g (x g)) = 0 := by
    have he : lp.single 2 g (x g) = (x g) • delta g := by
      ext k
      by_cases hkg : k=g <;> simp [delta_apply,lp.single_apply,hkg]
    rw [he,map_smul,hd,smul_zero]
  simp only [hz] at hs
  exact hs.unique hasSum_zero

lemma coefficient_faithful (T : Algebra G) (h : coefficient (star T*T) = 0) : T=0 := by
  rw [coefficient_square] at h
  exact delta_cyclic T ((inner_self_eq_zero).mp h)

def canonicalTrace : TracialState (Algebra G) where
  functional := PositiveLinearMap.mk₀
    { toFun := coefficient
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    (fun T hT => by
      obtain ⟨X,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hT
      change 0 ≤ coefficient (star X*X)
      rw [coefficient_square]
      rw [inner_self_eq_norm_sq_to_K]
      positivity)
  normalized := by
    change coefficient 1 = 1
    simp [coefficient,delta_apply]
  tracial := coefficient_tracial


end KaplanskyConsequences.Regular

end

end OAI
