import OAI.Analysis.FreeEntropy.ActualTuple

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace FreeSeries
variable {n : ℕ}
def leftIndex : Fin n → Fin (n+n) := Fin.castAdd n
def rightIndex : Fin n → Fin (n+n) := Fin.natAdd n
 theorem leftIndex_injective : Function.Injective (leftIndex (n := n)) := Fin.castAdd_injective n n
 theorem rightIndex_injective : Function.Injective (rightIndex (n := n)) := Fin.natAdd_injective n n
 theorem leftIndex_ne_rightIndex (i j : Fin n) : leftIndex i ≠ rightIndex j := by
  intro h
  have hh := congrArg Fin.val h
  simp [leftIndex, rightIndex] at hh
  have hi := i.isLt
  omega
 theorem joint_cases (j : Fin (n+n)) : (∃i, j=leftIndex i) ∨ (∃i, j=rightIndex i) := by
  induction j using Fin.addCases with
  | left i => exact Or.inl ⟨i,rfl⟩
  | right i => exact Or.inr ⟨i,rfl⟩
def gaussianJointR (R : Series (Fin n)) : Series (Fin (n+n)) :=
  liftSeries leftIndex R + liftSeries rightIndex quadratic
@[simp] theorem gaussianJointR_nil (R : Series (Fin n)) (hR : R [] = 0) : gaussianJointR R [] = 0 := by
  simp [gaussianJointR, hR]
 theorem gaussianJointR_noise_deriv (R : Series (Fin n)) (i : Fin n) :
    FreeSeries.deriv (rightIndex i) (gaussianJointR R) = letter (rightIndex i) := by
  change FreeSeries.deriv (rightIndex i) (liftSeries leftIndex R) +
    FreeSeries.deriv (rightIndex i) (liftSeries rightIndex quadratic) = _
  rw [deriv_liftSeries_out _ _ _ (fun j => leftIndex_ne_rightIndex j i),
    deriv_liftSeries_image _ rightIndex_injective, deriv_quadratic, liftSeries_letter, zero_add]
 theorem gaussianJointR_restrict (R : Series (Fin n)) : restrict leftIndex (gaussianJointR R) = R := by
  have hh := restrict_liftSeries_disjoint (rightIndex (n := n)) leftIndex
    (fun i j => (leftIndex_ne_rightIndex j i).symm) (quadratic : Series (Fin n)) quadratic_nil
  have hl := restrict_liftSeries (leftIndex (n := n)) leftIndex_injective R
  funext w
  exact (congrArg₂ (·+·) (congrFun hl w) (congrFun hh w)).trans (add_zero _)
 theorem gaussianJointR_cyclic {R : Series (Fin n)} (hR : Cyclic R) : Cyclic (gaussianJointR R) := by
  have hL := hR.reparam (fun a b => if leftIndex a=b then (1:ℂ) else 0)
  have hN := (cyclic_quadratic (α := Fin n)).reparam (fun a b => if rightIndex a=b then (1:ℂ) else 0)
  intro i
  change FreeSeries.deriv i (liftSeries leftIndex R) + FreeSeries.deriv i (liftSeries rightIndex quadratic) =
    rightDeriv i (liftSeries leftIndex R) + rightDeriv i (liftSeries rightIndex quadratic)
  exact congrArg₂ (·+·) (hL i) (hN i)
 theorem word_left_or_noise (w : List (Fin (n+n))) :
    (∃ v : List (Fin n), w=v.map leftIndex) ∨ (∃u i v, w=u++rightIndex i::v) := by
  induction w with
  | nil => exact Or.inl ⟨[],rfl⟩
  | cons a w ih =>
    rcases joint_cases a with ⟨i,rfl⟩ | ⟨i,rfl⟩
    · rcases ih with ⟨v,rfl⟩ | ⟨u,j,v,rfl⟩
      · exact Or.inl ⟨i::v,rfl⟩
      · exact Or.inr ⟨leftIndex i::u,j,v,rfl⟩
    · exact Or.inr ⟨[],i,w,rfl⟩

theorem mixed_gaussian_unique {M N : Series (Fin (n+n))}
    (hM : Cyclic M) (hN : Cyclic N) (hleft : restrict leftIndex M = restrict leftIndex N)
    (hm : ∀ i, FreeSeries.deriv (rightIndex i) M = conv M (subst M (letter (rightIndex i))))
    (hn : ∀ i, FreeSeries.deriv (rightIndex i) N = conv N (subst N (letter (rightIndex i)))) : M=N := by
  funext w
  induction w using length_induction with
  | h w ih =>
    rcases word_left_or_noise w with ⟨v,rfl⟩ | ⟨u,i,v,rfl⟩
    · exact congrFun hleft v
    · rw [hM.append u _, hN.append u _]
      change FreeSeries.deriv (rightIndex i) M (v++u) = FreeSeries.deriv (rightIndex i) N (v++u)
      rw [hm, hn]
      exact pairDerivative_congr (fun z hz => ih z (by simp at hz ⊢; omega)) _ (v++u) le_rfl
 theorem moments_cumulants {α : Type} [DecidableEq α] [Fintype α] {M : Series α} (hM : M [] = 1) :
    moments (cumulants M) = M := (moments_unique (cumulants_nil M) (cumulants_equation hM)).symm
end FreeSeries

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
variable {n : ℕ}
def jointTuple (X : Fin n → Space B N G →L[ℂ] Space B N G) (σ : Fin n → N) :
    Fin (n+n) → Space B N G →L[ℂ] Space B N G := Fin.addCases X (fun i => semicircularN (σ i))
@[simp] theorem jointTuple_left (X : Fin n → Space B N G →L[ℂ] Space B N G) (σ : Fin n → N) (i : Fin n) :
    jointTuple X σ (leftIndex i) = X i := Fin.addCases_left i
@[simp] theorem jointTuple_right (X : Fin n → Space B N G →L[ℂ] Space B N G) (σ : Fin n → N) (i : Fin n) :
    jointTuple X σ (rightIndex i) = semicircularN (σ i) := Fin.addCases_right i
 theorem jointTuple_mem (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J) (σ : Fin n → N) (j : Fin (n+n)) :
    jointTuple X σ j ∈ algebra B N G := by
  rcases joint_cases j with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · rw [jointTuple_left]; exact backgroundAlgebra_le J (hX i)
  · rw [jointTuple_right]; exact semicircularN_mem _
 theorem jointTuple_noise_deriv (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J) (i : Fin n) :
    FreeSeries.deriv (rightIndex i) (wordMoment (tracialVector B N G) (jointTuple X σ)) =
      conv (wordMoment (tracialVector B N G) (jointTuple X σ))
        (subst (wordMoment (tracialVector B N G) (jointTuple X σ)) (letter (rightIndex i))) := by
  let Z := jointTuple X σ
  let τ := tracialVector B N G
  have hc (j : Fin (n+n)) : star (rightCreationN (σ i)) * Z j =
      Z j * star (rightCreationN (σ i)) + if j=rightIndex i then (1:ℂ) • vacuumRankOne τ else 0 := by
    rcases joint_cases j with ⟨k,rfl⟩ | ⟨k,rfl⟩
    · simpa [Z, leftIndex_ne_rightIndex] using (rightAnnihilationN_background (hs i) (hX k)).eq
    · have he : σ i = σ k ↔ rightIndex k = rightIndex i := by
        rw [hσ.eq_iff, rightIndex_injective.eq_iff, eq_comm]
      simpa [Z, he] using rightAnnihilationN_semicircularN (B := B) (G := G) (σ i) (σ k)
  funext w
  rw [← derivativeMoment_series]
  have h := commutator_integration_by_parts τ Z (star (rightCreationN (σ i)))
    (rightIndex i) 1 hc (by simp [τ, tracialVector, basis, empty]) w
  simp only [star_star, one_mul] at h
  have hv : rightCreationN (σ i) τ.vacuum = semicircularN (σ i) τ.vacuum := by
    simp [τ, tracialVector, semicircularN, basis, rightCreationN_single, creationN_single,
      annihilationN_single, removeN, rightN_eq_append, empty, append, leftN, push]
  rw [hv, ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    (semicircularN_selfAdjoint (B := B) (G := G) (σ i)).star_eq] at h
  change trace τ (semicircularN (σ i) * wordEval Z w) = _ at h
  simpa [FreeSeries.deriv, wordMoment, wordEval, Z] using h

 theorem joint_moments_cumulants (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J) :
    wordMoment (tracialVector B N G) (jointTuple X σ) =
      moments (gaussianJointR (cumulants (wordMoment (tracialVector B N G) X))) := by
  let τ := tracialVector B N G
  let M := wordMoment τ X
  have hM : M [] = 1 := by simp [M]
  have hC : Cyclic M := wordMoment_cyclic τ X (fun i => backgroundAlgebra_le J (hX i))
  let R := gaussianJointR (cumulants M)
  have hR : R [] = 0 := gaussianJointR_nil _ (cumulants_nil M)
  apply mixed_gaussian_unique
  · exact wordMoment_cyclic τ _ (jointTuple_mem J X hX σ)
  · exact cyclic_moments hR (gaussianJointR_cyclic (cyclic_cumulants hM hC))
  · rw [restrict_moments leftIndex hR, gaussianJointR_restrict, moments_cumulants hM, wordMoment_restrict]
    congr 1
    funext i
    exact jointTuple_left X σ i
  · exact jointTuple_noise_deriv J X hX σ hσ hs
  · intro i
    rw [deriv_moments hR, gaussianJointR_noise_deriv]
end FreeTensor
end FiniteEntropySeparation

end

end OAI
