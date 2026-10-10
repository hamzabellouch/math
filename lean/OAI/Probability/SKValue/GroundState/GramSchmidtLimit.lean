import Mathlib
import OAI.Probability.SKValue.GroundState.GaussianColumn

namespace OAI

section

open Filter Set InnerProductSpace
open scoped Topology BigOperators RealInnerProductSpace
namespace SKValueG
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]

lemma inner_approx_tendsto {x x' y : (n : ℕ) → E n} {a b : ℝ}
    (hx : Tendsto (fun n ↦ ‖x n-x' n‖) atTop (𝓝 0))
    (hy : Tendsto (fun n ↦ ‖y n‖) atTop (𝓝 b))
    (hxy : Tendsto (fun n ↦ ⟪x' n,y n⟫) atTop (𝓝 a)) :
    Tendsto (fun n ↦ ⟪x n,y n⟫) atTop (𝓝 a) := by
  have hdiff : Tendsto (fun n ↦ ⟪x n,y n⟫-⟪x' n,y n⟫) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n ↦ ?_) (by simpa using hx.mul hy)
    rw [←inner_sub_left,Real.norm_eq_abs]
    exact abs_real_inner_le_norm _ _
  simpa only [sub_add_cancel,zero_add] using hdiff.add hxy

omit [∀ n, InnerProductSpace ℝ (E n)] in
lemma norm_approx_tendsto {x x' : (n : ℕ) → E n} {a : ℝ}
    (hx : Tendsto (fun n ↦ ‖x n-x' n‖) atTop (𝓝 0))
    (hx' : Tendsto (fun n ↦ ‖x' n‖) atTop (𝓝 a)) :
    Tendsto (fun n ↦ ‖x n‖) atTop (𝓝 a) := by
  have hd : Tendsto (fun n ↦ ‖x n‖-‖x' n‖) atTop (𝓝 0) := by
    exact squeeze_zero_norm (fun n ↦ by simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le (x n) (x' n)) hx
  simpa only [sub_add_cancel,zero_add] using hd.add hx'

theorem gramSchmidt_approx (a : (n : ℕ) → ℕ → E n) (K : ℕ)
    (hn : ∀ i≤K,Tendsto (fun n ↦ ‖a n i‖) atTop (𝓝 1))
    (hi : ∀ i j,i<j → j≤K → Tendsto (fun n ↦ ⟪a n i,a n j⟫) atTop (𝓝 0))
    (j : ℕ) (hj : j≤K) :
    Tendsto (fun n ↦ ‖gramSchmidt ℝ (a n) j-a n j‖) atTop (𝓝 0) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    have hnorm (i : ℕ) (hij : i<j) :
        Tendsto (fun n ↦ ‖gramSchmidt ℝ (a n) i‖) atTop (𝓝 1) :=
      norm_approx_tendsto (ih i hij (hij.le.trans hj)) (hn i (hij.le.trans hj))
    have hinner (i : ℕ) (hij : i<j) :
        Tendsto (fun n ↦ ⟪gramSchmidt ℝ (a n) i,a n j⟫) atTop (𝓝 0) :=
      inner_approx_tendsto (ih i hij (hij.le.trans hj)) (hn j hj) (hi i j hij hj)
    have hterm (i : ℕ) (hij : i<j) :
        Tendsto (fun n ↦ ‖(⟪gramSchmidt ℝ (a n) i,a n j⟫ /
          ‖gramSchmidt ℝ (a n) i‖^2) • gramSchmidt ℝ (a n) i‖) atTop (𝓝 0) := by
      simp only [norm_smul,Real.norm_eq_abs]
      have h := ((hinner i hij).div ((hnorm i hij).pow 2) (by norm_num)).abs.mul (hnorm i hij)
      simpa using h
    have hs : Tendsto (fun n ↦ ∑ i∈Finset.range j,
        ‖(⟪gramSchmidt ℝ (a n) i,a n j⟫/‖gramSchmidt ℝ (a n) i‖^2) •
          gramSchmidt ℝ (a n) i‖) atTop (𝓝 0) := by
      simpa only [Finset.sum_const_zero] using tendsto_finsetSum (Finset.range j)
        (fun i hi ↦ hterm i (Finset.mem_range.mp hi))
    apply squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hs
    have he := gramSchmidt_def'' ℝ (a n) j
    have he' : gramSchmidt ℝ (a n) j-a n j =
        -(∑ i∈Finset.range j,(⟪gramSchmidt ℝ (a n) i,a n j⟫ /
          ‖gramSchmidt ℝ (a n) i‖^2) • gramSchmidt ℝ (a n) i) := by
      simp only [Nat.Iio_eq_range] at he
      calc
        _ = gramSchmidt ℝ (a n) j-(gramSchmidt ℝ (a n) j+_) := congrArg (fun x ↦ gramSchmidt ℝ (a n) j-x) he
        _ = _ := by abel
    rw [he',norm_neg]
    exact norm_sum_le _ _

theorem gramSchmidtNormed_approx (a : (n : ℕ) → ℕ → E n) (K : ℕ)
    (hn : ∀ i≤K,Tendsto (fun n ↦ ‖a n i‖) atTop (𝓝 1))
    (hi : ∀ i j,i<j → j≤K → Tendsto (fun n ↦ ⟪a n i,a n j⟫) atTop (𝓝 0))
    (j : ℕ) (hj : j≤K) :
    Tendsto (fun n ↦ ‖gramSchmidtNormed ℝ (a n) j-a n j‖) atTop (𝓝 0) := by
  have hg := gramSchmidt_approx a K hn hi j hj
  have hgn := norm_approx_tendsto hg (hn j hj)
  have hscale : Tendsto (fun n ↦ |‖gramSchmidt ℝ (a n) j‖⁻¹-1| *
      ‖gramSchmidt ℝ (a n) j‖) atTop (𝓝 0) := by
    simpa using ((hgn.inv₀ (by norm_num)).sub_const 1).abs.mul hgn
  apply squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) (by simpa using hscale.add hg)
  calc
    _ ≤ ‖gramSchmidtNormed ℝ (a n) j-gramSchmidt ℝ (a n) j‖+
        ‖gramSchmidt ℝ (a n) j-a n j‖ := by
      calc
        _ = ‖(gramSchmidtNormed ℝ (a n) j-gramSchmidt ℝ (a n) j)+(gramSchmidt ℝ (a n) j-a n j)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    _ = _ := by
      congr 1
      change ‖‖gramSchmidt ℝ (a n) j‖⁻¹ • gramSchmidt ℝ (a n) j-gramSchmidt ℝ (a n) j‖ = _
      have he : ‖gramSchmidt ℝ (a n) j‖⁻¹ • gramSchmidt ℝ (a n) j-gramSchmidt ℝ (a n) j =
          (‖gramSchmidt ℝ (a n) j‖⁻¹-1) • gramSchmidt ℝ (a n) j := by rw [sub_smul,one_smul]
      rw [he,norm_smul,Real.norm_eq_abs]

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def orthogonalRemainder (v : ℕ → E) (w : E) (j : ℕ) : E :=
  w-∑ i∈Finset.range j,(⟪v i,w⟫ : ℝ) • v i

lemma inner_orthogonalRemainder (v : ℕ → E) (w : E) (j : ℕ)
    (ho : ∀ i<j,⟪v j,v i⟫=0) :
    ⟪v j,orthogonalRemainder v w j⟫=⟪v j,w⟫ := by
  simp only [orthogonalRemainder,inner_sub_right,inner_sum,real_inner_smul_right]
  have hz : (∑ i∈Finset.range j,⟪v i,w⟫*⟪v j,v i⟫)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [ho i (Finset.mem_range.mp hi)]
  rw [hz,sub_zero]

lemma orthogonalRemainder_succ (v : ℕ → E) (w : E) (j : ℕ) :
    orthogonalRemainder v w (j+1)=orthogonalRemainder v w j-⟪v j,w⟫ • v j := by
  simp only [orthogonalRemainder,Finset.sum_range_succ]
  abel

lemma columnResidual_orthogonalRemainder {κ : Type*} [Fintype κ]
    (v : ℕ → EuclideanSpace ℝ κ) (w : EuclideanSpace ℝ κ) (j : ℕ)
    (ho : ∀ i<j,⟪v j,v i⟫=0) :
    columnResidual (v j) (orthogonalRemainder v w j)=orthogonalRemainder v w (j+1) := by
  rw [columnResidual,inner_orthogonalRemainder v w j ho,orthogonalRemainder_succ]

lemma column_revealed_energy {κ : Type*} [Fintype κ]
    (v : ℕ → EuclideanSpace ℝ κ) (w z : EuclideanSpace ℝ κ) (j : ℕ)
    (ho : ∀ i<j,⟪v j,v i⟫=0) :
    ⟪columnVector (v j) (orthogonalRemainder v w j),z⟫=
      ⟪v j,w⟫*⟪orthogonalRemainder v w (j+1),z⟫+
      (⟪v j,w⟫^2/Real.sqrt 2)*⟪v j,z⟫ := by
  simp only [columnVector,inner_add_left,real_inner_smul_left]
  rw [inner_orthogonalRemainder v w j ho,columnResidual_orthogonalRemainder v w j ho]

section Limit
variable {E' : ℕ → Type*} [∀ n,NormedAddCommGroup (E' n)] [∀ n,InnerProductSpace ℝ (E' n)]

lemma orthogonalRemainder_inner_tendsto (v : (n : ℕ) → ℕ → E' n)
    (w z : (n : ℕ) → E' n) (K : ℕ) (A : ℕ → ℝ) (B : ℝ)
    (ha : ∀ j<K,Tendsto (fun n ↦ ⟪v n j,w n⟫) atTop (𝓝 (A j)))
    (hz : ∀ j<K,Tendsto (fun n ↦ ⟪v n j,z n⟫) atTop (𝓝 0))
    (hwz : Tendsto (fun n ↦ ⟪w n,z n⟫) atTop (𝓝 B)) :
    Tendsto (fun n ↦ ⟪orthogonalRemainder (v n) (w n) K,z n⟫) atTop (𝓝 B) := by
  have hs : Tendsto (fun n ↦ ∑ j∈Finset.range K,⟪v n j,w n⟫*⟪v n j,z n⟫) atTop (𝓝 0) := by
    have hh := tendsto_finsetSum (s:=Finset.range K)
      (fun j hj ↦ (ha j (Finset.mem_range.mp hj)).mul (hz j (Finset.mem_range.mp hj)))
    simpa using hh
  have ht := hwz.sub hs
  simpa only [orthogonalRemainder,inner_sub_left,sum_inner,real_inner_smul_left,sub_zero] using ht

theorem normalized_column_energy_tendsto (a : (n : ℕ) → ℕ → E' n)
    (w z : (n : ℕ) → E' n) (K : ℕ) (A : ℕ → ℝ) (B : ℝ)
    (hn : ∀ i≤K,Tendsto (fun n ↦ ‖a n i‖) atTop (𝓝 1))
    (hi : ∀ i j,i<j → j≤K → Tendsto (fun n ↦ ⟪a n i,a n j⟫) atTop (𝓝 0))
    (hwn : Tendsto (fun n ↦ ‖w n‖) atTop (𝓝 1))
    (hzn : Tendsto (fun n ↦ ‖z n‖) atTop (𝓝 1))
    (ha : ∀ j≤K,Tendsto (fun n ↦ ⟪a n j,w n⟫) atTop (𝓝 (A j)))
    (hz : ∀ j≤K,Tendsto (fun n ↦ ⟪a n j,z n⟫) atTop (𝓝 0))
    (hb : Tendsto (fun n ↦ ⟪w n,z n⟫) atTop (𝓝 B)) :
    Tendsto (fun n ↦
      ⟪gramSchmidtNormed ℝ (a n) K,w n⟫*
        ⟪orthogonalRemainder (gramSchmidtNormed ℝ (a n)) (w n) (K+1),z n⟫+
      (⟪gramSchmidtNormed ℝ (a n) K,w n⟫^2/Real.sqrt 2)*
        ⟪gramSchmidtNormed ℝ (a n) K,z n⟫) atTop (𝓝 (A K*B)) := by
  have hp (j : ℕ) (hj : j≤K) :
      Tendsto (fun n ↦ ‖gramSchmidtNormed ℝ (a n) j-a n j‖) atTop (𝓝 0) :=
    gramSchmidtNormed_approx a j (fun i h ↦ hn i (h.trans hj))
      (fun i l hil hl ↦ hi i l hil (hl.trans hj)) j le_rfl
  have ha' (j : ℕ) (hj : j≤K) := inner_approx_tendsto (hp j hj) hwn (ha j hj)
  have hz' (j : ℕ) (hj : j≤K) := inner_approx_tendsto (hp j hj) hzn (hz j hj)
  have hr := orthogonalRemainder_inner_tendsto (fun n ↦ gramSchmidtNormed ℝ (a n)) w z
    (K+1) A B (fun j hj ↦ ha' j (by omega)) (fun j hj ↦ hz' j (by omega)) hb
  simpa only [mul_zero,add_zero] using
    ((ha' K le_rfl).mul hr).add (((ha' K le_rfl).pow 2 |>.div_const _).mul (hz' K le_rfl))
end Limit
end SKValueG

end

end OAI
