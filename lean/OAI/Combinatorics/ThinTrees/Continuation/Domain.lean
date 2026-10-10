import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.PartitionGeometry
import OAI.Combinatorics.ThinTrees.Continuation.Ramp

namespace OAI

/-! Continuation domain. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

abbrev ResponseSpace (n m : ℕ) := Matrix (Fin n) (Fin n) ℝ × (Fin m → ℝ)

def admissible (H : MultiGraph n m) (s : ℝ) (u : Fin m → ℝ) : Set (ResponseSpace n m) :=
  {x | x.1 ∈ metricDomain H ∧ (∀e, 0 ≤ x.2 e ∧ x.2 e ≤ 1) ∧
    ∀e, 0 < u e → (6*s*x.2 e) • vecMulVec (H.incidence e) (H.incidence e) ≤ x.1}

lemma admissible_nonempty (H : MultiGraph n m) (s : ℝ) (u : Fin m → ℝ) :
    (admissible H s u).Nonempty := by
  refine ⟨(H.laplacian univ,0),laplacian_mem_domain H,fun e => ?_,?_⟩
  · exact ⟨le_rfl,by norm_num⟩
  · intro e _
    simp only [Pi.zero_apply,mul_zero,zero_smul]
    exact Matrix.nonneg_iff_posSemidef.mpr (H.laplacian_psd univ)

lemma admissible_closed (H : MultiGraph n m) (s : ℝ) (u : Fin m → ℝ) :
    IsClosed (admissible H s u) := by
  have hY : IsClosed {x : ResponseSpace n m | x.1 ∈ metricDomain H} :=
    (domain_closed H).preimage continuous_fst
  have hy : IsClosed {x : ResponseSpace n m | ∀e, 0 ≤ x.2 e ∧ x.2 e ≤ 1} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro e
    exact (isClosed_le continuous_const ((continuous_apply e).comp continuous_snd)).inter
      (isClosed_le ((continuous_apply e).comp continuous_snd) continuous_const)
  have hl : IsClosed {x : ResponseSpace n m | ∀e, 0 < u e →
      (6*s*x.2 e) • vecMulVec (H.incidence e) (H.incidence e) ≤ x.1} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro e
    apply isClosed_iInter
    intro _
    have hc : Continuous (fun x : ResponseSpace n m =>
        x.1-(6*s*x.2 e) • vecMulVec (H.incidence e) (H.incidence e)) := by fun_prop
    convert (isClosed_matrixAbove (0 : Matrix (Fin n) (Fin n) ℝ)).preimage hc using 1
    ext x
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,sub_nonneg]
  exact hY.inter (hy.inter hl)

lemma admissible_compact (H : MultiGraph n m) (hn : 0 < n) (s : ℝ) (u : Fin m → ℝ) :
    IsCompact (admissible H s u) := by
  have hb : IsCompact {y : Fin m → ℝ | ∀e, y e ∈ Set.Icc (0:ℝ) 1} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  apply ((domain_compact H hn).prod hb).of_isClosed_subset (admissible_closed H s u)
  intro x hx
  exact ⟨hx.1,hx.2.1⟩

lemma admissible_convex (H : MultiGraph n m) (s : ℝ) (u : Fin m → ℝ) :
    Convex ℝ (admissible H s u) := by
  intro x hx z hz a b ha hb hab
  refine ⟨domain_convex H hx.1 hz.1 ha hb hab,?_,?_⟩
  · intro e
    change 0 ≤ a*x.2 e+b*z.2 e ∧ a*x.2 e+b*z.2 e ≤ 1
    refine ⟨add_nonneg (mul_nonneg ha (hx.2.1 e).1) (mul_nonneg hb (hz.2.1 e).1),?_⟩
    have h1 := mul_le_mul_of_nonneg_left (hx.2.1 e).2 ha
    have h2 := mul_le_mul_of_nonneg_left (hz.2.1 e).2 hb
    nlinarith only [h1,h2,hab]
  · intro e he
    apply Matrix.le_iff.mpr
    have h1 := (Matrix.le_iff.mp (hx.2.2 e he)).smul ha
    have h2 := (Matrix.le_iff.mp (hz.2.2 e he)).smul hb
    convert h1.add h2 using 1
    change a • x.1+b • z.1-(6*s*(a*x.2 e+b*z.2 e)) •
      vecMulVec (H.incidence e) (H.incidence e)=_
    simp only [smul_sub,smul_smul]
    module

lemma lowerCapacity_continuous (κ t u : ℝ) : Continuous (lowerCapacity κ t u) := by
  unfold lowerCapacity
  split_ifs
  · fun_prop
  · exact continuous_const

lemma lowerCapacity_concave (κ t u : ℝ) : ConcaveOn ℝ Set.univ (lowerCapacity κ t u) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  change a*lowerCapacity κ t u x+b*lowerCapacity κ t u y ≤
    lowerCapacity κ t u (a*x+b*y)
  unfold lowerCapacity
  split_ifs with hu
  · have h1 := mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) (u+t*(5*x-4))) ha
    have h2 := mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) (u+t*(5*y-4))) hb
    have h3 := mul_le_mul_of_nonneg_left (min_le_right (1:ℝ) (u+t*(5*x-4))) ha
    have h4 := mul_le_mul_of_nonneg_left (min_le_right (1:ℝ) (u+t*(5*y-4))) hb
    have hc : a*κ+b*κ=κ := by rw [←add_mul,hab,one_mul]
    have hlin : a*(u+t*(5*x-4))+b*(u+t*(5*y-4))=u+t*(5*(a*x+b*y)-4) := by
      calc
        _ = (a+b)*(u-4*t)+5*t*(a*x+b*y) := by ring
        _ = _ := by rw [hab]; ring
    conv_rhs => rw [add_min]
    apply le_min <;> nlinarith only [h1,h2,h3,h4,hc,hlin,hab]
  · rw [←add_mul,hab,one_mul]

def responseSlack (H : MultiGraph n m) (κ t Q : ℝ) (u : Fin m → ℝ)
    (p : Setoid (Fin n)) (x : ResponseSpace n m) : ℝ :=
  Partitions.slack H.left H.right (fun e => lowerCapacity κ t (u e) (x.2 e)) Q p

lemma responseSlack_continuous (H : MultiGraph n m) (κ t Q : ℝ) (u : Fin m → ℝ)
    (p : Setoid (Fin n)) : Continuous (responseSlack H κ t Q u p) := by
  unfold responseSlack Partitions.slack Partitions.capacity
  apply Continuous.sub _ continuous_const
  apply continuous_finsetSum
  intro e _
  exact ((lowerCapacity_continuous κ t (u e)).comp
    ((continuous_apply e).comp continuous_snd)).mul_const _

lemma responseSlack_concave (H : MultiGraph n m) (κ t Q s : ℝ) (u : Fin m → ℝ)
    (p : Setoid (Fin n)) : ConcaveOn ℝ (admissible H s u) (responseSlack H κ t Q u p) := by
  refine ⟨admissible_convex H s u,?_⟩
  intro x hx z hz a b ha hb hab
  have hsum := sum_le_sum (s:=Partitions.crossing H p) (fun e (_ : e ∈ Partitions.crossing H p) =>
    (lowerCapacity_concave κ t (u e)).2 (Set.mem_univ (x.2 e)) (Set.mem_univ (z.2 e)) ha hb hab)
  simp only [smul_eq_mul,←mul_sum,sum_add_distrib] at hsum
  change a*responseSlack H κ t Q u p x+b*responseSlack H κ t Q u p z ≤
    responseSlack H κ t Q u p (a • x+b • z)
  unfold responseSlack Partitions.slack
  rw [Partitions.capacity_eq_sum,Partitions.capacity_eq_sum,Partitions.capacity_eq_sum]
  have hc : a*(Q*((Partitions.partCount p:ℝ)-1))+b*(Q*((Partitions.partCount p:ℝ)-1))=
      Q*((Partitions.partCount p:ℝ)-1) := by rw [←add_mul,hab,one_mul]
  change a*((∑e ∈ Partitions.crossing H p, lowerCapacity κ t (u e) (x.2 e))-
        Q*((Partitions.partCount p:ℝ)-1))+
      b*((∑e ∈ Partitions.crossing H p, lowerCapacity κ t (u e) (z.2 e))-
        Q*((Partitions.partCount p:ℝ)-1)) ≤
      (∑e ∈ Partitions.crossing H p, lowerCapacity κ t (u e) (a*x.2 e+b*z.2 e))-
        Q*((Partitions.partCount p:ℝ)-1)
  nlinarith only [hsum,hc]

lemma responseSlack_submodular (H : MultiGraph n m) {κ t Q s : ℝ} (u : Fin m → ℝ)
    (ht : 0 ≤ t) (hκ : 4*t ≤ κ) (hQ : 0 ≤ Q) {x : ResponseSpace n m}
    (hx : x ∈ admissible H s u) (p q : Setoid (Fin n)) :
    responseSlack H κ t Q u (p ⊓ q) x+responseSlack H κ t Q u (p ⊔ q) x ≤
      responseSlack H κ t Q u p x+responseSlack H κ t Q u q x :=
  Partitions.slack_submodular H.left H.right _
    (fun e => lowerCapacity_nonneg ht (hx.2.1 e).1 hκ) hQ p q

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
