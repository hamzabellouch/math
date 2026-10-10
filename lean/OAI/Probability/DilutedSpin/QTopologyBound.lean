import OAI.Probability.DilutedSpin.FiniteLogExpansion
import OAI.Probability.DilutedSpin.QTreeLaw

namespace OAI

section
namespace DilutedSpinGlass
open scoped BigOperators

noncomputable def insertionRadius (C : ℝ) : ℝ := 1-Real.exp (-2*C-1)
noncomputable def normalizedInsertion (C x : ℝ) : ℝ :=
  (Real.exp (x-C)-1)/insertionRadius C

lemma insertionRadius_pos {C : ℝ} (hC : 0≤C) : 0 < insertionRadius C := by
  have he : Real.exp (-2*C-1)<1 := Real.exp_lt_one_iff.mpr (by linarith)
  dsimp only [insertionRadius]
  linarith

lemma insertionRadius_lt_one (C : ℝ) : insertionRadius C < 1 := by
  have := Real.exp_pos (-2*C-1)
  dsimp only [insertionRadius]
  linarith

lemma normalizedInsertion_bound {C x : ℝ} (hC : 0≤C) (hx : |x|≤C) :
    |normalizedInsertion C x|≤1 := by
  have hc := insertionRadius_pos hC
  have helo : Real.exp (-2*C-1)≤Real.exp (x-C) := Real.exp_le_exp.mpr (by linarith [(abs_le.mp hx).1])
  have hehi : Real.exp (x-C)≤1 := Real.exp_le_one_iff.mpr (by linarith [(abs_le.mp hx).2])
  rw [normalizedInsertion,abs_div,abs_of_pos hc,div_le_one₀ hc]
  apply abs_le.mpr
  dsimp only [insertionRadius]
  constructor <;> linarith

lemma normalizedInsertion_log {C x : ℝ} (hC : 0≤C) :
    Real.log (1+insertionRadius C*normalizedInsertion C x)=x-C := by
  have hc := ne_of_gt (insertionRadius_pos hC)
  rw [normalizedInsertion,mul_div_cancel₀ _ hc]
  convert Real.log_exp (x-C) using 1
  congr 1
  ring

namespace KernelTower
variable {Ω : Type} [Fintype Ω]
lemma backwardLog_normalized {n : ℕ} (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : ∀ i : Fin n, m i.succ≠0)
    (F : FinitePath Ω n → ℝ) {C : ℝ} (hC : 0≤C) :
    backwardLog n T (fun i => m i.succ) F =
      PrescribedTree.logInsertion T m (fun y => normalizedInsertion C (F y)) (insertionRadius C)+C := by
  unfold PrescribedTree.logInsertion
  simp_rw [normalizedInsertion_log hC]
  rw [← backwardLog_add n T _ hm (fun y => F y-C) C]
  congr 1
  funext y
  ring
end KernelTower
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance qTopologyBoundDecidableEq (type : Type) :
    DecidableEq type := Classical.decEq type
noncomputable local instance qTopologyBoundDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

lemma chargeBound_mono {C D C' D' : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hCC : C ≤ C') (hDD : D ≤ D') (k b : ℕ) : chargeBound C D k b ≤ chargeBound C' D' k b := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih =>
    cases b with
    | zero => exact mul_le_mul hCC (ih 0) (chargeBound_nonneg hC hD _ _) (hC.trans hCC)
    | succ b =>
      exact add_le_add
        (mul_le_mul hCC (ih _) (chargeBound_nonneg hC hD _ _) (hC.trans hCC))
        (mul_le_mul hDD (ih _) (chargeBound_nonneg hC hD _ _) (hD.trans hDD))

noncomputable def qMass (L k : ℕ) (T : PrescribedTree L) : ℝ :=
  qExpect (grid L 0 L) (fun R => if R=T then 1 else 0) k (single L)

lemma qMass_nonneg (L k : ℕ) (hL : 0<L) (T : PrescribedTree L) : 0 ≤ qMass L k T := by
  apply qExpect_nonneg _ (grid_strictMono hL).monotone grid_nonneg
  intro R
  split_ifs <;> norm_num

/-- A shape-only constant, independent of every assigned depth and system size. -/
noncomputable def shapeCharge (k : ℕ) (S : ReducedTopology) : ℝ :=
  chargeBound (2*(1+k:ℕ)) ((Fintype.card S.Vertex:ℝ)*(1+k:ℕ)) k (Fintype.card S.Vertex)

lemma shapeCharge_nonneg (k : ℕ) (S : ReducedTopology) : 0 ≤ shapeCharge k S :=
  chargeBound_nonneg (by positivity) (by positivity) _ _

lemma qMass_realize_le {L : ℕ} (hL : 0<L) (k : ℕ) (S : ReducedTopology)
    (q : S.Vertex → Fin L) (hq : S.Admissible (fun v => q v) 0 L) :
    qMass L k (S.realize L 0 (fun v => q v)) ≤ 
      shapeCharge k S * (L:ℝ)⁻¹^(Fintype.card S.Vertex) := by
  let Q : Finset ℕ := Finset.univ.image (fun v => (q v).val)
  have hQ : Q.card ≤ Fintype.card S.Vertex := by
    exact (Finset.card_image_le).trans_eq (Finset.card_univ)
  have hb : branchingCount (S.realize L 0 (fun v => q v)) (·∈Q)=Fintype.card S.Vertex := by
    have h := S.realize_branchingCount L 0 (fun v => q v) (by simpa using hq) (·∈Q)
    have hm (v : S.Vertex) : (q v).val∈Q := Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩
    simpa only [Nat.zero_add,hm,ite_true,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using h
  have hmono : qMass L k (S.realize L 0 (fun v => q v)) ≤ 
      qExpect (grid L 0 L) (fun T => if branchingCount (single L) (·∈Q)+Fintype.card S.Vertex ≤ branchingCount T (·∈Q)
        then 1 else 0) k (single L) := by
    apply qExpect_mono _ (grid_strictMono hL).monotone grid_nonneg
    intro T
    by_cases he : T=S.realize L 0 (fun v => q v)
    · subst T
      simp only [ite_true,branchingCount_single,zero_add,hb,le_refl]
    · rw [ite_eq_right he]
      split_ifs <;> norm_num
  apply (hmono.trans (qExpect_grid_branching hL Q k (Fintype.card S.Vertex) (single L))).trans
  rw [leaves_single]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply chargeBound_mono (by positivity) (by positivity) le_rfl
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hQ) (Nat.cast_nonneg _)

/-- Finite enumeration is an inequality, not a quotient: multiple schedules
representing the same tree can only increase this nonnegative majorant. -/
lemma bounded_terminal_majorant {L K : ℕ} (F : PrescribedTree L → ℝ)
    (hF : ∀ T, 0 ≤ F T) (T : PrescribedTree L) (hT : T.leaves ≤ K) :
    F T ≤ ∑ S∈ReducedTopology.boundedTopologies K,
      ∑ q : S.Vertex → Fin L, if S.Admissible (fun v => q v) 0 L then
        (if T=S.realize L 0 (fun v => q v) then F (S.realize L 0 (fun v => q v)) else 0) else 0 := by
  obtain ⟨S,hS,q,hq,he⟩ := ReducedTopology.exists_bounded_realize T K hT
  have hn (R : ReducedTopology) (v : R.Vertex → Fin L) :
      0 ≤ (if R.Admissible (fun w => v w) 0 L then
        (if T=R.realize L 0 (fun w => v w) then F (R.realize L 0 (fun w => v w)) else 0) else 0) := by
    split_ifs <;> first | exact hF _ | rfl
  apply le_trans _ (Finset.single_le_sum (fun R _ => Finset.sum_nonneg (fun v _ => hn R v)) hS)
  apply le_trans _ (Finset.single_le_sum (fun v _ => hn S v) (Finset.mem_univ q))
  rw [ite_eq_left hq,ite_eq_left he.symm,he]

lemma qExpect_bounded_majorant {L : ℕ} (hL : 0<L) (k : ℕ)
    (F : PrescribedTree L → ℝ) (hF : ∀ T, 0 ≤ F T) :
    qExpect (grid L 0 L) F k (single L) ≤ 
      ∑ S∈ReducedTopology.boundedTopologies (k+1), ∑ q : S.Vertex → Fin L,
        if S.Admissible (fun v => q v) 0 L then
          qMass L k (S.realize L 0 (fun v => q v))*F (S.realize L 0 (fun v => q v)) else 0 := by
  have h0 : grid L 0 L 0=0 := by simp [grid]
  apply le_trans (qExpect_mono_leaves _ (grid_strictMono hL).monotone grid_nonneg F _ k (single L)
    (fun T hT => bounded_terminal_majorant (K := k+1) F hF T (by rw [leaves_single] at hT; omega)))
  rw [qExpect_sum]
  apply Finset.sum_le_sum
  intro S _
  rw [qExpect_sum]
  apply Finset.sum_le_sum
  intro q _
  by_cases hq : S.Admissible (fun v => q v) 0 L
  · simp only [hq,ite_true]
    have he : (fun T => if T=S.realize L 0 (fun v => q v) then F (S.realize L 0 (fun v => q v)) else 0)=
        (fun T => (if T=S.realize L 0 (fun v => q v) then 1 else 0)*F (S.realize L 0 (fun v => q v))) := by
      funext T; split_ifs <;> simp
    rw [he,qExpect_mul_const]
    rfl
  · simp only [hq,ite_false,qExpect_const _ h0 (grid_last hL),le_refl]

end DilutedSpinGlass.PrescribedTree

end

end OAI
