import OAI.Probability.DilutedSpin.EarliestChildDepth
import OAI.Probability.DilutedSpin.MatrixEnergy
import OAI.Probability.DilutedSpin.SingletonSelection

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {L p : ℕ}

/-- The interior grid exponents; the automatically adjoined root exponent is zero. -/
noncomputable def gridExponents (L : ℕ) : Fin (L+1) → ℝ :=
  fun j => (((j:ℕ)+1:ℕ):ℝ)/((L+1:ℕ):ℝ)

lemma gridExponents_cons (L : ℕ) :
    Fin.cons 0 (gridExponents L) = grid (L+1) 0 (L+1) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [grid]
  · simp [grid,gridExponents,Fin.val_succ]

lemma gridExponents_lower (L : ℕ) (j : Fin (L+1)) :
    ((L+1:ℕ):ℝ)⁻¹ ≤ gridExponents L j := by
  change _ ≤ (((j:ℕ)+1:ℕ):ℝ)/((L+1:ℕ):ℝ)
  rw [inv_eq_one_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (Nat.le_add_left 1 j.val)

lemma gridExponents_mono (L : ℕ) : Monotone (gridExponents L) := by
  intro i j hij
  change (((i:ℕ)+1:ℕ):ℝ)/((L+1:ℕ):ℝ) ≤ (((j:ℕ)+1:ℕ):ℝ)/((L+1:ℕ):ℝ)
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hij 1) (Nat.cast_nonneg _)

lemma gridExponents_last (L : ℕ) : gridExponents L (Fin.last L) = 1 := by
  simp only [gridExponents,Fin.val_last]
  exact div_self (ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos L)))

lemma physicalSingletonEnergy_nonneg (m : Fin (L+1) → ℝ) (M : Model p) (C H : ℝ)
    (N : ℕ) (u : Spec L×ℕ → ℝ) (d : ℕ) : 0 ≤ physicalSingletonEnergy m M C H N u d := by
  apply integral_nonneg
  intro z
  exact KernelTower.prefixEnergyAt_nonneg _ _ _ _

/-- The singleton depth domain of the manuscript, with no artificial
normalization by its cardinality. At height L+1 its mass is at most one. -/
noncomputable def regularSingletonDepths (L : ℕ) (η : ℝ) : Finset (Fin (L+1)) :=
  Finset.univ.filter (fun d => η < (d:ℝ)/(L+1:ℕ) ∧ (d:ℝ)/(L+1:ℕ) < 1-η)

 
theorem singleton_grid_selection (M : Model p) {C H : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ| ≤ C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h| ≤ H)
    (hθi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hhi : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ), StrictMono Ns ∧
      (∀ n i, us n i ∈ Icc (probeLow i.2) (probeHigh i.2)) ∧
      (∀ n, ConcreteReservoir.increment (weights L) prior (gridExponents L) direction anchor M (Ns n) (us n) ≤
        liminf (pressure M) atTop+ε) ∧
      (∀ η : ℝ, 0 < η → ∀ t : ℝ, 0 < t → ∀ᶠ n in atTop,
        ∀ d ∈ regularSingletonDepths L η,
          physicalSingletonEnergy (gridExponents L) M C H (Ns n+1) (us n) d ≤
            ((L+1:ℕ):ℝ)⁻¹/η+t) := by
  have hδ : 0 < ((L+1:ℕ):ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos L))
  obtain ⟨Ns,us,hNs,hus,hinc,henergy⟩ := singleton_energy_selection (gridExponents L) M hC hH hδ
    hθ hh hθi hhi (gridExponents_lower L) (gridExponents_mono L) (gridExponents_last L) hε
  refine ⟨Ns,us,hNs,hus,hinc,?_⟩
  intro η hη t ht
  apply (Filter.eventually_all_finset _).mpr
  intro d hd
  have hreg := (Finset.mem_filter.mp hd).2.1
  have hs := henergy d d.isLt (η*t) (mul_pos hη ht)
  filter_upwards [hs] with n hn
  rw [gridExponents_cons] at hn
  have hcoef : η ≤ 2*grid (L+1) 0 (L+1) ⟨d.val+1,by omega⟩-
      grid (L+1) 0 (L+1) ⟨d.val,by omega⟩ := by
    simp only [grid,Nat.zero_add,Nat.cast_add,Nat.cast_one,add_div]
    have hx : 0 ≤ (1:ℝ)/((L+1:ℕ):ℝ) := by simpa only [one_div] using hδ.le
    change η < (d.val:ℝ)/((L+1:ℕ):ℝ) at hreg
    simp only [Nat.cast_add,Nat.cast_one] at hreg hx
    linarith
  have hstep : grid (L+1) 0 (L+1) ⟨d.val+1,by omega⟩-
      grid (L+1) 0 (L+1) ⟨d.val,by omega⟩ = ((L+1:ℕ):ℝ)⁻¹ := by
    simp [grid,Nat.cast_add,add_div]
  rw [hstep] at hn
  have hen := physicalSingletonEnergy_nonneg (gridExponents L) M C H (Ns n+1) (us n) d
  have hh := mul_le_mul_of_nonneg_right hcoef hen
  have hx : η * physicalSingletonEnergy (gridExponents L) M C H (Ns n+1) (us n) d ≤
      ((L+1:ℕ):ℝ)⁻¹+η*t := hh.trans hn
  calc
    _ ≤ (((L+1:ℕ):ℝ)⁻¹+η*t)/η := (le_div_iff₀ hη).mpr (by nlinarith [hx])
    _ = _ := by rw [add_div,mul_div_cancel_left₀ t (ne_of_gt hη)]

end DilutedSpinGlass.UniversalDictionary
end

end

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance fullCubeConditionalPropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω α ι : Type} [Fintype Ω] [Fintype α] [DecidableEq α] [Fintype ι]
  {L N : ℕ} [NeZero L]

/-- A genuine positive one-step shift is the cyclic coordinate permutation
on the regular domain; its wrap-around part is absent, not discarded. -/
theorem averaged_conditional_positive_shift_le (M H p : ℕ) (htotal : M=H+p)
    (hheight : p+H=L) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → α) (he : ∀ j, Function.Injective (e j))
    (η : ℝ) (hlarge : 1<η*(L:ℝ)) (D : (α → Fin L) → Prop)
    (hD : ∀ Q, D Q → ∀ j, Admissible (C j) (fun v => (Q (e j v)).val) p L ∧
      DepthAverage.Regular η (fun v => Q (e j v)))
    (T : KernelTower Ω M) (f : FinitePath Ω M → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    DepthAverage.average D (fun Q => projectorChangeSq T
      (conditionalScheduledProduct M 0 p C (fun j v => (Q (e j v)).val+1) T f)
      (conditionalScheduledProduct M 0 p C (fun j v => (Q (e j v)).val) T f)) ≤
      (Fintype.card ι:ℝ)*∑ j, (Fintype.card (C j).Vertex:ℝ)*
        (∑ v : (C j).Vertex, (vertexArity (C j) v:ℝ)^2)/(L:ℝ) := by
  have hC (Q : α → Fin L) (hQ : D Q) :
      (fun j v => (DepthAverage.shiftPerm true (Q (e j v))).val)=
      (fun j v => (Q (e j v)).val+1) := by
    funext j v
    have hr := DepthAverage.regular_room hlarge (hD Q hQ j).2 v
    simp only [DepthAverage.shiftPerm,ite_true,DepthAverage.rotate_val_of_room _ hr]
  calc
    _ ≤ DepthAverage.average D (fun Q => projectorChangeSq T
        (conditionalScheduledProduct M 0 p C (fun j v => (Q (e j v)).val) T f)
        (conditionalScheduledProduct M 0 p C
          (fun j v => (DepthAverage.shiftPerm true (Q (e j v))).val) T f)) := by
      apply DepthAverage.average_mono_on
      intro Q hQ
      rw [hC Q hQ]
      exact (projectorChangeSq_symm T _ _).le
    _ ≤ _ := averaged_conditional_schedule_change_le M H p htotal hheight C e he
      (fun _ _ => Equiv.refl _) η hlarge (fun _ _ => true) D hD T f hf

/-- Simultaneous proper-child shift at the ACTUAL next evaluation depth,
on the full parent cube. Its spacetime marginal is a single-copy one. -/
theorem averaged_fullCube_schedule_le (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a}) (he : ∀ j, Function.Injective (e j))
    (η : ℝ) (hlarge : 1<η*(L:ℝ)) (D : (α → Fin L) → Prop)
    (hD : ∀ Q, D Q → ∀ j, Admissible (C j) (fun v => (Q (e j v)).val) ((Q a).val+1) L ∧
      DepthAverage.Regular η (fun v => Q (e j v)))
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    DepthAverage.average D (fun Q => projectorChangeSq T
      (conditionalScheduledProduct L 0 ((Q a).val+1) C (fun j v => (Q (e j v)).val+1) T f)
      (conditionalScheduledProduct L 0 ((Q a).val+1) C (fun j v => (Q (e j v)).val) T f)) ≤
      (Fintype.card ι:ℝ)*∑ j, (Fintype.card (C j).Vertex:ℝ)*
        (∑ v : (C j).Vertex, (vertexArity (C j) v:ℝ)^2)/(L:ℝ) := by
  apply DepthAverage.average_of_slice_le a
  intro t
  simp only [DepthAverage.insertCoordinate_self,DepthAverage.insertCoordinate_other]
  apply averaged_conditional_positive_shift_le L (L-(t.val+1)) (t.val+1)
    (by have := t.isLt; omega) (by have := t.isLt; omega) C e he η hlarge
    (fun rest => D (DepthAverage.insertCoordinate a t rest))
  intro rest hrest j
  simpa only [DepthAverage.insertCoordinate_self,DepthAverage.insertCoordinate_other] using
    hD (DepthAverage.insertCoordinate a t rest) hrest j
  exact hf

/-- Change the common evaluation depth back by one in the same physical
path, while EVERY proper-child branching coordinate is fixed. The terminal
case of leaf children uses a full unary stretch of length L. -/
theorem averaged_fullCube_evaluation_le (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (D : (α → Fin L) → Prop)
    (hD : ∀ Q, D Q → ∀ j v, (Q a).val<(Q (e j v)).val)
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    DepthAverage.average D (fun Q => projectorChangeSq T
      (conditionalScheduledProduct L 0 ((Q a).val+1) C (fun j v => (Q (e j v)).val) T f)
      (conditionalScheduledProduct L 0 (Q a).val C (fun j v => (Q (e j v)).val) T f)) ≤
      (Fintype.card ι:ℝ)^2/(L:ℝ) := by
  rw [DepthAverage.average_split_comm a]
  apply le_trans (FiniteLaw.expect_mono _ (fun rest => ?_)) (FiniteLaw.expect_const _ _).le
  simp only [DepthAverage.insertCoordinate_self,DepthAverage.insertCoordinate_other]
  let q := fun j v => rest (e j v)
  let r := earliestChildDepth C q
  have hr : r≤L := earliestChildDepth_le_horizon C q
  let F := fun t : ℕ => projectorChangeSq T
    (conditionalScheduledProduct L 0 (t+1) C (fun j v => (q j v).val) T f)
    (conditionalScheduledProduct L 0 t C (fun j v => (q j v).val) T f)
  change (FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun t =>
    if D (DepthAverage.insertCoordinate a t rest) then F t.val else 0)≤_
  calc
    _ ≤ (FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun t => if h : t.val<r then F t.val else 0) := by
      apply FiniteLaw.expect_mono
      intro t
      by_cases ht : D (DepthAverage.insertCoordinate a t rest)
      · have htr : t.val<r := lt_earliestChildDepth C q t (by
          intro j v
          simpa only [DepthAverage.insertCoordinate_self,DepthAverage.insertCoordinate_other] using
            hD (DepthAverage.insertCoordinate a t rest) ht j v)
        simp only [ht,ite_true,htr,dite_eq_left]
        exact le_rfl
      · simp only [ht,ite_false]
        split_ifs
        · exact projectorChangeSq_nonneg T _ _
        · exact le_rfl
    _ = (∑ t : Fin r, F t.val)/(L:ℝ) := DepthAverage.uniform_zeroExtension hr (fun t => F t.val)
    _ ≤ _ := by
      simpa only [F] using conditional_evaluation_sum_le L (L-r) r (by omega) C
        (fun j v => (q j v).val) (earliestChildDepth_le C q) Finset.univ T f hf

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
