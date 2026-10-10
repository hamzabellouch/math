import OAI.Probability.DilutedSpin.AdmissibleInterval
import OAI.Probability.DilutedSpin.MatrixLeafProjection

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

lemma depthLaw_split (v : α) (F : (α → Fin L) → ℝ) :
    (depthLaw α L).expect F =
      (depthLaw {w : α // w ≠ v} L).expect (fun rest =>
        (FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun t =>
          F ((Equiv.piSplitAt v (fun _ : α => Fin L)).symm (t,rest)))) := by
  unfold depthLaw
  rw [FiniteLaw.expect_pi_split _ v]
  simp only [FiniteLaw.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rest _
  apply Finset.sum_congr rfl
  intro t _
  ring

 
theorem coordinate_fiber_bound (v : α) (F : (α → Fin L) → ℝ) (B : ℝ)
    (hF : ∀ rest : {w : α // w ≠ v} → Fin L,
      (∑ t : Fin L, F ((Equiv.piSplitAt v (fun _ : α => Fin L)).symm (t,rest))) ≤ B) :
    (depthLaw α L).expect F ≤ B/(L:ℝ) := by
  rw [depthLaw_split v F]
  calc
    _ ≤ (depthLaw {w : α // w ≠ v} L).expect (fun _ => B/(L:ℝ)) := by
      apply FiniteLaw.expect_mono
      intro rest
      unfold FiniteLaw.expect FiniteLaw.uniform
      simp only [Fintype.card_fin,← Finset.mul_sum]
      rw [mul_comm,← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (hF rest) (Nat.cast_nonneg _)
    _ = _ := FiniteLaw.expect_const _ _

end DilutedSpinGlass.DepthAverage

namespace DilutedSpinGlass

@[simp] lemma updateCoordinate_update {α : Type} (q : α → ℕ) (v : α) (a b : ℕ) :
    updateCoordinate (updateCoordinate q v a) v b = updateCoordinate q v b := by
  classical
  funext w
  by_cases h : w=v
  · subst w; simp
  · simp only [updateCoordinate_of_ne h]

namespace DepthAverage
open scoped BigOperators
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

omit [Fintype α] in
lemma splitAt_values_update (v : α) (rest : {w : α // w ≠ v} → Fin L) (t : Fin L) :
    (fun w => ((Equiv.piSplitAt v (fun _ : α => Fin L)).symm (t,rest) w).val) =
      updateCoordinate
        (fun w => ((Equiv.piSplitAt v (fun _ : α => Fin L)).symm (0,rest) w).val) v t.val := by
  classical
  funext w
  by_cases h : w=v
  · subst w
    simp only [Equiv.piSplitAt_symm_apply,dite_true,updateCoordinate_self]
  · simp only [Equiv.piSplitAt_symm_apply,dite_eq_right h,updateCoordinate_of_ne h]

end DepthAverage
namespace ReducedTopology
open scoped BigOperators
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {Ω : Type} [Fintype Ω] {L : ℕ} [NeZero L]

/-- Actual change in the conditional tree mean when one assigned vertex
moves by one grid step. All remaining topology coordinates are unchanged. -/
noncomputable def vertexChangeSq (H d : ℕ) (S : ReducedTopology) (v : S.Vertex)
    (T : KernelTower Ω H) (f : FinitePath Ω H → ℝ) (q : S.Vertex → Fin L) : ℝ :=
  (PrescribedTree.treeMean (realize H d S (fun w => (q w).val)) T f-
   PrescribedTree.treeMean (realize H d S
    (updateCoordinate (fun w => (q w).val) v ((q v).val+1))) T f)^2

omit [NeZero L] in
lemma vertexChangeSq_nonneg (H d : ℕ) (S : ReducedTopology) (v : S.Vertex)
    (T : KernelTower Ω H) (f : FinitePath Ω H → ℝ) (q : S.Vertex → Fin L) :
    0 ≤ vertexChangeSq H d S v T f q := sq_nonneg _

 
theorem averaged_vertexChangeSq_le (H d : ℕ) (S : ReducedTopology) (v : S.Vertex)
    (D : (S.Vertex → Fin L) → Prop)
    (hD : ∀ q, D q → Admissible S (fun w => (q w).val) d (d+H) ∧
      Admissible S (updateCoordinate (fun w => (q w).val) v ((q v).val+1)) d (d+H))
    (T : KernelTower Ω H) (f : FinitePath Ω H → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    DepthAverage.average D (vertexChangeSq H d S v T f) ≤ (vertexArity S v:ℝ)^2/(L:ℝ) := by
  classical
  apply DepthAverage.coordinate_fiber_bound v
  intro rest
  let split (t : Fin L) : S.Vertex → Fin L :=
    (Equiv.piSplitAt v (fun _ : S.Vertex => Fin L)).symm (t,rest)
  let q0 : S.Vertex → ℕ := fun w => (split 0 w).val
  let E : ℕ → ℝ := fun t =>
    (PrescribedTree.treeMean (realize H d S (updateCoordinate q0 v t)) T f-
     PrescribedTree.treeMean (realize H d S (updateCoordinate q0 v (t+1))) T f)^2
  have hv (t : Fin L) : (split t v).val=t.val := by
    simp only [split,Equiv.piSplitAt_symm_apply,dite_true]
  have he (t : Fin L) : vertexChangeSq H d S v T f (split t)=E t.val := by
    unfold vertexChangeSq
    rw [DepthAverage.splitAt_values_update,updateCoordinate_update]
    rw [hv]
  let U : Finset (Fin L) := Finset.univ.filter (fun t => D (split t))
  let I : Finset ℕ := U.image Fin.val
  have hadm : ∀ t ∈ I, Admissible S (updateCoordinate q0 v t) d (d+H) ∧
      Admissible S (updateCoordinate q0 v (t+1)) d (d+H) := by
    intro t ht
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
    have hh := hD (split a) (Finset.mem_filter.mp ha).2
    rw [DepthAverage.splitAt_values_update,updateCoordinate_update,hv] at hh
    exact hh
  have hE := scheduled_vertex_subset_energy_le H d S q0 v I hadm T f hf
  change (∑ t : Fin L, if D (split t) then vertexChangeSq H d S v T f (split t) else 0) ≤ _
  simp_rw [he]
  rw [← Finset.sum_filter]
  have hs : (∑ t ∈ U, E t.val) = ∑ t ∈ I, E t := by
    symm
    exact Finset.sum_image (fun a _ b _ h => Fin.ext h)
  change (∑ t ∈ U, E t.val) ≤ _
  rw [hs]
  exact hE

end ReducedTopology
end DilutedSpinGlass
end

end

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {N : ℕ}

/-- Squared normalized spatial norm, with the original zero-size convention. -/
noncomputable def spatialSq (x : Fin N → ℝ) : ℝ := (∑ i, (x i)^2)/(N:ℝ)

lemma spatialSq_nonneg (x : Fin N → ℝ) : 0 ≤ spatialSq x :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)

lemma spatial_mean_sq_le (x : Fin N → ℝ) : ((∑ i, x i)/(N:ℝ))^2 ≤ spatialSq x := by
  by_cases hN : N=0
  · subst N
    simp [spatialSq]
  · have hn : 0<(N:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    have h := @sq_sum_le_card_mul_sum_sq (Fin N) ℝ _ _ _ _ Finset.univ x
    simp only [Finset.card_univ,Fintype.card_fin] at h
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
    calc
      _ ≤ (N:ℝ)*∑ i, (x i)^2 := h
      _ = spatialSq x*(N:ℝ)^2 := by
        unfold spatialSq
        field_simp

/-- The simultaneous change of both vectors in a contraction is controlled
by the two actual coupled spatial norms, regardless of correlation. -/
theorem dot_pair_change_sq (x y u v : Fin N → ℝ)
    (hx : ∀ i, |x i|≤1) (hy : ∀ i, |y i|≤1)
    (hu : ∀ i, |u i|≤1) (hv : ∀ i, |v i|≤1) :
    (dot x y-dot u v)^2 ≤ 2*spatialSq (fun i => x i-u i)+2*spatialSq (fun i => y i-v i) := by
  have hpt (i : Fin N) : (x i*y i-u i*v i)^2 ≤ 2*((x i-u i)^2+(y i-v i)^2) := by
    have h := bounded_product_difference_sq
      (fun j : Fin 2 => if j=0 then x i else y i)
      (fun j : Fin 2 => if j=0 then u i else v i)
      (fun j => by split_ifs <;> [exact hx i;exact hy i])
      (fun j => by split_ifs <;> [exact hu i;exact hv i])
    simpa only [Fintype.card_fin,Fin.prod_univ_two,Fin.sum_univ_two,ite_true,
      show ¬(1:Fin 2)=0 by decide,ite_false,Nat.cast_ofNat] using h
  have h := spatial_mean_sq_le (fun i => x i*y i-u i*v i)
  change ((∑ i, (x i*y i-u i*v i))/(N:ℝ))^2 ≤ _ at h
  change ((∑ i, x i*y i)/(N:ℝ)-(∑ i, u i*v i)/(N:ℝ))^2 ≤ _
  rw [← sub_div,← Finset.sum_sub_distrib]
  apply h.trans
  unfold spatialSq
  calc
    _ ≤ (∑ i, 2*((x i-u i)^2+(y i-v i)^2))/(N:ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => hpt i)) (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_add_distrib]; ring

end DilutedSpinGlass.FiniteLaw
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I] {n N : ℕ}

/-- A target contraction change costs only the single-path marginal spatial
change. This is uniform over the entire target shape and does NOT assume
regularity of a union with any old tree. -/
theorem coupled_projection_change_l2 (S : PrescribedTree n) (T : KernelTower Ω n)
    (a b : S.Leaf) (X Y : FinitePath Ω n → Fin N → ℝ)
    (hX : ∀ x i, |X x i|≤1) (hY : ∀ x i, |Y x i|≤1) :
    (S.sampleLaw T).l2 (fun z => FiniteLaw.dot (X (S.pathAt a z)) (X (S.pathAt b z))-
      FiniteLaw.dot (Y (S.pathAt a z)) (Y (S.pathAt b z))) ≤
      2*Real.sqrt ((KernelTower.law n T).expect (fun x => FiniteLaw.spatialSq (fun i => X x i-Y x i))) := by
  let E := (KernelTower.law n T).expect (fun x => FiniteLaw.spatialSq (fun i => X x i-Y x i))
  have hn : 0≤E := FiniteLaw.expect_nonneg _ (fun x => FiniteLaw.spatialSq_nonneg _)
  have h := (S.sampleLaw T).expect_mono (fun z => FiniteLaw.dot_pair_change_sq
    (X (S.pathAt a z)) (X (S.pathAt b z)) (Y (S.pathAt a z)) (Y (S.pathAt b z))
    (hX _) (hX _) (hY _) (hY _))
  rw [FiniteLaw.expect_add,FiniteLaw.expect_mul_left,FiniteLaw.expect_mul_left,
    leaf_marginal S T a (fun x => FiniteLaw.spatialSq (fun i => X x i-Y x i)),
    leaf_marginal S T b (fun x => FiniteLaw.spatialSq (fun i => X x i-Y x i))] at h
  unfold FiniteLaw.l2
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · rw [mul_pow,Real.sq_sqrt hn]
    change _ ≤ 2*E+2*E at h
    nlinarith [h]

omit [Fintype I] [DecidableEq I] in
/-- The full target matrix error splits into its genuine proper-child
projection and a shape-independent single-path coupled comparison. -/
theorem matrixProjectionError_change_spatial (S : PrescribedTree n) (q : I → S.Leaf)
    (T : KernelTower Ω n) (a c : I) (A : (I → FinitePath Ω n) → ℝ)
    (X Y : FinitePath Ω n → Fin N → ℝ)
    (hX : ∀ x i, |X x i|≤1) (hY : ∀ x i, |Y x i|≤1) :
    matrixProjectionError S q T a c A X ≤ matrixProjectionError S q T a c A Y +
      2*Real.sqrt ((KernelTower.law n T).expect (fun x => FiniteLaw.spatialSq (fun i => Y x i-X x i))) :=
  by
  have h := matrixProjectionError_change S q T a c A X Y
  have h2 := coupled_projection_change_l2 S T (q a) (q c) Y X hY hX
  linarith

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
