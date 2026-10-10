import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.FiniteContinuation
import OAI.Combinatorics.ThinTrees.Continuation.Pencil

namespace OAI

/-! Continuation pencil correctness. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Orientations RationalForms
open scoped BigOperators
variable {n m : ℕ}

@[simp] lemma step_y (v : Fin (dimension n m) → ℝ) (e : Fin m) :
    (step v).y e = v (edgeIndex 0 e) := rfl
@[simp] lemma step_z (v : Fin (dimension n m) → ℝ) (e : Fin m) :
    (step v).z e = v (edgeIndex 1 e) := rfl
@[simp] lemma step_mul (v : Fin (dimension n m) → ℝ) (ijk : DistinctTriple n) :
    (step v).multiplier ijk = v (mulIndex ijk.val) := rfl
@[simp] lemma flow_x (v : Fin (dimension n m) → ℝ) (e : Fin m) :
    (flow v).x e = v (edgeIndex 2 e) := rfl
@[simp] lemma flow_a (v : Fin (dimension n m) → ℝ) (r : Fin n) (e : Fin m) :
    (flow v).a r e = v (flowIndex 0 r e) := rfl
@[simp] lemma flow_b (v : Fin (dimension n m) → ℝ) (r : Fin n) (e : Fin m) :
    (flow v).b r e = v (flowIndex 1 r e) := rfl

lemma real_capacityForm (κ : ℚ) (u : Fin m → ℚ) (e : Fin m) (v : Fin (dimension n m) → ℝ) :
    Affine.real v (capacityForm κ u e) = (step v).capacities (κ:ℝ) (fun e => (u e:ℝ)) e := by
  simp only [capacityForm,StepFree.capacities,step,StepFree.z,z]
  have h : (0:ℝ)<(u e:ℝ) ↔ (0:ℚ)<u e := by exact_mod_cast Iff.rfl
  simp only [h]
  split_ifs <;> simp

lemma matrixBlocks_psd (H : MultiGraph n m) (s : ℚ) (u : Fin m → ℚ)
    (v : Fin (dimension n m) → ℝ) :
    (∀b, ((matrixBlocks H s u b).map (Affine.real v)).PosSemidef) ↔
      ((step v).lowerPencil H).PosSemidef ∧ ((step v).upperPencil H).PosSemidef ∧
        ∀e, (0:ℝ)<(u e:ℝ) → ((step v).edgePencil H (s:ℝ) e).PosSemidef := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · simpa only [matrixBlocks,ite_true,real_lowerForm] using h (.inl 0)
    · simpa only [matrixBlocks,show (1 : Fin 2)≠0 from by decide,ite_false,real_upperForm] using h (.inl 1)
    · intro e he
      have he' : 0<u e := by exact_mod_cast he
      simpa only [matrixBlocks,ite_eq_left he',real_edgeForm] using h (.inr e)
  · rintro ⟨hl,hu,he⟩ b
    cases b with
    | inl p => simp only [matrixBlocks]; split_ifs <;> first | simpa only [real_lowerForm] using hl | simpa only [real_upperForm] using hu
    | inr e =>
      simp only [matrixBlocks]
      split_ifs with h
      · simpa only [real_edgeForm] using he e (by exact_mod_cast h)
      · simpa using (show (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef from PosSemidef.zero)

lemma scalarForms_nonneg (H : MultiGraph n m) (κ t qbar ε : ℚ) (u : Fin m → ℚ)
    (v : Fin (dimension n m) → ℝ) :
    (∀b, 0 ≤ Affine.real v (scalarForms H κ t qbar ε u b)) ↔
      (∀ijk, 0 ≤ (step v).multiplier ijk) ∧
      (∀e, (step v).y e ∈ Set.Icc (0:ℝ) 1) ∧
      (∀e, (step v).z e ∈ Set.Icc 0 ((κ:ℝ)+1)) ∧
      (∀e, (0:ℝ)<(u e:ℝ) → (step v).z e ≤ (κ:ℝ)+(u e:ℝ)+(t:ℝ)*(5*(step v).y e-4)) ∧
      (flow v).Feasible H ((step v).capacities (κ:ℝ) (fun e => (u e:ℝ))) (qbar:ℝ) (ε:ℝ) := by
  have cast_pos (e : Fin m) : (0:ℝ)<(u e:ℝ) ↔ (0:ℚ)<u e := by exact_mod_cast Iff.rfl
  constructor
  · intro h
    refine ⟨?_,?_,?_,?_,⟨?_,?_,?_,?_⟩⟩
    · intro ijk
      simpa only [scalarForms,ite_eq_left ijk.property,Affine.real_coord,step,StepFree.multiplier,multiplier]
        using h (.inl ijk.val)
    · intro e
      have h0 := h (.inr (.inl (0,e)))
      have h1 := h (.inr (.inl (1,e)))
      simp only [scalarForms,Matrix.cons_val_zero,Matrix.cons_val_one,Affine.real_coord,
        Affine.real_sub,Affine.real_cst,Rat.cast_one] at h0 h1
      exact ⟨h0, sub_nonneg.mp h1⟩
    · intro e
      have h2 := h (.inr (.inl (2,e)))
      have h3 := h (.inr (.inl (3,e)))
      simp [scalarForms] at h2 h3
      exact ⟨h2, h3⟩
    · intro e he
      have h4 := h (.inr (.inl (4,e)))
      simp [scalarForms,(cast_pos e).mp he] at h4
      change (step v).z e ≤ (κ:ℝ)+(u e:ℝ)+(t:ℝ)*(5*(step v).y e-4)
      change 0 ≤ (κ:ℝ)+(u e:ℝ)-(step v).z e+(t:ℝ)*(5*(step v).y e-4) at h4
      linarith only [h4]
    · intro e
      have h5 := h (.inr (.inl (5,e)))
      have h6 := h (.inr (.inl (6,e)))
      simp [scalarForms,real_capacityForm] at h5 h6
      exact ⟨h5,h6⟩
    · intro r e
      have h0 := h (.inr (.inr (.inl (0,(r,e)))))
      have h1 := h (.inr (.inr (.inl (1,(r,e)))))
      have h2 := h (.inr (.inr (.inl (2,(r,e)))))
      simp [scalarForms] at h0 h1 h2
      exact ⟨h0,h1,h2⟩
    · intro r w
      have hr := h (.inr (.inr (.inr (.inl (r,w)))))
      simp only [scalarForms,Affine.real_sub,Affine.real_cst,Affine.real_sum,Affine.real_add] at hr
      have hi (a b : Form n m) (p : Prop) [Decidable p] :
          Affine.real v (if p then a else b) = if p then Affine.real v a else Affine.real v b := by split_ifs <;> rfl
      simp only [hi,Affine.real_coord,Affine.real_zero] at hr
      have hh : ((if w=r then ε else qbar : ℚ):ℝ) = if w=r then (ε:ℝ) else (qbar:ℝ) := by split_ifs <;> rfl
      rw [hh] at hr
      exact sub_nonneg.mp hr
    · have hh := h (.inr (.inr (.inr (.inr 0))))
      simp only [scalarForms,Affine.real_sub,Affine.real_sum,Affine.real_coord,Affine.real_cst,
        Rat.cast_sub,Rat.cast_mul,Rat.cast_natCast,Rat.cast_one] at hh
      exact sub_nonneg.mp hh
  · rintro ⟨hm,hy,hz,hactive,hF⟩ b
    cases b with
    | inl ijk =>
      simp only [scalarForms]
      split_ifs with h
      · simpa only [Affine.real_coord,step_mul] using hm ⟨ijk,h⟩
      · simp
    | inr b =>
      cases b with
      | inl pe =>
        rcases pe with ⟨p,e⟩
        fin_cases p
        · simpa [scalarForms] using (hy e).1
        · simpa [scalarForms] using sub_nonneg.mpr (hy e).2
        · simpa [scalarForms] using (hz e).1
        · simpa [scalarForms] using sub_nonneg.mpr (hz e).2
        · change 0 ≤ Affine.real v (if 0<u e then Affine.cst (κ+u e)-Affine.coord (edgeIndex 1 e)+
            t • ((5:ℚ) • Affine.coord (edgeIndex 0 e)-Affine.cst 4) else 0)
          split_ifs with he
          · simp only [Affine.real_add,Affine.real_sub,Affine.real_cst,Affine.real_smul,
              Affine.real_coord,Rat.cast_add,Rat.cast_ofNat]
            have hh := hactive e ((cast_pos e).mpr he)
            change (step v).z e ≤ (κ:ℝ)+(u e:ℝ)+(t:ℝ)*(5*(step v).y e-4) at hh
            change 0 ≤ (κ:ℝ)+(u e:ℝ)-(step v).z e+(t:ℝ)*(5*(step v).y e-4)
            linarith only [hh]
          · simp
        · simpa [scalarForms] using (hF.1 e).1
        · simpa [scalarForms,real_capacityForm] using (hF.1 e).2
      | inr b =>
        cases b with
        | inl pre =>
          rcases pre with ⟨p,r,e⟩
          fin_cases p
          · simpa [scalarForms] using (hF.2.1 r e).1
          · simpa [scalarForms] using (hF.2.1 r e).2.1
          · simpa [scalarForms] using sub_nonneg.mpr (hF.2.1 r e).2.2
        | inr b =>
          cases b with
          | inl rv =>
            rcases rv with ⟨r,w⟩
            have hr := sub_nonneg.mpr (hF.2.2.1 r w)
            simp only [scalarForms,Affine.real_sub,Affine.real_sum,Affine.real_add]
            have hi (a b : Form n m) (p : Prop) [Decidable p] :
                Affine.real v (if p then a else b) = if p then Affine.real v a else Affine.real v b := by split_ifs <;> rfl
            simp only [hi,Affine.real_coord,Affine.real_zero,Affine.real_cst]
            have hh : ((if w=r then ε else qbar : ℚ):ℝ) = if w=r then (ε:ℝ) else (qbar:ℝ) := by split_ifs <;> rfl
            rw [hh]
            exact hr
          | inr p =>
            simpa only [scalarForms,Affine.real_sub,Affine.real_sum,Affine.real_coord,flow_x,
              Affine.real_cst,Rat.cast_sub,Rat.cast_mul,Rat.cast_natCast,Rat.cast_one]
              using sub_nonneg.mpr hF.2.2.2

lemma continuationPencil_psd (H : MultiGraph n m) (s κ t qbar ε : ℚ) (u : Fin m → ℚ)
    (v : Fin (dimension n m) → ℝ) :
    ((continuationPencil H s κ t qbar ε u).realEval v).PosSemidef ↔
      finiteStep H (s:ℝ) (κ:ℝ) (t:ℝ) (qbar:ℝ) (ε:ℝ) (fun e => (u e:ℝ)) (step v) (flow v) := by
  rw [continuationPencil,pencil_realEval]
  simp only [affineMatrix,←Matrix.submatrix_map,submatrix_equiv_psd,RationalForms.fromBlocks_map,
    RationalForms.blockDiagonal_map,RationalForms.diagonal_map,fromBlocks_psd,blockDiagonal_psd,Matrix.posSemidef_diagonal_iff]
  rw [matrixBlocks_psd,scalarForms_nonneg]
  simp only [finiteStep,stepCore,Set.mem_ofPred_eq,forall_and]
  tauto

lemma order_bound (n m : ℕ) : order n m ≤ (n+m+2)^3 := by
  unfold order
  nlinarith [Nat.zero_le (n*n*m),Nat.zero_le (n*m*m),Nat.zero_le (m*m*m)]

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
