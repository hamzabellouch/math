import OAI.Analysis.InterpolatedFactors.Fresh

namespace OAI

noncomputable section

universe u_1 u_2

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock
variable {ι : Type u_1} [DecidableEq ι]

theorem annihilation_commute_diagonalInsert (n j : ι) (hnj : n≠j) (r : Bool) (w : Path ι) :
    Commute (star (creation n r)) (diagonalInsert j w) := by
  have hA : Commute (star (creation n r)) (rightInsert j w) := by
    have hh := annihilation_rightInsert n j r w
    exact (show Commute _ _ from by
      change _ * _ = _ * _
      simpa only [hnj,ite_false,add_zero] using hh)
  have ht := (terminalVertex_commute_creation (start w) n r).star_star
  simp only [terminalVertex_star] at ht
  exact hA.mul_right ht.symm

theorem Cstar_commute_diagonalInsert (u v : ℝ) (n j : ι) (hnj : n≠j) (w : Path ι) :
    Commute (star (C u v n)) (diagonalInsert j w) := by
  have hh := ((annihilation_commute_diagonalInsert n j hnj true w).smul_left (u:ℂ)).add_left
    ((annihilation_commute_diagonalInsert n j hnj false w).smul_left (v:ℂ))
  simpa only [C,star_add (R := Operator ι),star_smul,Complex.star_def,Complex.conj_ofReal] using hh

theorem fresh_C_edge_root (u v : ℝ) (i n : ι) (hni : n≠i) (T : edgeAlgebra u v i) (s : Bool) :
    star (C u v n) ((T : Operator ι) (lp.single 2 ([],s) 1))=0 := by
  let a : oldAlgebra u v {i} := ⟨T,edgeAlgebra_le_old u v {i} i (Set.mem_singleton i) T.property⟩
  have hh (r) : star (creation n r) ((T : Operator ι) (lp.single 2 ([],s) 1))=0 :=
    annihilation_old_root u v {i} n hni a r s
  simp only [C,star_add (R := Operator ι),star_smul,Complex.star_def,Complex.conj_ofReal,add_apply,_root_.smul_apply,
    hh,smul_zero,add_zero]

theorem fresh_C_diagonal_edge (u v : ℝ) (i n j : ι) (hni : n≠i) (hnj : n≠j)
    (T : edgeAlgebra u v i) (r : Bool) :
    star (C u v n)*(T : Operator ι)*edgeCreation j r r=0 := by
  apply operator_basis_ext
  intro w
  by_cases hs : start w=r
  · have hc := ((StarSubalgebra.mem_centralizer_iff ℂ).mp T.property _
      (diagonalInsert_mem_edgeCommutant u v i j w)).1
    have ht := DFunLike.congr_fun hc (lp.single 2 ([],r) 1)
    simp only [mul_apply_eq_comp,diagonalInsert_nil,hs,ite_true] at ht
    have ha := DFunLike.congr_fun (Cstar_commute_diagonalInsert u v n j hnj w).eq
      ((T : Operator ι) (lp.single 2 ([],r) 1))
    simp only [mul_apply_eq_comp,fresh_C_edge_root u v i n hni T,map_zero] at ha
    simpa only [mul_apply_eq_comp,edgeCreation_single,hs,ite_true,ht,zero_apply] using ha
  · simp only [mul_apply_eq_comp,edgeCreation_single,hs,ite_false,map_zero,zero_apply]

theorem diagonal_weightedDefect (u v : ℝ) (i j k : ι) (hji : j≠i) (hjk : j≠k)
    (T : edgeAlgebra u v i) (r : Bool) :
    star (edgeCreation k r r)*(T : Operator ι)*weightedDefectCreation u v i j=0 := by
  let a : edgeAlgebra u v i := T*⟨edgeDefect u v i,edgeDefect_mem_edge u v i⟩
  have hh := congrArg star (fresh_C_diagonal_edge u v i j k hji hjk (star a) r)
  simp only [star_mul,star_star,star_zero (Operator ι),StarMemClass.coe_star] at hh
  change star (edgeCreation k r r)*((T : Operator ι)*edgeDefect u v i)*C u v j=0 at hh
  calc
    _ = (star (edgeCreation k r r)*((T : Operator ι)*edgeDefect u v i)*C u v j)*edgeDefect u v i := by
      simp only [weightedDefectCreation,mul_assoc]
    _ = 0 := by rw [hh,zero_mul]

theorem weightedDefect_edge_root (u v : ℝ) (i j : ι) (hji : j≠i)
    (T : edgeAlgebra u v i) (r : Bool) :
    star (weightedDefectCreation u v i j) ((T : Operator ι) (lp.single 2 ([],r) 1))=0 := by
  let a : edgeAlgebra u v i := ⟨edgeDefect u v i,edgeDefect_mem_edge u v i⟩*T
  have hh := fresh_C_edge_root u v i j hji a r
  simp only [weightedDefectCreation,star_mul,(edgeDefect_projection u v i).isSelfAdjoint.star_eq,
    mul_apply_eq_comp]
  change star (C u v j) (edgeDefect u v i ((T : Operator ι) (lp.single 2 ([],r) 1)))=0 at hh
  rw [hh,map_zero]

theorem diagonal_filled_contraction (u v : ℝ) (i j k l : ι) (hji : j≠i) (hjk : j≠k) (hjl : j≠l)
    (r s : Bool) (T : filledEdgeAlgebra u v i j) :
    star (edgeCreation k r r)*(T : Operator ι)*edgeCreation l s s=
      (inner ℂ (lp.single 2 ([],r) 1) ((T : Operator ι) (lp.single 2 ([],s) 1))) •
        (if k=l ∧ r=s then vertex s else 0) := by
  apply GaussianExtension.covariance_extension (edgeAlgebra u v i) (weightedDefectCreation u v i j)
    (defectCovariance u v i) (weightedDefect_contraction u v i j hji)
    (edgeCreation k r r) (edgeCreation l s s) _ (lp.single 2 ([],r) 1) (lp.single 2 ([],s) 1)
    (fun a => weightedDefect_edge_root u v i j hji a r)
    (fun a => weightedDefect_edge_root u v i j hji a s)
    (fun a => diagonal_weightedDefect u v i j k hji hjk a r) _ _ (T : Operator ι) T.property
  · intro a
    have hh := congrArg star (diagonal_weightedDefect u v i j l hji hjl (star a) s)
    simpa only [star_mul,star_star,star_zero (Operator ι),StarMemClass.coe_star,mul_assoc] using hh
  · intro a
    have hh := diagonal_edge_contraction u v i k l a r s
    split_ifs with h
    · simpa [h,lp.inner_single_left] using hh
    · simpa only [h,ite_false,smul_zero] using hh

theorem diagonal_filled_annihilation (u v : ℝ) (i j k : ι) (hji : j≠i) (hjk : j≠k)
    (r : Bool) (T : filledEdgeAlgebra u v i j) :
    star (edgeCreation k r r) ((T : Operator ι) (vacuum u v))=0 := by
  apply GaussianExtension.annihilation_extension (edgeAlgebra u v i) (weightedDefectCreation u v i j)
    (defectCovariance u v i) (weightedDefect_contraction u v i j hji)
    (edgeCreation k r r) (vacuum u v) (weightedDefect_annihilates_edge u v i j hji) _
    (fun a => diagonal_weightedDefect u v i j k hji hjk a r) T T.property
  intro a
  simp only [vacuum,map_add,map_smul,diagonal_annihilation_edge_root u v i k a,
    smul_zero,add_zero]
end

open FreeFock
variable {ι : Type u_2} [DecidableEq ι]

theorem vertex_trace_inner (u v : ℝ) (r : Bool) (T : Operator ι) :
    vacuumTrace u v (vertex r*T*vertex r)=
      (weight u v r : ℂ)^2*inner ℂ (lp.single 2 ([],r) 1) (T (lp.single 2 ([],r) 1)) := by
  unfold vacuumTrace
  simp only [mul_apply_eq_comp]
  rw [← ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (star (vertex r) (vacuum u v)) (T (vertex r (vacuum u v)))=_
  rw [vertex_star,vertex_vacuum]
  simp only [map_smul,inner_smul_left,inner_smul_right,Complex.conj_ofReal,pow_two,mul_assoc]

theorem supportedLeg_vertex (u v : ℝ) (i : ι) (r : Bool) :
    supportedLeg u v i r*vertex (!r)=supportedLeg u v i r := by
  cases r
  · exact projection_P.isIdempotentElem.eq
  · exact edgePolar_right u v i

theorem vertex_star_supportedLeg (u v : ℝ) (i : ι) (r : Bool) :
    vertex (!r)*star (supportedLeg u v i r)=star (supportedLeg u v i r) := by
  simpa only [star_mul,vertex_star] using congrArg star (supportedLeg_vertex u v i r)

theorem supportedLeg_root_trace (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i : ι) (r : Bool) (T : ambientAlgebra (ι := ι) u v) :
    (weight u v (!r) : ℂ)^2*inner ℂ (lp.single 2 ([],!r) 1)
        ((star (supportedLeg u v i r)*(T : Operator ι)*supportedLeg u v i r) (lp.single 2 ([],!r) 1))=
      vacuumTrace u v ((T : Operator ι)*legSupport u v i r) := by
  rw [← vertex_trace_inner]
  rw [← mul_assoc,← mul_assoc,vertex_star_supportedLeg,mul_assoc _ _ (vertex (!r)),supportedLeg_vertex]
  simpa only [ite_true] using supportedLeg_trace_covariance u v hu hv i r r T

def transportedDiagonal (u v : ℝ) (i k : ι) (r : Bool) : Operator ι :=
  supportedLeg u v i r*edgeCreation k (!r) (!r)*star (supportedLeg u v i r)

def normalizedDiagonal (u v : ℝ) (i k : ι) (r : Bool) : Operator ι :=
  ((weight u v (!r) : ℂ)/(u:ℂ)) • transportedDiagonal u v i k r

theorem transportedDiagonal_filled_contraction (u v : ℝ) (i j k l : ι)
    (hji : j≠i) (hjk : j≠k) (hjl : j≠l) (r s : Bool) (T : filledEdgeAlgebra u v i j) :
    star (transportedDiagonal u v i k r)*(T : Operator ι)*transportedDiagonal u v i l s=
      if k=l ∧ r=s then (inner ℂ (lp.single 2 ([],!r) 1)
        ((star (supportedLeg u v i r)*(T : Operator ι)*supportedLeg u v i r) (lp.single 2 ([],!r) 1))) •
          legSupport u v i r else 0 := by
  let a (b : Bool) : filledEdgeAlgebra u v i j :=
    ⟨supportedLeg u v i b,edgeAlgebra_le_filled u v i j (supportedLeg_mem_edge u v i b)⟩
  have h := diagonal_filled_contraction u v i j k l hji hjk hjl (!r) (!s) (star (a r)*T*a s)
  calc
    _ = supportedLeg u v i r*(star (edgeCreation k (!r) (!r))*
        ((star (a r)*T*a s : filledEdgeAlgebra u v i j) : Operator ι)*edgeCreation l (!s) (!s))*
        star (supportedLeg u v i s) := by
      simp only [transportedDiagonal,StarMemClass.coe_star,MulMemClass.coe_mul,star_mul,star_star,mul_assoc]
      rfl
    _ = _ := by
      rw [h]
      by_cases hr : r=s
      · subst s
        by_cases hk : k=l
        · simp only [hk,ite_true,true_and,mul_smul_comm,smul_mul_assoc,supportedLeg_vertex,
            supportedLeg_mul_star]
          rfl
        · simp only [hk,false_and,ite_false,smul_zero (M := ℂ) (A := Operator ι),mul_zero,zero_mul]
      · have hr' : (!r)≠(!s) := by cases r <;> cases s <;> simp_all
        simp only [hr,hr',and_false,ite_false,smul_zero (M := ℂ) (A := Operator ι),mul_zero,zero_mul]

theorem normalizedDiagonal_filled_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i j k l : ι) (hji : j≠i) (hjk : j≠k) (hjl : j≠l)
    (r s : Bool) (T : filledEdgeAlgebra u v i j) :
    star (normalizedDiagonal u v i k r)*(T : Operator ι)*normalizedDiagonal u v i l s=
      if k=l ∧ r=s then pVacuumTrace u v ((T : Operator ι)*legSupport u v i r) • legSupport u v i r else 0 := by
  simp only [normalizedDiagonal,star_smul,Complex.star_def,map_div₀,Complex.conj_ofReal,
    smul_mul_assoc,mul_smul_comm]
  rw [transportedDiagonal_filled_contraction u v i j k l hji hjk hjl]
  by_cases h : k=l ∧ r=s
  · obtain ⟨hk,hrs⟩ := h
    subst l;subst s
    simp only [and_self,ite_true,smul_smul]
    congr 1
    unfold pVacuumTrace
    rw [← supportedLeg_root_trace u v hu hv i r ⟨T,filledEdgeAlgebra_le_ambient u v i j T.property⟩]
    ring
  · simp only [h,ite_false,smul_zero (M := ℂ) (A := Operator ι)]
end FreeGroupFactorMain.WeightedFock

end

end OAI
