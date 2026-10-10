import OAI.Analysis.InterpolatedFactors.Gaussian

namespace OAI

noncomputable section

universe u_1 u_2 u_3

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock
variable {ι : Type u_1} [DecidableEq ι]

theorem P_mem_old (u v : ℝ) (J : Set ι) : (P : Operator ι)∈oldAlgebra u v J :=
  Bicommutant.subset _ (Set.mem_insert _ _)

theorem S_mem_old (u v : ℝ) (J : Set ι) (i : ι) (hi : i∈J) : S u v i∈oldAlgebra u v J :=
  Bicommutant.subset _ (Set.mem_insert_of_mem _ ⟨i,hi,rfl⟩)

theorem offDiagonal_mem_old (u v : ℝ) (J : Set ι) (i : ι) (hi : i∈J) :
    offDiagonal u v i∈oldAlgebra u v J := by
  unfold offDiagonal
  exact mul_mem (mul_mem (P_mem_old u v J) (S_mem_old u v J i hi))
    (sub_mem (one_mem _) (P_mem_old u v J))

theorem edgeAlgebra_le_old (u v : ℝ) (J : Set ι) (i : ι) (hi : i∈J) :
    edgeAlgebra u v i≤oldAlgebra u v J := by
  apply Bicommutant.generated_le
  rintro T (rfl|hT)
  · exact P_mem_old u v J
  · have he : T=offDiagonal u v i+star (offDiagonal u v i) := hT
    rw [he]
    exact add_mem (offDiagonal_mem_old u v J i hi) (star_mem (offDiagonal_mem_old u v J i hi))

def weightedDefectCreation (u v : ℝ) (i j : ι) : Operator ι :=
  edgeDefect u v i*C u v j*edgeDefect u v i

def defectCovariance (u v : ℝ) (i : ι) (a : edgeAlgebra u v i) : edgeAlgebra u v i :=
  ⟨vacuumTrace u v (edgeDefect u v i*(a : Operator ι)*edgeDefect u v i) • edgeDefect u v i,
    (edgeAlgebra u v i).smul_mem (edgeDefect_mem_edge u v i) _⟩

theorem weightedDefect_contraction (u v : ℝ) (i j : ι) (hji : j≠i) (a : edgeAlgebra u v i) :
    star (weightedDefectCreation u v i j)*(a : Operator ι)*weightedDefectCreation u v i j=
      (defectCovariance u v i a : Operator ι) := by
  let d : edgeAlgebra u v i := ⟨edgeDefect u v i,edgeDefect_mem_edge u v i⟩
  let b : oldAlgebra u v {i} := ⟨(d*a*d : edgeAlgebra u v i),
    edgeAlgebra_le_old u v {i} i (Set.mem_singleton i) (d*a*d).property⟩
  have hc := fresh_C_contraction u v {i} j j hji hji b
  simp only [ite_true] at hc
  change star (C u v j)*(edgeDefect u v i*(a : Operator ι)*edgeDefect u v i)*C u v j=_ at hc
  calc
    _ = edgeDefect u v i*(star (C u v j)*(edgeDefect u v i*(a : Operator ι)*edgeDefect u v i)*
        C u v j)*edgeDefect u v i := by
      simp only [weightedDefectCreation,star_mul,(edgeDefect_projection u v i).isSelfAdjoint.star_eq]
      noncomm_ring
    _ = _ := by
      rw [hc,mul_smul_comm,smul_mul_assoc,mul_one,(edgeDefect_projection u v i).isIdempotentElem.eq]
      rfl

theorem weightedDefect_annihilates_edge (u v : ℝ) (i j : ι) (hji : j≠i) (a : edgeAlgebra u v i) :
    star (weightedDefectCreation u v i j) ((a : Operator ι) (vacuum u v))=0 := by
  let b : oldAlgebra u v {i} := ⟨edgeDefect u v i*(a : Operator ι),
    edgeAlgebra_le_old u v {i} i (Set.mem_singleton i)
      (mul_mem (edgeDefect_mem_edge u v i) a.property)⟩
  have hc := fresh_C_annihilates_old_vacuum u v {i} j hji b
  rw [weightedDefectCreation,star_mul,star_mul,(edgeDefect_projection u v i).isSelfAdjoint.star_eq]
  change edgeDefect u v i (star (C u v j) (edgeDefect u v i ((a : Operator ι) (vacuum u v))))=0
  rw [show star (C u v j) (edgeDefect u v i ((a : Operator ι) (vacuum u v)))=0 from hc,map_zero]

theorem fresh_C_weightedDefect (u v : ℝ) (i j n : ι) (hji : j≠i) (hni : n≠i) (hnj : n≠j)
    (a : edgeAlgebra u v i) : star (C u v n)*(a : Operator ι)*weightedDefectCreation u v i j=0 := by
  let b : oldAlgebra u v {i} := ⟨(a : Operator ι)*edgeDefect u v i,
    edgeAlgebra_le_old u v {i} i (Set.mem_singleton i)
      (mul_mem a.property (edgeDefect_mem_edge u v i))⟩
  have hc := fresh_C_contraction u v {i} n j hni hji b
  rw [ite_eq_right hnj] at hc
  change star (C u v n)*((a : Operator ι)*edgeDefect u v i)*C u v j=0 at hc
  rw [weightedDefectCreation]
  calc
    _ = (star (C u v n)*((a : Operator ι)*edgeDefect u v i)*C u v j)*edgeDefect u v i := by
      simp only [mul_assoc]
    _ = 0 := by rw [hc,zero_mul]

def filledEdgeAlgebra (u v : ℝ) (i j : ι) : StarSubalgebra ℂ (Operator ι) :=
  Bicommutant.algebra (insert (weightedDefectCreation u v i j+star (weightedDefectCreation u v i j))
    (edgeAlgebra u v i : Set (Operator ι)))

theorem fresh_C_filled_contraction (u v : ℝ) (i j n m : ι) (hji : j≠i)
    (hni : n≠i) (hnj : n≠j) (hmi : m≠i) (hmj : m≠j) (T : filledEdgeAlgebra u v i j) :
    star (C u v n)*(T : Operator ι)*C u v m=
      if n=m then vacuumTrace u v (T : Operator ι) • 1 else 0 := by
  have hD := weightedDefect_annihilates_edge u v i j hji
  have hR (a : edgeAlgebra u v i) : star (weightedDefectCreation u v i j)*(a : Operator ι)*C u v m=0 := by
    have hh := congrArg star (fresh_C_weightedDefect u v i j m hji hmi hmj (star a))
    simpa only [star_mul,star_star,StarMemClass.coe_star,star_zero (Operator ι),mul_assoc] using hh
  have hb (a : edgeAlgebra u v i) : star (C u v n)*(a : Operator ι)*C u v m=
      (inner ℂ (vacuum u v) ((a : Operator ι) (vacuum u v))) • (if n=m then (1 : Operator ι) else 0) := by
    have hh := fresh_C_contraction u v {i} n m hni hmi
      ⟨a,edgeAlgebra_le_old u v {i} i (Set.mem_singleton i) a.property⟩
    split_ifs with h <;> simpa only [vacuumTrace,h,ite_true,ite_false,
      smul_zero (M := ℂ) (A := Operator ι)] using hh
  have hh := GaussianExtension.covariance_extension (edgeAlgebra u v i) (weightedDefectCreation u v i j)
    (defectCovariance u v i) (weightedDefect_contraction u v i j hji)
    (C u v n) (C u v m) (if n=m then (1 : Operator ι) else 0) (vacuum u v) (vacuum u v)
    hD hD (fresh_C_weightedDefect u v i j n hji hni hnj) hR hb (T : Operator ι) T.property
  split_ifs with h <;> simpa only [vacuumTrace,h,ite_true,ite_false,
    smul_zero (M := ℂ) (A := Operator ι)] using hh

theorem fresh_C_filled_annihilation (u v : ℝ) (i j n : ι) (hji : j≠i) (hni : n≠i) (hnj : n≠j)
    (T : filledEdgeAlgebra u v i j) : star (C u v n) ((T : Operator ι) (vacuum u v))=0 := by
  apply GaussianExtension.annihilation_extension (edgeAlgebra u v i) (weightedDefectCreation u v i j)
    (defectCovariance u v i) (weightedDefect_contraction u v i j hji)
    (C u v n) (vacuum u v) (weightedDefect_annihilates_edge u v i j hji)
    _ (fresh_C_weightedDefect u v i j n hji hni hnj) (T : Operator ι) T.property
  intro a
  exact fresh_C_annihilates_old_vacuum u v {i} n hni
    ⟨a,edgeAlgebra_le_old u v {i} i (Set.mem_singleton i) a.property⟩
end
section
open FreeFock
variable {ι : Type u_2} [DecidableEq ι]

theorem edgeAlgebra_le_ambient (u v : ℝ) (i : ι) : edgeAlgebra u v i≤ambientAlgebra u v := by
  apply Bicommutant.generated_le
  rintro T (rfl|hT)
  · exact P_mem_ambient u v
  · have he : T=offDiagonal u v i+star (offDiagonal u v i) := hT
    rw [he]
    exact add_mem (offDiagonal_mem_ambient u v i) (star_mem (offDiagonal_mem_ambient u v i))

theorem edgeAlgebra_le_filled (u v : ℝ) (i j : ι) : edgeAlgebra u v i≤filledEdgeAlgebra u v i j :=
  fun _ h => Bicommutant.subset _ (Set.mem_insert_of_mem _ h)

theorem weightedDefect_semicircle_mem_filled (u v : ℝ) (i j : ι) :
    weightedDefectCreation u v i j+star (weightedDefectCreation u v i j)∈filledEdgeAlgebra u v i j :=
  Bicommutant.subset _ (Set.mem_insert _ _)

theorem filledEdgeAlgebra_le_ambient (u v : ℝ) (i j : ι) : filledEdgeAlgebra u v i j≤ambientAlgebra u v := by
  apply Bicommutant.generated_le
  rintro T (rfl|hT)
  · have he : weightedDefectCreation u v i j+star (weightedDefectCreation u v i j)=
        edgeDefect u v i*S u v j*edgeDefect u v i := by
      simp only [weightedDefectCreation,S_eq,star_mul,(edgeDefect_projection u v i).isSelfAdjoint.star_eq,
        mul_add,add_mul,mul_assoc]
    rw [he]
    have hd := edgeAlgebra_le_ambient u v i (edgeDefect_mem_edge u v i)
    exact mul_mem (mul_mem hd (S_mem_ambient u v j)) hd
  · exact edgeAlgebra_le_ambient u v i hT

theorem weightedDefectCreation_eq (u v : ℝ) (i j : ι) :
    weightedDefectCreation u v i j=(u:ℂ) • defectCreation u v i j := by
  have he : P*C u v j*P=(u:ℂ) • edgeCreation j true true := by
    simp only [C,mul_add,mul_smul_comm,smul_mul_assoc,P_creation_true,P_creation_false,
      smul_zero (M := ℂ) (A := Operator ι),add_zero,edgeCreation,vertex_true]
  calc
    _ = edgeDefect u v i*(P*C u v j*P)*edgeDefect u v i := by
      simp only [weightedDefectCreation,mul_assoc,P_mul_edgeDefect]
      rw [← mul_assoc (edgeDefect u v i) P,edgeDefect_mul_P]
    _ = _ := by rw [he,mul_smul_comm,smul_mul_assoc]; rfl

theorem defectSemicircle_mem_filled (u v : ℝ) (hu : u≠0) (i j : ι) :
    defectSemicircle u v i j∈filledEdgeAlgebra u v i j := by
  have he : weightedDefectCreation u v i j+star (weightedDefectCreation u v i j)=
      (u:ℂ) • defectSemicircle u v i j := by
    simp only [weightedDefectCreation_eq,star_smul,Complex.star_def,Complex.conj_ofReal,
      defectSemicircle,smul_add]
  have hh := (filledEdgeAlgebra u v i j).smul_mem (weightedDefect_semicircle_mem_filled u v i j) (u:ℂ)⁻¹
  rw [he,smul_smul,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hu),one_smul] at hh
  exact hh

theorem diffuseBase_le_filled (u v : ℝ) (hu : u≠0) (i j : ι) :
    diffuseBase u v i j≤filledEdgeAlgebra u v i j := by
  apply Bicommutant.generated_le
  rintro T (rfl|hT)
  · exact edgeAlgebra_le_filled u v i j (P_mem_edge u v i)
  · have he : T=oldBaseGenerator u v i j := hT
    rw [he,oldBaseGenerator]
    apply add_mem
    · apply add_mem
      · exact edgeAlgebra_le_filled u v i j
          (mul_mem (offDiagonal_mem_edge u v i) (star_mem (edgePolar_mem_edge u v i)))
      · exact defectSemicircle_mem_filled u v hu i j
    · exact (filledEdgeAlgebra u v i j).smul_mem
        (edgeAlgebra_le_filled u v i j (edgeRange_mem_edge u v i)) _
end

open FreeFock
variable {ι : Type u_3} [DecidableEq ι]

theorem edgePolar_mul_P (u v : ℝ) (i : ι) : edgePolar u v i*P=0 :=
  CornerRerouting.right_zero (edgePolar_right u v i)

theorem P_mul_star_edgePolar (u v : ℝ) (i : ι) : P*star (edgePolar u v i)=0 :=
  CornerRerouting.star_left_zero projection_P.isSelfAdjoint (edgePolar_mul_P u v i)

def supportedLeg (u v : ℝ) (i₀ : ι) (r : Bool) : Operator ι :=
  if r then edgePolar u v i₀ else P

def legSupport (u v : ℝ) (i₀ : ι) (r : Bool) : Operator ι :=
  if r then edgeRange u v i₀ else P

theorem supportedLeg_mem_edge (u v : ℝ) (i : ι) (r : Bool) :
    supportedLeg u v i r∈edgeAlgebra u v i := by
  cases r
  · exact P_mem_edge u v i
  · exact edgePolar_mem_edge u v i

theorem supportedLeg_mem_ambient (u v : ℝ) (i : ι) (r : Bool) :
    supportedLeg u v i r∈ambientAlgebra u v :=
  edgeAlgebra_le_ambient u v i (supportedLeg_mem_edge u v i r)

theorem supportedLeg_mul_star (u v : ℝ) (i : ι) (r s : Bool) :
    supportedLeg u v i r*star (supportedLeg u v i s)=
      if r=s then legSupport u v i r else 0 := by
  cases r <;> cases s <;>
    simp only [supportedLeg,legSupport,Bool.false_eq_true,ite_false,ite_true,
      projection_P.isSelfAdjoint.star_eq,projection_P.isIdempotentElem.eq,
      P_mul_star_edgePolar,edgePolar_mul_P,Bool.true_eq_false,edgeRange]

theorem supportedLeg_trace_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i : ι) (r s : Bool) (T : ambientAlgebra (ι := ι) u v) :
    vacuumTrace u v (star (supportedLeg u v i r)*(T : Operator ι)*supportedLeg u v i s)=
      if r=s then vacuumTrace u v ((T : Operator ι)*legSupport u v i r) else 0 := by
  have ht := ambient_trace_mul u v hu hv
    ⟨star (supportedLeg u v i r),star_mem (supportedLeg_mem_ambient u v i r)⟩
    (T*⟨supportedLeg u v i s,supportedLeg_mem_ambient u v i s⟩)
  change vacuumTrace u v (star (supportedLeg u v i r)*((T : Operator ι)*supportedLeg u v i s))=
    vacuumTrace u v (((T : Operator ι)*supportedLeg u v i s)*star (supportedLeg u v i r)) at ht
  rw [mul_assoc,ht,mul_assoc,supportedLeg_mul_star]
  by_cases h : r=s
  · subst s
    simp only [ite_true]
  · simp only [h,Ne.symm h,ite_false,mul_zero,vacuumTrace,zero_apply,inner_zero_right]

def supportedCreation (u v : ℝ) (i₀ i : ι) (r s : Bool) : Operator ι :=
  supportedLeg u v i₀ r*C u v i*star (supportedLeg u v i₀ s)

theorem supportedCreation_filled_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i j n m : ι) (hji : j≠i) (hni : n≠i) (hnj : n≠j) (hmi : m≠i) (hmj : m≠j)
    (r s r' s' : Bool) (T : filledEdgeAlgebra u v i j) :
    star (supportedCreation u v i n r s)*(T : Operator ι)*supportedCreation u v i m r' s'=
      if n=m ∧ r=r' ∧ s=s' then
        vacuumTrace u v ((T : Operator ι)*legSupport u v i r) • legSupport u v i s else 0 := by
  let a (b : Bool) : filledEdgeAlgebra u v i j :=
    ⟨supportedLeg u v i b,edgeAlgebra_le_filled u v i j (supportedLeg_mem_edge u v i b)⟩
  have hc := fresh_C_filled_contraction u v i j n m hji hni hnj hmi hmj (star (a r)*T*a r')
  change star (C u v n)*(star (supportedLeg u v i r)*(T : Operator ι)*supportedLeg u v i r')*C u v m=_ at hc
  calc
    _ = supportedLeg u v i s*(star (C u v n)*
        (star (supportedLeg u v i r)*(T : Operator ι)*supportedLeg u v i r')*C u v m)*
        star (supportedLeg u v i s') := by simp only [supportedCreation,star_mul,star_star,mul_assoc]
    _ = _ := by
      rw [hc]
      change (supportedLeg u v i s*(if n=m then
        vacuumTrace u v (star (supportedLeg u v i r)*(T : Operator ι)*supportedLeg u v i r') • 1 else 0)*
        star (supportedLeg u v i s'))=_
      rw [supportedLeg_trace_covariance u v hu hv i r r'
        ⟨T,filledEdgeAlgebra_le_ambient u v i j T.property⟩]
      by_cases hnm : n=m
      · rw [ite_eq_left hnm,mul_smul_comm,smul_mul_assoc,mul_one,supportedLeg_mul_star]
        by_cases hr : r=r' <;> by_cases hs : s=s' <;>
          simp only [hnm,hr,hs,ite_true,ite_false,zero_smul ℂ (A := Operator ι),
            smul_zero (M := ℂ) (A := Operator ι),true_and,false_and,and_false]
      · simp only [hnm,ite_false,mul_zero,zero_mul,false_and]

theorem supportedCreation_filled_annihilation (u v : ℝ)
    (i j n : ι) (hji : j≠i) (hni : n≠i) (hnj : n≠j)
    (r s : Bool) (T : filledEdgeAlgebra u v i j) :
    star (supportedCreation u v i n r s) ((T : Operator ι) (vacuum u v))=0 := by
  let a : filledEdgeAlgebra u v i j :=
    ⟨star (supportedLeg u v i r),star_mem
      (edgeAlgebra_le_filled u v i j (supportedLeg_mem_edge u v i r))⟩*T
  have hh := fresh_C_filled_annihilation u v i j n hji hni hnj a
  simp only [supportedCreation,star_mul,star_star,mul_apply_eq_comp]
  change supportedLeg u v i s (star (C u v n) ((a : Operator ι) (vacuum u v)))=0
  rw [hh,map_zero]

def pVacuumTrace (u v : ℝ) (T : Operator ι) : ℂ := (u:ℂ)⁻¹*(u:ℂ)⁻¹*vacuumTrace u v T

def normalizedCreation (u v : ℝ) (i n : ι) (r s : Bool) : Operator ι :=
  (u:ℂ)⁻¹ • supportedCreation u v i n r s

theorem normalizedCreation_filled_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i j n m : ι) (hji : j≠i) (hni : n≠i) (hnj : n≠j) (hmi : m≠i) (hmj : m≠j)
    (r s r' s' : Bool) (T : filledEdgeAlgebra u v i j) :
    star (normalizedCreation u v i n r s)*(T : Operator ι)*normalizedCreation u v i m r' s'=
      if n=m ∧ r=r' ∧ s=s' then
        pVacuumTrace u v ((T : Operator ι)*legSupport u v i r) • legSupport u v i s else 0 := by
  simp only [normalizedCreation,star_smul,Complex.star_def,map_inv₀,Complex.conj_ofReal,
    smul_mul_assoc,mul_smul_comm]
  rw [supportedCreation_filled_covariance u v hu hv i j n m hji hni hnj hmi hmj]
  split_ifs <;> simp only [smul_zero (M := ℂ) (A := Operator ι),smul_smul,pVacuumTrace,mul_assoc]

theorem supportedCreation_paired (u v : ℝ) (i n : ι) (r s : Bool) :
    supportedCreation u v i n r s+star (supportedCreation u v i n s r)=
      supportedLeg u v i r*S u v n*star (supportedLeg u v i s) := by
  simp only [supportedCreation,S_eq,star_mul,star_star,mul_add,add_mul,mul_assoc]

theorem normalizedCreation_paired_mem (u v : ℝ) (i n : ι) (r s : Bool) :
    normalizedCreation u v i n r s+star (normalizedCreation u v i n s r)∈ambientAlgebra u v := by
  simp only [normalizedCreation,star_smul,Complex.star_def,map_inv₀,Complex.conj_ofReal,
  ← smul_add (M := ℂ) (A := Operator ι)]
  rw [supportedCreation_paired]
  exact (ambientAlgebra u v).smul_mem
    (mul_mem (mul_mem (supportedLeg_mem_ambient u v i r) (S_mem_ambient u v n))
      (star_mem (supportedLeg_mem_ambient u v i s))) _
end FreeGroupFactorMain.WeightedFock

end

end OAI
