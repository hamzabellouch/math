import OAI.Analysis.InterpolatedFactors.Splitting

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace FreeGroupFactorMain.WeightedFock
open FreeFock
variable {ι : Type u_1} [DecidableEq ι]

theorem residualCreation_filled_annihilation (u v : ℝ) (i j : ι) (hji : j≠i)
    (r s : Option Bool) (hrs : ¬(r=none ∧ s=none)) (T : filledEdgeAlgebra u v i j) :
    star (residualCreation u v i j r s) ((T : Operator ι) (vacuum u v))=0 := by
  let a : filledEdgeAlgebra u v i j :=
    ⟨star (residualLeg u v i r),star_mem
      (edgeAlgebra_le_filled u v i j (residualLeg_mem_edge u v i r))⟩*T
  have hh := splitBlock_filled_annihilation u v i j hji (residualCut r) (residualCut s)
    (residual_allowed r s hrs) a
  rw [residualCreation_split]
  simp only [star_mul,star_star,mul_apply_eq_comp]
  change residualLeg u v i s (star (splitBlock u v i j (residualCut r) (residualCut s))
    ((a : Operator ι) (vacuum u v)))=0
  rw [hh,map_zero]

def normalizedResidual (u v : ℝ) (i j : ι) (r s : Option Bool) : Operator ι :=
  (u:ℂ)⁻¹ • residualCreation u v i j r s

theorem normalizedResidual_filled_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i j : ι) (hji : j≠i) (r s r' s' : Option Bool)
    (hrs : ¬(r=none ∧ s=none)) (hrs' : ¬(r'=none ∧ s'=none))
    (T : filledEdgeAlgebra u v i j) :
    star (normalizedResidual u v i j r s)*(T : Operator ι)*normalizedResidual u v i j r' s'=
      if r=r' ∧ s=s' then
        pVacuumTrace u v ((T : Operator ι)*residualSupport u v i r) • residualSupport u v i s else 0 := by
  simp only [normalizedResidual,star_smul,Complex.star_def,map_inv₀,Complex.conj_ofReal,
    smul_mul_assoc,mul_smul_comm]
  rw [residualCreation_filled_covariance u v hu hv i j hji r s r' s' hrs hrs']
  split_ifs <;> simp only [smul_zero (M := ℂ) (A := Operator ι),smul_smul,pVacuumTrace,mul_assoc]

def residualPair (u v : ℝ) (i j : ι) (r s : Option Bool) : Operator ι :=
  residualCreation u v i j r s+star (residualCreation u v i j s r)

theorem residualPair_eq (u v : ℝ) (i j : ι) (r s : Option Bool) :
    residualPair u v i j r s=residualLeg u v i r*S u v j*star (residualLeg u v i s) := by
  simp only [residualPair,residualCreation,S_eq,star_mul,star_star,mul_add,add_mul,mul_assoc]

theorem residualPair_mem_ambient (u v : ℝ) (i j : ι) (r s : Option Bool) :
    residualPair u v i j r s∈ambientAlgebra u v := by
  rw [residualPair_eq]
  exact mul_mem (mul_mem (edgeAlgebra_le_ambient u v i (residualLeg_mem_edge u v i r))
    (S_mem_ambient u v j)) (star_mem (edgeAlgebra_le_ambient u v i (residualLeg_mem_edge u v i s)))

theorem normalizedResidual_paired_mem (u v : ℝ) (i j : ι) (r s : Option Bool) :
    normalizedResidual u v i j r s+star (normalizedResidual u v i j s r)∈ambientAlgebra u v := by
  simp only [normalizedResidual,star_smul,Complex.star_def,map_inv₀,Complex.conj_ofReal,
    ← smul_add (M := ℂ) (A := Operator ι)]
  exact (ambientAlgebra u v).smul_mem (residualPair_mem_ambient u v i j r s) _

theorem residualPair_none_none (u v : ℝ) (i j : ι) :
    residualPair u v i j none none=(u:ℂ) • defectSemicircle u v i j := by
  rw [residualPair_eq]
  change edgeDefect u v i*S u v j*star (edgeDefect u v i)=_
  rw [(edgeDefect_projection u v i).isSelfAdjoint.star_eq,defectSemicircle_smul]

theorem residualLeg_sum (u v : ℝ) (i : ι) :
    residualLeg u v i none+residualLeg u v i (some false)=P := by
  change (P-edgeRange u v i)+edgeRange u v i=P
  abel

theorem filledLabel_generation (u v : ℝ) (i j : ι) (M : StarSubalgebra ℂ (Operator ι))
    (hD : (u:ℂ) • defectSemicircle u v i j∈M)
    (hR : ∀ r s : Option Bool,¬(r=none ∧ s=none) → residualPair u v i j r s∈M)
    (r s : Bool) :
    supportedCreation u v i j r s+star (supportedCreation u v i j s r)∈M := by
  have h (a b : Option Bool) : residualPair u v i j a b∈M := by
    by_cases hh : a=none ∧ b=none
    · rcases hh with ⟨rfl,rfl⟩; rwa [residualPair_none_none]
    · exact hR a b hh
  rw [supportedCreation_paired]
  cases r <;> cases s
  · change P*S u v j*star P∈M
    rw [← residualLeg_sum u v i]
    simpa only [star_add (R := Operator ι),mul_add,add_mul,← residualPair_eq] using
      add_mem (add_mem (h none none) (h (some false) none))
        (add_mem (h none (some false)) (h (some false) (some false)))
  · change P*S u v j*star (residualLeg u v i (some true))∈M
    rw [← residualLeg_sum u v i]
    simpa only [add_mul,← residualPair_eq] using add_mem (h none (some true)) (h (some false) (some true))
  · change residualLeg u v i (some true)*S u v j*star P∈M
    rw [← residualLeg_sum u v i]
    simpa only [star_add (R := Operator ι),mul_add,← residualPair_eq] using add_mem (h (some true) none) (h (some true) (some false))
  · simpa only [residualPair_eq,residualLeg,supportedLeg,ite_true] using h (some true) (some true)
end FreeGroupFactorMain.WeightedFock

section
namespace FreeGroupFactorMain.GaussianExtension
variable {E : Type u_2} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (B : StarSubalgebra ℂ (E →L[ℂ] E)) (D : E →L[ℂ] E)
variable (κ : B → B) (hκ : ∀ a : B,star D*(a : E →L[ℂ] E)*D=(κ a : E →L[ℂ] E))
include hκ in
theorem orthogonality_extension (L R : E →L[ℂ] E)
    (hLD : ∀ a : B,star L*(a : E →L[ℂ] E)*D=0)
    (hDR : ∀ a : B,star D*(a : E →L[ℂ] E)*R=0)
    (hLR : ∀ a : B,star L*(a : E →L[ℂ] E)*R=0)
    (T : E →L[ℂ] E)
    (hT : T∈StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (insert (D+star D) (B : Set (E →L[ℂ] E))) : Set (E →L[ℂ] E))) :
    star L*T*R=0 := by
  have hh := covariance_extension B D κ hκ L R 0 0 0
    (fun _ => by simp only [map_zero]) (fun _ => by simp only [map_zero]) hLD hDR
    (fun a => by simpa only [smul_zero (M := ℂ) (A := E →L[ℂ] E)] using hLR a) T hT
  simpa only [smul_zero (M := ℂ) (A := E →L[ℂ] E)] using hh
end FreeGroupFactorMain.GaussianExtension

namespace FreeGroupFactorMain.GaussianOrthogonal
variable {A : Type u_3} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
def Relation (B : StarSubalgebra ℂ A) (L R : A) := ∀ a : B,star L*(a:A)*R=0
variable {B : StarSubalgebra ℂ A} {L R : A}
theorem symm (h : Relation B L R) : Relation B R L := by
  intro a
  have hh := congrArg star (h (star a))
  simpa only [star_mul,star_star,star_zero,StarMemClass.coe_star,mul_assoc] using hh

theorem sandwich_left (h : Relation B L R) (a b : B) : Relation B ((a:A)*L*(b:A)) R := by
  intro T
  calc
    _ = star (b:A)*(star L*((star a*T:B):A)*R) := by
      simp only [star_mul,StarMemClass.coe_star,MulMemClass.coe_mul,mul_assoc]
    _ = 0 := by rw [h (star a*T),mul_zero]

theorem sandwich_right (h : Relation B L R) (a b : B) : Relation B L ((a:A)*R*(b:A)) :=
  symm (sandwich_left (symm h) a b)
end FreeGroupFactorMain.GaussianOrthogonal
namespace FreeGroupFactorMain.WeightedFock
open FreeFock GaussianOrthogonal
variable {ι : Type u_4} [DecidableEq ι]

theorem fresh_C_edge_orthogonal (u v : ℝ) (i n m : ι) (hni : n≠i) (hmi : m≠i) (hnm : n≠m) :
    Relation (edgeAlgebra u v i) (C u v n) (C u v m) := by
  intro a
  have hh := fresh_C_contraction u v {i} n m hni hmi
    ⟨a,edgeAlgebra_le_old u v {i} i (Set.mem_singleton i) a.property⟩
  simpa only [ite_eq_right hnm] using hh

theorem splitBlock_weightedDefect (u v : ℝ) (i j : ι) (hji : j≠i)
    (r s : Bool) (hrs : ¬(r=true ∧ s=true)) :
    Relation (edgeAlgebra u v i) (splitBlock u v i j r s) (weightedDefectCreation u v i j) :=
  GaussianSplit.block_D (edgeAlgebra u v i) (C u v j) (vacuum u v)
    (fresh_C_edge_contraction u v i j hji) (defectAsEdge u v i) (defectAsEdge_projection u v i)
    (defectAsEdge_central u v i) r s hrs

theorem fresh_diagonal_filled (u v : ℝ) (i j n k : ι) (hji : j≠i)
    (hni : n≠i) (hnj : n≠j) (hnk : n≠k) (hjk : j≠k) (r : Bool) :
    Relation (filledEdgeAlgebra u v i j) (C u v n) (edgeCreation k r r) := by
  intro T
  exact GaussianExtension.orthogonality_extension (edgeAlgebra u v i) (weightedDefectCreation u v i j)
    (defectCovariance u v i) (weightedDefect_contraction u v i j hji) (C u v n) (edgeCreation k r r)
    (fresh_C_weightedDefect u v i j n hji hni hnj)
    (symm (fun a => diagonal_weightedDefect u v i j k hji hjk a r))
    (fun a => fresh_C_diagonal_edge u v i n k hni hnk a r) T T.property

theorem fresh_split_filled (u v : ℝ) (i j n : ι) (hji : j≠i)
    (hni : n≠i) (hnj : n≠j) (r s : Bool) (hrs : ¬(r=true ∧ s=true)) :
    Relation (filledEdgeAlgebra u v i j) (C u v n) (splitBlock u v i j r s) := by
  intro T
  exact GaussianExtension.orthogonality_extension (edgeAlgebra u v i) (weightedDefectCreation u v i j)
    (defectCovariance u v i) (weightedDefect_contraction u v i j hji) (C u v n) (splitBlock u v i j r s)
    (fresh_C_weightedDefect u v i j n hji hni hnj)
    (symm (splitBlock_weightedDefect u v i j hji r s hrs))
    (sandwich_right (fresh_C_edge_orthogonal u v i n j hni hji hnj)
      (GaussianSplit.cut (edgeAlgebra u v i) (defectAsEdge u v i) r)
      (GaussianSplit.cut (edgeAlgebra u v i) (defectAsEdge u v i) s)) T T.property

theorem split_diagonal_filled (u v : ℝ) (i j k : ι) (hji : j≠i) (hjk : j≠k)
    (r s t : Bool) (hrs : ¬(r=true ∧ s=true)) :
    Relation (filledEdgeAlgebra u v i j) (splitBlock u v i j r s) (edgeCreation k t t) := by
  intro T
  exact GaussianExtension.orthogonality_extension (edgeAlgebra u v i) (weightedDefectCreation u v i j)
    (defectCovariance u v i) (weightedDefect_contraction u v i j hji) (splitBlock u v i j r s) (edgeCreation k t t)
    (splitBlock_weightedDefect u v i j hji r s hrs)
    (symm (fun a => diagonal_weightedDefect u v i j k hji hjk a t))
    (sandwich_left (fun a => fresh_C_diagonal_edge u v i j k hji hjk a t)
      (GaussianSplit.cut (edgeAlgebra u v i) (defectAsEdge u v i) r)
      (GaussianSplit.cut (edgeAlgebra u v i) (defectAsEdge u v i) s)) T T.property
end FreeGroupFactorMain.WeightedFock

end

namespace FreeGroupFactorMain.GaussianOrthogonal
variable {A : Type u_5} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {B : StarSubalgebra ℂ A} {L R : A}
theorem smul_left (h : Relation B L R) (z : ℂ) : Relation B (z • L) R := by
  intro a
  simp only [star_smul,smul_mul_assoc,h a,smul_zero]
theorem smul_right (h : Relation B L R) (z : ℂ) : Relation B L (z • R) := by
  intro a
  simp only [mul_smul_comm,h a,smul_zero]
end FreeGroupFactorMain.GaussianOrthogonal

namespace FreeGroupFactorMain.WeightedFock
open FreeFock GaussianOrthogonal
variable {ι : Type u_6} [DecidableEq ι]

def legAsFilled (u v : ℝ) (i j : ι) (r : Bool) : filledEdgeAlgebra u v i j :=
  ⟨supportedLeg u v i r,edgeAlgebra_le_filled u v i j (supportedLeg_mem_edge u v i r)⟩
def residualLegAsFilled (u v : ℝ) (i j : ι) (r : Option Bool) : filledEdgeAlgebra u v i j :=
  ⟨residualLeg u v i r,edgeAlgebra_le_filled u v i j (residualLeg_mem_edge u v i r)⟩

theorem normalized_fresh_diagonal (u v : ℝ) (i j n k : ι) (hji : j≠i)
    (hni : n≠i) (hnj : n≠j) (hnk : n≠k) (hjk : j≠k) (r s t : Bool) :
    Relation (filledEdgeAlgebra u v i j) (normalizedCreation u v i n r s)
      (normalizedDiagonal u v i k t) := by
  exact smul_right (smul_left (sandwich_right (sandwich_left
    (fresh_diagonal_filled u v i j n k hji hni hnj hnk hjk (!t))
    (legAsFilled u v i j r) (star (legAsFilled u v i j s)))
    (legAsFilled u v i j t) (star (legAsFilled u v i j t))) _) _

theorem normalized_fresh_residual (u v : ℝ) (i j n : ι) (hji : j≠i)
    (hni : n≠i) (hnj : n≠j) (r s : Bool) (a b : Option Bool)
    (hab : ¬(a=none ∧ b=none)) :
    Relation (filledEdgeAlgebra u v i j) (normalizedCreation u v i n r s)
      (normalizedResidual u v i j a b) := by
  have hh := sandwich_right (sandwich_left
    (fresh_split_filled u v i j n hji hni hnj (residualCut a) (residualCut b)
      (residual_allowed a b hab))
    (legAsFilled u v i j r) (star (legAsFilled u v i j s)))
    (residualLegAsFilled u v i j a) (star (residualLegAsFilled u v i j b))
  change Relation _ (supportedCreation u v i n r s)
    (residualLeg u v i a*splitBlock u v i j (residualCut a) (residualCut b)*star (residualLeg u v i b)) at hh
  rw [← residualCreation_split] at hh
  exact smul_right (smul_left hh _) _

theorem normalized_residual_diagonal (u v : ℝ) (i j k : ι) (hji : j≠i) (hjk : j≠k)
    (a b : Option Bool) (hab : ¬(a=none ∧ b=none)) (r : Bool) :
    Relation (filledEdgeAlgebra u v i j) (normalizedResidual u v i j a b)
      (normalizedDiagonal u v i k r) := by
  have hh := sandwich_right (sandwich_left
    (split_diagonal_filled u v i j k hji hjk (residualCut a) (residualCut b) (!r)
      (residual_allowed a b hab))
    (residualLegAsFilled u v i j a) (star (residualLegAsFilled u v i j b)))
    (legAsFilled u v i j r) (star (legAsFilled u v i j r))
  change Relation _
    (residualLeg u v i a*splitBlock u v i j (residualCut a) (residualCut b)*star (residualLeg u v i b))
    (transportedDiagonal u v i k r) at hh
  rw [← residualCreation_split] at hh
  exact smul_right (smul_left hh _) _

theorem normalizedCreation_annihilate (u v : ℝ) (i j n : ι) (hji : j≠i)
    (hni : n≠i) (hnj : n≠j) (r s : Bool) (T : filledEdgeAlgebra u v i j) :
    star (normalizedCreation u v i n r s) ((T : Operator ι) (vacuum u v))=0 := by
  simp only [normalizedCreation,star_smul,_root_.smul_apply,
    supportedCreation_filled_annihilation u v i j n hji hni hnj r s T,smul_zero]

theorem normalizedResidual_annihilate (u v : ℝ) (i j : ι) (hji : j≠i)
    (r s : Option Bool) (hrs : ¬(r=none ∧ s=none)) (T : filledEdgeAlgebra u v i j) :
    star (normalizedResidual u v i j r s) ((T : Operator ι) (vacuum u v))=0 := by
  simp only [normalizedResidual,star_smul,_root_.smul_apply,
    residualCreation_filled_annihilation u v i j hji r s hrs T,smul_zero]

theorem transportedDiagonal_annihilate (u v : ℝ) (i j k : ι) (hji : j≠i) (hjk : j≠k)
    (r : Bool) (T : filledEdgeAlgebra u v i j) :
    star (transportedDiagonal u v i k r) ((T : Operator ι) (vacuum u v))=0 := by
  have hh := diagonal_filled_annihilation u v i j k hji hjk (!r) (star (legAsFilled u v i j r)*T)
  simp only [transportedDiagonal,star_mul,star_star,mul_apply_eq_comp]
  change star (edgeCreation k (!r) (!r)) (star (supportedLeg u v i r) ((T : Operator ι) (vacuum u v)))=0 at hh
  rw [hh,map_zero]

theorem normalizedDiagonal_annihilate (u v : ℝ) (i j k : ι) (hji : j≠i) (hjk : j≠k)
    (r : Bool) (T : filledEdgeAlgebra u v i j) :
    star (normalizedDiagonal u v i k r) ((T : Operator ι) (vacuum u v))=0 := by
  simp only [normalizedDiagonal,star_smul,_root_.smul_apply,
    transportedDiagonal_annihilate u v i j k hji hjk r T,smul_zero]
end FreeGroupFactorMain.WeightedFock

end

end OAI
