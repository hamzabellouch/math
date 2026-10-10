import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.Encoding
import OAI.Combinatorics.ThinTrees.Continuation.Feasibility
import OAI.Combinatorics.ThinTrees.Continuation.SpectralSize

namespace OAI

/-! Continuation interior. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

lemma qform_transpose (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    qform Aᵀ v=qform A v := by
  simp only [qform,dotProduct_mulVec,vecMul_transpose,dotProduct_comm]

lemma qform_responseMatrix (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    qform (responseMatrix A) v=qform A (centering n *ᵥ v) := by
  rw [responseMatrix,qform_centered,qform_smul,qform_add,qform_transpose]
  ring

lemma qform_sum {J : Type*} [Fintype J] (A : J → Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    qform (∑j, A j) v=∑j, qform (A j) v := by
  simp only [qform,sum_mulVec,dotProduct_sum]

lemma abs_qform_le_entries {A : Matrix (Fin n) (Fin n) ℝ} {η : ℝ}
    (hη : 0 ≤ η) (hA : ∀i j, |A i j| ≤ η) (v : Fin n → ℝ) :
    |qform A v| ≤ (n : ℝ)*η*(∑i, v i^2) := by
  have hq : qform A v=∑i, ∑j, v i*A i j*v j := by
    simp only [qform,mulVec,dotProduct,mul_sum]
    congr 1
    ext i
    exact sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
  have hh : ∑i, ∑j, |v i*A i j*v j| ≤ η*(∑i, |v i|)^2 := by
    calc
      _ ≤ ∑i, ∑j, |v i| *η*|v j| := sum_le_sum fun i _ => sum_le_sum fun j _ => by
        rw [abs_mul,abs_mul]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hA i j) (abs_nonneg _)) (abs_nonneg _)
      _ = _ := by simp only [←mul_sum,←sum_mul]; ring
  have hcs : (∑i, |v i|)^2 ≤ (n : ℝ)*(∑i, v i^2) := by
    simpa only [sq_abs,card_univ,Fintype.card_fin] using sq_sum_le_card_mul_sum_sq (s:=univ) (f:=fun i => |v i|)
  calc
    _ ≤ ∑i, ∑j, |v i*A i j*v j| := by
      rw [hq]
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => abs_sum_le_sum_abs _ _)
    _ ≤ η*(∑i, |v i|)^2 := hh
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hcs hη]

lemma difference_outer_centered {a b : Fin n} (hab : a ≠ b) (v : Fin n → ℝ) :
    qform (vecMulVec (difference a b) (difference a b)) v ≤
      2*(∑i, (centering n *ᵥ v) i^2) := by
  have h := difference_outer_le hab (centering n *ᵥ v)
  rwa [qform_outer,centered_dot _ _ (difference_sum a b),←qform_outer] at h

lemma abs_triangle_energy (ijk : DistinctTriple n) (v : Fin n → ℝ) :
    |qform (triangleGenerator ijk) v| ≤ 6*(∑i, (centering n *ᵥ v) i^2) := by
  have h1 := difference_outer_centered ijk.property.1 v
  have h2 := difference_outer_centered ijk.property.2.1 v
  have h3 := difference_outer_centered ijk.property.2.2 v
  have h1n := qform_nonneg (ShortcutDual.outer_posSemidef (difference ijk.1.1 ijk.1.2.1)) v
  have h2n := qform_nonneg (ShortcutDual.outer_posSemidef (difference ijk.1.2.1 ijk.1.2.2)) v
  have h3n := qform_nonneg (ShortcutDual.outer_posSemidef (difference ijk.1.1 ijk.1.2.2)) v
  rw [triangleGenerator,triangleMatrix,qform_sub,qform_add]
  apply abs_le.mpr
  constructor <;> linarith only [h1,h2,h3,h1n,h2n,h3n]

lemma distinctTriple_card_le : Fintype.card (DistinctTriple n) ≤ n^3 := by
  have h := Fintype.card_subtype_le (fun p : Fin n × Fin n × Fin n =>
    p.1 ≠ p.2.1 ∧ p.2.1 ≠ p.2.2 ∧ p.1 ≠ p.2.2)
  simpa only [Fintype.card_prod,Fintype.card_fin,pow_succ,pow_zero,one_mul,mul_assoc] using h

lemma abs_triangle_sum {lam : DistinctTriple n → ℝ} {η : ℝ}
    (hη : 0 ≤ η) (hlam : ∀ijk, |lam ijk| ≤ η) (v : Fin n → ℝ) :
    |qform (∑ijk, lam ijk • triangleGenerator ijk) v| ≤
      6*(n : ℝ)^3*η*(∑i, (centering n *ᵥ v) i^2) := by
  simp only [qform_sum,qform_smul]
  calc
    _ ≤ ∑ijk, |lam ijk*qform (triangleGenerator ijk) v| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ijk : DistinctTriple n, η*(6*(∑i, (centering n *ᵥ v) i^2)) := by
      apply sum_le_sum
      intro ijk _
      rw [abs_mul]
      exact mul_le_mul (hlam ijk) (abs_triangle_energy ijk v) (abs_nonneg _) hη
    _ = (Fintype.card (DistinctTriple n) : ℝ)*η*6*(∑i, (centering n *ᵥ v) i^2) := by
      simp only [sum_const,card_univ,nsmul_eq_mul]; ring
    _ ≤ _ := by
      have hc : (Fintype.card (DistinctTriple n) : ℝ) ≤ (n : ℝ)^3 := by exact_mod_cast distinctTriple_card_le (n:=n)
      nlinarith only [mul_le_mul_of_nonneg_right hc
        (show 0 ≤ η*6*(∑i, (centering n *ᵥ v) i^2) by positivity)]

lemma lowerPencil_hermitian (H : MultiGraph n m) (x : StepFree n m) :
    (x.lowerPencil H).IsHermitian :=
  (responseMatrix_hermitian x.1).sub (H.laplacian_psd univ).isHermitian

lemma upperPencil_hermitian (H : MultiGraph n m) (x : StepFree n m) :
    (x.upperPencil H).IsHermitian := by
  apply ((H.laplacian_psd univ).smul (by norm_num : (0 : ℝ) ≤ 3)).isHermitian.sub (responseMatrix_hermitian x.1) |>.sub
  change (∑ijk, x.multiplier ijk • triangleGenerator ijk)ᴴ = _
  rw [conjTranspose_sum]
  apply sum_congr rfl
  intro ijk _
  exact (triangleMatrix_hermitian _ _ _).smul (by rfl)

lemma edgePencil_hermitian (H : MultiGraph n m) (s : ℝ) (x : StepFree n m) (e : Fin m) :
    (x.edgePencil H s e).IsHermitian :=
  (responseMatrix_hermitian x.1).sub ((ShortcutDual.outer_posSemidef _).isHermitian.smul (by rfl))

namespace StepFree

def Close (x w : StepFree n m) (η : ℝ) : Prop :=
  (∀i j, |x.1 i j-w.1 i j| ≤ η) ∧
  (∀ijk, |x.multiplier ijk-w.multiplier ijk| ≤ η) ∧
  (∀e, |x.y e-w.y e| ≤ η) ∧ (∀e, |x.z e-w.z e| ≤ η)

lemma Close.symm {x w : StepFree n m} {η : ℝ} (h : Close x w η) : Close w x η := by
  simpa only [Close,abs_sub_comm] using h

lemma Close.mono {x w : StepFree n m} {η δ : ℝ} (h : Close x w η) (hηδ : η ≤ δ) : Close x w δ :=
  ⟨fun i j => (h.1 i j).trans hηδ,fun ijk => (h.2.1 ijk).trans hηδ,
    fun e => (h.2.2.1 e).trans hηδ,fun e => (h.2.2.2 e).trans hηδ⟩

lemma Close.qform_bound {x w : StepFree n m} {η : ℝ}
    (hη : 0 ≤ η) (h : Close x w η) (v : Fin n → ℝ) :
    |qform x.matrix v-qform w.matrix v| ≤ (n : ℝ)*η*(∑i, (centering n *ᵥ v) i^2) := by
  rw [←qform_sub,matrix,matrix,←responseMatrix_sub,qform_responseMatrix]
  exact abs_qform_le_entries hη h.1 _

lemma Close.lower_error (H : MultiGraph n m) {x w : StepFree n m} {η : ℝ}
    (hη : 0 ≤ η) (h : Close x w η) (v : Fin n → ℝ) :
    |qform (x.lowerPencil H) v-qform (w.lowerPencil H) v| ≤
      (n : ℝ)*η*(∑i, (centering n *ᵥ v) i^2) := by
  simpa only [lowerPencil,qform_sub,sub_sub_sub_cancel_right] using h.qform_bound hη v

lemma Close.upper_error (H : MultiGraph n m) {x w : StepFree n m} {η : ℝ}
    (hη : 0 ≤ η) (h : Close x w η) (v : Fin n → ℝ) :
    |qform (x.upperPencil H) v-qform (w.upperPencil H) v| ≤
      ((n : ℝ)+6*(n : ℝ)^3)*η*(∑i, (centering n *ᵥ v) i^2) := by
  have h1 := h.qform_bound hη v
  have h2 := abs_triangle_sum hη h.2.1 v
  have he : qform (∑ijk, (x.multiplier ijk-w.multiplier ijk) • triangleGenerator ijk) v=
      qform (∑ijk, x.multiplier ijk • triangleGenerator ijk) v-
      qform (∑ijk, w.multiplier ijk • triangleGenerator ijk) v := by
    simp only [sub_smul,sum_sub_distrib,qform_sub]
  rw [he] at h2
  simp only [upperPencil,qform_sub]
  have hb : ∀a b c d e : ℝ, |a-b-c-(a-d-e)| ≤ |b-d|+|c-e| := by
    intro a b c d e
    have h := abs_add_le (b-d) (c-e)
    rwa [show a-b-c-(a-d-e) = -((b-d)+(c-e)) by ring,abs_neg]
  exact (hb _ _ _ _ _).trans (by nlinarith only [h1,h2])

lemma Close.edge_error (H : MultiGraph n m) {x w : StepFree n m} {η : ℝ}
    {s : ℝ} (hs : 0 ≤ s) (hη : 0 ≤ η) (h : Close x w η) (e : Fin m) (v : Fin n → ℝ) :
    |qform (x.edgePencil H s e) v-qform (w.edgePencil H s e) v| ≤
      ((n : ℝ)+12*s)*η*(∑i, (centering n *ᵥ v) i^2) := by
  have h1 := h.qform_bound hη v
  have h2 := difference_outer_centered (H.loopless e) v
  have hn := qform_nonneg (ShortcutDual.outer_posSemidef (H.incidence e)) v
  have hy := h.2.2.1 e
  have hr : |6*s*(x.y e-w.y e)*qform (vecMulVec (H.incidence e) (H.incidence e)) v| ≤
      12*s*η*(∑i, (centering n *ᵥ v) i^2) := by
    rw [abs_mul,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 6*s),abs_of_nonneg hn]
    have hb := mul_le_mul hy h2 hn hη
    change |x.y e-w.y e| *qform (vecMulVec (H.incidence e) (H.incidence e)) v ≤ _ at hb
    nlinarith only [mul_le_mul_of_nonneg_left hb (show 0 ≤ 6*s by positivity)]
  simp only [edgePencil,qform_sub,qform_smul]
  have hrewrite : qform x.matrix v-6*s*x.y e*qform (vecMulVec (H.incidence e) (H.incidence e)) v-
      (qform w.matrix v-6*s*w.y e*qform (vecMulVec (H.incidence e) (H.incidence e)) v)=
      (qform x.matrix v-qform w.matrix v)-6*s*(x.y e-w.y e)*qform (vecMulVec (H.incidence e) (H.incidence e)) v := by ring
  rw [hrewrite]
  exact (abs_sub _ _).trans (by nlinarith only [h1,hr])

end StepFree

lemma scaled_inverse_power {P c : ℝ} (hP : 0 < P) (a b : ℕ) (hc : c ≤ P^b) :
    c*P^(-((a+b : ℕ) : ℤ)) ≤ P^(-(a : ℤ)) := by
  have h := mul_le_mul_of_nonneg_right hc (zpow_nonneg hP.le (-((a+b : ℕ) : ℤ)))
  calc
    _ ≤ P^b*P^(-((a+b : ℕ) : ℤ)) := h
    _ = _ := by
      rw [←zpow_natCast,←zpow_add₀ (ne_of_gt hP)]
      congr 1
      push_cast
      ring

lemma inverse_power_mono {P : ℝ} (hP : 1 ≤ P) {a b : ℕ} (hab : a ≤ b) :
    P^(-(b : ℤ)) ≤ P^(-(a : ℤ)) := by
  simp only [_root_.zpow_neg,zpow_natCast]
  exact (inv_le_inv₀ (pow_pos (lt_of_lt_of_le zero_lt_one hP) _)
    (pow_pos (lt_of_lt_of_le zero_lt_one hP) _)).mpr (pow_le_pow_right₀ hP hab)

lemma auxiliary_numbers {P s κ : ℝ} (hP : 5 ≤ P) (hnP : (n : ℝ) ≤ P)
    (_hs : 0 ≤ s) (hsP : s ≤ P) (hκ : P⁻¹ ≤ κ) :
    let c := P^(-8 : ℤ)
    let η := P^(-20 : ℤ)
    let μ := P^(-3 : ℤ)
    0 < c ∧ 0 < η ∧ η ≤ c ∧ c+η ≤ 1 ∧ 4*η ≤ κ ∧
      (n : ℝ)*η ≤ μ ∧
      (n : ℝ)*η+6*(n : ℝ)^3*(c+η) ≤ μ ∧
      (n : ℝ)*η+12*s*(c+η) ≤ 2*μ := by
  dsimp only
  have hP0 : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have hc0 := zpow_pos hP0 (-8)
  have hη0 := zpow_pos hP0 (-20)
  have hηc : P^(-20 : ℤ) ≤ P^(-8 : ℤ) := inverse_power_mono hP1 (by norm_num : 8 ≤ 20)
  have hP2 : 25 ≤ P^2 := by nlinarith only [hP,sq_nonneg (P-5)]
  have hP4 : 25 ≤ P^4 := by
    have hh : P^2 ≤ P^4 := pow_le_pow_right₀ hP1 (by norm_num)
    exact hP2.trans hh
  have hsmall := scaled_inverse_power hP0 0 8 (show (2 : ℝ) ≤ P^8 by
    exact (by linarith : (2 : ℝ) ≤ P).trans (by simpa using pow_le_pow_right₀ hP1 (by norm_num : 1 ≤ 8)))
  simp only [Nat.cast_zero,Nat.zero_add,neg_zero,zpow_zero,Nat.cast_ofNat] at hsmall
  have hfour : 4*P^(-20 : ℤ) ≤ P⁻¹ := by
    have hh := scaled_inverse_power hP0 1 19 (show (4 : ℝ) ≤ P^19 by
      exact (by linarith : (4 : ℝ) ≤ P).trans (by simpa using pow_le_pow_right₀ hP1 (by norm_num : 1 ≤ 19)))
    simpa using hh
  have hnη : (n : ℝ)*P^(-20 : ℤ) ≤ P^(-8 : ℤ) := by
    calc
      _ ≤ P*P^(-20 : ℤ) := mul_le_mul_of_nonneg_right hnP hη0.le
      _ = P^(-19 : ℤ) := by simpa using (zpow_add₀ (ne_of_gt hP0) 1 (-20)).symm
      _ ≤ _ := inverse_power_mono hP1 (by norm_num : 8 ≤ 19)
  have hn3 : (n : ℝ)^3 ≤ P^3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hnP 3
  have hP3 : 1 ≤ P^3 := one_le_pow₀ hP1
  have hu : 13*P^(-5 : ℤ) ≤ P^(-3 : ℤ) := by
    simpa using scaled_inverse_power hP0 3 2 (show (13 : ℝ) ≤ P^2 by linarith)
  have he : 25*P^(-7 : ℤ) ≤ P^(-3 : ℤ) := by
    simpa using scaled_inverse_power hP0 3 4 hP4
  have hupper : (n : ℝ)*P^(-20 : ℤ)+6*(n : ℝ)^3*(P^(-8 : ℤ)+P^(-20 : ℤ)) ≤ P^(-3 : ℤ) := by
    calc
      _ ≤ P^(-8 : ℤ)+12*P^3*P^(-8 : ℤ) := by
        have hh := mul_le_mul hn3 (show P^(-8 : ℤ)+P^(-20 : ℤ) ≤ 2*P^(-8 : ℤ) by linarith)
          (by positivity) (by positivity : 0 ≤ P^3)
        nlinarith only [hnη,hh]
      _ ≤ 13*P^3*P^(-8 : ℤ) := by nlinarith only [mul_le_mul_of_nonneg_right hP3 hc0.le]
      _ = 13*P^(-5 : ℤ) := by rw [mul_assoc,←zpow_natCast,←zpow_add₀ (ne_of_gt hP0)]; norm_num
      _ ≤ _ := hu
  have hedge : (n : ℝ)*P^(-20 : ℤ)+12*s*(P^(-8 : ℤ)+P^(-20 : ℤ)) ≤ P^(-3 : ℤ) := by
    calc
      _ ≤ P^(-8 : ℤ)+24*P*P^(-8 : ℤ) := by
        have hh := mul_le_mul hsP (show P^(-8 : ℤ)+P^(-20 : ℤ) ≤ 2*P^(-8 : ℤ) by linarith)
          (by positivity) hP0.le
        nlinarith only [hnη,hh]
      _ ≤ 25*P*P^(-8 : ℤ) := by nlinarith only [mul_le_mul_of_nonneg_right hP1 hc0.le]
      _ = 25*P^(-7 : ℤ) := by
        rw [mul_assoc]
        congr 1
        simpa using (zpow_add₀ (ne_of_gt hP0) 1 (-8)).symm
      _ ≤ _ := he
  exact ⟨hc0,hη0,hηc,by linarith,hfour.trans hκ,
    hnη.trans (inverse_power_mono hP1 (by norm_num : 3 ≤ 8)),hupper,
    hedge.trans (le_mul_of_one_le_left (zpow_nonneg hP0.le _) (by norm_num))⟩

def auxiliaryPoint (H : MultiGraph n m) (κ : ℝ) : StepFree n m :=
  ((2 : ℝ) • H.laplacian univ,fun _ => (graphSize n m)^(-8 : ℤ),
    fun _ => (graphSize n m)^(-8 : ℤ),fun _ => κ/2)

lemma auxiliaryPoint_matrix (H : MultiGraph n m) {κ : ℝ} :
    (auxiliaryPoint H κ).matrix=(2 : ℝ) • H.laplacian univ := by
  apply responseMatrix_fixed ((H.laplacian_psd univ).smul (by norm_num : (0 : ℝ) ≤ 2)).isHermitian
  rw [smul_mulVec,laplacian_ones,smul_zero]

lemma connected_size_five (H : MultiGraph n m) (hn : 2 ≤ n) (hc : H.Connected univ) :
    5 ≤ graphSize n m := by
  have hm : 0 < m := by
    have hproper : ({⟨0,by omega⟩} : Finset (Fin n)) ≠ univ := by
      intro h
      have hh := congrArg Finset.card h
      simp only [card_singleton,card_univ,Fintype.card_fin] at hh
      omega
    obtain ⟨e,_⟩ := hc _ (singleton_nonempty _) hproper
    exact Nat.zero_lt_of_lt e.isLt
  dsimp [graphSize]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  linarith

lemma baseline_lower : (graphSize n m)⁻¹ ≤ continuationBaseline m := by
  rw [continuationBaseline,one_div]
  exact (inv_le_inv₀ graphSize_pos (by positivity : (0 : ℝ) < m+1)).mpr (by
    dsimp [graphSize]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith)

theorem auxiliary_cube (H : MultiGraph n m) (hn : 2 ≤ n) (hc : H.Connected univ)
    {s : ℝ} (hs : 0 ≤ s) (hsP : s ≤ graphSize n m)
    (u : Fin m → ℝ) (hu0 : ∀e, 0 ≤ u e)
    {x : StepFree n m}
    (hx : x.Close (auxiliaryPoint H (continuationBaseline m)) ((graphSize n m)^(-20 : ℤ))) :
    x ∈ stepCore H s (continuationBaseline m) (continuationStep m) u := by
  let P := graphSize n m
  let c := P^(-8 : ℤ)
  let η := P^(-20 : ℤ)
  let μ := P^(-3 : ℤ)
  let κ := continuationBaseline m
  have hP := connected_size_five H hn hc
  have hnP : (n : ℝ) ≤ P := by dsimp [P,graphSize]; linarith [Nat.cast_nonneg (α:=ℝ) m]
  obtain ⟨hc0,hη0,hηc,hcy,hηκ,hl,hu,he⟩ := auxiliary_numbers hP hnP hs hsP (baseline_lower (n:=n) (m:=m))
  have hκ0 : 0 < κ := (continuation_parameters m).1
  have hlam (ijk : DistinctTriple n) : 0 ≤ x.multiplier ijk ∧ |x.multiplier ijk| ≤ c+η := by
    have hh := abs_le.mp (hx.2.1 ijk)
    change -(η) ≤ x.multiplier ijk-c ∧ x.multiplier ijk-c ≤ η at hh
    have hl : 0 ≤ x.multiplier ijk := by linarith only [hh.1,hηc]
    refine ⟨hl,?_⟩
    rw [abs_of_nonneg hl]
    linarith only [hh.2]
  have hy (e : Fin m) : 0 ≤ x.y e ∧ x.y e ≤ c+η := by
    have hh := abs_le.mp (hx.2.2.1 e)
    change -η ≤ x.y e-c ∧ x.y e-c ≤ η at hh
    constructor <;> linarith only [hh.1,hh.2,hηc]
  have hz (e : Fin m) : κ/2-η ≤ x.z e ∧ x.z e ≤ κ/2+η := by
    have hh := abs_le.mp (hx.2.2.2 e)
    change -η ≤ x.z e-κ/2 ∧ x.z e-κ/2 ≤ η at hh
    constructor <;> linarith only [hh.1,hh.2]
  have henergy (v : Fin n → ℝ) : μ*(∑i, (centering n *ᵥ v) i^2) ≤ qform (H.laplacian univ) v := by
    simpa only [qform_smul,qform_centering_sum_sq (by omega : 0 < n)] using
      qform_mono (laplacian_lower_order H (by omega) hc) v
  have herror (v : Fin n → ℝ) :
      |qform x.matrix v-2*qform (H.laplacian univ) v| ≤
        (n : ℝ)*η*(∑i, (centering n *ᵥ v) i^2) := by
    simpa only [auxiliaryPoint_matrix,qform_smul] using hx.qform_bound hη0.le v
  refine ⟨?_,?_,fun ijk => (hlam ijk).1,fun e => ⟨(hy e).1,(hy e).2.trans hcy⟩,?_,?_⟩
  · apply PosSemidef.of_dotProduct_mulVec_nonneg (lowerPencil_hermitian H x)
    intro v
    change 0 ≤ qform (x.lowerPencil H) v
    rw [StepFree.lowerPencil,qform_sub]
    have hb := (abs_le.mp (herror v)).1
    have he := mul_le_mul_of_nonneg_right hl (show 0 ≤ ∑i, (centering n *ᵥ v) i^2 by positivity)
    linarith only [hb,he,henergy v]
  · apply PosSemidef.of_dotProduct_mulVec_nonneg (upperPencil_hermitian H x)
    intro v
    change 0 ≤ qform (x.upperPencil H) v
    rw [StepFree.upperPencil,qform_sub,qform_sub,qform_smul]
    have hb := (abs_le.mp (herror v)).2
    have hT := (abs_le.mp (abs_triangle_sum (show 0 ≤ c+η by positivity) (fun ijk => (hlam ijk).2) v)).2
    have he := mul_le_mul_of_nonneg_right hu (show 0 ≤ ∑i, (centering n *ᵥ v) i^2 by positivity)
    change ((n : ℝ)*η+6*(n : ℝ)^3*(c+η))*(∑i, (centering n *ᵥ v) i^2) ≤ _ at he
    linarith only [hb,hT,he,henergy v]
  · intro e
    exact ⟨by linarith only [(hz e).1,hηκ,hκ0],by linarith only [(hz e).2,hηκ,hκ0]⟩
  · intro e _
    refine ⟨?_,?_⟩
    · apply PosSemidef.of_dotProduct_mulVec_nonneg (edgePencil_hermitian H s x e)
      intro v
      change 0 ≤ qform (x.edgePencil H s e) v
      rw [StepFree.edgePencil,qform_sub,qform_smul]
      have hb := (abs_le.mp (herror v)).1
      have hE : 0 ≤ ∑i, (centering n *ᵥ v) i^2 := by positivity
      have hn0 := qform_nonneg (ShortcutDual.outer_posSemidef (H.incidence e)) v
      have hR := mul_le_mul (hy e).2 (difference_outer_centered (H.loopless e) v) hn0 (by positivity : 0 ≤ c+η)
      have hR' := mul_le_mul_of_nonneg_left hR (show 0 ≤ 6*s by positivity)
      change 6*s*(x.y e*qform (vecMulVec (H.incidence e) (H.incidence e)) v) ≤ _ at hR'
      have he' := mul_le_mul_of_nonneg_right he hE
      change ((n : ℝ)*η+12*s*(c+η))*(∑i, (centering n *ᵥ v) i^2) ≤ _ at he'
      linarith only [hb,hR',he',henergy v]
    · have hgain : 0 ≤ (κ/32)*x.y e := mul_nonneg (by positivity) (hy e).1
      change x.z e ≤ κ+u e+(κ/32)*(5*x.y e-4)
      nlinarith only [(hz e).2,hηκ,hκ0,hu0 e,hgain]

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
