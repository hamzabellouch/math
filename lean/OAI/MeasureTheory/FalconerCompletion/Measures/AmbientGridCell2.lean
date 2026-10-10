import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphJetMul

namespace OAI

/-! Measures and the conditional distance-set completion. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set MeasureTheory Metric

def ambientGridCell {d : ℕ} (n : ℕ) (a : Fin d → ℤ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, (a i : ℝ) ≤ (2:ℝ)^n*x i ∧ (2:ℝ)^n*x i < (a i : ℝ)+1}

lemma mem_ambientGridCell_iff {d n : ℕ} {a : Fin d → ℤ}
    {x : EuclideanSpace ℝ (Fin d)} :
    x ∈ ambientGridCell n a ↔ ∀ i, ⌊(2:ℝ)^n*x i⌋ = a i := by
  simp only [ambientGridCell,mem_ofPred_eq,Int.floor_eq_iff]

lemma measurableSet_ambientGridCell {d : ℕ} (n : ℕ) (a : Fin d → ℤ) :
    MeasurableSet (ambientGridCell n a) := by
  have he : ambientGridCell n a = ⋂ i : Fin d,
      {x : EuclideanSpace ℝ (Fin d) | (a i : ℝ) ≤ (2:ℝ)^n*x i} ∩
      {x : EuclideanSpace ℝ (Fin d) | (2:ℝ)^n*x i < (a i : ℝ)+1} := by
    ext x; simp only [ambientGridCell,mem_iInter,mem_inter_iff,mem_ofPred_eq]
  rw [he]
  apply MeasurableSet.iInter
  intro i
  exact (isClosed_le continuous_const (continuous_const.mul (EuclideanSpace.proj i).continuous)).measurableSet.inter
    ((isOpen_lt (continuous_const.mul (EuclideanSpace.proj i).continuous) continuous_const).measurableSet)

lemma ambientGridCell_disjoint {d n : ℕ} {a b : Fin d → ℤ} (hab : a ≠ b) :
    Disjoint (ambientGridCell n a) (ambientGridCell n b) := by
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  apply hab
  funext i
  exact ((mem_ambientGridCell_iff.mp hxa) i).symm.trans ((mem_ambientGridCell_iff.mp hxb) i)

lemma ambientGridCell_dist_le {d n : ℕ} {a : Fin d → ℤ}
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ ambientGridCell n a)
    (hy : y ∈ ambientGridCell n a) :
    dist y x ≤ (d+1:ℝ)/(2:ℝ)^n := by
  have ht : 0 < (2:ℝ)^n := by positivity
  have hcoord (i : Fin d) : |y i-x i| ≤ 1/(2:ℝ)^n := by
    rw [abs_le]
    constructor
    · rw [show -(1/(2:ℝ)^n)=(-1)/(2:ℝ)^n by ring]
      apply (div_le_iff₀ ht).mpr
      have h1 := (hx i).2
      have h2 := (hy i).1
      nlinarith
    · apply (le_div_iff₀ ht).mpr
      have h1 := (hy i).2
      have h2 := (hx i).1
      nlinarith
  have hsq : dist y x^2 ≤ (d:ℝ)*(1/(2:ℝ)^n)^2 := by
    rw [EuclideanSpace.dist_sq_eq]
    calc
      _ ≤ ∑ _ : Fin d, (1/(2:ℝ)^n)^2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [Real.dist_eq,sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) (by positivity : (0:ℝ) ≤ 1/(2:ℝ)^n)).mpr (hcoord i)
      _ = _ := by simp
  have hh : (d:ℝ)*(1/(2:ℝ)^n)^2 ≤ ((d+1:ℝ)/(2:ℝ)^n)^2 := by
    have hd : 0 ≤ (d:ℝ) := by positivity
    have hd' : (d:ℝ) ≤ (d+1:ℝ)^2 := by nlinarith
    calc
      _ ≤ (d+1:ℝ)^2*(1/(2:ℝ)^n)^2 := mul_le_mul_of_nonneg_right hd' (sq_nonneg _)
      _ = _ := by ring
  exact (sq_le_sq₀ dist_nonneg (by positivity)).mp (hsq.trans hh)

lemma ambientGridCell_subset_ancestor {d m n : ℕ} (hnm : n ≤ m) (a : Fin d → ℤ) :
    ambientGridCell m a ⊆ ambientGridCell n (fun i => a i/(2:ℤ)^(m-n)) := by
  intro x hx
  apply mem_ambientGridCell_iff.mpr
  intro i
  have hf := Int.floor_div_natCast ((2:ℝ)^m*x i) (2^(m-n))
  rw [(mem_ambientGridCell_iff.mp hx) i] at hf
  have he : (2:ℝ)^m*x i/(2^(m-n):ℕ) = (2:ℝ)^n*x i := by
    have hpow : (2:ℝ)^m=(2:ℝ)^n*(2:ℝ)^(m-n) := by
      rw [← pow_add,Nat.add_sub_of_le hnm]
    rw [Nat.cast_pow,Nat.cast_ofNat,hpow]
    field_simp
  rw [he] at hf
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using hf

noncomputable def ambientGridCenter {d : ℕ} (n : ℕ) (a : Fin d → ℤ) :
    EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun i => ((a i : ℝ)+1/2)/(2:ℝ)^n)

lemma ambientGridCenter_apply {d : ℕ} (n : ℕ) (a : Fin d → ℤ) (i : Fin d) :
    ambientGridCenter n a i = ((a i : ℝ)+1/2)/(2:ℝ)^n := rfl

lemma ambientGridCenter_mem {d : ℕ} (n : ℕ) (a : Fin d → ℤ) :
    ambientGridCenter n a ∈ ambientGridCell n a := by
  intro i
  change (a i:ℝ) ≤ (2:ℝ)^n*(((a i:ℝ)+1/2)/(2:ℝ)^n) ∧
    (2:ℝ)^n*(((a i:ℝ)+1/2)/(2:ℝ)^n) < (a i:ℝ)+1
  have ht : (2:ℝ)^n ≠ 0 := by positivity
  field_simp
  constructor <;> linarith

lemma ambientGridCenter_injective {d : ℕ} (n : ℕ) :
    Function.Injective (ambientGridCenter (d := d) n) := by
  intro a b hab
  have hx := ambientGridCell_disjoint (n := n) (a := a) (b := b)
  by_contra hne
  exact Set.disjoint_left.mp (hx hne) (ambientGridCenter_mem n a)
    (hab.symm ▸ ambientGridCenter_mem n b)

lemma ambientGridCenter_coordinate_bound {d n : ℕ} {a : Fin d → ℤ}
    {x : EuclideanSpace ℝ (Fin d)} {r : ℝ} (h : dist (ambientGridCenter n a) x ≤ r)
    (i : Fin d) : |(a i:ℝ)+1/2-(2:ℝ)^n*x i| ≤ (2:ℝ)^n*r := by
  have hc : |ambientGridCenter n a i-x i| ≤ r := by
    exact (PiLp.norm_apply_le (ambientGridCenter n a-x) i).trans h
  have ht : 0 < (2:ℝ)^n := by positivity
  have hc' := mul_le_mul_of_nonneg_left hc ht.le
  rw [← abs_of_pos ht,← abs_mul] at hc'
  rw [abs_of_pos ht] at hc'
  convert hc' using 1
  congr 1
  rw [ambientGridCenter_apply]
  field_simp

lemma ambientGridCenter_index_bounds {d n : ℕ} {a : Fin d → ℤ}
    {x : EuclideanSpace ℝ (Fin d)} {r : ℝ} (h : dist (ambientGridCenter n a) x ≤ r)
    (i : Fin d) :
    ⌊(2:ℝ)^n*x i⌋-(⌈(2:ℝ)^n*r+1⌉₊:ℤ) ≤ a i ∧
    a i ≤ ⌊(2:ℝ)^n*x i⌋+(⌈(2:ℝ)^n*r+1⌉₊:ℤ) := by
  have hh := abs_le.mp (ambientGridCenter_coordinate_bound h i)
  have hf := Int.floor_le ((2:ℝ)^n*x i)
  have hf' := Int.lt_floor_add_one ((2:ℝ)^n*x i)
  have hK := Nat.le_ceil ((2:ℝ)^n*r+1)
  constructor <;> apply (Int.cast_le (R := ℝ)).mp <;> push_cast <;> linarith

theorem ambientGridCenter_ball_card {d : ℕ} (n : ℕ) (P : Finset (Fin d → ℤ))
    (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 ≤ r)
    (hP : ∀ a ∈ P, dist (ambientGridCenter n a) x ≤ r) :
    (P.card : ℝ) ≤ (2*(2:ℝ)^n*r+5)^d := by
  classical
  let K : ℕ := ⌈(2:ℝ)^n*r+1⌉₊
  let F : Fin d → ℤ := fun i => ⌊(2:ℝ)^n*x i⌋
  let B := Fintype.piFinset (fun i : Fin d => Finset.Icc (F i-(K:ℤ)) (F i+K))
  have hPB : P ⊆ B := by
    intro a ha
    simp only [B,Fintype.mem_piFinset,Finset.mem_Icc]
    exact fun i => ambientGridCenter_index_bounds (hP a ha) i
  have hBc : B.card=(2*K+1)^d := by
    have hI (i : Fin d) : (Finset.Icc (F i-(K:ℤ)) (F i+K)).card=2*K+1 := by
      rw [Int.card_Icc]
      have he : (F i+(K:ℤ)+1-(F i-K)) = (2*K+1:ℕ) := by push_cast; ring
      rw [he,Int.toNat_natCast]
    simp [B,Fintype.card_piFinset,hI]
  have hK : (K:ℝ) ≤ (2:ℝ)^n*r+2 := by
    have hh := (Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ (2:ℝ)^n*r+1)).le
    dsimp [K]; linarith
  calc
    _ ≤ (((2*K+1)^d:ℕ):ℝ) := by exact_mod_cast (Finset.card_le_card hPB).trans_eq hBc
    _ = (2*(K:ℝ)+1)^d := by push_cast; rfl
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (by linarith) d

theorem translated_ambientGridCenter_ball_card {d : ℕ} (n : ℕ)
    (P : Finset (Fin d → ℤ)) (b x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 ≤ r)
    (hP : ∀ a ∈ P, dist (b+ambientGridCenter n a) x ≤ r) :
    (P.card : ℝ) ≤ (2*(2:ℝ)^n*r+5)^d := by
  apply ambientGridCenter_ball_card n P (x-b) hr
  intro a ha
  convert hP a ha using 1
  rw [dist_eq_norm,dist_eq_norm]
  congr 1
  abel

noncomputable def ambientAncestor {d : ℕ} (p g : ℕ) (a : Fin d → ℤ) : Fin d → ℤ :=
  fun i => a i/(2:ℤ)^(p-g)

lemma ambientGridCenter_mem_ancestor {d p g : ℕ} (hgp : g ≤ p) (a : Fin d → ℤ) :
    ambientGridCenter p a ∈ ambientGridCell g (ambientAncestor p g a) :=
  ambientGridCell_subset_ancestor hgp a (ambientGridCenter_mem p a)

lemma ambientAncestor_comp {d p g a : ℕ} (hag : a ≤ g) (hgp : g ≤ p)
    (c : Fin d → ℤ) : ambientAncestor g a (ambientAncestor p g c)=ambientAncestor p a c := by
  have h1 := ambientGridCell_subset_ancestor hag (ambientAncestor p g c)
    (ambientGridCenter_mem_ancestor hgp c)
  have h2 := ambientGridCenter_mem_ancestor (hag.trans hgp) c
  funext i
  exact ((mem_ambientGridCell_iff.mp h1) i).symm.trans ((mem_ambientGridCell_iff.mp h2) i)

lemma ambientAncestor_coordinate {d p g : ℕ} {a b : Fin d → ℤ}
    (h : ambientAncestor p g a=b) (i : Fin d) :
    b i*(2:ℤ)^(p-g) ≤ a i ∧ a i ≤ (b i+1)*(2:ℤ)^(p-g)-1 := by
  have he : a i/(2:ℤ)^(p-g)=b i := congrFun h i
  have hl := Int.ediv_mul_le (a i) (by positivity : (2:ℤ)^(p-g) ≠ 0)
  have hu := Int.lt_ediv_add_one_mul_self (a i) (by positivity : (0:ℤ) < (2:ℤ)^(p-g))
  rw [he] at hl hu
  exact ⟨hl,by omega⟩

theorem ambientAncestor_fiber_card {d : ℕ} (p g : ℕ) (b : Fin d → ℤ)
    (P : Finset (Fin d → ℤ)) (hP : ∀ a ∈ P, ambientAncestor p g a=b) :
    P.card ≤ 2^((p-g)*d) := by
  classical
  let M : ℕ := 2^(p-g)
  let B := Fintype.piFinset (fun i : Fin d => Finset.Icc (b i*(M:ℤ)) ((b i+1)*M-1))
  have hPB : P ⊆ B := by
    intro a ha
    simp only [B,Fintype.mem_piFinset,Finset.mem_Icc]
    intro i
    simpa [M] using ambientAncestor_coordinate (hP a ha) i
  have hBc : B.card=M^d := by
    have hI (i : Fin d) : (Finset.Icc (b i*(M:ℤ)) ((b i+1)*M-1)).card=M := by
      rw [Int.card_Icc]
      have he : (b i+1)*(M:ℤ)-1+1-b i*M=(M:ℤ) := by ring
      rw [he,Int.toNat_natCast]
    simp [B,Fintype.card_piFinset,hI]
  calc
    _ ≤ B.card := Finset.card_le_card hPB
    _ = M^d := hBc
    _ = _ := by dsimp [M]; rw [← pow_mul]

lemma ambientAncestor_image_card {d p g a : ℕ} (hag : a ≤ g) (hgp : g ≤ p)
    (b : Fin d → ℤ) (P : Finset (Fin d → ℤ))
    (hP : ∀ c ∈ P, ambientAncestor p a c=b) :
    (P.image (ambientAncestor p g)).card ≤ 2^((g-a)*d) := by
  classical
  apply ambientAncestor_fiber_card g a b
  intro c hc
  obtain ⟨c,hcP,rfl⟩ := Finset.mem_image.mp hc
  rw [ambientAncestor_comp hag hgp,hP c hcP]

end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI
