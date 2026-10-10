import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Freeze
import OAI.Combinatorics.KMedianRecovery.Recovery.Height

namespace OAI

namespace MetricKMedianRecovery.BirdRational
open Matrix RationalHeight
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]

def commonDen (q : J → ℚ) : ℤ := ∏ i, ((q i).den:ℤ)
def scaled (q : J → ℚ) (i : J) : ℤ :=
  (q i).num * ∏ j ∈ Finset.univ.erase i, ((q j).den:ℤ)

omit [DecidableEq J] in
lemma commonDen_pos (q : J → ℚ) : 0<commonDen q := by
  exact Finset.prod_pos (fun i _ => by exact_mod_cast (q i).den_pos)

lemma scaled_cast (q : J → ℚ) (i : J) :
    (scaled q i:ℚ)=(commonDen q:ℚ)*q i := by
  have hh : commonDen q = (q i).den * ∏ j ∈ Finset.univ.erase i, ((q j).den:ℤ) :=
    (Finset.mul_prod_erase Finset.univ (fun j => ((q j).den:ℤ)) (Finset.mem_univ i)).symm
  have hn : ((q i).den:ℚ)≠0 := by exact_mod_cast (q i).den_nz
  calc
    _ = (commonDen q:ℚ)*((q i).num/(q i).den) := by
      rw [hh]
      unfold scaled
      push_cast
      field_simp
    _ = _ := by rw [Rat.num_div_den]

lemma scaled_height (q : J → ℚ) (a : ℕ) (hq : ∀ i,Height (q i) a) (i : J) :
    (scaled q i).natAbs≤2^((Fintype.card J+1)*a) := by
  have hp : (∏ j∈Finset.univ.erase i,((q j).den:ℤ)).natAbs≤2^(Fintype.card J*a) := by
    rw [show (∏ j∈Finset.univ.erase i,((q j).den:ℤ)).natAbs =
      ∏ j∈Finset.univ.erase i,((q j).den:ℤ).natAbs from map_prod Int.natAbsHom _ _]
    calc
      _ ≤ ∏ _j∈Finset.univ.erase i,2^a := by
        apply Finset.prod_le_prod
        intro j _
        simpa only [Int.natAbs_natCast] using (hq j).2
      _ = 2^((Finset.univ.erase i).card*a) := by rw [Finset.prod_const,←pow_mul]; congr 1; ring
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right a (Finset.card_le_univ _))
  rw [scaled,Int.natAbs_mul]
  calc
    _ ≤ 2^a*2^(Fintype.card J*a) := Nat.mul_le_mul (hq i).1 hp
    _ = _ := by rw [←pow_add]; congr 1; ring

lemma intCast_height (z : ℤ) (a : ℕ) (hz : z.natAbs≤2^a) : Height (z:ℚ) a := by
  constructor
  · simpa using hz
  · simpa using (one_le_pow₀ (by norm_num : (1:ℕ)≤2) : 1≤2^a)

def data {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
    (Fin n × Option (Fin n)) → ℚ := fun ⟨i,j⟩ => match j with
  | none => b i
  | some j => A i j

def integerMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) : Matrix (Fin n) (Fin n) ℤ :=
  BirdInteger.freeze (Matrix.of (fun i j => scaled (data A b) (i,some j)))

def integerVector {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) : Fin n → ℤ :=
  let ar := Vector.ofFn (fun i => scaled (data A b) (i,none))
  fun i => ar[i]

lemma integerMatrix_cast {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
    ((integerMatrix A b).map (Int.cast : ℤ → ℚ))=(commonDen (data A b):ℚ) • A := by
  ext i j
  change ((BirdInteger.freeze (Matrix.of (fun i j => scaled (data A b) (i,some j)))) i j:ℚ) = _
  rw [BirdInteger.freeze_eq]
  exact scaled_cast (data A b) (i,some j)
lemma integerVector_cast {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
    (fun i => (integerVector A b i:ℚ))=(commonDen (data A b):ℚ) • b := by
  ext i
  simp [integerVector,scaled_cast,Pi.smul_apply,smul_eq_mul,data]

def solve {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) : Fin n → ℚ :=
  let Z := integerMatrix A b
  let w := integerVector A b
  let d := BirdInteger.determinant Z
  let ar := Vector.ofFn (fun i =>
    (BirdInteger.determinant (BirdInteger.freeze (Z.updateCol i w)):ℚ)/(d:ℚ))
  fun i => ar[i]

lemma solve_as_cramer {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
    solve A b =
      (Matrix.det ((integerMatrix A b).map (Int.cast : ℤ → ℚ)))⁻¹ •
        (Matrix.cramer ((integerMatrix A b).map (Int.cast : ℤ → ℚ)) (fun i => (integerVector A b i:ℚ))) := by
  funext i
  simp [solve,BirdInteger.determinant_eq,Matrix.cramer_apply,Int.cast_det,
    Matrix.map_updateCol,div_eq_mul_inv,mul_comm]
  left
  rfl

theorem solve_correct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ)
    (hA : A.det≠0) : A *ᵥ solve A b=b := by
  let D : ℚ := commonDen (data A b)
  have hD : D≠0 := by dsimp [D]; exact_mod_cast (commonDen_pos (data A b)).ne'
  have hZ : Matrix.det ((integerMatrix A b).map (Int.cast : ℤ → ℚ))≠0 := by
    rw [integerMatrix_cast,Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hD) hA
  have he : ((integerMatrix A b).map (Int.cast : ℤ → ℚ)) *ᵥ solve A b =
      (fun i => (integerVector A b i:ℚ)) := by
    rw [solve_as_cramer,Matrix.mulVec_smul,Matrix.mulVec_cramer,smul_smul,inv_mul_cancel₀ hZ,one_smul]
  rw [integerMatrix_cast,integerVector_cast,Matrix.smul_mulVec] at he
  funext i
  exact mul_left_cancel₀ hD (congrFun he i)

def clearedHeight (n a : ℕ) : ℕ := (n*(n+1)+1)*a
def detHeight (n a : ℕ) : ℕ := (n+1)*clearedHeight n a+n*(n+1)

lemma data_height {n a : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ)
    (hA : ∀ i j,Height (A i j) a) (hb : ∀ i,Height (b i) a) :
    ∀ x,Height (data A b x) a := by
  rintro ⟨i,j⟩
  cases j with
  | none => exact hb i
  | some j => exact hA i j

lemma integerMatrix_height {n a : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ)
    (hA : ∀ i j,Height (A i j) a) (hb : ∀ i,Height (b i) a) (i j : Fin n) :
    (integerMatrix A b i j).natAbs≤2^(clearedHeight n a) := by
  change (BirdInteger.freeze (Matrix.of (fun i j => scaled (data A b) (i,some j))) i j).natAbs≤_
  rw [BirdInteger.freeze_eq]
  simpa only [Matrix.of_apply,Fintype.card_prod,Fintype.card_option,Fintype.card_fin,clearedHeight] using
    scaled_height (data A b) a (data_height A b hA hb) (i,some j)

lemma integerVector_height {n a : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ)
    (hA : ∀ i j,Height (A i j) a) (hb : ∀ i,Height (b i) a) (i : Fin n) :
    (integerVector A b i).natAbs≤2^(clearedHeight n a) := by
  simpa only [integerVector,Fin.getElem_fin,Vector.getElem_ofFn,Fintype.card_prod,Fintype.card_option,
    Fintype.card_fin,clearedHeight] using scaled_height (data A b) a (data_height A b hA hb) (i,none)

lemma updated_height {n a : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ)
    (hA : ∀ i j,Height (A i j) a) (hb : ∀ i,Height (b i) a) (i j k : Fin n) :
    ((integerMatrix A b).updateCol i (integerVector A b) j k).natAbs≤2^(clearedHeight n a) := by
  by_cases hk : k=i
  · subst k
    simpa using integerVector_height A b hA hb j
  · simpa [Matrix.updateCol_ne hk] using integerMatrix_height A b hA hb j k

theorem solve_height {n a : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ)
    (hA : ∀ i j,Height (A i j) a) (hb : ∀ i,Height (b i) a) (i : Fin n) :
    Height (solve A b i) (2*detHeight n a) := by
  have hn := intCast_height _ _ (BirdInteger.determinant_height _ (updated_height A b hA hb i))
  have hd := intCast_height _ _ (BirdInteger.determinant_height _ (integerMatrix_height A b hA hb))
  simpa [solve,detHeight,two_mul] using hn.div hd

end MetricKMedianRecovery.BirdRational

end OAI
