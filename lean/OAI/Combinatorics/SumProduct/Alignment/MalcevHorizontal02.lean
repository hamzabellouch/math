import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.MalcevHorizontal01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open scoped BigOperators commutatorElement
noncomputable section
end
end
 

 
section
open scoped BigOperators commutatorElement
noncomputable section
namespace MalcevHorizontal
open RationalLattice CubeFaces LeibmanSquare SquareHorizontalCharacter
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {n d : ℕ} (c : RealCoordinates G n) (hd : d ≤ n)
variable (hlin : ∀ i : Fin d, c.correction (Fin.castLE hd i) = 0)

 

def character (k : Fin d → ℤ) : G →* Multiplicative ℝ where
  toFun g := Multiplicative.ofAdd (∑ i, (k i : ℝ) * horizontal c hd g i)
  map_one' := by simp [horizontal_one c hd]
  map_mul' a b := by
    change (∑ i, (k i : ℝ) * horizontal c hd (a*b) i) =
      (∑ i, (k i : ℝ) * horizontal c hd a i) + (∑ i, (k i : ℝ) * horizontal c hd b i)
    simp [horizontal_mul c hd hlin, mul_add, Finset.sum_add_distrib]

lemma character_continuous (k : Fin d → ℤ) : Continuous (character c hd hlin k) := by
  change Continuous (fun g => ∑ i, (k i : ℝ) * horizontal c hd g i)
  exact continuous_finsetSum _ fun i _ => continuous_const.mul
    ((continuous_apply i).comp (continuous_horizontal c hd))

@[simp] lemma character_basis (k : Fin d → ℤ) (j : Fin d) :
    Multiplicative.toAdd (character c hd hlin k
      (coordSection c hd (IntegralBilinear.basisVector j))) = (k j : ℝ) := by
  classical
  simp [character, horizontal_section, IntegralBilinear.basisVector, Pi.single_apply]

lemma character_ne_one {k : Fin d → ℤ} (hk : k ≠ 0) : character c hd hlin k ≠ 1 := by
  intro h
  apply hk
  funext j
  have hj := congrArg (fun f : G →* Multiplicative ℝ =>
      Multiplicative.toAdd (f (coordSection c hd (IntegralBilinear.basisVector j)))) h
  rw [character_basis] at hj
  change (k j : ℝ) = 0 at hj
  exact_mod_cast hj

lemma character_injective : Function.Injective (character c hd hlin) := by
  intro k l h
  funext j
  have hj := congrArg (fun f : G →* Multiplicative ℝ =>
      Multiplicative.toAdd (f (coordSection c hd (IntegralBilinear.basisVector j)))) h
  simp only [character_basis] at hj
  exact_mod_cast hj

variable (Γ : Subgroup G)
variable (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z)
include hΓ in
lemma character_integer (k : Fin d → ℤ) {g : G} (hg : g ∈ Γ) :
    ∃ z : ℤ, Multiplicative.toAdd (character c hd hlin k g) = z := by
  classical
  choose z hz using (hΓ g).mp hg
  refine ⟨∑ i, k i * z (Fin.castLE hd i), ?_⟩
  change (∑ i, (k i : ℝ) * horizontal c hd g i) = _
  simp only [Int.cast_sum, Int.cast_mul, horizontal, hz]

variable (H : Filtration G) (h0 : H.level 0 = ⊤) (h1 : H.level 1 = ⊤)
variable (ξ : level H h0 1 →* Multiplicative ℝ)
variable (M : Matrix (Fin d) (Fin d) ℤ)
variable (hM : ∀ a b : G, Multiplicative.toAdd (pairing H h0 h1 ξ a b) =
  ∑ i, ∑ j, horizontal c hd a i * (M i j : ℝ) * horizontal c hd b j)

include hM in
lemma matrix_entry (i j : Fin d) : (M i j : ℝ) =
    Multiplicative.toAdd (pairing H h0 h1 ξ
      (coordSection c hd (IntegralBilinear.basisVector i))
      (coordSection c hd (IntegralBilinear.basisVector j))) := by
  classical
  rw [hM]
  simp [horizontal_section, IntegralBilinear.basisVector, Pi.single_apply]

include hM in
lemma column_character (j : Fin d) (g : G) :
    character c hd hlin (fun i => M i j) g =
      pairing H h0 h1 ξ g (coordSection c hd (IntegralBilinear.basisVector j)) := by
  classical
  apply Multiplicative.toAdd.injective
  rw [hM]
  change (∑ i, (M i j : ℝ) * horizontal c hd g i) = _
  simp only [horizontal_section, IntegralBilinear.basisVector, Pi.single_apply]
  simp [mul_comm]

include hM in
lemma matrix_zero_iff : M = 0 ↔ ∀ a b : G, pairing H h0 h1 ξ a b = 1 := by
  constructor
  · intro hz a b
    apply Multiplicative.toAdd.injective
    rw [hM, hz]
    simp
  · intro h
    ext i j
    have hij := matrix_entry c hd H h0 h1 ξ M hM i j
    rw [h] at hij
    change (M i j : ℝ) = 0 at hij
    exact_mod_cast hij

include hM hΓ in
 

theorem nonzero_column (hM0 : M ≠ 0) (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ i j, |(M i j : ℝ)| ≤ A) :
    ∃ j : Fin d, character c hd hlin (fun i => M i j) ≠ 1 ∧
      Continuous (character c hd hlin (fun i => M i j)) ∧
      (∀ g ∈ Γ, ∃ z : ℤ, Multiplicative.toAdd
        (character c hd hlin (fun i => M i j) g) = z) ∧
      ‖(fun i => (M i j : ℝ))‖ ≤ A ∧
      ∀ g, character c hd hlin (fun i => M i j) g =
        pairing H h0 h1 ξ g (coordSection c hd (IntegralBilinear.basisVector j)) := by
  classical
  have hex : ∃ j : Fin d, (fun i => M i j) ≠ 0 := by
    by_contra! h
    apply hM0
    ext i j
    exact congrFun (h j) i
  obtain ⟨j,hj⟩ := hex
  exact ⟨j,character_ne_one c hd hlin hj, character_continuous c hd hlin _,
    fun g hg => character_integer c hd hlin Γ hΓ _ hg,
    (pi_norm_le_iff_of_nonneg hA).mpr (fun i => hbound i j),
    column_character c hd hlin H h0 h1 ξ M hM j⟩

 

def squareMatrixBound (Ξ : Finset (level H h0 1 →* Multiplicative ℝ)) : ℝ :=
  ∑ χ ∈ Ξ, ∑ i : Fin d, ∑ j : Fin d,
    |Multiplicative.toAdd (pairing H h0 h1 χ
      (coordSection c hd (IntegralBilinear.basisVector i))
      (coordSection c hd (IntegralBilinear.basisVector j)))|

lemma squareMatrixBound_nonneg (Ξ : Finset (level H h0 1 →* Multiplicative ℝ)) :
    0 ≤ squareMatrixBound c hd H h0 h1 Ξ := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _

include hM in
lemma matrix_bound (Ξ : Finset (level H h0 1 →* Multiplicative ℝ)) (hξ : ξ ∈ Ξ)
    (i j : Fin d) : |(M i j : ℝ)| ≤ squareMatrixBound c hd H h0 h1 Ξ := by
  let b (χ : level H h0 1 →* Multiplicative ℝ) (i j : Fin d) :=
    |Multiplicative.toAdd (pairing H h0 h1 χ
      (coordSection c hd (IntegralBilinear.basisVector i))
      (coordSection c hd (IntegralBilinear.basisVector j)))|
  have hb (χ : level H h0 1 →* Multiplicative ℝ) (i j : Fin d) : 0 ≤ b χ i j := abs_nonneg _
  rw [matrix_entry c hd H h0 h1 ξ M hM]
  change b ξ i j ≤ ∑ χ ∈ Ξ, ∑ a : Fin d, ∑ b' : Fin d, b χ a b'
  calc
    _ ≤ ∑ b' : Fin d, b ξ i b' := Finset.single_le_sum (fun j _ => hb ξ i j) (Finset.mem_univ j)
    _ ≤ ∑ a : Fin d, ∑ b' : Fin d, b ξ a b' :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun j _ => hb ξ a j) (Finset.mem_univ i)
    _ ≤ _ := Finset.single_le_sum (fun χ _ => Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun j _ => hb χ a j) hξ

end MalcevHorizontal
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial Finset
open scoped BigOperators
namespace PolynomialCharacterDescent

 

def shiftCoefficient (r : ℕ) (P Q : ℝ[X]) : ℝ[X] :=
  hasseDeriv r Q + C (P.coeff r-Q.coeff r)

lemma shiftCoefficient_eval (r : ℕ) (P Q : ℝ[X]) (h : ℝ) :
    (shiftCoefficient r P Q).eval h = (P+taylor h Q-Q).coeff r := by
  simp only [shiftCoefficient, eval_add, eval_C, coeff_sub, coeff_add, taylor_coeff]
  ring

lemma shiftCoefficient_degree (r : ℕ) (P Q : ℝ[X]) (d : ℕ) (hQ : Q.natDegree ≤ d) :
    (shiftCoefficient r P Q).natDegree ≤ d := by
  apply natDegree_add_le_of_degree_le
  · exact (natDegree_hasseDeriv_le Q r).trans ((Nat.sub_le _ _).trans hQ)
  · simp

lemma shiftCoefficient_coeff (r : ℕ) (P Q : ℝ[X]) (j : ℕ) (hj : 0 < j) :
    (shiftCoefficient r P Q).coeff j = ((j+r).choose r:ℝ)*Q.coeff (j+r) := by
  simp [shiftCoefficient,coeff_add,hasseDeriv_coeff,coeff_C,ne_of_gt hj]

lemma choose_dvd_factorial (r j d : ℕ) (hj : r ≤ j) (hjd : j ≤ d) :
    j.choose r ∣ d.factorial := by
  apply dvd_trans _ (Nat.factorial_dvd_factorial hjd)
  refine ⟨r.factorial*(j-r).factorial,?_⟩
  symm
  simpa only [Nat.mul_assoc] using Nat.choose_mul_factorial_mul_factorial hj

 

theorem shift_coefficients (d r : ℕ) (hr : 0 < r) (δ A : ℝ) (hδ : 0 < δ) (hA : 0 ≤ A) :
    ∃ B : ℕ, 0 < B ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ P Q : ℝ[X], Q.natDegree ≤ d →
        ∀ S : Finset ℕ, S ⊆ range N → δ*N ≤ (S.card:ℝ) →
        (∀ h ∈ S, ∃ z : ℤ, |(P+taylor (h:ℝ) Q-Q).coeff r-z| ≤ A/(N:ℝ)^r) →
        ∃ q : ℤ, q ≠ 0 ∧ |q| ≤ B ∧ ∀ j : ℕ, r < j → j ≤ d →
          ∃ m : ℤ, |(q:ℝ)*Q.coeff j-m| ≤ C/(N:ℝ)^j := by
  obtain ⟨B,hB,ε,hε,L,hL,hinv⟩ := DenseModularPolynomial.lattice_inverse d δ hδ
  obtain ⟨T,hT⟩ := exists_nat_gt (max 1 (A/ε))
  let N₀ := max L T
  let D := d.factorial
  have hD : 0 < D := Nat.factorial_pos _
  let C : ℝ := (B:ℝ)*A*D+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨B*D,Nat.mul_pos hB hD,C,hC,N₀,hL.trans_le (le_max_left _ _),?_⟩
  intro N hN₀ P Q hQ S hSN hS hsmall
  have hLN : L ≤ N := (le_max_left _ _).trans hN₀
  have hTN : T ≤ N := (le_max_right _ _).trans hN₀
  have hN : 0 < N := hL.trans_le hLN
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hTNr : (T:ℝ)≤N := by exact_mod_cast hTN
  have hAN : A/ε ≤ (N:ℝ) := (le_max_right _ _).trans (hT.le.trans hTNr)
  have hAN' : A ≤ ε*N := by nlinarith [(div_le_iff₀ hε).mp hAN]
  have heps : A/(N:ℝ)^r ≤ ε := by
    apply (div_le_iff₀ (pow_pos hNr r)).mpr
    have hp : (N:ℝ) ≤ (N:ℝ)^r := by
      simpa using pow_le_pow_right₀ hN1 (show 1 ≤ r from hr)
    exact hAN'.trans (mul_le_mul_of_nonneg_left hp hε.le)
  obtain ⟨q,hq,hqB,m,hm⟩ := hinv N hLN (A/(N:ℝ)^r) (by positivity) heps S hSN hS
    (shiftCoefficient r P Q) (shiftCoefficient_degree r P Q d hQ)
    (by intro h hh; simpa only [shiftCoefficient_eval] using hsmall h hh)
  refine ⟨q*D,mul_ne_zero hq (by exact_mod_cast Nat.ne_of_gt hD),?_,?_⟩
  · simpa only [abs_mul,Int.abs_natCast,Nat.cast_mul] using
      mul_le_mul_of_nonneg_right hqB (Int.natCast_nonneg D)
  · intro j hj hjd
    obtain ⟨t,ht⟩ := choose_dvd_factorial r j d (by omega) hjd
    have hc : 0 < j.choose r := Nat.choose_pos (by omega)
    have htD : t ≤ D := by
      change t ≤ d.factorial
      rw [ht]
      exact Nat.le_mul_of_pos_left t hc
    have htr : (t:ℝ)≤D := by exact_mod_cast htD
    have htR : (D:ℝ) = (j.choose r:ℝ)*t := by exact_mod_cast ht
    have hj2 : j-r+r=j := by omega
    have hh := hm (j-r) (by omega) (by omega)
    rw [shiftCoefficient_coeff r P Q (j-r) (by omega),hj2] at hh
    refine ⟨(t:ℤ)*m (j-r),?_⟩
    calc
      |((q*D:ℤ):ℝ)*Q.coeff j-((t:ℤ)*m (j-r):ℤ)| =
          (t:ℝ)*|(q:ℝ)*((j.choose r:ℝ)*Q.coeff j)-m (j-r)| := by
        push_cast
        rw [htR]
        calc
          _ = |(t:ℝ)*((q:ℝ)*((j.choose r:ℝ)*Q.coeff j)-(m (j-r):ℝ))| := by
            congr 1; ring
          _ = _ := by rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg t)]
      _ ≤ (t:ℝ)*((B:ℝ)*(A/(N:ℝ)^r)/(N:ℝ)^(j-r)) :=
        mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)
      _ = (B:ℝ)*A*t/(N:ℝ)^j := by
        have hp : (N:ℝ)^j = (N:ℝ)^r*(N:ℝ)^(j-r) := by
          rw [← pow_add]; congr 1; omega
        rw [hp]
        field_simp
      _ ≤ C/(N:ℝ)^j := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        dsimp [C]
        nlinarith [mul_le_mul_of_nonneg_left htr (mul_nonneg (Nat.cast_nonneg B) hA)]

 
theorem high_coefficients (d : ℕ) (δ A : ℝ) (hδ : 0 < δ) (hA : 0 ≤ A) :
    ∃ B : ℕ, 0 < B ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ P Q : ℝ[X], Q.natDegree ≤ d →
        ∀ S : Finset ℕ, S ⊆ range N → δ*N ≤ (S.card:ℝ) →
        (∀ h ∈ S, ∃ z : ℤ, |(P+taylor (h:ℝ) Q-Q).coeff 2-z| ≤ A/(N:ℝ)^2) →
        ∃ q : ℤ, q ≠ 0 ∧ |q| ≤ B ∧ ∀ j : ℕ, 2 < j → j ≤ d →
          ∃ m : ℤ, |(q:ℝ)*Q.coeff j-m| ≤ C/(N:ℝ)^j :=
  shift_coefficients d 2 (by decide) δ A hδ hA

 

theorem nonlinear_coefficients (d : ℕ) (δ A : ℝ) (hδ : 0 < δ) (hA : 0 ≤ A) :
    ∃ B : ℕ, 0 < B ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ P Q : ℝ[X], Q.natDegree ≤ d →
        ∀ S : Finset ℕ, S ⊆ range N → δ*N ≤ (S.card:ℝ) →
        (∀ h ∈ S, ∃ z : ℤ, |(P+taylor (h:ℝ) Q-Q).coeff 1-z| ≤ A/(N:ℝ)) →
        ∃ q : ℤ, q ≠ 0 ∧ |q| ≤ B ∧ ∀ j : ℕ, 1 < j → j ≤ d →
          ∃ m : ℤ, |(q:ℝ)*Q.coeff j-m| ≤ C/(N:ℝ)^j := by
  simpa only [pow_one] using shift_coefficients d 1 (by decide) δ A hδ hA

end PolynomialCharacterDescent

end
end
end
end
end

end OAI
