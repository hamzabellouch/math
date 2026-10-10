import Mathlib
import OAI.Analysis.MatrixSigning.Realization.SearchRealization
import OAI.Analysis.MatrixSigning.Complexity.PolynomialRoots
import OAI.Analysis.MatrixSigning.Complexity.PolynomialStored

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23 RationalGridSize
open scoped BigOperators

local notation "X" => NaturalPolynomial.variable

instance poly_roundedUpdate : PolyTime roundedUpdate := by unfold roundedUpdate;apply poly_then
instance poly_stateView : PolyTime stateView := by unfold stateView;apply poly_reindex
instance poly_statePencil : PolyTime statePencil := by unfold statePencil;apply poly_then
instance poly_stateParameters : PolyTime stateParameters := by unfold stateParameters;apply poly_then
instance poly_stateY : PolyTime stateY := by unfold stateY;apply poly_then
instance poly_stateWitness : PolyTime stateWitness := by unfold stateWitness;apply poly_then
instance poly_stateNextVector : PolyTime stateNextVector := by unfold stateNextVector;apply poly_congr
instance poly_pencilNext : PolyTime pencilNext := by unfold pencilNext;apply poly_changeOutput

lemma round_abs (ρ x : ℚ) : |RationalSDP.roundScalar ρ x|≤|x|+|ρ| := by
  by_cases hρ : ρ=0
  · simp [hρ,RationalSDP.roundScalar]
  have he : RationalSDP.roundScalar ρ x-x=ρ*((⌊x/ρ⌋:ℚ)-x/ρ) := by
    unfold RationalSDP.roundScalar
    rw [mul_sub, mul_div_cancel₀ _ hρ]
  have hf : |(⌊x/ρ⌋:ℚ)-x/ρ|≤1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr (Int.floor_le _))]
    linarith [Int.lt_floor_add_one (x/ρ)]
  have hd : |RationalSDP.roundScalar ρ x-x|≤|ρ| := by
    rw [he,abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hf (abs_nonneg ρ)
  have ht := abs_add_le (RationalSDP.roundScalar ρ x-x) x
  rw [sub_add_cancel] at ht
  linarith

lemma l1_coordinate {n : ℕ} (a : Fin n → ℚ) (i : Fin n) : |a i/RationalSDP.l1 a|≤1 := by
  have h0 : 0≤RationalSDP.l1 a := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hi : |a i|≤RationalSDP.l1 a := Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
  by_cases h : RationalSDP.l1 a=0
  · simp [h]
  rw [abs_div,abs_of_nonneg h0]
  exact (div_le_one (lt_of_le_of_ne h0 (Ne.symm h))).mpr hi

lemma pencil_next_abs {n m : ℕ} (B : RationalSDP.Pencil n m) (step mesh : ℚ)
    (y : Fin n → ℚ) (i : Fin n) : |B.next step mesh y i|≤|y i|+|step|+|mesh| := by
  unfold RationalSDP.Pencil.next
  cases B.witness y with
  | none =>
    have h1 := abs_nonneg step;have h2 := abs_nonneg mesh;linarith
  | some v =>
    apply (round_abs mesh _).trans
    have hm : |step * B.normal v i / RationalSDP.l1 (B.normal v)|≤|step| := by
      rw [mul_div_assoc,abs_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (l1_coordinate (B.normal v) i) (abs_nonneg step)
    have ht := abs_sub (y i) (step*B.normal v i/RationalSDP.l1 (B.normal v))
    linarith

lemma pencil_next_grid {n m D : ℕ} (B : RationalSDP.Pencil n m) (step mesh : ℚ)
    (y : Fin n → ℚ) (i : Fin n) (hy : Grid D (y i)) (hm : Grid D mesh) :
    Grid D (B.next step mesh y i) := by
  unfold RationalSDP.Pencil.next
  cases hw : B.witness y with
  | none => exact hy
  | some v => exact hm.mul_integer _

lemma pencil_iterate_parts {n m L : ℕ} (B : RationalSDP.Pencil n m) (step mesh : ℚ)
    (y : Fin n → ℚ) (hs : QParts L step) (hm : QParts L mesh)
    (hy : ∀i,QParts L (y i)) (k : ℕ) (i : Fin n) :
    QParts (3*L+k+1) ((B.next step mesh)^[k] y i) := by
  have hg : ∀k,Grid ((y i).den*mesh.den) ((B.next step mesh)^[k] y i) := by
    intro k
    induction k with
    | zero => exact Nat.dvd_mul_right _ _
    | succ k ih => rw [Function.iterate_succ_apply'];exact pencil_next_grid B step mesh _ i ih (Nat.dvd_mul_left _ _)
  have ha : ∀k,|((B.next step mesh)^[k] y) i|≤(2:ℚ)^(L+k+1) := by
    intro k
    induction k with
    | zero =>
      exact (hy i).abs_le.trans (pow_le_pow_right₀ (by norm_num) (by omega))
    | succ k ih =>
      have ht := pencil_next_abs B step mesh ((B.next step mesh)^[k] y) i
      have hlow : (2:ℚ)^(L+1)≤2^(L+k+1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hp : (2:ℚ)^(L+(k+1)+1)=2*2^(L+k+1) := by rw [show L+(k+1)+1=(L+k+1)+1 by omega,pow_succ,mul_comm]
      rw [Function.iterate_succ_apply',hp]
      have hs' := hs.abs_le
      have hm' := hm.abs_le
      rw [pow_succ] at hlow
      linarith
  have hd : (y i).den*mesh.den≤2^(2*L) := by
    rw [show 2*L=L+L by omega,pow_add]
    exact Nat.mul_le_mul (hy i).2 hm.2
  have ht := qparts_of_grid (by positivity : 0<(y i).den*mesh.den) (hg k) hd (ha k)
  convert ht using 1; omega

instance size_pencilNext : IterateSize pencilNext := by
  refine ⟨⟨100*(X+1)^2,?_⟩⟩
  intro s k
  let L := (pencilStateCode s).length
  have hb : (pencilCode (pencilData s.B)).length≤L := le_prodCode_left (pencilStateData s)
  have hp : (stepParametersCode (s.step,s.mesh)).length≤L := (le_prodCode_left (pencilStateData s).2).trans (le_prodCode_right (pencilStateData s))
  have hy : (vectorCode (List.ofFn s.y)).length≤L := (le_prodCode_right (pencilStateData s).2).trans (le_prodCode_right (pencilStateData s))
  have hs : QParts L s.step := (qparts_length s.step).mono ((le_prodCode_left (s.step,s.mesh)).trans hp)
  have hm : QParts L s.mesh := (qparts_length s.mesh).mono ((le_prodCode_right (s.step,s.mesh)).trans hp)
  have hy' : ∀i,QParts L (s.y i) := by
    intro i
    exact (qparts_length (s.y i)).mono ((mem_length_le_code (List.ofFn s.y) (List.mem_ofFn.mpr ⟨i,rfl⟩)).trans hy)
  have hn : s.n≤L := by simpa only [List.length_ofFn] using (list_length_le_code ratCode (List.ofFn s.y)).trans hy
  have ht := listCode_length_bound (List.ofFn ((s.B.next s.step s.mesh)^[k] s.y)) (4*(3*L+k+1)+7) (by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact (pencil_iterate_parts s.B s.step s.mesh s.y hs hm hy' k i).length)
  rw [List.length_ofFn] at ht
  have ht' := ht.trans (Nat.mul_le_mul_right _ hn)
  change (pencilStateCode (PencilState.next^[k] s)).length≤100*(L+k+1)^2
  rw [pencilNext_iterate]
  simp only [pencilStateCode,pencilStateData,pencilStateDataCode,prodCode_length]
  simp only [pencilCode,prodCode_length] at hb
  simp only [stepParametersCode,prodCode_length] at hp
  change (vectorCode (List.ofFn ((s.B.next s.step s.mesh)^[k] s.y))).length≤_ at ht'
  nlinarith
end CurrentKS.Realization

end OAI
