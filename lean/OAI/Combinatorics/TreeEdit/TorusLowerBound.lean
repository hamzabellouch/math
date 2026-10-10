import OAI.Combinatorics.TreeEdit.CircleParameters
import OAI.Combinatorics.TreeEdit.Delimiter
import OAI.Combinatorics.TreeEdit.DistortionTransfer
import OAI.Combinatorics.TreeEdit.CapInversion

namespace OAI

namespace TreeEdit

def singletonCode (a : Bool) : Word Bool 1 := ⟨[a], rfl⟩

lemma encode_singletonCode (x : List Bool) : encode singletonCode x = x := by
  induction x with
  | nil => rfl
  | cons a x ih => simpa only [encode, List.flatMap_cons, singletonCode, List.singleton_append] using congrArg (List.cons a) ih

namespace TorusTree
open scoped BigOperators
open Classical Filter

theorem binary_witness {k : ℕ} (hk : 2 ≤ k) (j : Fin (16*k) ↪ Pool k)
    (C : Config (Pool k) (residueModulus k) (branching k) k)
    (hgood : Good (resolution k : ℝ)⁻¹ poolPrime j k C (point 2)) :
    ∃ W : Finset (List Bool), 2 ≤ W.card ∧ (∀ v ∈ W, v.length = binaryLength k) ∧
      ((k : ℝ)/128)^k / (1286400*(k : ℝ)^2) ≤ c1 W := by
  let : NeZero (fineModulus j) := ⟨(fine_parameters hk j).1.ne'⟩
  let : NeZero (resolution k) := ⟨(pow_pos (by omega : 0 < k) (8*k)).ne'⟩
  let A := State (ZMod (fineModulus j)) (branching k) k
  let Γ := Symbol (branching k) (resolution k) k
  let N := FiniteTree.length (branching k) (repetitions k) k
  let B := Delimiter.width (Fintype.card Γ)
  have hN : N = wordLength k := FiniteTree.length_eq _ _ _
  have hB : B = binaryWidth k := by
    dsimp only [B, Γ, Delimiter.width, binaryWidth, alphabetSize]
    rw [symbol_card]
  have hNp : 0 < N := lt_of_lt_of_le (by omega : 0 < k) (hN ▸ wordLength_ge hk)
  have hBp : 0 < B := by dsimp [B, Delimiter.width]; omega
  let w : A → Word Γ N := sampledWord poolPrime j (repetitions k) (resolution k) k C
  let z : A := diagonal (A := ZMod (fineModulus j)) (m := branching k) k (fineModulus j/2 : ℕ)
  obtain ⟨c, hc⟩ := Delimiter.transfer Γ
  let instG : AddCommGroup A := stateAddCommGroup (A := ZMod (fineModulus j)) (branching k) k
  let instF : Fintype A := stateFintype (A := ZMod (fineModulus j)) (branching k) k
  let wb (x : A) : Word Bool (N*B) :=
    ⟨encode c (w x).val, by rw [length_encode, (w x).property]⟩
  let hadd : HAdd A A A := ⟨@Add.add A instG.toAdd⟩
  have hsep (x : A) : (N*B : ℝ) ≤ (2*B*(128 : ℝ)^k) * ed (wb x).val (wb (@HAdd.hAdd A A A hadd x z)).val := by
    have hh : (N : ℝ) ≤ (128 : ℝ)^k * deficit (w x).val (w (@HAdd.hAdd A A A hadd x z)).val := by
      exact_mod_cast sampled_separation hk j C hgood x
    have he := (hc N (w x) (w (@HAdd.hAdd A A A hadd x z))).2.1
    calc
      _ ≤ B * ((128 : ℝ)^k * deficit (w x).val (w (@HAdd.hAdd A A A hadd x z)).val) := by nlinarith only [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg B)]
      _ ≤ B * ((128 : ℝ)^k * (2 * ed (wb x).val (wb (@HAdd.hAdd A A A hadd x z)).val)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg B)
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
        dsimp only [wb]
        linarith
      _ = _ := by ring
  have hobs (F : A → RealL1) (a : ℝ) (ha : 0 ≤ a)
      (hlip : ∀ x y, dist (F x) (F y) ≤ a * ed (wb x).val (wb y).val) :
      @FiniteFourier.average A instF (fun x => dist (F x) (F (@HAdd.hAdd A A A hadd x z))) ≤
        a * (N*B : ℕ) * (20*(k : ℝ)⁻¹^k) := by
    have hlip' (x y : A) : dist (F x) (F y) ≤ (a*B) * ed (w x).val (w y).val := by
      calc
        _ ≤ a * ed (wb x).val (wb y).val := hlip x y
        _ ≤ a * (B * (ed (w x).val (w y).val : ℝ)) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast (hc N (w x) (w y)).2.2) ha
        _ = _ := by ring
    have hh := concrete_displacement hk j C F (a*B) (mul_nonneg ha (Nat.cast_nonneg B)) hlip'
    convert hh using 1
    push_cast
    ring
  obtain ⟨W, hW, hlen, hdist⟩ := @binary_transfer A Bool instF instG inferInstance (N*B) 1 (Nat.mul_pos hNp hBp) (by norm_num : 0 < 1)
    wb z singletonCode (2*B*(128 : ℝ)^k) (20*(k : ℝ)⁻¹^k)
    (by positivity) (by
      have hkreal : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      exact mul_pos (by norm_num) (pow_pos (inv_pos.mpr hkreal) _))
    (fun x y => by
      rw [encode_singletonCode, encode_singletonCode]
      exact mul_le_of_le_one_left (Nat.cast_nonneg _) (by norm_num))
    (fun x => by simpa only [Nat.cast_mul] using hsep x) hobs
  refine ⟨W, hW, ?_, ?_⟩
  · intro v hv
    simpa only [mul_one, hN, hB, binaryLength] using hlen v hv
  · have hkreal : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hBreal : (0 : ℝ) < B := by exact_mod_cast hBp
    have hwidth : (B : ℝ) ≤ 40*(k : ℝ)^2 := by rw [hB]; exact_mod_cast binaryWidth_le hk
    have heq : (804*(2*B*(128 : ℝ)^k)*(20*(k : ℝ)⁻¹^k))⁻¹ =
        ((k : ℝ)/128)^k / (32160*B) := by
      rw [div_pow, inv_pow]
      field_simp
      ring
    rw [heq] at hdist
    apply le_trans _ hdist
    apply div_le_div_of_nonneg_left (pow_nonneg (by positivity) _) (by positivity)
    nlinarith

lemma witnesses_eventually : ∀ᶠ k : ℕ in atTop,
    ∃ W : Finset (List Bool), 2 ≤ W.card ∧ (∀ v ∈ W, v.length = binaryLength k) ∧
      ((k : ℝ)/128)^k / (1286400*(k : ℝ)^2) ≤ c1 W := by
  filter_upwards [good_halfturn_eventually] with k hk
  obtain ⟨hk2, j, C, hgood⟩ := hk
  exact binary_witness hk2 j C hgood

end TorusTree

theorem binary_torus : BinaryLowerBound := by
  apply all_caps_of_witnesses (N := TorusTree.binaryLength) (A := 60) (by norm_num)
  filter_upwards [TorusTree.witnesses_eventually,
    eventually_exponential_lower (b := 128) (C := 1286400) (by norm_num) (by norm_num) 2,
    Filter.eventually_ge_atTop 2] with k hw he hk
  obtain ⟨W, hW, hlen, hD⟩ := hw
  exact ⟨TorusTree.binaryLength_ge hk, TorusTree.length_log_bound hk,
    W, hW, hlen, he.trans hD⟩

end TreeEdit

end OAI
