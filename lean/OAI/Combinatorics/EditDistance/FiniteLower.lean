import OAI.Combinatorics.EditDistance.LowerParameters
import OAI.Combinatorics.EditDistance.LowerDistortion

namespace OAI

/-!
# Finite nonempty binary witnesses of a common length
-/

namespace EditLower
open EditDistortion EditFamily EditCode EditParameters

noncomputable def binaryLabels (k : ℕ) : Fin (familyAlphabet (b k) (P k) k) ↪ (Fin (codeBits k) → Bool) := by
  simpa only [codeBits,Fintype.card_fin] using labels (Fin (familyAlphabet (b k) (P k) k))

theorem family_ratio {k p : ℕ} (hk : 0 < k) (hp : 1 < p)
    (F : Family p (familyLength (b k) (P k) k) (familyAlphabet (b k) (P k) k)
      (familyAlpha k) (familyBudget (b k) (P k) (h k) k))
    (f : codeSet F (binaryLabels k) ↪ L1) :
    lowerRatio k ≤ distortion (fun x y : codeSet F (binaryLabels k) => (edit x.val y.val : ℝ)) f := by
  classical
  let label := binaryLabels k
  let : Fintype (codeSet F label) := (codeSet_finite F label).fintype
  have hn := familyLength_pos (by dsimp [b]; omega : 0 < b k) (prime_parameter_pos hk) k
  let : Nontrivial (codeSet F label) := codeSet_nontrivial F label hp hn (familyAlpha_pos k)
  let D := distortion (fun x y : codeSet F label => (edit x.val y.val : ℝ)) f
  have hD : 0 ≤ D := distortion_nonneg _ (fun x => edit_real_diag x.val)
    (fun x y hxy => edit_real_pos x.val y.val (fun h => hxy (Subtype.ext h))) f
  have hl := family_distortion F label hp hn (familyAlpha_pos k) f
  change familyAlpha k ≤ 4*(codeWidth k : ℝ)*familyBudget (b k) (P k) (h k) k*D at hl
  have hw : (0 : ℝ) < codeWidth k := by exact_mod_cast EditParameters.width_pos k
  have hh : (0 : ℝ) < (h k : ℝ)^k := by dsimp [h]; positivity
  have hb : familyAlpha k ≤ (16*(codeWidth k : ℝ)*D)/(h k : ℝ)^k := by
    calc
      _ ≤ 4*(codeWidth k : ℝ)*(4/(h k : ℝ)^k)*D := by
        apply hl.trans
        gcongr
        exact budget_small hk
      _ = _ := by ring
  have hmul := (le_div_iff₀ hh).mp hb
  have hpow : familyAlpha k*(h k : ℝ)^k = ((h k : ℝ)/24)^k := by
    unfold familyAlpha
    rw [←mul_pow]
    congr 1
    ring
  change ((h k : ℝ)/24)^k/(16*(codeWidth k : ℝ)) ≤ D
  apply (div_le_iff₀ (by positivity : 0 < 16*(codeWidth k : ℝ))).mpr
  rw [hpow] at hmul
  nlinarith

theorem eventually_depth_witness : ∀ᶠ k : ℕ in Filter.atTop,
    ∃ S : Set (List Bool), S.Finite ∧ S.Nonempty ∧ S.Nontrivial ∧
      (∀ w ∈ S, w.length = encodedLength k) ∧
      lowerRatio k ≤ leastDistortion (fun x y : S => (edit x.val y.val : ℝ)) := by
  classical
  obtain ⟨B,hB⟩ := Filter.eventually_atTop.mp EditPrimes.eventually_pool_square
  filter_upwards [Filter.eventually_ge_atTop (max 1 B)] with k hk
  have hk0 : 0 < k := by omega
  have hb0 : 0 < b k := by dsimp [b]; omega
  have hpool := hB (b k) (by dsimp [b]; omega)
  obtain ⟨p,hinj,hprime,hlow,hhigh⟩ := EditPrimes.primes_of_pool hpool
  have hP : 1 ≤ P k := Nat.one_le_iff_ne_zero.mpr (prime_parameter_pos hk0).ne'
  let j : Fin (b k) := ⟨0,hb0⟩
  let F : Family (p j) (familyLength (b k) (P k) k) (familyAlphabet (b k) (P k) k)
      (familyAlpha k) (familyBudget (b k) (P k) (h k) k) := by
    simpa only [Fintype.card_fin] using recursive p hprime hinj (P k) hP hlow hhigh
      (h k) (by dsimp [h]; omega) k j
  let S := codeSet F (binaryLabels k)
  let : Fintype S := (codeSet_finite F (binaryLabels k)).fintype
  refine ⟨S,codeSet_finite F (binaryLabels k),codeSet_nonempty F (binaryLabels k),?_,?_,?_⟩
  · exact Set.nontrivial_coe_sort.mp (codeSet_nontrivial F (binaryLabels k) (hprime j).one_lt
      (familyLength_pos hb0 (prime_parameter_pos hk0) k) (familyAlpha_pos k))
  · intro w hw
    exact codeSet_length F (binaryLabels k) w hw
  · apply leastDistortion_lower
    intro f
    exact family_ratio hk0 (hprime j).one_lt F f

end EditLower

end OAI
