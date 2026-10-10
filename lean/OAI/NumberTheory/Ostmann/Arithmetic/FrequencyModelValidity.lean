import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyModelCoefficients

namespace OAI

/-! # The original frequency gate supplies modular adaptive validity -/

namespace Ostmann
open scoped Classical

theorem FrequencyModelState.compensation_coprime {σ : Type*} (value : σ → ℕ) (R : ℤ)
    (hsmall : ∀ i, IsCoprime (value i : ℤ) R) (z : FrequencyModelState σ) :
    IsCoprime (z.compensation value) R := by
  rcases z with ⟨n, T, x, y⟩
  cases T with
  | leaf => exact isCoprime_one_left
  | node s CL CR U l r => exact movingNaturalProduct_coprime value U R (fun i _ => hsmall i)

theorem FrequencyModelState.relation {σ : Type*} (value : σ → ℕ) (R : ℤ)
    (z : FrequencyModelState σ)
    (hU : IsCoprime (z.compensation value) R)
    (hg : movingFrequencyGate value R z.data z.leftGiant z.rightGiant) :
    z.frequencies.left * z.rightProduct value - z.frequencies.right * z.leftProduct value ≡
      z.frequencies.root * z.compensation value * z.pivot value R [ZMOD R ^ z.level] := by
  rcases z with ⟨n, T, x, y⟩
  cases T with
  | leaf => simp [FrequencyModelState.frequencies, FrequencyModelState.leftProduct,
      FrequencyModelState.rightProduct, FrequencyModelState.pivot]
  | @node n s CL CR U l r =>
    let step := MovingSlotData.step s CL CR U l r false
    let N := step.signedNumerator value x y
    let u : ℤ := MovingSlotReversal.naturalProduct value U
    have hd : s ∣ N := hg.2.1
    have hu : IsCoprime u R := hU
    have hinv := coprime_bezout_inverse_modEq u R hu (n + 1)
    change N ≡ s * u * ((N / s) * Int.gcdA u (R ^ (n + 1))) [ZMOD R ^ (n + 1)]
    calc
      N = s * (N / s) := (Int.mul_ediv_cancel' hd).symm
      _ ≡ (s * (N / s)) * (u * Int.gcdA u (R ^ (n + 1))) [ZMOD R ^ (n + 1)] := by
        simpa only [mul_one] using hinv.symm.mul_left (s * (N / s))
      _ = _ := by ring

theorem FrequencyModelState.products_units {σ : Type*} (value : σ → ℕ)
    (R : ℤ) (z : FrequencyModelState σ)
    (hsmall : ∀ i, IsCoprime (value i : ℤ) z.frequencies.root)
    (hg : movingFrequencyGate value R z.data z.leftGiant z.rightGiant) :
    IsCoprime (z.leftProduct value) z.frequencies.root ∧
      IsCoprime (z.rightProduct value) z.frequencies.root := by
  have hlocal : movingFrequencyLocalUnits z.data z.leftGiant z.rightGiant := by
    rcases z with ⟨n, T, x, y⟩
    cases T
    · exact hg
    · exact hg.1
  rcases z with ⟨n, T, x, y⟩
  cases T with
  | leaf => exact ⟨isCoprime_one_left, isCoprime_one_left⟩
  | node s CL CR U l r =>
    have hl := hlocal.1.of_isCoprime_of_dvd_right
      (MovingSlotData.frequency_dvd_product (.node s CL CR U l r))
    have hr := hlocal.2.of_isCoprime_of_dvd_right
      (MovingSlotData.frequency_dvd_product (.node s CL CR U l r))
    exact ⟨hl.mul_left (movingNaturalProduct_coprime value CL s (fun i _ => hsmall i)),
      hr.mul_left (movingNaturalProduct_coprime value CR s (fun i _ => hsmall i))⟩

theorem frequencyModel_modularEquations {σ : Type*} (value : σ → ℕ) (R : ℕ)
    (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (x y : ℤ)
    (hsmall : ∀ i, IsCoprime (value i : ℤ) (R : ℤ))
    (hg : movingFrequencyGate value R
      (buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a) x y) :
    let T := buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a
    let b := actualChildProducts n (treeLeafMap (fun q : ℕ => (q : ℤ)) n
      (movingSlotValues value n bulk))
    (frequencyModelAncestorScheme value S n t small a x y).modularCompensatedEquations R (n - 1)
      (movingSampleCompensation value n small a)
      (fun j => (b.getD j.val (1, 1)).1) (fun j => (b.getD j.val (1, 1)).2)
      (frequencyModelPivots value R n T x y) := by
  dsimp only
  intro j
  let T := buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a
  let z := frequencyModelAtPath value R n T x y (preorderNodePath n j)
  have hgate := frequencyModelAtPath_gate value R n T x y (preorderNodePath n j) hg
  have he := z.relation value R (z.compensation_coprime value R hsmall) hgate
  have hp := frequencyModelNode_products value R S n t small bulk a x y j
  have hf := frequencyModelAtPath_frequencies value R S n T t
    (buildMovingSlotData_follows n _ small bulk a) x y (preorderNodePath n j)
    (preorderNodePath_length n j)
  have hl := frequencyModelAtPath_level value R n T x y (preorderNodePath n j)
    (preorderNodePath_length n j)
  rw [nodePathIndex_preorderNodePath] at hf
  change z.level + (preorderNodePath n j).length = n at hl
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (preorderNodePath_length n j)
  have helevel : z.level = n - 1 + 1 - (preorderNodePath n j).length := by omega
  change z.frequencies.left * z.rightProduct value - z.frequencies.right * z.leftProduct value ≡
    z.frequencies.root * z.compensation value * z.pivot value R [ZMOD (R : ℤ) ^ z.level] at he
  rw [hp.1, hp.2.1, hp.2.2, hf, helevel] at he
  simpa only [frequencyModelAncestorScheme, forwardTreeAncestorScheme, treeAncestorScheme,
    frequencyModelPivots, mul_assoc] using he

/-- Unit factors are retained from the exact local frequency gates. -/
theorem frequencyModel_coefficient_units {σ : Type*} (value : σ → ℕ) (R : ℕ)
    (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (x y : ℤ)
    (hsmall : ∀ i, IsCoprime (value i : ℤ) (R : ℤ))
    (hR : ∀ j : Fin (2 ^ n - 1), (singleTreeNodeFrequencies S n t j.val).root.natAbs ∣ R)
    (hg : movingFrequencyGate value R
      (buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a) x y)
    (j : Fin (2 ^ n - 1)) :
    let T := buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a
    let D := frequencyModelAncestorScheme value S n t small a x y
    let p := frequencyModelPivots value R n T x y
    IsCoprime (D.leftCoefficient p j) (D.frequencies j).root ∧
      IsCoprime (D.rightCoefficient p j) (D.frequencies j).root := by
  dsimp only
  let T := buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a
  let z := frequencyModelAtPath value R n T x y (preorderNodePath n j)
  have hf := frequencyModelAtPath_frequencies value R S n T t
    (buildMovingSlotData_follows n _ small bulk a) x y (preorderNodePath n j)
    (preorderNodePath_length n j)
  rw [nodePathIndex_preorderNodePath] at hf
  have hroot := congrArg NodeFrequencies.root hf
  have hd : z.frequencies.root ∣ (R : ℤ) := by
    rw [hroot]
    exact Int.natAbs_dvd.mp (Int.natCast_dvd_natCast.mpr
      (hR j))
  have hu := z.products_units value R
    (fun i => (hsmall i).of_isCoprime_of_dvd_right hd)
    (frequencyModelAtPath_gate value R n T x y (preorderNodePath n j) hg)
  have hp := frequencyModelNode_products value R S n t small bulk a x y j
  rw [hp.2.1, hp.2.2, hroot] at hu
  exact ⟨hu.2.of_mul_left_left, hu.1.of_mul_left_left⟩

end Ostmann

end OAI
