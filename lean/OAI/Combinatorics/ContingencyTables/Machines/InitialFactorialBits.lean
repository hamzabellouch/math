import OAI.Combinatorics.ContingencyTables.Transport.InitialFactorialLaw

namespace OAI

/-! # One finite Boolean word for the actual initial transversal

The word is split into disjoint cell blocks; each block chooses a size
and then a subset of that size. The total variation errors add before
the exact paired-transversal encoding is applied.
-/

namespace ContingencyTables.InitialFactorialBits

open CommonBasesFPRAS ResidualMixture FirstSuccess FairBits TwoLiftStates
open FixedCardinalityMixture InitialFactorialLaw InitialTransversals
open CompanionFactorialApplication
open scoped BigOperators Classical
noncomputable section

variable {q : ℕ}

def bitCount (b : Fin q → ℕ) (B : ℕ) : ℕ := ∑ i,drawBits B (b i)

def wordEquiv (b : Fin q → ℕ) (B : ℕ) :
    (Fin (bitCount b B) → Bool) ≃ (∀ i,Fin (drawBits B (b i)) → Bool) :=
  (Equiv.arrowCongr finSigmaFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.piCurry (fun _ _ => Bool))

def drawChoices (b : Fin q → ℕ) (B : ℕ) (bits : Fin (bitCount b B) → Bool) :
    ∀ i,Finset (Fin (b i)) :=
  fun i => subsetDraw B (b i) (wordEquiv b B bits i)

theorem drawChoices_law (b : Fin q → ℕ) (B : ℕ) :
    mapLaw (uniformLaw (α := Fin (bitCount b B) → Bool)) (drawChoices b B)=
      piLaw (fun i => mapLaw (uniformLaw (α := Fin (drawBits B (b i)) → Bool))
        (subsetDraw B (b i))) := by
  have he := map_equiv (wordEquiv b B)
    (uniformLaw (α := Fin (bitCount b B) → Bool))
    (fun words i => subsetDraw B (b i) (words i))
  rw [uniform_equiv,←pi_uniformLaw,pi_mapLaw] at he
  exact he.symm

theorem drawChoices_error (b : Fin q → ℕ) (B : ℕ) :
    variation (mapLaw (uniformLaw (α := Fin (bitCount b B) → Bool)) (drawChoices b B))
      (piLaw (fun i => localLaw (b i)))≤
        ∑ i,((b i+1:ℚ)/(2*(2:ℚ)^B)+(b i:ℚ)/(2:ℚ)^B) := by
  rw [drawChoices_law]
  exact (variation_pi _ _ _).trans (Finset.sum_le_sum (fun i _ => subsetDraw_error B (b i)))

theorem bitCount_eq (b : Fin q → ℕ) (B : ℕ) :
    bitCount b B=(q+∑ i,b i)*B := by
  simp only [bitCount,drawBits,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,←Finset.sum_mul]
  simp only [Nat.cast_id]
  ring

theorem bitCount_bound (b : Fin q → ℕ) (B W : ℕ) (hb : ∀ i,b i≤W) :
    bitCount b B≤q*(W+1)*B := by
  rw [bitCount_eq]
  apply Nat.mul_le_mul_right
  have hs : (∑ i,b i)≤q*W := by
    calc
      _ ≤ ∑ _i : Fin q,W := Finset.sum_le_sum (fun i _ => hb i)
      _ = q*W := by simp
  nlinarith

theorem drawChoices_error_bound (b : Fin q → ℕ) (B W : ℕ) (hb : ∀ i,b i≤W) :
    variation (mapLaw (uniformLaw (α := Fin (bitCount b B) → Bool)) (drawChoices b B))
      (piLaw (fun i => localLaw (b i)))≤(q:ℚ)*(3*W+1)/(2*(2:ℚ)^B) := by
  apply (drawChoices_error b B).trans
  calc
    _ ≤ ∑ _i : Fin q,((W+1:ℚ)/(2*(2:ℚ)^B)+(W:ℚ)/(2:ℚ)^B) := by
      apply Finset.sum_le_sum
      intro i _
      have hi : (b i:ℚ)≤W := by exact_mod_cast hb i
      exact _root_.add_le_add
        (div_le_div_of_nonneg_right (by linarith) (by positivity))
        (div_le_div_of_nonneg_right hi (by positivity))
    _ = _ := by simp; ring

variable {C : Type*} [Fintype C]

def choiceEquiv (b : C → ℕ) (e : C ≃ Fin q) :
    (∀ i : Fin q,Finset (Fin (b (e.symm i)))) ≃ (∀ c,Finset (Fin (b c))) :=
  (Equiv.piCongrLeft' (fun c => Finset (Fin (b c))) e).symm

theorem choiceEquiv_law (b : C → ℕ) (e : C ≃ Fin q) :
    equivLaw (choiceEquiv b e) (piLaw (fun i => localLaw (b (e.symm i))))=choiceLaw b := by
  apply RationalLaw.ext
  funext S
  change (∏ i : Fin q,(localLaw (b (e.symm i))).mass (S (e.symm i)))=
    ∏ c,(localLaw (b c)).mass (S c)
  symm
  apply Fintype.prod_equiv e
  intro c
  exact congrArg (fun x => (localLaw (b x)).mass (S x)) (e.symm_apply_apply c).symm

def transversalDraw (b : C → ℕ) (e : C ≃ Fin q) (B : ℕ)
    (bits : Fin (bitCount (fun i => b (e.symm i)) B) → Bool) :
    {S : Set (Copy b×Bool) // PlainState pairs S} :=
  (plainEquivChoices b).symm
    (choiceEquiv b e (drawChoices (fun i => b (e.symm i)) B bits))

theorem transversalDraw_error (b : C → ℕ) (e : C ≃ Fin q) (B W : ℕ)
    (hb : ∀ c,b c≤W) :
    variation (mapLaw (uniformLaw (α := Fin (bitCount (fun i => b (e.symm i)) B) → Bool))
      (transversalDraw b e B)) (plainLaw b)≤(q:ℚ)*(3*W+1)/(2*(2:ℚ)^B) := by
  let E := (choiceEquiv b e).trans (plainEquivChoices b).symm
  have he := mapLaw_equiv_output E
    (uniformLaw (α := Fin (bitCount (fun i => b (e.symm i)) B) → Bool))
    (drawChoices (fun i => b (e.symm i)) B)
  have ht : equivLaw E (piLaw (fun i => localLaw (b (e.symm i))))=plainLaw b := by
    have hh := choiceEquiv_law b e
    apply RationalLaw.ext
    funext S
    exact congrArg (fun p => p.mass ((plainEquivChoices b) S)) hh
  change variation (mapLaw _ (fun bits => E (drawChoices _ B bits))) _≤_
  rw [he,←ht,variation_equiv]
  exact drawChoices_error_bound _ B W (fun i => hb (e.symm i))

end
end ContingencyTables.InitialFactorialBits

end OAI
