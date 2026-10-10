import OAI.Combinatorics.SquareDifference.ExceptionalBasics

namespace OAI

section

open Finset Filter

open scoped BigOperators Topology

namespace SquareDifference

open LiftTheory.SquareDifference

lemma signedHolder_uniform_bound {V X : Type*} [Fintype V] [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hd : ∀g,0≤diagonalIntegral L g)
    (hh : ∀F : V → X → ℝ,|multilinearIntegral L F|≤∏v,diagonalRoot L (F v))
    (F : V → X → ℝ) (K : ℝ) (hK : 0≤K) (hF : ∀v,diagonalIntegral L (F v)≤K) :
    |multilinearIntegral L F|≤K := by
  apply (hh F).trans
  calc
    _ ≤ ∏_v : V,K^(1/(Fintype.card V:ℝ)) := by
      apply prod_le_prod₀ (fun v _ => diagonalRoot_nonneg L hd (F v))
      intro v _
      exact Real.rpow_le_rpow (hd _) (hF v) (by positivity)
    _ = K := by
      rw [prod_const,card_univ,←Real.rpow_mul_natCast hK]
      rw [one_div_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),Real.rpow_one]

lemma positiveLaw_const {X : Type*} (L : (X → ℝ) →ₗ[ℝ] ℝ) (c : ℝ) : L (fun _ => c)=c*L (fun _ => 1) := by
  rw [show (fun _ : X => c)=c • (fun _ : X => (1:ℝ)) by ext; simp]
  exact L.map_smul c (fun _ => (1:ℝ))

section Mixed

variable {J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]

lemma actualMixedLaw_freeze (hp : ∀j,tupleMassThreshold≤(p j:ℝ)) (B : Finset J)
    (F : (TupleVertex → ResidueSpace p) → ℝ) :
    actualMixedLaw p B (fun z => productTupleLaw p (fun x => F (fun v => freezeCoordinates B (z v) (x v))))=
      actualMixedLaw p B F := by
  exact tensorLaw_freeze (fun j => if j∈B then tupleExceptionalLaw (p:=p j) else tupleLaw (p:=p j))
    (fun j => tupleLaw (p:=p j)) B (fun j => tupleLaw_probability (hp j))
    (fun j hj => ite_eq_right hj) F

lemma actualMixedLaw_transfer (hp : ∀j,tupleMassThreshold≤(p j:ℝ))
    (href : ∀j,tupleReflectionThreshold≤(p j:ℝ)) (B : Finset J)
    (F : TupleVertex → ResidueSpace p → ℝ) (K : ℝ) (hK : 0≤K)
    (hF : ∀(v : TupleVertex) (z : ResidueSpace p),
      diagonalIntegral (productTupleLaw p) (fun x => F v (freezeCoordinates B z x))≤K) :
    |multilinearIntegral (actualMixedLaw p B) F|≤exceptionalProduct p B*K := by
  unfold multilinearIntegral
  rw [←actualMixedLaw_freeze p hp B]
  apply (positiveLaw_abs _ (actualMixedLaw_nonneg p B) _).trans
  calc
    _ ≤ actualMixedLaw p B (fun _ => K) := by
      apply positiveLaw_mono _ (actualMixedLaw_nonneg p B)
      intro z
      exact signedHolder_uniform_bound _ (productTupleLaw_diagonal_nonneg p href)
        (productTupleLaw_signed_holder p href) (fun v x => F v (freezeCoordinates B (z v) x)) K hK
        (fun v => hF v (z v))
    _ = _ := by rw [positiveLaw_const,actualMixedLaw_mass p hp]; ring

end Mixed

lemma source_mixed_transfer (M : ℕ) [NeZero M] (hM2 : 2≤M) :
    ∃C : ℝ,0<C ∧ ∀ᶠ N : ℕ in atTop,
      ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime],
      Function.Injective p → (∀j,max tupleMassThreshold tupleConditionalThreshold≤(p j:ℝ)) →
      (∀j,tupleReflectionThreshold≤(p j:ℝ)) → (∀j,M.Coprime (p j)) →
      ∀(B : Finset J),(∏j∈B,p j:ℝ)≤(N:ℝ)^(sourceTau (Fintype.card TupleVertex)) →
      ∀(s : TupleVertex → ZMod M) (A : Finset ℕ),A⊆range N → NatSquareFree A →
      ∀K : ℝ,0≤K →
      (∀A' : Finset ℕ,A'⊆range (childLength N (M*(∏j∈B,p j))) → NatSquareFree A' →
        setFunctional p (childLength N (M*(∏j∈B,p j)))
          (powerCutoff (childLength N (M*(∏j∈B,p j))) sourceBeta) A'≤K) →
      |multilinearIntegral (actualMixedLaw p B)
        (fun v => actualTruncatedLift p N (powerCutoff N sourceBeta) (smallResidueInput M A (s v)))|≤
      exceptionalProduct p B*(transferFactor (Fintype.card TupleVertex) M N*K+C*(N:ℝ)^(-sourceSigma (Fintype.card TupleVertex))) := by
  obtain ⟨C,hC,hb⟩ := source_actual_fiber_transfer M hM2
  refine ⟨C,hC,?_⟩
  filter_upwards [hb] with N hb
  intro J _ _ p _ hinj hp href hcop B hB s A hA hfree K hK hchild
  exact actualMixedLaw_transfer p (fun j => (le_max_left _ _).trans (hp j)) href B _ _
    (add_nonneg (mul_nonneg (transferFactor_nonneg _ _ _) hK) (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg N) _)))
    (fun v z => hb p hinj (fun j => (le_max_right _ _).trans (hp j)) href hcop B hB (s v) z A hA hfree K hK hchild)

end SquareDifference

end

end OAI
