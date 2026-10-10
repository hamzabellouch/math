import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.ThreeBranch
import OAI.Combinatorics.RamseyFive.Decoding.FreshPublicValidation

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining Metadata Filter ParameterHierarchy FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K : Type*} [Field K] [Finite K] [Fintype K]
  [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]

noncomputable def threeSelectedLaw (σ : ℝ)
    (X U : Finset (ℙ K (Fin 4→K))) (T UT : Finset (ℙ K (Dual K (Fin 4→K))))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) : Law (Option (Finset (ℙ K (Fin 4→K)))) :=
  let F := flatIndices (K:=K) (V:=Fin 4→K) 3
  let p := threeBranchLaw σ F flatEnumeration X U T UT P τ R L₀
  let Good := fun br=>p br none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
    ∀W,0<p br (some W)→CaptureBound X U (9/1000) ((X.card:ℝ)*Real.exp (10*P)) W
  if h : ∃br,Good br then p h.choose else pureLaw none

theorem eventually_three_selected {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K : Type) [Field K] [Finite K] [Fintype K] [CharP K q]
      [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))],
    ∀ (X U : Finset (ℙ K (Fin 4→K))) (T UT : Finset (ℙ K (Dual K (Fin 4→K)))),
      Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-400*beta η) → X⊆U → T⊆UT → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^4*Real.exp (-b)≤(X.card:ℝ)*T.card →
        let p := threeSelectedLaw σ X U T UT (P η σ D R) τ R L₀
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        ∀W,0<p (some W)→CaptureBound X U (9/1000) ((X.card:ℝ)*Real.exp (10*P η σ D R)) W := by
  filter_upwards [eventually_three_branch hη hη' Cb hCb] with σ hh
  intro D b τ R L₀ q K _ _ _ _ _ _ X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod
  let (point : ℙ K (Fin 4→K)) : Fintype (RadialLine point) := Fintype.ofFinite _
  let F := flatIndices (K:=K) (V:=Fin 4→K) 3
  have hF : F.Nonempty := flatIndices_nonempty 3 (by rw [Module.finrank_pi];norm_num)
  have he := hh D b τ R L₀ q K (Fin 4) (Fin (Fintype.card (Submodule K (Fin 4→K))))
    F hF flatEnumeration X U T UT hcard hσq (Fintype.card_fin 4) hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod
    (flatIndices_rank 3) (flatIndices_cover 3)
  have he' : ∃br : ThreeBranch (K:=K) (I:=Fin 4) σ F,
      threeBranchLaw σ F flatEnumeration X U T UT (P η σ D R) τ R L₀ br none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
      ∀W,0<threeBranchLaw σ F flatEnumeration X U T UT (P η σ D R) τ R L₀ br (some W)→
        CaptureBound X U (9/1000) ((X.card:ℝ)*Real.exp (10*P η σ D R)) W := by
    simpa only [CaptureBound,Finset.inter_comm] using he
  dsimp only [threeSelectedLaw]
  rw [dite_eq_left he']
  exact he'.choose_spec
end

section
open Module ProjectiveIncidence ProjectiveTraining Metadata Filter ParameterHierarchy FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [Fintype K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]

noncomputable def threeCoordinateLaw (e : V≃ₗ[K](Fin 4→K)) (σ : ℝ)
    (X U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) : Law (Option (Finset (ℙ K V))) :=
  map (threeSelectedLaw σ (X.map (projectiveEquiv e).toEmbedding)
    (U.map (projectiveEquiv e).toEmbedding)
    (T.map (projectiveEquiv e.symm.dualMap).toEmbedding)
    (UT.map (projectiveEquiv e.symm.dualMap).toEmbedding) P τ R L₀)
    (Option.map fun Z=>Z.map (projectiveEquiv e).symm.toEmbedding)

theorem eventually_three_coordinates {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [Fintype K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))],
    ∀ (e : V≃ₗ[K](Fin 4→K))
      (X U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))),
      Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-400*beta η) → X⊆U → T⊆UT → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^4*Real.exp (-b)≤(X.card:ℝ)*T.card →
        let p := threeCoordinateLaw e σ X U T UT (P η σ D R) τ R L₀
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        ∀W,0<p (some W)→CaptureBound X U (9/1000) ((X.card:ℝ)*Real.exp (10*P η σ D R)) W := by
  filter_upwards [eventually_three_selected hη hη' Cb hCb] with σ hh
  intro D b τ R L₀ q K V _ _ _ _ _ _ _ _ _ _ _ e X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod
  let X' := X.map (projectiveEquiv e).toEmbedding
  let U' := U.map (projectiveEquiv e).toEmbedding
  let T' := T.map (projectiveEquiv e.symm.dualMap).toEmbedding
  let UT' := UT.map (projectiveEquiv e.symm.dualMap).toEmbedding
  have hXU' : X'⊆U' := Finset.map_subset_map.mpr hXU
  have hTU' : T'⊆UT' := Finset.map_subset_map.mpr hTU
  have hdens' : (Nat.card K:ℝ)*(incidences X' T':ℝ)≤τ*X'.card*T'.card := by
    simpa only [X',T',incidences_coordinates,Finset.card_map] using hdens
  have hprod' : (Nat.card K:ℝ)^4*Real.exp (-b)≤(X'.card:ℝ)*T'.card := by
    simpa only [X',T',Finset.card_map] using hprod
  obtain ⟨hf,hg⟩ := hh D b τ R L₀ q K X' U' T' UT' hcard hσq hr hL hb hbhi hτ hτhi hXU' hTU'
    (by simpa only [X',T',Finset.card_map] using hXT) hdens' hprod'
  let pp := threeSelectedLaw σ X' U' T' UT' (P η σ D R) τ R L₀
  refine ⟨?_,?_⟩
  · dsimp only [threeCoordinateLaw]
    rw [map_option_none]
    exact hf
  · intro W hW
    obtain ⟨Z,hZ,he⟩ := map_positive pp (Option.map fun Z=>Z.map (projectiveEquiv e).symm.toEmbedding) (some W) hW
    cases Z with
    | none => simp at he
    | some Z =>
      have he' : Z.map (projectiveEquiv e).symm.toEmbedding=W := Option.some.inj he
      subst W
      have hz := hg Z hZ
      obtain ⟨hU,hcard',hcap⟩ := decoded_coordinates e U X Z hz.1
      refine ⟨hU,?_,?_⟩
      · simpa only [hcard',X',Finset.card_map] using hz.2.1
      · rw [Finset.inter_comm,hcap,Finset.inter_comm]
        simpa only [X',Finset.card_map] using hz.2.2
end

open Module ProjectiveIncidence ProjectiveTraining Metadata Filter ParameterHierarchy FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def threeFreeLaw (hd : finrank K V=4) (σ : ℝ)
    (X U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) : Law (Option (Finset (ℙ K V))) := by
  letI : Fintype K := Fintype.ofFinite _
  letI : Finite (Dual K (Fin 4→K)) := Module.finite_of_finite K
  letI : Fintype (ℙ K (Fin 4→K)) := Fintype.ofFinite _
  letI : Fintype (ℙ K (Dual K (Fin 4→K))) := Fintype.ofFinite _
  let e := LinearEquiv.ofFinrankEq V (Fin 4→K) (by rw [Module.finrank_pi,Fintype.card_fin,hd])
  exact threeCoordinateLaw e σ X U T UT P τ R L₀

theorem eventually_three_free {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (hd : finrank K V=4) (X U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))),
      Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-400*beta η) → X⊆U → T⊆UT → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^4*Real.exp (-b)≤(X.card:ℝ)*T.card →
        let p := threeFreeLaw hd σ X U T UT (P η σ D R) τ R L₀
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        ∀W,0<p (some W)→CaptureBound X U (9/1000) ((X.card:ℝ)*Real.exp (10*P η σ D R)) W := by
  filter_upwards [eventually_three_coordinates hη hη' Cb hCb] with σ hh
  intro D b τ R L₀ q K V _ _ _ _ _ _ _ _ hd X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod
  let : Fintype K := Fintype.ofFinite _
  let : Finite (Dual K (Fin 4→K)) := Module.finite_of_finite K
  let : Fintype (ℙ K (Fin 4→K)) := Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K (Fin 4→K))) := Fintype.ofFinite _
  let e := LinearEquiv.ofFinrankEq V (Fin 4→K) (by rw [Module.finrank_pi,Fintype.card_fin,hd])
  exact hh D b τ R L₀ q K V e X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod
end SharpRamseyFive.ScoreGeometry

end OAI
