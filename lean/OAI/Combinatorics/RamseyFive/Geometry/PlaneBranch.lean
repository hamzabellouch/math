import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.RecursivePlane

namespace OAI

namespace SharpRamseyFive.ProjectiveRestriction
open Module ProjectiveIncidence ProjectiveTraining ScoreGeometry FiniteEntropy
open DyadicLifts ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)]

noncomputable def planeBranchLaw (A : Submodule K V)
    [Fintype (ℙ K A)] [Fintype (ℙ K (Dual K A))]
    [Fintype (ℙ K (Dual K (Dual K A)))]
    (X UX : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (τ P : ℝ) (R : ℕ) (L₀ : ℝ≥0) (k : ℕ) : Law (Option (Finset (ℙ K V))) :=
  let S := flatSection A X
  let US := flatSection A UX
  let G := nonzeroLifts A (goodLifts A S T (Real.sqrt τ/Nat.card K))
  let T₀ := restrictions (image A.dualRestrict) G k
  let UT₀ := enclosure (image A.dualRestrict) (nonzeroLifts A UT) (2^k)
  if h : T₀.Nonempty then
    map (twoOrientedLaw S US T₀ UT₀ h P (Real.sqrt τ) R L₀)
      (Option.map fun Z=>Z.map (flatEmbedding A))
  else pureLaw none

theorem eventually_plane_branch {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)],
    ∀ (A : Submodule K V)
      [Fintype (ℙ K A)] [Fintype (ℙ K (Dual K A))]
      [Fintype (ℙ K (Dual K (Dual K A)))]
      [∀x : ℙ K A,Fintype (RadialLine x)]
      [∀x : ℙ K (Dual K A),Fintype (RadialLine x)],
    ∀ (X UX : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))),
      finrank K A=3 → finrank K V≤5 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-400*beta η) → X.Nonempty → T.Nonempty → X⊆UX → T⊆UT →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^(finrank K V)*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (X.card:ℝ)≤100*(X∩flatPoints A).card →
      ∃k≤Nat.log 2 ((Nat.card K)^(finrank K V-finrank K A)),
        let p := planeBranchLaw A X UX T UT τ (P η σ D R) R L₀ k
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        ∀W,0<p (some W)→W⊆UX ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (2*P η σ D R) ∧
          (9/1000:ℝ)*X.card≤(W∩X).card := by
  filter_upwards [eventually_plane_reduction_law hη hη' Cb hCb] with σ hh
  intro D b τ R L₀ K V _ _ _ _ _ _ A _ _ _ _ _ X UX T UT hA hV hq hr hL hb hbhi hτ hτhi hX hT hXU hTU hdens hprod hflat
  obtain ⟨k,hk,hT₀,hgood⟩ := hh D b τ R L₀ K V A X UX T UT hA hV hq hr hL hb hbhi hτ hτhi hX hT hXU hTU hdens hprod hflat
  refine ⟨k,hk,?_⟩
  dsimp only [planeBranchLaw]
  rw [dite_eq_left hT₀]
  exact hgood

noncomputable def planeAutoLaw (A : Submodule K V)
    (X UX : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (τ P : ℝ) (R : ℕ) (L₀ : ℝ≥0) (k : ℕ) : Law (Option (Finset (ℙ K V))) := by
  letI : Finite A := Module.finite_of_finite K
  letI : Finite (Dual K A) := Module.finite_of_finite K
  letI : Finite (Dual K (Dual K A)) := Module.finite_of_finite K
  letI : Fintype (ℙ K A) := Fintype.ofFinite _
  letI : Fintype (ℙ K (Dual K A)) := Fintype.ofFinite _
  letI : Fintype (ℙ K (Dual K (Dual K A))) := Fintype.ofFinite _
  exact planeBranchLaw A X UX T UT τ P R L₀ k

theorem eventually_plane_auto {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)],
    ∀ (A : Submodule K V)
      (X UX : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))),
      finrank K A=3 → finrank K V≤5 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-400*beta η) → X.Nonempty → T.Nonempty → X⊆UX → T⊆UT →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^(finrank K V)*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (X.card:ℝ)≤100*(X∩flatPoints A).card →
      ∃k≤Nat.log 2 ((Nat.card K)^(finrank K V-finrank K A)),
        let p := planeAutoLaw A X UX T UT τ (P η σ D R) R L₀ k
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        ∀W,0<p (some W)→W⊆UX ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (2*P η σ D R) ∧
          (9/1000:ℝ)*X.card≤(W∩X).card := by
  filter_upwards [eventually_plane_branch hη hη' Cb hCb] with σ hh
  intro D b τ R L₀ K V _ _ _ _ _ _ A X UX T UT hA hV hq hr hL hb hbhi hτ hτhi hX hT hXU hTU hdens hprod hflat
  let : Finite A := Module.finite_of_finite K
  let : Finite (Dual K A) := Module.finite_of_finite K
  let : Finite (Dual K (Dual K A)) := Module.finite_of_finite K
  let : Fintype (ℙ K A) := Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K A)) := Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K (Dual K A))) := Fintype.ofFinite _
  let (point : ℙ K A) : Fintype (RadialLine point) := Fintype.ofFinite _
  let (point : ℙ K (Dual K A)) : Fintype (RadialLine point) := Fintype.ofFinite _
  exact hh D b τ R L₀ K V A X UX T UT hA hV hq hr hL hb hbhi hτ hτhi hX hT hXU hTU hdens hprod hflat
end SharpRamseyFive.ProjectiveRestriction

end OAI
