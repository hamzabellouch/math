import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.TwoPublic

namespace OAI


namespace SharpRamseyFive.ProjectiveRestriction
open Module ProjectiveIncidence ProjectiveTraining ScoreGeometry FiniteEntropy
open DyadicLifts ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)]
variable (A : Submodule K V) [Fintype (ℙ K A)] [Fintype (ℙ K (Dual K A))]
  [Fintype (ℙ K (Dual K (Dual K A)))]
noncomputable def planeHidden (X : Finset (ℙ K V)) (T : Finset (ℙ K (Dual K V))) (τ : ℝ) (k : ℕ) :=
  restrictions (image A.dualRestrict)
    (nonzeroLifts A (goodLifts A (flatSection A X) T (Real.sqrt τ/Nat.card K))) k
noncomputable def planeEnclosure (UT : Finset (ℙ K (Dual K V))) (k : ℕ) :=
  enclosure (image A.dualRestrict) (nonzeroLifts A UT) (2^k)
abbrev PlanePublicTape (UX : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V))) (P τ : ℝ) (k : ℕ) :=
  TwoPublicTape (flatSection A UX) (planeEnclosure A UT k) P (Real.sqrt τ) (1000*(Nat.card K)^2) (Nat.card K)
abbrev PlanePublicMessage (UX : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V))) (P τ : ℝ) (k : ℕ)
    (t : PlanePublicTape A UX UT P τ k) :=
  TwoPublicMessage (flatSection A UX) (planeEnclosure A UT k) P (Real.sqrt τ) (1000*(Nat.card K)^2) (Nat.card K) t
noncomputable def planePublicLaw (UX : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) (k : ℕ) : Law (PlanePublicTape A UX UT P τ k) :=
  twoPublicLaw (flatSection A UX) (planeEnclosure A UT k) P (Real.sqrt τ) R L₀ (1000*(Nat.card K)^2) (Nat.card K)
noncomputable def planePublicDecoded (UX : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (k : ℕ) (t : PlanePublicTape A UX UT P τ k) (m : PlanePublicMessage A UX UT P τ k t) : Finset (ℙ K V) :=
  (twoPublicDecoded (flatSection A UX) (planeEnclosure A UT k) P (Real.sqrt τ) (1000*(Nat.card K)^2) (Nat.card K) t m).map (flatEmbedding A)
noncomputable def planePublicEncoded (X UX : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (k : ℕ) (t : PlanePublicTape A UX UT P τ k) : Option (PlanePublicMessage A UX UT P τ k t) :=
  let n := reverseLength (Nat.card K) (Real.log (((flatSection A UX).card:ℝ)/(flatSection A X).card))
  if hn : n≤1000*(Nat.card K)^2 then
    twoPublicEncoded (flatSection A X) (flatSection A UX) (planeHidden A X T τ k) (planeEnclosure A UT k)
      P (Real.sqrt τ) (1000*(Nat.card K)^2) ⟨n,Nat.lt_succ_of_le hn⟩ (Nat.card K)
      ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^3/(planeHidden A X T τ k).card)
      (((planeHidden A X T τ k).card:ℝ)*Real.exp (2*P)) t
  else none
noncomputable def planePublicCost (UX : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (k : ℕ) (t : PlanePublicTape A UX UT P τ k) (m : PlanePublicMessage A UX UT P τ k t) : ℝ :=
  twoPublicCost (flatSection A UX) (planeEnclosure A UT k) P (Real.sqrt τ) (1000*(Nat.card K)^2) (Nat.card K) t m

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma planePublic_encoded_eq (X UX : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (k : ℕ) (n : Fin (1000*(Nat.card K)^2+1))
    (hn : n.val=reverseLength (Nat.card K) (Real.log (((flatSection A UX).card:ℝ)/(flatSection A X).card))) :
    planePublicEncoded A X UX T UT P τ k=
      twoPublicEncoded (flatSection A X) (flatSection A UX) (planeHidden A X T τ k) (planeEnclosure A UT k)
        P (Real.sqrt τ) (1000*(Nat.card K)^2) n (Nat.card K)
        ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^3/(planeHidden A X T τ k).card)
        (((planeHidden A X T τ k).card:ℝ)*Real.exp (2*P)) := by
  funext t
  unfold planePublicEncoded
  have hb : reverseLength (Nat.card K) (Real.log (((flatSection A UX).card:ℝ)/(flatSection A X).card))≤1000*(Nat.card K)^2 := by
    rw [←hn]; exact Nat.le_of_lt_succ n.prop
  rw [dite_eq_left hb]
  congr 1
  exact Fin.ext hn.symm
end SharpRamseyFive.ProjectiveRestriction

namespace SharpRamseyFive.ProjectiveRestriction
open Module ProjectiveIncidence ProjectiveTraining ScoreGeometry FiniteEntropy
open DyadicLifts ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

theorem eventually_plane_public {η : ℝ} (hη : 0<η) (hη' : η<1/10)
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
        let P₀ := P η σ D R
        let p := map (planePublicLaw A UX UT P₀ τ R L₀ k)
          (fun t=>(planePublicEncoded A X UX T UT P₀ τ k t).map (planePublicDecoded A UX UT P₀ τ k t))
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→W⊆UX ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (2*P₀) ∧
          (9/1000:ℝ)*X.card≤(W∩X).card) ∧
        (∀t m,planePublicEncoded A X UX T UT P₀ τ k t=some m →
          planePublicCost A UX UT P₀ τ k t m≤
          4000*(Nat.card K:ℝ)*P₀*(Real.log ((UX.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P₀)) := by
  filter_upwards [eventually_plane_public_complete hη hη' Cb hCb] with σ hh
  intro D b τ R L₀ K V _ _ _ _ _ _ A _ _ _ _ _ X UX T UT hA hV hq hr hL hb hbhi hτ hτhi hX hT hXU hTU hdens hprod hflat
  obtain ⟨k,hk,n,hn,hfail,hgood,hcost⟩ := hh D b τ R L₀ K V A X UX T UT hA hV hq hr hL hb hbhi hτ hτhi hX hT hXU hTU hdens hprod hflat
  refine ⟨k,hk,?_⟩
  dsimp only
  rw [planePublic_encoded_eq A X UX T UT (P η σ D R) τ k n hn]
  exact ⟨hfail,hgood,hcost⟩
end SharpRamseyFive.ProjectiveRestriction

end OAI
