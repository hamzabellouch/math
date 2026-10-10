import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.ThreePublic

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining Metadata Filter ParameterHierarchy FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [Fintype K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K A)]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K A))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K (Dual K A)))]

abbrev ThreeCoordinateTape (e : V≃ₗ[K](Fin 4→K))
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V))) (σ P τ : ℝ) :=
  ThreePublicTape (U.map (projectiveEquiv e).toEmbedding)
    (UT.map (projectiveEquiv e.symm.dualMap).toEmbedding) σ P τ
abbrev ThreeCoordinateMessage (e : V≃ₗ[K](Fin 4→K))
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V))) (σ P τ : ℝ)
    (t : ThreeCoordinateTape e U UT σ P τ) :=
  ThreePublicMessage (U.map (projectiveEquiv e).toEmbedding)
    (UT.map (projectiveEquiv e.symm.dualMap).toEmbedding) σ P τ t
noncomputable def threeCoordinatePublicLaw (e : V≃ₗ[K](Fin 4→K))
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    Law (ThreeCoordinateTape e U UT σ P τ) :=
  threePublicLaw (U.map (projectiveEquiv e).toEmbedding)
    (UT.map (projectiveEquiv e.symm.dualMap).toEmbedding) σ P τ R L₀
noncomputable def threeCoordinateEncoded (e : V≃ₗ[K](Fin 4→K))
    (X U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (t : ThreeCoordinateTape e U UT σ P τ) : Option (ThreeCoordinateMessage e U UT σ P τ t) :=
  threeCertifiedEncoded (X.map (projectiveEquiv e).toEmbedding) (U.map (projectiveEquiv e).toEmbedding)
    (T.map (projectiveEquiv e.symm.dualMap).toEmbedding) (UT.map (projectiveEquiv e.symm.dualMap).toEmbedding)
    σ P τ R L₀ t
noncomputable def threeCoordinateDecoded (e : V≃ₗ[K](Fin 4→K))
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V))) (σ P τ : ℝ)
    (t : ThreeCoordinateTape e U UT σ P τ) (m : ThreeCoordinateMessage e U UT σ P τ t) : Finset (ℙ K V) :=
  (threePublicDecoded (U.map (projectiveEquiv e).toEmbedding)
    (UT.map (projectiveEquiv e.symm.dualMap).toEmbedding) σ P τ t m).map (projectiveEquiv e).symm.toEmbedding
noncomputable def threeCoordinateCost (e : V≃ₗ[K](Fin 4→K))
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V))) (σ P τ : ℝ)
    (t : ThreeCoordinateTape e U UT σ P τ) (m : ThreeCoordinateMessage e U UT σ P τ t) : ℝ :=
  threePublicCost (U.map (projectiveEquiv e).toEmbedding)
    (UT.map (projectiveEquiv e.symm.dualMap).toEmbedding) σ P τ t m
noncomputable def threeCoordinateCertifiedLaw (e : V≃ₗ[K](Fin 4→K)) (σ : ℝ)
    (X U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) : Law (Option (Finset (ℙ K V))) :=
  map (threeCoordinatePublicLaw e U UT σ P τ R L₀)
    (fun t=>(threeCoordinateEncoded e X U T UT σ P τ R L₀ t).map (threeCoordinateDecoded e U UT σ P τ t))
omit [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma threeCoordinateCertified_exact (e : V≃ₗ[K](Fin 4→K)) (σ : ℝ)
    (X U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    threeCoordinateCertifiedLaw e σ X U T UT P τ R L₀=
    map (threeCertifiedLaw (X.map (projectiveEquiv e).toEmbedding)
      (U.map (projectiveEquiv e).toEmbedding)
      (T.map (projectiveEquiv e.symm.dualMap).toEmbedding)
      (UT.map (projectiveEquiv e.symm.dualMap).toEmbedding) σ P τ R L₀)
      (Option.map fun Z=>Z.map (projectiveEquiv e).symm.toEmbedding) := by
  simp only [threeCoordinateCertifiedLaw,threeCoordinatePublicLaw,threeCoordinateEncoded,
    threeCertifiedLaw,map_comp,Option.map_map,Function.comp_def]
  rfl

theorem eventually_three_coordinates_certified {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [Fintype K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K A)]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K A))]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K (Dual K A)))],
    ∀ (e : V≃ₗ[K](Fin 4→K))
      (X U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))),
      Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-400*beta η) → X⊆U → T⊆UT → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^4*Real.exp (-b)≤(X.card:ℝ)*T.card →
        let p := threeCoordinateCertifiedLaw e σ X U T UT (P η σ D R) τ R L₀
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→CaptureBound X U (9/1000) ((X.card:ℝ)*Real.exp (10*P η σ D R)) W) ∧
        (∀t m,threeCoordinateEncoded e X U T UT σ (P η σ D R) τ R L₀ t=some m →
          threeCoordinateCost e U UT σ (P η σ D R) τ t m≤
            4100*(Nat.card K:ℝ)*(P η σ D R)*
              (Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+(P η σ D R))) := by
  filter_upwards [eventually_three_certified hη hη' Cb hCb] with σ hh
  intro D b τ R L₀ q K V _ _ _ _ _ _ _ _ _ _ _ _ _ _ e X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod
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
  let (x : ℙ K (Fin 4→K)) : Fintype (RadialLine x) := Fintype.ofFinite _
  obtain ⟨hf,hg,hc⟩ := hh D b τ R L₀ q K X' U' T' UT' hcard hσq hr hL hb hbhi hτ hτhi hXU' hTU'
    (by simpa only [X',T',Finset.card_map] using hXT) hdens' hprod'
  let pp := threeCertifiedLaw X' U' T' UT' σ (P η σ D R) τ R L₀
  refine ⟨?_,?_,?_⟩
  · rw [threeCoordinateCertified_exact]
    rw [map_option_none]
    exact hf
  · intro W hW
    rw [threeCoordinateCertified_exact] at hW
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
        simpa only [X',Finset.card_map,Finset.inter_comm] using hz.2.2
  · intro t m hm
    have hh := hc t m hm
    simpa only [threeCoordinateCost,U',X',T',UT',Finset.card_map] using hh
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def publicGeneralReverseResult (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (_hB : B.Nonempty)
    (H : ℕ) (n : Fin (H+1)) (q MA MB c : ℝ) (_hc : 0<c)
    (Y : Option (Finset (ℙ K (Dual K V)))) (t : UniversalFresh (ℙ K (Dual K V)) H q) :
    Option (Finset (ℙ K V)) :=
  match Y with
  | none => none
  | some W => if _hW : CaptureBound B UB c MB W then
      (universalFreshEncoded Incident A UA (B∩W) W Finset.inter_subset_right H n q MA t).map
        (fun m=>UA∩universalFreshDecoded Incident W H q t m)
    else none

omit [Finite K] [FiniteDimensional K V] in
theorem publicGeneralReverseResult_law (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty)
    (H : ℕ) (n : Fin (H+1)) (q MA MB c : ℝ) (hc : 0<c)
    (Y : Option (Finset (ℙ K (Dual K V)))) :
    map (universalFreshLaw (ℙ K (Dual K V)) H q) (publicGeneralReverseResult A UA B UB hB H n q MA MB c hc Y)=
      generalNextCapLaw A UA B UB hB c hc n q MA MB Y := by
  cases Y with
  | none => exact map_const _ none
  | some W =>
    change map (universalFreshLaw (ℙ K (Dual K V)) H q)
      (fun t=>if _hW : CaptureBound B UB c MB W then
        (universalFreshEncoded Incident A UA (B∩W) W Finset.inter_subset_right H n q MA t).map
          (fun m=>UA∩universalFreshDecoded Incident W H q t m) else none) = _
    dsimp only [generalNextCapLaw]
    split_ifs with hv
    · have hW := (hv.nonempty hB hc).mono Finset.inter_subset_right
      have hh := congrArg (fun p=>map p (Option.map fun Z=>UA∩Z))
        (universalFreshEncoded_law Incident A UA (B∩W) W Finset.inter_subset_right hW H n q MA)
      rw [ambientCapLaw_restrict,map_comp] at hh
      simpa only [Function.comp_def,Option.map_map] using hh
    · exact map_const _ none
end SharpRamseyFive.ProjectiveIncidence

end OAI
