import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.PlaneBranch
import OAI.Combinatorics.RamseyFive.Decoding.LargeTrainingCell

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy MeasurePublicTable Metadata FiniteEntropy ProjectiveRestriction
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology
variable {K I J : Type*} [Field K] [Finite K] [Fintype I] [LinearOrder J]
  [Fintype (I→K)] [Fintype (ℙ K (I→K))] [Fintype (ℙ K (Dual K (I→K)))]

abbrev ThreeBranch (σ : ℝ) (F : Finset J) :=
  Unit ⊕ ((Fin (Fintype.card (ℙ K (I→K))+1) ×
    TrainingCode (I→K) (listCap σ) (productCap σ) (Nat.card (I→K))) ⊕
    ({a : J // a∈F} × Fin (Nat.log 2 (Nat.card K)+1)))

noncomputable def threeBranchLaw (σ : ℝ) (F : Finset J)
    (Flat : J→Submodule K (I→K))
    (X U : Finset (ℙ K (I→K))) (T UT : Finset (ℙ K (Dual K (I→K))))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) (br : ThreeBranch (K:=K) (I:=I) σ F) :
    Law (Option (Finset (ℙ K (I→K)))) :=
  match br with
  | .inl _ => baseCaptureLaw X U P τ R L₀
  | .inr (.inl c) => scoredCaptureLaw X U c.1 (messageOwn c.2) (messageBase c.2 L₀)
      P τ (9/20) 10 R L₀
  | .inr (.inr a) => planeAutoLaw (Flat a.1.1) X U T UT τ P R L₀ a.2

theorem eventually_three_branch {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [Fintype (I→K)] [Fintype (ℙ K (I→K))] [Fintype (ℙ K (Dual K (I→K)))]
      [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ (F : Finset J) (_ : F.Nonempty) (Flat : J→Submodule K (I→K))
      (X U : Finset (ℙ K (I→K))) (T UT : Finset (ℙ K (Dual K (I→K)))),
      Nat.card K=q → Real.exp σ=q → Fintype.card I=4 →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-400*beta η) → X⊆U → T⊆UT → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^4*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (∀j∈F,finrank K (Flat j)=3) →
      (∀V : Submodule K (I→K),finrank K V=3 → ∃j∈F,Flat j=V) →
      ∃br : ThreeBranch (K:=K) (I:=I) σ F,
        let p := threeBranchLaw σ F Flat X U T UT (P η σ D R) τ R L₀ br
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        ∀W,0<p (some W)→W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P η σ D R) ∧
          (9/1000:ℝ)*X.card≤(W∩X).card := by
  filter_upwards [eventually_three_public_law hη hη' Cb hCb,
    eventually_plane_auto hη hη' Cb hCb,eventually_ge_atTop (100000:ℝ)] with σ hscore hplane hσ
  intro D b τ R L₀ q K I J _ _ _ _ _ _ _ _ _ F hF Flat X U T UT hcard hσq hI hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod hFlat hcover
  have hσ1 : 1≤σ := by linarith
  have hP : 1≤P η σ D R :=
    (Real.one_le_rpow hσ1 (mul_nonneg (by norm_num) (beta_pos hη).le)).trans
      (finite_bounds hη hη' (by linarith) hr).2.2.2.2.2.1
  have hP0 : 0≤P η σ D R := by linarith
  have hq : (Nat.card K:ℝ)=Real.exp σ := by rw [hcard,hσq]
  have hd : finrank K (I→K)=4 := by rw [Module.finrank_pi,hI]
  have hqpos : (0:ℝ)<Nat.card K := by rw [hq];exact Real.exp_pos σ
  have hX : X.Nonempty := by
    have hp : 0<(X.card:ℝ)*T.card := lt_of_lt_of_le (by positivity : (0:ℝ)<(Nat.card K:ℝ)^4*Real.exp (-b)) hprod
    exact Finset.card_pos.mp (Nat.cast_pos.mp (pos_of_mul_pos_left hp (Nat.cast_nonneg _)))
  have hT : T.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hX.card_pos hXT)
  by_cases hn : (X.card:ℝ)≤100*(Nat.card K:ℝ)*P η σ D R
  · refine ⟨.inl (),?_,?_⟩
    · exact (baseSmallLaw X U hXU (P η σ D R) τ hP hn R L₀).1.trans (by positivity)
    · intro W hW
      have hw := baseCaptureLaw_positive X U (P η σ D R) τ R L₀ W hW
      refine ⟨hw.1,hw.2.1.trans ?_,?_⟩
      · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg _)
      · exact (mul_le_mul_of_nonneg_right (by norm_num : (9/1000:ℝ)≤9/10) (Nat.cast_nonneg _)).trans hw.2.2
  · let g := Real.log (X.card:ℝ)-3*σ/2
    have hXexp : (X.card:ℝ)=Real.exp (3*σ/2+g) := by
      dsimp only [g]
      rw [show 3*σ/2+(Real.log (X.card:ℝ)-3*σ/2)=Real.log (X.card:ℝ) by ring,Real.exp_log (by exact_mod_cast hX.card_pos)]
    let t := (Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5)
    have ht : 0<t := by dsimp [t];positivity
    let S := peelSet (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let m := peelLength (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let C := clippedPart S F hF (fun j=>flatPoints (Flat j)) X m
    by_cases hsmall : ∀i,(C i).card≤(S.card:ℝ)/25
    · have hτhi' := hτhi.trans (Real.rpow_le_rpow_of_exponent_le hσ1
        (by have := beta_pos hη;linarith : -400*beta η≤-200*beta η))
      obtain ⟨_,_,c,hf,hg⟩ := hscore D b τ g R L₀ q K I J F hF Flat X U T
        hcard hσq hI hr hL hb hbhi hτ hτhi' hXU hXT hdens hprod hXexp (lt_of_not_ge hn) hFlat hcover hsmall
      let n : Fin (Fintype.card (ℙ K (I→K))+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
      refine ⟨.inr (.inl (n,c)),?_,?_⟩
      · exact hf.trans (by nlinarith only [Real.exp_pos (-(Nat.card K:ℝ))])
      · intro W hW
        obtain ⟨hWU,hsize,hcap⟩ := hg W hW
        exact ⟨hWU,hsize,(mul_le_mul_of_nonneg_right (by norm_num : (9/1000:ℝ)≤9/20) (Nat.cast_nonneg _)).trans hcap⟩
    · have hSX : S⊆X := peel_subset _ F hF _ X _ _
      have hret' : X.card≤2*S.card := peel_half _ F hF _ X _ _
      have hret : X.card≤4*S.card := by omega
      obtain ⟨a,ha,hlarge⟩ := large_clipped_part X S X hSX hret F hF (fun j=>flatPoints (Flat j)) m hsmall
      obtain ⟨k,hk,hf,hg⟩ := hplane D b τ R L₀ K (I→K) (Flat a) X U T UT
        (hFlat a ha) (by omega) hq hr hL hb hbhi hτ hτhi hX hT hXU hTU hdens (by simpa only [hd] using hprod) hlarge
      have hk' : k≤Nat.log 2 (Nat.card K) := by simpa only [hd,hFlat a ha,Nat.reduceSub,pow_one] using hk
      refine ⟨.inr (.inr (⟨a,ha⟩,⟨k,Nat.lt_succ_of_le hk'⟩)),hf,?_⟩
      intro W hW
      obtain ⟨hWU,hsize,hcap⟩ := hg W hW
      refine ⟨hWU,hsize.trans ?_,hcap⟩
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg _)
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ProjectiveTraining
open Module
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]

omit [Finite K] [FiniteDimensional K V] [Fintype V] in
lemma exists_flat_finrank (d : ℕ) (hd : d≤finrank K V) :
    ∃A : Submodule K V,finrank K A=d := by
  obtain ⟨s,hn,hs⟩ := exists_finset_linearIndependent_of_le_finrank (R:=K) (M:=V) hd
  refine ⟨Submodule.span K (s:Set V),?_⟩
  have hspan : Set.range (fun x : s => (x:V))=(s:Set V) := by ext x;simp
  rw [←hspan,finrank_span_eq_card hs,Fintype.card_coe,hn]

noncomputable def flatEnumeration : Fin (Fintype.card (Submodule K V))→Submodule K V :=
  (Fintype.equivFin (Submodule K V)).symm
noncomputable def flatIndices (d : ℕ) : Finset (Fin (Fintype.card (Submodule K V))) :=
  Finset.univ.filter fun i=>finrank K (flatEnumeration (K:=K) (V:=V) i)=d
omit [Finite K] [FiniteDimensional K V] in
lemma flatIndices_cover (d : ℕ) (A : Submodule K V) (hA : finrank K A=d) :
    ∃i∈flatIndices (K:=K) (V:=V) d,flatEnumeration i=A := by
  let i := Fintype.equivFin (Submodule K V) A
  have he : flatEnumeration i=A := (Fintype.equivFin _).symm_apply_apply A
  exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [he,hA]⟩,he⟩
omit [Finite K] [FiniteDimensional K V] in
lemma flatIndices_nonempty (d : ℕ) (hd : d≤finrank K V) :
    (flatIndices (K:=K) (V:=V) d).Nonempty := by
  obtain ⟨A,hA⟩ := exists_flat_finrank d hd
  obtain ⟨i,hi,_⟩ := flatIndices_cover d A hA
  exact ⟨i,hi⟩
omit [Finite K] [FiniteDimensional K V] in
lemma flatIndices_rank (d : ℕ) (i) (hi : i∈flatIndices (K:=K) (V:=V) d) :
    finrank K (flatEnumeration i)=d := (Finset.mem_filter.mp hi).2
end SharpRamseyFive.ProjectiveTraining

end OAI
