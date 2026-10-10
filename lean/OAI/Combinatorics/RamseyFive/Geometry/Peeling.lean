import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.Training
import OAI.Combinatorics.RamseyFive.Geometry.PeelingGeometry

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [∀x : ℙ K V,Fintype (RadialLine x)]

lemma radialExceptions_low_density (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (hδ : 0<δ) (Lines : Finset (Submodule K V))
    (hLines : ∀l∈Lines,finrank K l=2) (Q : Finset (ℙ K V))
    (q n g χ : ℝ) (hq : 0<q) (hn : 0<n) (hsq : n^2=q^3*Real.exp (2*g))
    (hχ : 2*g<χ) (hmass : (δ:ℝ)*S.card≤q) :
    radialExceptions S O δ Lines Q q n χ=∅ := by
  unfold radialExceptions
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hx
  have ha : 0<((δ:ℝ)*2^i)/2 := by positivity
  have ha1 : ((δ:ℝ)*2^i)/2≤1 := by linarith only [(Finset.mem_filter.mp hi).2]
  have he := no_radial_exception_of_mass S O δ ha Lines hLines Q
    (ScoreScalars.radial_mass_of_scalar hq hn ha hmass
      (ScoreScalars.radial_low_density hq hn hsq hχ ha.le ha1))
  simp only [he,Finset.notMem_empty] at hx

end

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K I J : Type} [Field K] [Finite K] [Fintype I] [LinearOrder J]
  [∀x : ℙ K (I→K),Fintype (RadialLine x)]

theorem literal_plane_radial_exceptions {q : ℕ} [CharP K q]
    (hq : 2<q) (hcard : Nat.card K=q) (hI : Fintype.card I=4 ∨ Fintype.card I=5)
    (σ g b χ : ℝ) (hσq : Real.exp σ=q) (hσ : 1000≤σ)
    (hb : 100000000≤b) (hχb : 2*b<χ) (hghi : g≤2*σ)
    (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
    (hFlat : ∀j∈F,finrank K (Flat j)=3)
    (hcover : ∀U : Submodule K (I→K),finrank K U=3 → ∃j∈F,Flat j=U)
    (X : Finset (ℙ K (I→K))) (hX : (X.card:ℝ)≤Real.exp (3*σ/2+g))
    (t : ℝ) (ht : t=(Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5))
    (ht0 : 0<t)
    (S : Finset (ℙ K (I→K)))
    (hS : S=peelSet (b<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0))
    (hquarter : Real.exp (3*σ/2+g)/4≤S.card)
    (O : ℙ K (I→K)→Finset (ℙ K (I→K)))
    (hO : ∀x,ownCell F hF (fun j => flatPoints (Flat j)) X
      (peelLength (b<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0)) x⊆O x)
    (δ : ℝ≥0) (hδ : (δ:ℝ)=(q:ℝ)/S.card)
    (Lines : Finset (Submodule K (I→K))) (hLines : ∀l∈Lines,finrank K l=2)
    (Q : Finset (ℙ K (I→K))) :
    ((radialExceptions S (fun x => S∩O x) δ Lines Q q (Real.exp (3*σ/2+g)) χ).card:ℝ)≤
      Real.exp (3*σ/2+g)*(2664192*((Nat.clog 2 S.card:ℝ)+1)*Real.exp (-χ)) := by
  rw [radialExceptions_clip]
  have hq0 : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have hn0 : 0<(S.card:ℝ) := (by positivity : 0<Real.exp (3*σ/2+g)/4).trans_le hquarter
  have hδ0 : 0<δ := by rw [←NNReal.coe_pos,hδ];positivity
  have hsub : S⊆X := hS▸peel_subset (b<g) F hF (fun j => flatPoints (Flat j)) X _ _
  have hSn : (S.card:ℝ)≤Real.exp (3*σ/2+g) := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hX
  have hmass : (δ:ℝ)*S.card=(q:ℝ) := by rw [hδ];exact div_mul_cancel₀ _ (ne_of_gt hn0)
  have hscale : Real.exp (3*σ/2+g)*(δ:ℝ)≤4*q := by
    rw [hδ,←mul_div_assoc]
    apply (div_le_iff₀ hn0).mpr
    nlinarith only [hquarter,hq0]
  have hsq : (Real.exp (3*σ/2+g))^2=(q:ℝ)^3*Real.exp (2*g) := by
    rw [←hσq,←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add]
    congr 1;norm_num;ring
  by_cases hen : b<g
  · have hg : 100000000≤g := hb.trans hen.le
    have htE : t=Real.exp (σ+17*g/15) := ht.trans
      (ScoreScalars.plane_threshold_exp rfl rfl)
    have htq : (q:ℝ)≤t := by rw [htE,←hσq];apply Real.exp_le_exp.mpr;linarith only [hg]
    rcases peel_residual_real (b<g) hen F hF (fun j => flatPoints (Flat j)) X t ht0 with hcap|⟨hJ,hres⟩
    · have hc : S⊆X\remaining F hF (fun j => flatPoints (Flat j)) X
          (peelLength (b<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0)) := by
        rw [hS,hcap]
      have hjt := peel_length_real (b<g) F hF (fun j => flatPoints (Flat j)) X t ht0
      have hjq : (peelLength (b<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0):ℝ)*(Nat.card K:ℝ)≤X.card := by
        rw [hcard]
        exact (mul_le_mul_of_nonneg_left htq (Nat.cast_nonneg _)).trans hjt
      have hcut := ScoreScalars.plane_list_cutoff (n:=Real.exp (3*σ/2+g)) (q:=(q:ℝ))
        rfl hσq.symm htE (by linarith only [hg]) hghi δ.coe_nonneg (Nat.cast_nonneg _)
        (hjt.trans hX) hscale
      have hbound := captured_radial_exception_bound F hF Flat X S hFlat _ hc hjq O hO δ hδ0
        (Real.exp (3*σ/2+g)) g χ (Real.exp_pos _) hX (by simpa only [hcard] using hsq)
        (by linarith only [hg]) (by linarith only [hχb,hb]) (by simpa only [hcard] using hmass.le)
        (by simpa only [hcard] using hscale) hcut Lines hLines Q
      rw [hcard] at hbound
      apply hbound.trans
      gcongr
      norm_num
    · apply residual_radial_exception_bound hq hcard hI σ g S.card χ hσq hσ hg hghi hquarter S S
        (Finset.Subset.refl _) (le_refl _) hSn O δ hδ (by linarith only [hχb,hb]) _ Lines hLines Q
      intro U hU
      obtain ⟨j,hj,hjU⟩ := hcover U hU
      have hh := hres j hj
      rw [←hS,ht] at hh
      have he : (S.filter fun y => y.submodule≤U)=S∩flatPoints (Flat j) := by
        ext y
        simp only [Finset.mem_filter,Finset.mem_inter,mem_flatPoints,hjU]
      rw [he]
      exact hh.le
  · rw [radialExceptions_low_density S O δ hδ0 Lines hLines Q q (Real.exp (3*σ/2+g)) g χ
      hq0 (Real.exp_pos _) hsq (by linarith only [hχb,le_of_not_gt hen]) hmass.le]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

end
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

noncomputable def residualPlaneExceptions (Planes : Finset (Submodule K V))
    (X S Q : Finset (ℙ K V)) (δ : ℝ≥0) (χ : ℝ) : Finset (ℙ K V) :=
  (strengthDyads S.card δ).biUnion fun i =>
    if (Nat.card K:ℝ)^2<(X.card:ℝ)*((δ:ℝ)*2^i)^99
    then residualExceptions Planes X Q ((δ:ℝ)*2^i) χ else ∅

omit [FiniteDimensional K V] [Finite K] in
lemma off_residualPlaneExceptions (Planes : Finset (Submodule K V))
    (X S Q : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (δ : ℝ≥0) (χ : ℝ)
    (x : ℙ K V) [Fintype (RadialLine x)]
    (hx : x∉residualPlaneExceptions Planes X S Q δ χ) :
    ∀i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      (Nat.card K:ℝ)^2<(X.card:ℝ)*((δ:ℝ)*2^i)^99 →
      x∉residualExceptions Planes X Q ((δ:ℝ)*2^i) χ := by
  intro i hi hlarge hh
  apply hx
  exact Finset.mem_biUnion.mpr ⟨i,boundedOverlapDyads_subset x S (O x) δ hi,by simpa only [ite_eq_left hlarge] using hh⟩

theorem residualPlaneExceptions_card (Planes : Finset (Submodule K V))
    (hPlanes : ∀A∈Planes,finrank K A=3) (X S Q : Finset (ℙ K V))
    (δ : ℝ≥0) (hδ : 0<δ) (χ : ℝ) (hχ : 0≤χ)
    (hori : (X.card:ℝ)^2≤100*(Nat.card K:ℝ)^5)
    (hhigh : 8388608*(Nat.card K:ℝ)^2≤X.card)
    (hcap : ∀H : Submodule K V,finrank K H=4 →
      (X.filter fun x => x.submodule≤H).card≤(Nat.card K)^2) :
    ((residualPlaneExceptions Planes X S Q δ χ).card:ℝ)≤
      X.card*((Nat.clog 2 S.card:ℝ)+1)*(36864*Real.exp (-χ)) := by
  have hq0 : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hn : (0:ℝ)<X.card := (by positivity : 0<8388608*(Nat.card K:ℝ)^2).trans_le hhigh
  have hq2 : (Nat.card K:ℝ)^2≤X.card := by nlinarith only [hhigh,sq_nonneg (Nat.card K:ℝ)]
  have hh := biUnion_card_real_le (strengthDyads S.card δ)
    (fun i => if (Nat.card K:ℝ)^2<(X.card:ℝ)*((δ:ℝ)*2^i)^99
      then residualExceptions Planes X Q ((δ:ℝ)*2^i) χ else ∅)
    (e:=X.card*(36864*Real.exp (-χ))) (by
      intro i hi
      split_ifs with hlarge
      · have ha : 0<(δ:ℝ)*2^i := by positivity
        have ha2 := (Finset.mem_filter.mp hi).2
        have hbudget := (ScoreScalars.high_or_small hq0.le hn ha.le hhigh).resolve_right (not_le_of_gt hlarge)
        have hcap' : ∀H : Submodule K V,finrank K H=4 →
            (X.filter fun x => x.submodule≤H).card≤HighParameters.cap (Nat.card K) ((δ:ℝ)*2^i) := by
          intro H hH
          apply (hcap H hH).trans
          apply Nat.cast_le.mp (le_trans (b:=1024*(Nat.card K:ℝ)^2/((δ:ℝ)*2^i)) ?_ (Nat.le_ceil _))
          push_cast
          apply (le_div_iff₀ ha).mpr
          have hh := mul_le_mul_of_nonneg_left ha2 (sq_nonneg (Nat.card K:ℝ))
          nlinarith only [hh,sq_nonneg (Nat.card K:ℝ)]
        have hc := residual_exceptions_card Planes hPlanes X Q ((δ:ℝ)*2^i) χ
          (by exact_mod_cast hn) ha ha2 hori hbudget hχ hcap'
        apply hc.trans
        calc
          _ ≤ 36864*(X.card:ℝ)*Real.exp (-χ) := mul_le_mul
            (mul_le_mul_of_nonneg_left hq2 (by norm_num))
            (Real.exp_le_exp.mpr (by linarith only [hχ])) (Real.exp_nonneg _) (by positivity)
          _ = _ := by ring
      · simp only [Finset.card_empty,Nat.cast_zero]
        positivity)
  apply hh.trans
  have hc : ((strengthDyads S.card δ).card:ℝ)≤(Nat.clog 2 S.card:ℝ)+1 := by
    exact_mod_cast strengthDyads_card S.card δ
  calc
    _ ≤ ((Nat.clog 2 S.card:ℝ)+1)*(X.card*(36864*Real.exp (-χ))) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

end SharpRamseyFive.ScoreGeometry

end OAI
