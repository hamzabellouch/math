import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.Peeling
import OAI.Combinatorics.RamseyFive.Geometry.PlaneExceptionScalars
import OAI.Combinatorics.RamseyFive.Geometry.HighGeometryClosure

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V J : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [LinearOrder J]

noncomputable def hyperplanePeelExceptions (F : Finset J) (hF : F.Nonempty)
    (Flat : J→Submodule K V) (X XH S : Finset (ℙ K V))
    (Planes : Finset (Submodule K V)) (j : ℕ) (δ : ℝ≥0) (χ : ℝ) (Q : Finset (ℙ K V)) : Finset (ℙ K V) :=
  if XH=X\remaining F hF (fun i=>flatPoints (Flat i)) X j
  then highPlaneExceptions F hF Flat X S Planes j δ χ Q
  else residualPlaneExceptions Planes XH S Q δ χ

theorem hyperplanePeelExceptions_card (F : Finset J) (hF : F.Nonempty)
    (Flat : J→Submodule K V) (X XH S : Finset (ℙ K V))
    (Planes : Finset (Submodule K V))
    (hFlat : ∀i∈F,finrank K (Flat i)=4)
    (hcover : ∀H : Submodule K V,finrank K H=4 → ∃i∈F,Flat i=H)
    (hPlanes : ∀A∈Planes,finrank K A=3)
    (e : Prop) (he : e)
    (hXH : XH=peelSet e F hF (fun i=>flatPoints (Flat i)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _))
    (hS : S⊆XH) (δ : ℝ≥0) (hδ : 0<δ) (χ g : ℝ) (hg : 0≤g) (hχ : 0≤χ)
    (hn : (X.card:ℝ)=(Nat.card K:ℝ)^2*Real.exp g)
    (hcap : (X.card:ℝ)≤(Nat.card K:ℝ)^3)
    (hori : (X.card:ℝ)^2≤100*(Nat.card K:ℝ)^5)
    (hhigh : 8388608*(Nat.card K:ℝ)^2≤S.card) (Q : Finset (ℙ K V)) :
    ((hyperplanePeelExceptions F hF Flat X XH S Planes
      (peelLength e F hF (fun i=>flatPoints (Flat i)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)) δ χ Q).card:ℝ)≤
      X.card*((Nat.clog 2 S.card:ℝ)+1)*(3145728*Real.exp (-(4/5:ℝ)*g)+36872*Real.exp (-χ)) := by
  have hHX : XH⊆X := hXH▸peel_subset e F hF (fun i=>flatPoints (Flat i)) X _ _
  have hSH : (S.card:ℝ)≤XH.card := Nat.cast_le.mpr (Finset.card_le_card hS)
  have hHXn : (XH.card:ℝ)≤X.card := Nat.cast_le.mpr (Finset.card_le_card hHX)
  unfold hyperplanePeelExceptions
  split_ifs with hc
  · exact highPlaneExceptions_card F hF Flat X S hFlat hcover Planes hPlanes _ δ hδ χ g hg hχ hn hcap hori
      (hhigh.trans (hSH.trans hHXn)) Q
  · have hres := (peel_alternative e he F hF (fun i=>flatPoints (Flat i)) X ((Nat.card K)^2)
        (pow_pos (Nat.card_pos (α:=K)) _)).resolve_left (by simpa only [←hXH] using hc)
    have hcapH : ∀H : Submodule K V,finrank K H=4 → (XH.filter fun x=>x.submodule≤H).card≤(Nat.card K)^2 := by
      intro H hH
      obtain ⟨i,hi,hiH⟩ := hcover H hH
      have hh := hres.2 i hi
      rw [←hXH] at hh
      have heq : (XH.filter fun x=>x.submodule≤H)=XH∩flatPoints (Flat i) := by
        ext x;simp only [Finset.mem_filter,Finset.mem_inter,mem_flatPoints,hiH]
      rw [heq]
      exact hh.le
    have hh := residualPlaneExceptions_card Planes hPlanes XH S Q δ hδ χ hχ
      ((pow_le_pow_left₀ (Nat.cast_nonneg _) hHXn 2).trans hori) (hhigh.trans hSH) hcapH
    apply hh.trans
    apply mul_le_mul (mul_le_mul_of_nonneg_right hHXn (by positivity)) _ (by positivity) (by positivity)
    have hge : 0≤3145728*Real.exp (-(4/5:ℝ)*g) := by positivity
    nlinarith only [hge,Real.exp_nonneg (-χ)]

theorem literal_hyperplane_pair_moment [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] (hdim : finrank K V=5)
    (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K V)
    (X XH S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (Planes : Finset (Submodule K V)) (hPlanes : ∀A∈Planes,finrank K A=3)
    (hcomplete : ∀A : Submodule K V,finrank K A=3 → A∈Planes)
    (e : Prop) (_he : e)
    (hXH : XH=peelSet e F hF (fun i=>flatPoints (Flat i)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _))
    (hS : S⊆XH) (x : ℙ K V) [Fintype (RadialLine x)]
    (hO : ownCell F hF (fun i=>flatPoints (Flat i)) X
      (peelLength e F hF (fun i=>flatPoints (Flat i)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)) x⊆O x)
    (G : Finset (ℙ K (Dual K V))) (hG : ∀H∈G,Incident x H)
    (χ : ℝ) (hχ : (34359738369*2^200:ℝ)≤Real.exp χ)
    (hcap : (X.card:ℝ)≤(Nat.card K:ℝ)^3)
    (hscale : (X.card:ℝ)*(pointStrength (K:=K) S:ℝ)≤4*Nat.card K)
    (hhigh : 8388608*(Nat.card K:ℝ)^2≤S.card)
    (Lines : Finset (Submodule K V)) (hLines : ∀l : RadialLine x,l.val∈Lines)
    (Q : Finset (ℙ K V)) (hxQ : x∈Q)
    (hm : ∀H : G,mass (radialWeight x (outsideAt x S (O x)) (pointStrength S)) (pencilLines x G H)≤2)
    (hgood : x∉radialExceptions S O (pointStrength S) Lines Q (Nat.card K) X.card χ)
    (hpair : x∉hyperplanePeelExceptions F hF Flat X XH S Planes
      (peelLength e F hF (fun i=>flatPoints (Flat i)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)) (pointStrength S) χ Q) :
    (∑z : DistinctPairs G,strength (pencilLines x G)
      (radialWeight x (outsideAt x S (O x)) (pointStrength S)) z^200)≤
      dyadFactor (outsideAt x S (O x)).card χ*(geometryScale (Nat.card K) S.card)^2 := by
  have hHX : XH⊆X := hXH▸peel_subset e F hF (fun i=>flatPoints (Flat i)) X _ _
  have hSH : (S.card:ℝ)≤XH.card := Nat.cast_le.mpr (Finset.card_le_card hS)
  have hHXn : (XH.card:ℝ)≤X.card := Nat.cast_le.mpr (Finset.card_le_card hHX)
  have hq0 : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hS0 : (0:ℝ)<S.card := (by positivity : 0<8388608*(Nat.card K:ℝ)^2).trans_le hhigh
  have hH0 : (0:ℝ)<XH.card := hS0.trans_le hSH
  have hX0 : (0:ℝ)<X.card := hH0.trans_le hHXn
  have hδ : 0<pointStrength (K:=K) S := by
    rw [←NNReal.coe_pos,coe_pointStrength];positivity
  have hmass : (pointStrength (K:=K) S:ℝ)*S.card≤Nat.card K := by
    rw [coe_pointStrength,div_mul_cancel₀ _ hS0.ne']
  have hgoodH : x∉radialExceptions S O (pointStrength S) Lines Q (Nat.card K) XH.card χ := by
    exact fun hx=>hgood (radialExceptions_normalization S O (pointStrength S) Lines Q (Nat.card K) χ XH.card X.card hH0 hHXn hx)
  have hfin (N : ℕ) (hSN : S.card≤N) (hh :
      (∑z : DistinctPairs G,strength (pencilLines x G) (radialWeight x (outsideAt x S (O x)) (pointStrength S)) z^200)≤
      2^200*(Nat.clog 2 (outsideAt x S (O x)).card+1)*(((Nat.card K:ℝ)^4/N)^2*Real.exp (2*χ))) :
      (∑z : DistinctPairs G,strength (pencilLines x G) (radialWeight x (outsideAt x S (O x)) (pointStrength S)) z^200)≤
      dyadFactor (outsideAt x S (O x)).card χ*(geometryScale (Nat.card K) S.card)^2 := by
    apply hh.trans
    unfold dyadFactor geometryScale
    rw [show 2^200*((Nat.clog 2 (outsideAt x S (O x)).card:ℝ)+1)*(((Nat.card K:ℝ)^4/N)^2*Real.exp (2*χ))=
      (2^200*((Nat.clog 2 (outsideAt x S (O x)).card:ℝ)+1)*Real.exp (2*χ))*((Nat.card K:ℝ)^4/N)^2 by ring]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    gcongr
  unfold hyperplanePeelExceptions at hpair
  split_ifs at hpair with hc
  · apply hfin X.card (Finset.card_le_card (hS.trans hHX))
    apply score_pair_captured_moment_sharp x hdim F hF Flat X S O _ (hc▸hS) hO (pointStrength S) hδ G hG
      Planes hPlanes hcomplete χ Q hxQ (by exact_mod_cast hX0) hcap hscale (hhigh.trans (hSH.trans hHXn)) hχ hmass
      Lines hLines hm
      (off_radialExceptions S O (pointStrength S) Lines Q (Nat.card K) X.card χ x hgood)
      (off_highPlaneExceptions F hF Flat X S O Planes _ (pointStrength S) χ Q x hpair) 200 (le_refl _)
  · apply hfin XH.card (Finset.card_le_card hS)
    apply score_pair_residual_moment_sharp x hdim XH S O hS (pointStrength S) hδ G hG Planes hPlanes hcomplete
      χ Q hxQ (by exact_mod_cast hH0) (hHXn.trans hcap)
      ((mul_le_mul_of_nonneg_right hHXn (pointStrength (K:=K) S).coe_nonneg).trans hscale)
      (hhigh.trans hSH) hχ hmass Lines hLines hm
      (off_radialExceptions S O (pointStrength S) Lines Q (Nat.card K) XH.card χ x hgoodH)
      (off_residualPlaneExceptions Planes XH S Q O (pointStrength S) χ x hpair) 200 (le_refl _)

end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial PoissonScore
open Filter ParameterHierarchy MeasureTheory
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_literal_plane_global_trunc {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ) (L₀ : ℝ≥0),Range η σ D R → (L₀:ℝ)=L η σ D →
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [Fintype (ℙ K (I→K))] [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ (g : ℝ) (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
      (X S : Finset (ℙ K (I→K))) (t : ℝ) (ht0 : 0<t)
      (O : ℙ K (I→K)→Finset (ℙ K (I→K)))
      (Lines : Finset (Submodule K (I→K))) (Q : Finset (ℙ K (I→K))),
      2<q → Nat.card K=q → Real.exp σ=q → Fintype.card I=5 →
      P η σ D R/10000≤g → g≤σ →
      (∀j∈F,finrank K (Flat j)=3) →
      (∀U : Submodule K (I→K),finrank K U=3 → ∃j∈F,Flat j=U) →
      (X.card:ℝ)≤Real.exp (2*σ+g) →
      t=(Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5) →
      S=peelSet (P η σ D R/10000<g+σ/2) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0) →
      Real.exp (2*σ+g)/4≤S.card → (q:ℝ)^2≤S.card →
      (∀x,ownCell F hF (fun j => flatPoints (Flat j)) X
        (peelLength (P η σ D R/10000<g+σ/2) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0)) x⊆O x) →
      (∀l∈Lines,finrank K l=2) → (∀x∈Q,∀l : RadialLine x,l.val∈Lines) →
    (∑x : Q,∫ω,1-HighMoment.allTrunc R 5000 ω
      ∂batchMeasure (fun p : Fin R×RadialLine x.val =>
        L₀*radialWeight x.val (outsideAt x.val S (S∩O x.val)) (pointStrength S) p.2))≤Real.exp (2*σ) := by
  have hs := eventually_global_trunc_scalar hη hη' globalTruncConstant globalTruncConstant_pos
  have hm := eventually_plane_ambient_margins hη hη'
  filter_upwards [eventually_ge_atTop (1000:ℝ),hs,hm] with σ hσ hs hm
  intro D R L₀ hr hL q K I J _ _ _ _ _ _ _ g F hF Flat X S t ht0 O Lines Q
    hq hcard hσq hI hg hg' hFlat hcover hX ht hS hquarter hS2 hO hLines hQ
  have hdim : finrank K (I→K)=5 := by rw [Module.finrank_pi,hI]
  let P := ParameterHierarchy.P η σ D R
  have hm := hm D R hr
  have hlow : 100000000≤P/10000 := hm.1
  have hg0 : 0≤g := by dsimp [P] at hlow;linarith only [hg,hlow]
  have hgp : 100000000≤g+σ/2 := by dsimp [P] at hlow;linarith only [hg,hlow,hσ]
  have he : 3*σ/2+(g+σ/2)=2*σ+g := by ring
  have hen : P/10000<g+σ/2 := by dsimp [P];linarith only [hg,hσ]
  have hn0 : 0<(S.card:ℝ) := (by positivity : 0<Real.exp (2*σ+g)/4).trans_le hquarter
  have hδ : (pointStrength (K:=K) S:ℝ)=(q:ℝ)/S.card := by
    simp only [pointStrength,NNReal.coe_div,NNReal.coe_natCast,hcard]
  have hδ0 : 0<pointStrength (K:=K) S := by rw [←NNReal.coe_pos,hδ];positivity
  have hscale : Real.exp (2*σ+g)*(pointStrength (K:=K) S:ℝ)≤4*q := by
    rw [hδ,←mul_div_assoc]
    apply (div_le_iff₀ hn0).mpr
    nlinarith only [hquarter,(Nat.cast_nonneg q : (0:ℝ)≤q)]
  have hsub : S⊆X := hS▸peel_subset (P/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) X _ _
  have hSn : (S.card:ℝ)≤Real.exp (2*σ+g) := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hX
  have htE : t=Real.exp (σ+17*(g+σ/2)/15) := by
    rw [←he] at ht
    exact ht.trans (ScoreScalars.plane_threshold_exp rfl rfl)
  have htq : (q:ℝ)≤t := by rw [htE,←hσq];exact Real.exp_le_exp.mpr (by linarith only [hgp])
  have hmax : (pointStrength (K:=K) S:ℝ)*((q:ℝ)+1)≤2 := by
    rw [hδ,div_mul_eq_mul_div]
    apply (div_le_iff₀ hn0).mpr
    have hq1 : (1:ℝ)≤q := by exact_mod_cast (by omega : 1≤q)
    nlinarith only [hS2,hq1]
  have hbound : (∑x : Q,∫ω,1-HighMoment.allTrunc R 5000 ω
      ∂batchMeasure (fun p : Fin R×RadialLine x.val =>
        L₀*radialWeight x.val (outsideAt x.val S (O x.val)) (pointStrength S) p.2))≤
      globalTruncConstant*((R:ℝ)*(L₀:ℝ))^5000*Real.exp (8*σ-250*(g+σ/2))+
      globalTruncConstant*((R:ℝ)*(L₀:ℝ))^5000*σ*Real.exp (2*σ-4998*g) := by
    rcases peel_residual_real (P/10000<g+σ/2) hen F hF (fun j=>flatPoints (Flat j)) X t ht0 with hcap|⟨hJ,hres⟩
    · have hc : S⊆X\remaining F hF (fun j=>flatPoints (Flat j)) X
          (peelLength (P/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0)) := by rw [hS,hcap]
      have hjt := peel_length_real (P/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) X t ht0
      have hjq : (peelLength (P/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0):ℝ)*(Nat.card K:ℝ)≤X.card := by
        rw [hcard]
        exact (mul_le_mul_of_nonneg_left htq (Nat.cast_nonneg _)).trans hjt
      have hcut := ScoreScalars.plane_list_cutoff (n:=Real.exp (2*σ+g)) (q:=(q:ℝ))
        (by rw [he]) hσq.symm htE (by linarith only [hgp]) (by linarith only [hg',hσ])
        (pointStrength (K:=K) S).coe_nonneg (Nat.cast_nonneg _) (hjt.trans hX) hscale
      apply captured_global_trunc_exp_bound hdim F hF Flat X S hFlat _ hc hjq O hO
        (pointStrength S) L₀ hδ0 σ g (Real.exp (2*σ+g)) (by linarith) (by rw [hcard];exact hσq.symm)
        rfl hg' hX (by rwa [hcard]) _ Lines hLines Q hQ R
      exact hcut.trans (by have hh:=Real.exp_nonneg (-(g+σ/2)/20);linarith only [hh])
    · apply residual_global_trunc_exp_bound_dim hq hcard hI σ g S.card hσq.symm hσ hgp hg'
        hquarter S hSn O (pointStrength S) L₀ hδ0 hδ hmax Lines hLines Q hQ _ R
      intro U hU
      obtain ⟨j,hj,hjU⟩ := hcover U hU
      have hh := hres j hj
      rw [←hS,ht] at hh
      have heq : (S.filter fun y=>y.submodule≤U)=S∩flatPoints (Flat j) := by
        ext y;simp only [Finset.mem_filter,Finset.mem_inter,mem_flatPoints,hjU]
      rw [heq]
      exact hh.le
  simp only [outsideAt_clip] at ⊢
  apply hbound.trans
  have hP : (R:ℝ)*(L₀:ℝ)=P := by rw [mul_comm,hL];rfl
  rw [hP]
  exact hs D R g hr hg

end SharpRamseyFive.ScoreGeometry

end OAI
