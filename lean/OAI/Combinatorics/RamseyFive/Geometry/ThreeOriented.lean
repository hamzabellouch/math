import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.ThreeSelected

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

noncomputable def threeOrientedLaw (hd : finrank K V=4) (σ : ℝ)
    (S U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty)
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) : Law (Option (Finset (ℙ K V))) :=
  if S.card≤T.card then threeFreeLaw hd σ S U T UT P τ R L₀ else
    optionCompose (threeFreeLaw (Subspace.dual_finrank_eq.trans hd) σ T UT
      (S.map bidualPoint.toEmbedding) (U.map bidualPoint.toEmbedding) P τ R L₀)
      (generalNextCapLaw S U T UT hT (9/1000) (by norm_num)
        (reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card)))
        (Nat.card K) ((320/((9:ℝ)/1000)+320)*(Nat.card K:ℝ)^4/T.card)
        ((T.card:ℝ)*Real.exp (10*P)))

lemma three_cap_size_absorb (Q s t b P : ℝ) (hs : 0≤ s) (ht : 0<t)
    (hp : Q*Real.exp (-b)≤ s*t) (hP : 0≤P) (hb : b≤P) (hexp : 1000≤Real.exp P) :
    (320/((9:ℝ)/1000)+320)*Q/t≤ s*Real.exp (10*P) := by
  have hh := source_product_to_cap Q s t b (320/((9:ℝ)/1000)+320) hs ht (by norm_num) hp
  have hh2 : (1000000:ℝ)≤Real.exp (2*P) := by
    calc
      _ = (1000:ℝ)*1000 := by norm_num
      _ ≤ Real.exp P*Real.exp P := mul_le_mul hexp hexp (by norm_num) (Real.exp_pos _).le
      _ = _ := by rw [←Real.exp_add];congr 1;ring
  have hc : 320/((9:ℝ)/1000)+320≤Real.exp (2*P) := by linarith only [hh2]
  have he : (320/((9:ℝ)/1000)+320)*Real.exp b≤Real.exp (10*P) := by
    calc
      _ ≤ Real.exp (2*P)*Real.exp P := mul_le_mul hc (Real.exp_le_exp.mpr hb) (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (3*P) := by rw [←Real.exp_add];congr 1;ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  exact hh.trans (mul_le_mul_of_nonneg_left he hs)

theorem eventually_three_oriented {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=4) (S U : Finset (ℙ K V))
      (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty),
      Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-400*beta η) → S.Nonempty → S⊆U → T⊆UT →
      (Nat.card K:ℝ)*(incidences S T:ℝ)≤τ*S.card*T.card →
      (Nat.card K:ℝ)^4*Real.exp (-b)≤(S.card:ℝ)*T.card →
        let p := threeOrientedLaw hd σ S U T UT hT (P η σ D R) τ R L₀
        p none≤3*Real.exp (-(Nat.card K:ℝ)) ∧
        ∀W,0<p (some W)→CaptureBound S U (9/1000) ((S.card:ℝ)*Real.exp (10*P η σ D R)) W := by
  have hsparse : ∀ᶠ σ : ℝ in atTop,σ^(-400*beta η)≤(9:ℝ)/1000000 := by
    have hp : 0<400*beta η := mul_pos (by norm_num) (beta_pos hη)
    exact (Filter.Eventually.mono ((tendsto_rpow_neg_atTop hp).eventually_lt_const
      (by norm_num : (0:ℝ)<9/1000000))) fun σ h=>by simpa only [neg_mul] using h.le
  filter_upwards [eventually_three_free hη hη' Cb hCb,
    eventually_reverse_parameters hη hη' Cb hCb,hsparse,eventually_ge_atTop (1:ℝ)] with σ hbase hrev hsparse hσ
  intro D b τ R L₀ q K V _ _ _ _ _ _ _ _ _ hd S U T UT hT hcard hσq hr hL hb hbhi hτ hτhi hS hSU hTU hdens hprod
  have hq : (Nat.card K:ℝ)=Real.exp σ := by rw [hcard,hσq]
  have hτ200 := hτhi.trans (Real.rpow_le_rpow_of_exponent_le hσ
    (by have := beta_pos hη;linarith : -400*beta η≤-200*beta η))
  obtain ⟨hP,hbP,heP,_,hq3⟩ := hrev D R b τ hr hbhi hτ.le hτ200
  have hqnat : 3≤Nat.card K := by exact_mod_cast (hq ▸ hq3 : (3:ℝ)≤Nat.card K)
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast (by omega : 1≤Nat.card K)
  dsimp only [threeOrientedLaw]
  split_ifs with hST
  · obtain ⟨hf,hg⟩ := hbase D b τ R L₀ q K V hd S U T UT hcard hσq hr hL hb hbhi hτ hτhi hSU hTU hST hdens hprod
    exact ⟨hf.trans (by nlinarith only [Real.exp_pos (-(Nat.card K:ℝ))]),hg⟩
  · have hddual : finrank K (Dual K V)=4 := Subspace.dual_finrank_eq.trans hd
    have hTS : T.card≤(S.map bidualPoint.toEmbedding).card := by rw [Finset.card_map];omega
    have hSU' : S.map bidualPoint.toEmbedding⊆U.map bidualPoint.toEmbedding := Finset.map_subset_map.mpr hSU
    have hdens' : (Nat.card K:ℝ)*(incidences T (S.map bidualPoint.toEmbedding):ℝ)≤
        τ*T.card*(S.map bidualPoint.toEmbedding).card := by
      rw [incidences_bidual,Finset.card_map]
      nlinarith only [hdens]
    have hprod' : (Nat.card K:ℝ)^4*Real.exp (-b)≤(T.card:ℝ)*(S.map bidualPoint.toEmbedding).card := by
      rw [Finset.card_map];nlinarith only [hprod]
    obtain ⟨hf,hg⟩ := hbase D b τ R L₀ q K (Dual K V) hddual T UT
      (S.map bidualPoint.toEmbedding) (U.map bidualPoint.toEmbedding)
      hcard hσq hr hL hb hbhi hτ hτhi hTU hSU' hTS hdens' hprod'
    have hsparse' : 1000*(Nat.card K:ℝ)*incidences S T≤(9:ℝ)/1000*S.card*T.card := by
      have htau := hτhi.trans hsparse
      have hh := mul_le_mul_of_nonneg_left hdens (by norm_num : (0:ℝ)≤1000)
      have hh' := mul_le_mul_of_nonneg_right htau (show (0:ℝ)≤(S.card:ℝ)*T.card from mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      nlinarith only [hh,hh']
    have hl := reverseLength_spec (Nat.card K) (Real.log ((U.card:ℝ)/S.card)) hq1 (enclosure_gap_nonneg S U hS hSU)
    obtain ⟨hf',hg'⟩ := reverse_after_general_capture (d:=3) hd (by norm_num) hqnat S U hS hSU T UT hT
      (9/1000) (by norm_num) (by norm_num)
      ((T.card:ℝ)*Real.exp (10*P η σ D R)) (2*Real.exp (-(Nat.card K:ℝ)))
      (threeFreeLaw hddual σ T UT (S.map bidualPoint.toEmbedding) (U.map bidualPoint.toEmbedding) (P η σ D R) τ R L₀)
      hf hg hsparse' (reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card))) hl.1 hl.2.1
    refine ⟨by convert hf' using 1; ring,?_⟩
    intro W hW
    have hw := hg' W hW
    refine ⟨hw.1,hw.2.1.trans ?_,?_⟩
    · exact three_cap_size_absorb _ _ _ _ _ (Nat.cast_nonneg _) (by exact_mod_cast hT.card_pos) hprod (by linarith) hbP heP
    · exact (mul_le_mul_of_nonneg_right (by norm_num : (9/1000:ℝ)≤9/10) (Nat.cast_nonneg _)).trans hw.2.2
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ProjectiveRestriction
open Module ProjectiveIncidence ProjectiveTraining ScoreGeometry FiniteEntropy
open DyadicLifts ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)]

noncomputable def threeFlatBranchLaw (A : Submodule K V) (hA : finrank K A=4) (σ : ℝ)
    (X UX : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (τ P : ℝ) (R : ℕ) (L₀ : ℝ≥0) (k : ℕ) : Law (Option (Finset (ℙ K V))) := by
  letI : Finite A := Module.finite_of_finite K
  letI : Finite (Dual K A) := Module.finite_of_finite K
  letI : Finite (Dual K (Dual K A)) := Module.finite_of_finite K
  letI : Fintype (ℙ K A) := Fintype.ofFinite _
  letI : Fintype (ℙ K (Dual K A)) := Fintype.ofFinite _
  letI : Fintype (ℙ K (Dual K (Dual K A))) := Fintype.ofFinite _
  let S := flatSection A X
  let US := flatSection A UX
  let G := nonzeroLifts A (goodLifts A S T (Real.sqrt τ/Nat.card K))
  let T₀ := restrictions (image A.dualRestrict) G k
  let UT₀ := enclosure (image A.dualRestrict) (nonzeroLifts A UT) (2^k)
  exact if h : T₀.Nonempty then
    map (threeOrientedLaw hA σ S US T₀ UT₀ h P (Real.sqrt τ) R L₀)
      (Option.map fun Z=>Z.map (flatEmbedding A))
    else pureLaw none

theorem eventually_three_flat_branch {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V] [Fintype (ℙ K V)],
    ∀ (A : Submodule K V) (hA : finrank K A=4)
      (X UX : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))),
      finrank K V≤5 → Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-800*beta η) → X.Nonempty → T.Nonempty → X⊆UX → T⊆UT →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^(finrank K V)*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (X.card:ℝ)≤100*(X∩flatPoints A).card →
      ∃k≤Nat.log 2 ((Nat.card K)^(finrank K V-finrank K A)),
        let p := threeFlatBranchLaw A hA σ X UX T UT τ (P η σ D R) R L₀ k
        p none≤3*Real.exp (-(Nat.card K:ℝ)) ∧
        ∀W,0<p (some W)→W⊆UX ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P η σ D R) ∧
          (9/100000:ℝ)*X.card≤(W∩X).card := by
  have ht : ∀ᶠ σ : ℝ in atTop,σ^(-400*beta η)<(1:ℝ)/200 := by
    have hp : 0<400*beta η := mul_pos (by norm_num) (beta_pos hη)
    simpa only [neg_mul] using (tendsto_rpow_neg_atTop hp).eventually_lt_const
      (by norm_num : (0:ℝ)<1/200)
  filter_upwards [eventually_three_oriented hη hη' (Cb+1) (by linarith),
    eventually_restriction_overheads hη hη',ht,eventually_ge_atTop (1:ℝ)] with σ hbase hover ht hσ
  intro D b τ R L₀ q K V _ _ _ _ _ _ _ A hA X UX T UT hV hcard hσq hr hL hb hbhi hτ hτhi hX hT hXU hTU hdens hprod hflat
  let : Finite A := Module.finite_of_finite K
  let : Finite (Dual K A) := Module.finite_of_finite K
  let : Finite (Dual K (Dual K A)) := Module.finite_of_finite K
  let : Fintype (ℙ K A) := Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K A)) := Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K (Dual K A))) := Fintype.ofFinite _
  have hq : (Nat.card K:ℝ)=Real.exp σ := by rw [hcard,hσq]
  have htroot : Real.sqrt τ≤σ^(-400*beta η) := by
    have hh := root_density_scale (j:=3) (d:=4) hσ hτ.le (beta_pos hη).le (by norm_num) (by norm_num)
      (show τ≤σ^(-200*(2:ℝ)^(4-2)*beta η) by norm_num;simpa only [neg_mul] using hτhi)
    convert hh using 1; norm_num
  have hsmall : Real.sqrt τ≤1/200 := htroot.trans ht.le
  obtain ⟨hS,hSU,hsX,hxs,k,hk,hT₀,hTU₀,hp,hdegrees,hd,hgap,hsgap⟩ :=
    original_large_cell A X UX T UT hX hT hXU hTU τ b hτ hsmall hflat hprod hdens
  let S := flatSection A X
  let US := flatSection A UX
  let M := (Nat.card K)^(finrank K V-finrank K A)
  let B := b+Real.log (400*(Nat.log 2 M+1:ℝ))
  let G := nonzeroLifts A (goodLifts A S T (Real.sqrt τ/Nat.card K))
  let T₀ := restrictions (image A.dualRestrict) G k
  let UT₀ := enclosure (image A.dualRestrict) (nonzeroLifts A UT) (2^k)
  let pp := threeOrientedLaw hA σ S US T₀ UT₀ hT₀ (P η σ D R) (Real.sqrt τ) R L₀
  have hB : 0≤B := by
    refine add_nonneg hb (Real.log_nonneg ?_)
    have hn : (0:ℝ)≤Nat.log 2 M := by positivity
    linarith only [hn]
  have hBhi : B≤(Cb+1)*D*σ^(6*beta η) :=
    (hover D R b Cb (Nat.card K) (finrank K V-finrank K A) hr hq (by omega) hbhi).2.2
  have hp' : (Nat.card K:ℝ)^4*Real.exp (-B)≤(S.card:ℝ)*T₀.card := by
    simpa only [S,T₀,G,B,M,hA,Nat.cast_add,Nat.cast_one] using hp
  obtain ⟨hfail,hgood⟩ := hbase D B (Real.sqrt τ) R L₀ q K A hA S US T₀ UT₀ hT₀ hcard hσq hr hL
    hB hBhi (Real.sqrt_pos.mpr hτ) htroot hS hSU hTU₀ hd hp'
  refine ⟨k,hk,?_⟩
  dsimp only [threeFlatBranchLaw]
  rw [dite_eq_left hT₀]
  change map pp (Option.map fun Z=>Z.map (flatEmbedding A)) none≤_ ∧ _
  refine ⟨by rw [map_option_none];exact hfail,?_⟩
  intro W hW
  obtain ⟨Z,hZ,he⟩ := map_positive pp (Option.map fun Z=>Z.map (flatEmbedding A)) (some W) hW
  cases Z with
  | none => simp at he
  | some Z =>
    have he' : Z.map (flatEmbedding A)=W := Option.some.inj he
    subst W
    have hz := hgood Z hZ
    obtain ⟨hu,hcard',hcap⟩ := section_decoder A X UX Z hz.1
    refine ⟨hu,?_,?_⟩
    · rw [hcard']
      exact hz.2.1.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hsX) (Real.exp_pos _).le)
    · rw [hcap,Finset.inter_comm]
      have hc := hz.2.2
      nlinarith only [hc,hxs]
end SharpRamseyFive.ProjectiveRestriction

end OAI
