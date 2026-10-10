import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.BaseSmallLaw
import OAI.Combinatorics.RamseyFive.Geometry.ReverseAfterCapture
import OAI.Combinatorics.RamseyFive.Decoding.ReverseParameters

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

noncomputable def twoOrientedLaw (S U : Finset (ℙ K V))
    (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty)
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) : Law (Option (Finset (ℙ K V))) :=
  if S.card≤T.card then baseCaptureLaw S U P τ R L₀ else
    optionCompose (baseCaptureLaw T UT P τ R L₀)
      (nextCapLaw S U T UT hT (reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card)))
        (Nat.card K) ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^3/T.card)
        ((T.card:ℝ)*Real.exp (2*P)))

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma baseCaptureLaw_valid (S U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (W : Finset (ℙ K V)) (hW : 0<baseCaptureLaw S U P τ R L₀ (some W)) :
    ValidCap S U ((S.card:ℝ)*Real.exp (2*P)) W := by
  simpa only [ValidCap,Finset.inter_comm] using baseCaptureLaw_positive S U P τ R L₀ W hW

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)]
  [Fintype (ℙ K (Dual K V))] [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma enclosure_gap_nonneg (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U) :
    0≤Real.log ((U.card:ℝ)/S.card) := by
  exact Real.log_nonneg ((le_div_iff₀ (by exact_mod_cast hS.card_pos)).mpr
    (by simpa only [one_mul] using (show (S.card:ℝ)≤U.card from by exact_mod_cast Finset.card_le_card hSU)))

lemma cap_size_absorb (q s t b P : ℝ) (hs : 0≤ s) (ht : 0<t)
    (hp : q^3*Real.exp (-b)≤ s*t) (hb : b≤P) (hP : 1000≤Real.exp P) :
    (320/((9:ℝ)/10)+320)*q^3/t≤ s*Real.exp (2*P) := by
  have hh := source_product_to_cap (q^3) s t b (320/((9:ℝ)/10)+320) hs ht (by norm_num) hp
  have hc : 320/((9:ℝ)/10)+320≤Real.exp P := by linarith only [hP]
  have he : (320/((9:ℝ)/10)+320)*Real.exp b≤Real.exp (2*P) := by
    calc
      _ ≤ Real.exp P*Real.exp P := mul_le_mul hc (Real.exp_le_exp.mpr hb) (Real.exp_pos _).le (Real.exp_pos _).le
      _ = _ := by rw [←Real.exp_add];congr 1;ring
  exact hh.trans (mul_le_mul_of_nonneg_left he hs)

theorem eventually_two_oriented {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))]
      [∀x : ℙ K V,Fintype (RadialLine x)]
      [∀x : ℙ K (Dual K V),Fintype (RadialLine x)],
    ∀ (S U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty),
      finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → S.Nonempty → S⊆U → T⊆UT →
      (Nat.card K:ℝ)*(incidences S T:ℝ)≤τ*S.card*T.card →
      (Nat.card K:ℝ)^3*Real.exp (-b)≤(S.card:ℝ)*T.card →
      let p := twoOrientedLaw S U T UT hT (P η σ D R) τ R L₀
      p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
      (∀W,0<p (some W)→ValidCap S U ((S.card:ℝ)*Real.exp (2*P η σ D R)) W) := by
  filter_upwards [eventually_two_law hη hη' Cb hCb,
    eventually_reverse_parameters hη hη' Cb hCb] with σ hbase hrev
  intro D b τ R L₀ K V _ _ _ _ _ _ _ _ _ _ S U T UT hT hdim hq hr hL hb hbhi hτ hτhi hS hSU hTU hdens hprod
  obtain ⟨hP,hbP,heP,hτsmall,hq3⟩ := hrev D R b τ hr hbhi hτ.le hτhi
  have hqnat : 3≤Nat.card K := by exact_mod_cast (hq ▸ hq3 : (3:ℝ)≤Nat.card K)
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast (by omega : 1≤Nat.card K)
  dsimp only [twoOrientedLaw]
  split_ifs with hST
  · refine ⟨?_,fun W hW=>baseCaptureLaw_valid S U _ τ R L₀ W hW⟩
    have hh := hbase D b τ R L₀ K V S U T hdim hq hr hL hb hbhi hτ hτhi hS hSU hST hdens hprod
    linarith only [hh,Real.exp_pos (-(Nat.card K:ℝ))]
  · have hddual : finrank K (Dual K V)=3 := Subspace.dual_finrank_eq.trans hdim
    have hTS : T.card≤(S.map bidualPoint.toEmbedding).card := by rw [Finset.card_map];omega
    have hdens' : (Nat.card K:ℝ)*(incidences T (S.map bidualPoint.toEmbedding):ℝ)≤
        τ*T.card*(S.map bidualPoint.toEmbedding).card := by
      rw [incidences_bidual,Finset.card_map]
      nlinarith only [hdens]
    have hprod' : (Nat.card K:ℝ)^3*Real.exp (-b)≤(T.card:ℝ)*(S.map bidualPoint.toEmbedding).card := by
      rw [Finset.card_map];nlinarith only [hprod]
    have hp := hbase D b τ R L₀ K (Dual K V) T UT (S.map bidualPoint.toEmbedding)
      hddual hq hr hL hb hbhi hτ hτhi hT hTU hTS hdens' hprod'
    have hsparse : 1000*(Nat.card K:ℝ)*incidences S T≤(9:ℝ)/10*S.card*T.card := by
      have hh := mul_le_mul_of_nonneg_left hdens (by norm_num : (0:ℝ)≤1000)
      have hh' := mul_le_mul_of_nonneg_right hτsmall (show (0:ℝ)≤(S.card:ℝ)*T.card by positivity)
      nlinarith only [hh,hh']
    have hl := reverseLength_spec (Nat.card K) (Real.log ((U.card:ℝ)/S.card)) hq1 (enclosure_gap_nonneg S U hS hSU)
    obtain ⟨hf,hg⟩ := reverse_after_capture (d:=2) hdim (by norm_num) hqnat S U hS hSU T UT hT
      ((T.card:ℝ)*Real.exp (2*P η σ D R)) (Real.exp (-(Nat.card K:ℝ)))
      (baseCaptureLaw T UT (P η σ D R) τ R L₀) hp
      (fun W hW=>baseCaptureLaw_valid T UT _ τ R L₀ W hW) hsparse
      (reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card))) hl.1 hl.2.1
    refine ⟨by simpa only [two_mul] using hf,?_⟩
    intro W hW
    have hw := hg W hW
    exact ⟨hw.1,hw.2.1.trans (cap_size_absorb _ _ _ _ _ (by positivity)
      (by exact_mod_cast hT.card_pos) hprod hbP heP),hw.2.2⟩

end SharpRamseyFive.ScoreGeometry

end OAI
