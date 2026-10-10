import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.DimensionThreePublic
import OAI.Combinatorics.RamseyFive.Geometry.BasePublicFamily
import OAI.Combinatorics.RamseyFive.Entropy.BaseAlphabetCost

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity SubsetEncoding
open MeasureTheory PoissonScore ScoreAcceptance MeasurePublicTable ParameterHierarchy Filter
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_two_complete_predictor {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [∀x : ℙ K V,Fintype (RadialLine x)],
    ∀ (S U : Finset (ℙ K V)) (T : Finset (ℙ K (Dual K V))),
      finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → S.Nonempty → S⊆U → S.card≤T.card →
      (Nat.card K:ℝ)*(incidences S T:ℝ)≤τ*S.card*T.card →
      (Nat.card K:ℝ)^3*Real.exp (-b)≤(S.card:ℝ)*T.card →
    let n : Fin (Fintype.card (ℙ K V)+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
    Real.log (Fintype.card (baseAlphabet U S.card (P η σ D R) τ):ℝ)≤
      100*(Nat.card K:ℝ)*P η σ D R*(Real.log ((U.card:ℝ)/S.card)+P η σ D R) ∧
    ∃ Good : Set (BaseTape U (P η σ D R) τ R),
      (baseTapeMeasure U (P η σ D R) τ R L₀).real Goodᶜ≤Real.exp (-(Nat.card K:ℝ)) ∧
      ∀t∈Good,∃ m : baseAlphabet U S.card (P η σ D R) τ,
        let W := baseMessageDecoded U (P η σ D R) τ R L₀ t ⟨n,m⟩
        W⊆U ∧ (W.card:ℝ)≤(S.card:ℝ)*Real.exp (2*P η σ D R) ∧
        (9/10:ℝ)*S.card≤((W∩S).card:ℝ) := by
  have hh := eventually_two_public_predictor hη hη' Cb hCb
  filter_upwards [hh,eventually_ge_atTop (10:ℝ)] with σ hh hσ
  intro D b τ R L₀ K V _ _ _ _ _ _ _ _ S U T hdim hq hr hL hb hbhi hτ hτhi hS hSU hST hdens hprod
  dsimp only
  let P₀ := P η σ D R
  have hP1 : 1≤P₀ :=
    (Real.one_le_rpow (by linarith : (1:ℝ)≤σ) (mul_nonneg (by norm_num) (beta_pos hη).le)).trans
      (finite_bounds hη hη' (by linarith) hr).2.2.2.2.2.1
  have ht1 : τ≤1 := hτhi.trans (Real.rpow_le_one_of_one_le_of_nonpos
    (by linarith : (1:ℝ)≤σ) (by have := beta_pos hη;linarith))
  refine ⟨baseAlphabet_cost hdim S U hS hSU _ τ hP1 hτ.le ht1,?_⟩
  let n : Fin (Fintype.card (ℙ K V)+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
  change ∃Good : Set (BaseTape U P₀ τ R), _
  by_cases hn : (S.card:ℝ)≤100*(Nat.card K:ℝ)*P₀
  · refine ⟨Set.univ,?_,?_⟩
    · simp only [Set.compl_univ,measureReal_empty]
      exact (Real.exp_pos _).le
    · intro t ht
      let m : baseAlphabet U S.card P₀ τ := by
        simpa only [baseAlphabet,hn,ite_true] using encode S U hSU
      refine ⟨m,?_⟩
      have hd := baseDecoded_small U S.card P₀ τ L₀ (t n) hn (encode S U hSU)
      change (baseDecoded U S.card P₀ τ L₀ (t n) m)⊆U ∧
        ((baseDecoded U S.card P₀ τ L₀ (t n) m).card:ℝ)≤(S.card:ℝ)*Real.exp (2*P₀) ∧
        (9/10:ℝ)*S.card≤((baseDecoded U S.card P₀ τ L₀ (t n) m∩S).card:ℝ)
      rw [hd,decode_encode S U hSU,Finset.inter_self]
      refine ⟨hSU,?_,?_⟩
      · exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp_iff.mpr (by linarith))
      · nlinarith only [show (0:ℝ)≤S.card by positivity]
  · have hl := hh D b τ R L₀ K V S U T hdim hq hr hL hb hbhi hτ hτhi hSU hST hdens hprod (lt_of_not_ge hn)
    dsimp only at hl
    obtain ⟨hcost,E,hE,hdecode⟩ := hl
    change Set (Fin (sizeScoreCutoff U S.card P₀ τ)→Fin R→ℙ K V→ℕ) at E
    refine ⟨{t | t n∈E},?_,?_⟩
    · have hm := baseTape_marginal U P₀ τ R L₀ n Eᶜ
      have he : {t : BaseTape U P₀ τ R | t n∈E}ᶜ={t | t n∈Eᶜ} := by ext t;rfl
      rw [he,hm]
      exact hE
    · intro t ht
      obtain ⟨i,z,hw⟩ := hdecode (t n) ht
      let m : baseAlphabet U S.card P₀ τ := by
        simpa only [baseAlphabet,hn,ite_false] using
          (show Fin (sizeScoreCutoff U S.card P₀ τ) × Fin (Fintype.card (ℙ K (Dual K V))+1) from (i,z))
      refine ⟨m,?_⟩
      have hd := baseDecoded_large U S.card P₀ τ L₀ (t n) hn (i,z)
      change (baseDecoded U S.card P₀ τ L₀ (t n) m)⊆U ∧
        ((baseDecoded U S.card P₀ τ L₀ (t n) m).card:ℝ)≤(S.card:ℝ)*Real.exp (2*P₀) ∧
        (9/10:ℝ)*S.card≤((baseDecoded U S.card P₀ τ L₀ (t n) m∩S).card:ℝ)
      rw [hd]
      exact hw

end SharpRamseyFive.ScoreGeometry

end OAI
