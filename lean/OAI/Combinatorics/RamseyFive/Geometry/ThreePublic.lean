import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.ThreeLocal
import OAI.Combinatorics.RamseyFive.Entropy.ThreeHeader

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining Metadata FiniteEntropy
open Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

theorem eventually_three_public_complete {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K : Type) [Field K] [Finite K] [Fintype K] [CharP K q]
      [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]
      [∀x : ℙ K (Fin 4→K),Fintype (RadialLine x)]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K A)]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K A))]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K (Dual K A)))],
    ∀ (X U : Finset (ℙ K (Fin 4→K))) (T UT : Finset (ℙ K (Dual K (Fin 4→K)))),
      Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-400*beta η) → X⊆U → T⊆UT → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^4*Real.exp (-b)≤(X.card:ℝ)*T.card →
      ∃br : ThreePublicIndex K σ,
        let P₀ := P η σ D R
        let p := map (threePublicLaw U UT σ P₀ τ R L₀)
          (fun t=>(threePublicEncoded X U T UT σ P₀ τ br t).map (threePublicDecoded U UT σ P₀ τ t))
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P₀) ∧
          (9/1000:ℝ)*X.card≤(W∩X).card) ∧
        (∀t m,threePublicEncoded X U T UT σ P₀ τ br t=some m →
          threePublicCost U UT σ P₀ τ t m≤
          4100*(Nat.card K:ℝ)*P₀*(Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P₀)) := by
  filter_upwards [eventually_three_local_complete hη hη' Cb hCb,
    eventually_ge_atTop (100000:ℝ)] with σ hh hσ
  intro D b τ R L₀ q K _ _ _ _ _ _ _ _ _ _ X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod
  obtain ⟨br,hf,hg,hc⟩ := hh D b τ R L₀ q K X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod
  refine ⟨br,?_,?_,?_⟩
  ·
    rw [threePublic_law]
    exact hf
  ·
    rw [threePublic_law]
    exact hg
  · intro t m hm
    obtain ⟨z,hz,rfl⟩ := branch_sent br (threeLocalEncoded X U T UT σ (P η σ D R) τ br) t m hm
    change Real.log (Fintype.card (ThreePublicIndex K σ):ℝ)+
      threeLocalCost U UT σ (P η σ D R) τ br (t br) z≤_
    have hP : 1≤P η σ D R :=
      (Real.one_le_rpow (by linarith : (1:ℝ)≤σ) (mul_nonneg (by norm_num) (beta_pos hη).le)).trans
        (finite_bounds hη hη' (by linarith) hr).2.2.2.2.2.1
    have hq : (Nat.card K:ℝ)=Real.exp σ := by rw [hcard,hσq]
    have hqpos : (0:ℝ)<Nat.card K := by rw [hq];exact Real.exp_pos σ
    have hX : X.Nonempty := by
      have hp : 0<(X.card:ℝ)*T.card := lt_of_lt_of_le (by positivity : (0:ℝ)<(Nat.card K:ℝ)^4*Real.exp (-b)) hprod
      exact Finset.card_pos.mp (Nat.cast_pos.mp (pos_of_mul_pos_left hp (Nat.cast_nonneg _)))
    have hT : T.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hX.card_pos hXT)
    have hgT : 0≤Real.log ((UT.card:ℝ)/T.card) := Real.log_nonneg
      ((le_div_iff₀ (by exact_mod_cast hT.card_pos)).mpr (by
        simpa using (show (T.card:ℝ)≤UT.card by exact_mod_cast Finset.card_le_card hTU)))
    have hgX : 0≤Real.log ((U.card:ℝ)/X.card) := Real.log_nonneg
      ((le_div_iff₀ (by exact_mod_cast hX.card_pos)).mpr (by
        simpa using (show (X.card:ℝ)≤U.card by exact_mod_cast Finset.card_le_card hXU)))
    have hbase : (Nat.card K:ℝ)≤(Nat.card K:ℝ)*P η σ D R*
        (Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P η σ D R) := by
      apply (le_mul_of_one_le_right hqpos.le hP).trans
      exact le_mul_of_one_le_right (by positivity) (by linarith)
    have hl := threePublic_header (K:=K) σ hσ hq.symm
    have hz' := hc (t br) z hz
    nlinarith only [hz',hl,hbase]
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining Metadata FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K : Type} [Field K] [Finite K] [Fintype K]
  [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K A)]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K A))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K (Dual K A)))]

def ThreeCertified (X U : Finset (ℙ K (Fin 4→K)))
    (T UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (br : ThreePublicIndex K σ) : Prop :=
  let p := map (threePublicLaw U UT σ P τ R L₀)
    (fun t=>(threePublicEncoded X U T UT σ P τ br t).map (threePublicDecoded U UT σ P τ t))
  p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
  (∀W,0<p (some W)→W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P) ∧
    (9/1000:ℝ)*X.card≤(W∩X).card) ∧
  (∀t m,threePublicEncoded X U T UT σ P τ br t=some m →
    threePublicCost U UT σ P τ t m≤
    4100*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P))

noncomputable def threeCertifiedBranch (X U : Finset (ℙ K (Fin 4→K)))
    (T UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) : ThreePublicIndex K σ :=
  if h : ∃br,ThreeCertified X U T UT σ P τ R L₀ br then h.choose else .inl ()

lemma threeCertifiedBranch_spec (X U : Finset (ℙ K (Fin 4→K)))
    (T UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (h : ∃br,ThreeCertified X U T UT σ P τ R L₀ br) :
    ThreeCertified X U T UT σ P τ R L₀ (threeCertifiedBranch X U T UT σ P τ R L₀) := by
  unfold threeCertifiedBranch
  rw [dite_eq_left h]
  exact h.choose_spec

noncomputable def threeCertifiedEncoded (X U : Finset (ℙ K (Fin 4→K)))
    (T UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (t : ThreePublicTape U UT σ P τ) : Option (ThreePublicMessage U UT σ P τ t) :=
  threePublicEncoded X U T UT σ P τ (threeCertifiedBranch X U T UT σ P τ R L₀) t
noncomputable def threeCertifiedLaw (X U : Finset (ℙ K (Fin 4→K)))
    (T UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) : Law (Option (Finset (ℙ K (Fin 4→K)))) :=
  map (threePublicLaw U UT σ P τ R L₀)
    (fun t=>(threeCertifiedEncoded X U T UT σ P τ R L₀ t).map (threePublicDecoded U UT σ P τ t))
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining Metadata FiniteEntropy
open Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

theorem eventually_three_certified {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K : Type) [Field K] [Finite K] [Fintype K] [CharP K q]
      [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]
      [∀x : ℙ K (Fin 4→K),Fintype (RadialLine x)]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K A)]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K A))]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K (Dual K A)))],
    ∀ (X U : Finset (ℙ K (Fin 4→K))) (T UT : Finset (ℙ K (Dual K (Fin 4→K)))),
      Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-400*beta η) → X⊆U → T⊆UT → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^4*Real.exp (-b)≤(X.card:ℝ)*T.card →
        let P₀ := P η σ D R
        let p := threeCertifiedLaw X U T UT σ P₀ τ R L₀
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P₀) ∧
          (9/1000:ℝ)*X.card≤(W∩X).card) ∧
        (∀t m,threeCertifiedEncoded X U T UT σ P₀ τ R L₀ t=some m →
          threePublicCost U UT σ P₀ τ t m≤
          4100*(Nat.card K:ℝ)*P₀*(Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P₀)) := by
  filter_upwards [eventually_three_public_complete hη hη' Cb hCb] with σ hh
  intro D b τ R L₀ q K _ _ _ _ _ _ _ _ _ _ X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod
  exact threeCertifiedBranch_spec X U T UT σ (P η σ D R) τ R L₀
    (hh D b τ R L₀ q K X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod)
end SharpRamseyFive.ScoreGeometry

end OAI
