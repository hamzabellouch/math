import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.DimensionFourHighProtocol

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining Metadata FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization

theorem fourPublic_header {K : Type} [Field K] [Finite K] [Fintype K]
    [Fintype (ℙ K (Fin 5→K))] (σ : ℝ) (hσ : 100000≤σ)
    (hq : Real.exp σ=Nat.card K) :
    Real.log (Fintype.card (FourPublicIndex K σ):ℝ)≤40*(Nat.card K:ℝ) := by
  have hd : finrank K (Fin 5→K)≤5 := by simp
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hσq : σ≤Nat.card K := by rw [←hq];linarith only [Real.add_one_le_exp σ]
  have hh := projective_header_le (K:=K) (V:=Fin 5→K) σ (by linarith) hq hd
  have ht := log_card_training_le (V:=Fin 5→K) σ hσ (vector_card_le_exp σ hq hd)
  rw [hq,Nat.card_eq_fintype_card] at ht
  let a : ℕ := 2*((Fintype.card (ℙ K (Fin 5→K))+1)*
    Fintype.card (TrainingCode (Fin 5→K) (listCap σ) (productCap σ) (Nat.card (Fin 5→K))))
  let c : ℕ := Fintype.card (Submodule K (Fin 5→K))
  let l : ℕ := (Nat.card K+1)^2
  have ha1 : (1:ℝ)≤a := by
    have h : 0<a := Nat.mul_pos (by norm_num) (Nat.mul_pos (Nat.succ_pos _) Fintype.card_pos)
    exact_mod_cast h
  have hc1 : (1:ℝ)≤c := by exact_mod_cast Fintype.card_pos (α:=Submodule K (Fin 5→K))
  have hl1 : (1:ℝ)≤l := by exact_mod_cast (show 1≤(Nat.card K+1)^2 by exact one_le_pow₀ (Nat.succ_pos _))
  have ha : Real.log (a:ℝ)≤8*(Nat.card K:ℝ) := by
    dsimp only [a]
    rw [Nat.cast_mul,Real.log_mul (by norm_num) (by positivity),Nat.cast_mul,
      Real.log_mul (by positivity) (by exact_mod_cast (Fintype.card_pos (α:=TrainingCode (Fin 5→K) (listCap σ) (productCap σ) (Nat.card (Fin 5→K)))).ne')]
    have h2 : Real.log 2≤1 := by simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    push_cast at hh ⊢
    linarith
  have hvc := vector_card_le_exp (K:=K) (V:=Fin 5→K) σ hq hd
  have hc : Real.log (c:ℝ)≤25*(Nat.card K:ℝ) := by
    have hsc := FlatAtlas.card_submodules_le (K:=K) (V:=Fin 5→K) 5 hd
    rw [Nat.card_eq_fintype_card] at hsc
    have hsc' : (c:ℝ)≤(Nat.card (Fin 5→K):ℝ)^5 := by exact_mod_cast hsc
    have he : (Real.exp (5*σ))^5=Real.exp (25*σ) := by
      rw [←Real.exp_nat_mul];congr 1;ring
    have hle := hsc'.trans ((pow_le_pow_left₀ (by positivity) hvc 5).trans_eq he)
    have hh' := Real.log_le_log (by linarith : (0:ℝ)<c) hle
    rw [Real.log_exp] at hh'
    linarith
  have hl : Real.log (l:ℝ)≤2*(Nat.card K:ℝ) := by
    dsimp only [l]
    rw [Nat.cast_pow,Nat.cast_add,Nat.cast_one,Real.log_pow]
    have hx := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ)<(Nat.card K:ℝ)+1)
    norm_num only [Nat.cast_ofNat] at ⊢
    linarith
  let z : ℕ := (flatIndices (K:=K) (V:=Fin 5→K) 3).card*(Nat.log 2 ((Nat.card K)^2)+1)+
    (flatIndices (K:=K) (V:=Fin 5→K) 4).card*(Nat.log 2 (Nat.card K)+1)
  have hz : (z:ℝ)≤2*((c:ℝ)*l) := by
    have hf : (flatIndices (K:=K) (V:=Fin 5→K) 3).card≤c := by
      exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
    have hh : (flatIndices (K:=K) (V:=Fin 5→K) 4).card≤c := by
      exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
    have h1 : Nat.log 2 ((Nat.card K)^2)+1≤l := by
      have hx := Nat.log_le_self 2 ((Nat.card K)^2)
      change _≤(Nat.card K+1)^2
      calc
        _≤(Nat.card K)^2+1 := Nat.add_le_add_right hx 1
        _≤(Nat.card K)^2+2*(Nat.card K)+1 := by omega
        _=(Nat.card K+1)^2 := by ring
    have h2 : Nat.log 2 (Nat.card K)+1≤l := by
      have hx := Nat.log_le_self 2 (Nat.card K)
      change _≤(Nat.card K+1)^2
      calc
        _≤Nat.card K+1 := Nat.add_le_add_right hx 1
        _≤_ := by nlinarith only []
    have hz' : z≤2*(c*l) := by
      have h1' := Nat.mul_le_mul hf h1
      have h2' := Nat.mul_le_mul hh h2
      dsimp only [z];omega
    exact_mod_cast hz'
  have hcl : Real.log ((c:ℝ)*l)≤27*(Nat.card K:ℝ) := by
    rw [Real.log_mul (by linarith) (by linarith)];linarith
  have hay : (a:ℝ)≤(a:ℝ)*((c:ℝ)*l) :=
    le_mul_of_one_le_right (by linarith) (one_le_mul_of_one_le_of_one_le hc1 hl1)
  have hya : (c:ℝ)*l≤(a:ℝ)*((c:ℝ)*l) := le_mul_of_one_le_left (by positivity) ha1
  have h1ay : 1≤(a:ℝ)*((c:ℝ)*l) := ha1.trans hay
  have hlog := Real.log_le_log (by positivity : 0<1+((a:ℝ)+z))
    (show 1+((a:ℝ)+z)≤4*((a:ℝ)*((c:ℝ)*l)) by linarith)
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_mul (by linarith) (by positivity)] at hlog
  have h4 : Real.log 4≤3 := by
    have hx := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
    linarith
  have he : (Fintype.card (FourPublicIndex K σ):ℝ)=1+((a:ℝ)+z) := by
    simp only [FourPublicIndex,FourBranch,Fintype.card_sum,Fintype.card_prod,Fintype.card_unit,Fintype.card_bool,
      Fintype.card_fin,Fintype.card_coe,Nat.cast_add,Nat.cast_one,Nat.cast_mul,a,z]
  rw [he]
  linarith
end

open Module ProjectiveIncidence ProjectiveTraining Metadata FiniteEntropy
open Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
theorem eventually_four_certified {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K : Type) [Field K] [Finite K] [Fintype K] [CharP K q]
      [Fintype (ℙ K (Fin 5→K))] [Fintype (ℙ K (Dual K (Fin 5→K)))]
      [∀x : ℙ K (Fin 5→K),Fintype (RadialLine x)]
      [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K A)]
      [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K (Dual K A))]
      [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K (Dual K (Dual K A)))],
    ∀ (X U : Finset (ℙ K (Fin 5→K))) (T UT : Finset (ℙ K (Dual K (Fin 5→K)))),
      Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-800*beta η) → X⊆U → T⊆UT → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^5*Real.exp (-b)≤(X.card:ℝ)*T.card →
        let pred := fourCertifiedPredictor U UT σ (P η σ D R) τ R L₀
        let p := pred.output X T
        p none≤3*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P η σ D R) ∧
          (9/100000:ℝ)*X.card≤(W∩X).card) ∧
        (∀t m,pred.encoded X T t=some m→pred.cost t m≤
          30100*(Nat.card K:ℝ)*(P η σ D R)*
            (Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+(P η σ D R))) := by
  filter_upwards [eventually_four_local_complete hη hη' Cb hCb,
    eventually_ge_atTop (100000:ℝ)] with σ hh hσ
  intro D b τ R L₀ q K _ _ _ _ _ _ _ _ _ _ X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod
  have hex : ∃br,FourCertified X U T UT σ (P η σ D R) τ R L₀ br :=
    hh D b τ R L₀ q K X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod
  obtain ⟨hf,hg,hc⟩ := fourCertifiedBranch_spec X U T UT σ (P η σ D R) τ R L₀ hex
  refine ⟨?_,?_,?_⟩
  · rw [fourCertifiedPredictor,FinitePredictor.family_output]
    exact hf
  · rw [fourCertifiedPredictor,FinitePredictor.family_output]
    exact hg
  · intro t m hm
    have ht := FinitePredictor.family_cost (fourLocalPredictor U UT σ (P η σ D R) τ R L₀)
      (fun X T=>fourCertifiedBranch X U T UT σ (P η σ D R) τ R L₀) X T _ hc t m hm
    have hP : 1≤P η σ D R :=
      (Real.one_le_rpow (by linarith : (1:ℝ)≤σ) (mul_nonneg (by norm_num) (beta_pos hη).le)).trans
        (finite_bounds hη hη' (by linarith) hr).2.2.2.2.2.1
    have hq : (Nat.card K:ℝ)=Real.exp σ := by rw [hcard,hσq]
    have hqpos : (0:ℝ)<Nat.card K := by rw [hq];exact Real.exp_pos σ
    have hX : X.Nonempty := by
      have hp : 0<(X.card:ℝ)*T.card := lt_of_lt_of_le (by positivity : (0:ℝ)<(Nat.card K:ℝ)^5*Real.exp (-b)) hprod
      exact Finset.card_pos.mp (Nat.cast_pos.mp (pos_of_mul_pos_left hp (Nat.cast_nonneg _)))
    have hT : T.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hX.card_pos hXT)
    let : Finite (Dual K (Dual K (Fin 5→K))) := Module.finite_of_finite K
    let : Fintype (ℙ K (Dual K (Dual K (Fin 5→K)))) := Fintype.ofFinite _
    have hgX : 0≤Real.log ((U.card:ℝ)/X.card) := by
      exact Real.log_nonneg ((le_div_iff₀ (by exact_mod_cast hX.card_pos)).mpr
        (by simpa only [one_mul] using (show (X.card:ℝ)≤U.card from by exact_mod_cast Finset.card_le_card hXU)))
    have hgT : 0≤Real.log ((UT.card:ℝ)/T.card) := by
      exact Real.log_nonneg ((le_div_iff₀ (by exact_mod_cast hT.card_pos)).mpr
        (by simpa only [one_mul] using (show (T.card:ℝ)≤UT.card from by exact_mod_cast Finset.card_le_card hTU)))
    have hbase : (Nat.card K:ℝ)≤(Nat.card K:ℝ)*P η σ D R*
        (Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P η σ D R) := by
      apply (le_mul_of_one_le_right hqpos.le hP).trans
      exact le_mul_of_one_le_right (by positivity) (by linarith)
    have hl := fourPublic_header (K:=K) σ hσ hq.symm
    change (FinitePredictor.family _ _).cost t m≤_
    nlinarith only [ht,hl,hbase]

end SharpRamseyFive.ScoreGeometry

end OAI
