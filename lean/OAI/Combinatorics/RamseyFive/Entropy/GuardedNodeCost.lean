import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.ReadyRefinement
import OAI.Combinatorics.RamseyFive.Trees.PivotPotential

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap ScoreGeometry Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

theorem eventually_guarded_node_cost {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (hd : finrank K V=5) (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
      (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty)
      (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q → Range η σ D R → (L₀:ℝ)=L η σ D →
      0≤b → b≤Cb*D*σ^(6*beta η) →
      OriginalNodeReady A₀ UA B₀ UB (9/10) (σ^(-1000*beta η)) →
      (A₀∩UA).card≤(B₀∩UB).card →
      (Nat.card K:ℝ)^5*Real.exp (-b)≤(A₀.card:ℝ)*B₀.card →
      let f := fourFinitePredictor hd σ UA UB (P η σ D R) (σ^(-800*beta η)) R L₀
      ∀ t m,guardedNodeEncoded f σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀ (9/100000) (9/10)
        (σ^(-1000*beta η)) (((A₀∩UA).card:ℝ)*Real.exp (10*P η σ D R)) (by norm_num) t=some m →
      finiteNodeCost f UB (1000*(Nat.card K)^2) (Nat.card K) t m≤
        (32120+21*(12-Real.log ((9:ℝ)/100000)-Real.log ((9:ℝ)/10)))*(Nat.card K:ℝ)*(P η σ D R)*
          (Real.log ((UA.card:ℝ)/(A₀∩UA).card)+Real.log ((UB.card:ℝ)/(B₀∩UB).card)+(P η σ D R)) := by
  have ht : ∀ᶠ σ : ℝ in atTop,σ^(-200*beta η)≤(9/10:ℝ)^2 := by
    have hp : 0<200*beta η := mul_pos (by norm_num) (beta_pos hη)
    exact ((tendsto_rpow_neg_atTop hp).eventually_lt_const
      (by norm_num : (0:ℝ)<(9/10:ℝ)^2)).mono (fun σ h=>by simpa only [neg_mul] using h.le)
  filter_upwards [eventually_finite_node hη hη' (Cb+1) (by linarith),ht] with σ hn ht
  intro D b R L₀ q K V _ _ _ _ _ _ _ _ hd A₀ UA B₀ UB hA₀ hB₀ hσ hq hcard hr hL hb hbhi hready hAB hprod
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hD : 1≤D := (Real.one_le_rpow hσ (beta_pos hη).le).trans hr.dlo
  have hF : 1≤σ^(6*beta η) := Real.one_le_rpow hσ (by positivity [beta_pos hη])
  have hb' : b+1≤(Cb+1)*D*σ^(6*beta η) := by
    have hx := mul_le_mul hD hF (by norm_num : (0:ℝ)≤1) (by linarith : 0≤D)
    nlinarith only [hbhi,hx]
  have hτ : σ^(-1000*beta η)≤σ^(-800*beta η)*(9/10:ℝ)^2 := by
    have hm := mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg hs.le (-800*beta η))
    rw [←Real.rpow_add hs] at hm
    simpa only [show -800*beta η+(-200*beta η)=-1000*beta η by ring] using hm
  have hdens := ready_trimmed_density A₀ UA B₀ UB _ _ (Real.rpow_nonneg hs.le _) hτ hready
  have hp := ready_trimmed_product A₀ UA B₀ UB _ b hready hprod
  obtain ⟨hnA,hnB,_,_,hcost⟩ := hn D (b+1) (σ^(-800*beta η)) R L₀ q K V hd (A₀∩UA) UA (B₀∩UB) UB
    hcard (hq.trans (by exact_mod_cast hcard)) hr hL (by linarith) hb'
    (Real.rpow_pos_of_pos hs _) le_rfl Finset.inter_subset_right Finset.inter_subset_right hAB hdens hp
  simpa only [guardedNodeEncoded,dite_eq_left hready] using hcost

theorem eventually_oriented_guarded_node_cost {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
      (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty)
      (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q → Range η σ D R → (L₀:ℝ)=L η σ D →
      0≤b → b≤Cb*D*σ^(6*beta η) →
      OriginalNodeReady A₀ UA B₀ UB (9/10) (σ^(-1000*beta η)) →
      (Nat.card K:ℝ)^5*Real.exp (-b)≤(A₀.card:ℝ)*B₀.card →
      let f := fourFinitePredictor hd σ UA UB (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fourFinitePredictor (K:=K) (V:=Dual K V) (by simpa using hd) σ UB
        (UA.map bidualPoint.toEmbedding) (P η σ D R) (σ^(-800*beta η)) R L₀
      ∀ t m,orientedGuardedNodeEncoded f r σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀ (9/100000)
        (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) t=some m →
      orientedNodeCost f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m≤
        Real.log 2+
        (32120+21*(12-Real.log ((9:ℝ)/100000)-Real.log ((9:ℝ)/10)))*(Nat.card K:ℝ)*(P η σ D R)*
          (Real.log ((UA.card:ℝ)/(A₀∩UA).card)+Real.log ((UB.card:ℝ)/(B₀∩UB).card)+(P η σ D R)) := by
  filter_upwards [eventually_guarded_node_cost hη hη' Cb hCb] with σ hn
  intro D b R L₀ q K V _ _ _ _ _ _ _ _ _ hd A₀ UA B₀ UB hA₀ hB₀ hσ hq hcard hr hL hb hbhi hready hprod
  dsimp only
  intro t m hm
  unfold orientedGuardedNodeEncoded at hm
  split_ifs at hm with hAB
  · obtain ⟨m',hm',rfl⟩ := Option.map_eq_some_iff.mp hm
    have hc := hn D b R L₀ q K V hd A₀ UA B₀ UB hA₀ hB₀ hσ hq hcard hr hL hb hbhi hready hAB hprod
      t.1 m' hm'
    change Real.log 2+_≤Real.log 2+_
    linarith only [hc]
  · obtain ⟨m',hm',rfl⟩ := Option.map_eq_some_iff.mp hm
    have hc := hn D b R L₀ q K (Dual K V) (by simpa using hd) B₀ UB
      (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) hB₀ hA₀.map
      hσ hq hcard hr hL hb hbhi ((ready_bidual A₀ UA B₀ UB _ _).mpr hready)
      (by simpa only [←Finset.map_inter,Finset.card_map] using (le_of_not_ge hAB))
      (by simpa only [Finset.card_map,mul_comm (B₀.card:ℝ) (A₀.card:ℝ)] using hprod)
      t.2 m' hm'
    simp only [←Finset.map_inter,Finset.card_map] at hc
    change Real.log 2+_≤Real.log 2+_
    linarith only [hc]
end

open Module FiniteEntropy ReverseCap ScoreGeometry PivotTree
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma ready_log_deficits (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (τ b : ℝ)
    (hr : OriginalNodeReady A₀ UA B₀ UB (9/10) τ)
    (hp : (Nat.card K:ℝ)^5*Real.exp (-b)≤(A₀.card:ℝ)*B₀.card) :
    Real.log ((UA.card:ℝ)/(A₀∩UA).card)+Real.log ((UB.card:ℝ)/(B₀∩UB).card)≤
      potential UA.card UB.card ((Nat.card K:ℝ)^5)+(b+1) := by
  have hnA := nonempty_of_positive_trim _ _ hA₀ (9/10) (by norm_num) hr.1
  have hnB := nonempty_of_positive_trim _ _ hB₀ (9/10) (by norm_num) hr.2.1
  have hnA' : (0:ℝ)<(A₀∩UA).card := by exact_mod_cast hnA.card_pos
  have hnB' : (0:ℝ)<(B₀∩UB).card := by exact_mod_cast hnB.card_pos
  have hQ : (0:ℝ)<(Nat.card K:ℝ)^5 := by
    have hh : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos
    exact pow_pos hh _
  have hd := log_deficits UA.card UB.card (A₀∩UA).card (B₀∩UB).card ((Nat.card K:ℝ)^5)
    hnA' hnB' (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_right (s₁:=A₀) (s₂:=UA)))
    (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_right (s₁:=B₀) (s₂:=UB))) hQ
  have ht := ready_trimmed_product A₀ UA B₀ UB τ b hr hp
  have he : Real.exp (-(b+1))*Real.exp (b+1)=1 := by rw [←Real.exp_add];simp
  have hx : (Nat.card K:ℝ)^5≤((A₀∩UA).card:ℝ)*(B₀∩UB).card*Real.exp (b+1) := by
    calc
      _=(((Nat.card K:ℝ)^5)*Real.exp (-(b+1)))*Real.exp (b+1) := by rw [mul_assoc,he,mul_one]
      _≤_ := mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
  have hlog : Real.log (((Nat.card K:ℝ)^5)/(((A₀∩UA).card:ℝ)*(B₀∩UB).card))≤b+1 := by
    apply (Real.log_le_iff_le_exp (div_pos hQ (mul_pos hnA' hnB'))).mpr
    apply (div_le_iff₀ (mul_pos hnA' hnB')).mpr
    simpa only [mul_comm (Real.exp (b+1))] using hx
  linarith only [hd,hlog]

end SharpRamseyFive.ProjectiveIncidence

end OAI
