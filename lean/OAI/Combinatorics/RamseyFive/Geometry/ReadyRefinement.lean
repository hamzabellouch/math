import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.GuardedNodeSent

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap ScoreGeometry Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization Topology
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma ready_trimmed_product (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (τ b : ℝ) (hr : OriginalNodeReady A₀ UA B₀ UB (9/10) τ)
    (hp : (Nat.card K:ℝ)^5*Real.exp (-b)≤(A₀.card:ℝ)*B₀.card) :
    (Nat.card K:ℝ)^5*Real.exp (-(b+1))≤((A₀∩UA).card:ℝ)*(B₀∩UB).card := by
  have hmul := mul_le_mul hr.1 hr.2.1
    (show (0:ℝ)≤(9/10:ℝ)*B₀.card by positivity) (Nat.cast_nonneg (A₀∩UA).card)
  have he : Real.exp (-1)≤(81:ℝ)/100 := by
    rw [Real.exp_neg]
    rw [←one_div]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    have h := Real.add_one_le_exp (1:ℝ)
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left he
    (show (0:ℝ)≤(Nat.card K:ℝ)^5*Real.exp (-b) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤81/100)
  rw [neg_add,Real.exp_add]
  nlinarith only [hmul,h1,h2]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma ready_trimmed_density (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (τ ε : ℝ) (hε : 0≤ε) (hτε : τ≤ε*(9/10:ℝ)^2)
    (hr : OriginalNodeReady A₀ UA B₀ UB (9/10) τ) :
    (Nat.card K:ℝ)*incidences (A₀∩UA) (B₀∩UB)≤ε*(A₀∩UA).card*(B₀∩UB).card := by
  have hh := original_ready_sparse A₀ UA B₀ UB (1000*ε) (9/10) τ
    (by positivity) (by norm_num) (by nlinarith only [hτε]) hr
  nlinarith only [hh]

omit [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma ready_bidual (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V))) (δ τ : ℝ) :
    OriginalNodeReady B₀ UB (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) δ τ ↔
      OriginalNodeReady A₀ UA B₀ UB δ τ := by
  simp only [OriginalNodeReady,←Finset.map_inter,Finset.card_map,incidences_bidual]
  constructor <;> rintro ⟨h1,h2,h3⟩ <;> refine ⟨h2,h1,?_⟩ <;> nlinarith only [h3]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
theorem eventually_ready_refinement {η : ℝ} (hη : 0<η) (Cb : ℝ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b R : ℝ), Range η σ D R →
      0≤b → b≤Cb*D*σ^(6*beta η) →
      ∀ (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V))),
      OriginalNodeReady A₀ UA B₀ UB (9/10) (σ^(-1000*beta η)) →
      (Nat.card K:ℝ)^5*Real.exp (-b)≤(A₀.card:ℝ)*B₀.card →
      0≤b+1 ∧ b+1≤(Cb+1)*D*σ^(6*beta η) ∧
      (Nat.card K:ℝ)*incidences (A₀∩UA) (B₀∩UB)≤σ^(-800*beta η)*(A₀∩UA).card*(B₀∩UB).card ∧
      (Nat.card K:ℝ)^5*Real.exp (-(b+1))≤((A₀∩UA).card:ℝ)*(B₀∩UB).card := by
  have ht : ∀ᶠ σ : ℝ in atTop,σ^(-200*beta η)≤(9/10:ℝ)^2 := by
    have hp : 0<200*beta η := mul_pos (by norm_num) (beta_pos hη)
    exact ((tendsto_rpow_neg_atTop hp).eventually_lt_const
      (by norm_num : (0:ℝ)<(9/10:ℝ)^2)).mono (fun σ h=>by simpa only [neg_mul] using h.le)
  filter_upwards [ht,eventually_ge_atTop (1:ℝ)] with σ ht hσ
  intro D b R hR hb hbhi A₀ UA B₀ UB hr hp
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hD : 1≤D := (Real.one_le_rpow hσ (beta_pos hη).le).trans hR.dlo
  have hF : 1≤σ^(6*beta η) := Real.one_le_rpow hσ (by positivity [beta_pos hη])
  refine ⟨by linarith,?_,?_,ready_trimmed_product A₀ UA B₀ UB _ b hr hp⟩
  · have hx := mul_le_mul hD hF (by norm_num : (0:ℝ)≤1) (by linarith : 0≤D)
    nlinarith only [hbhi,hx]
  · apply ready_trimmed_density A₀ UA B₀ UB _ _ (Real.rpow_nonneg hs.le _) _ hr
    have hm := mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg hs.le (-800*beta η))
    rw [←Real.rpow_add hs] at hm
    simpa only [show -800*beta η+(-200*beta η)=-1000*beta η by ring] using hm
end

open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

omit [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
    [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma bidual_inter_card (A UA : Finset (ℙ K V)) (Y : Finset (ℙ K (Dual K (Dual K V)))) :
    (A.map bidualPoint.toEmbedding∩(UA.map bidualPoint.toEmbedding∩Y)).card=
      (A∩(UA∩Y.map bidualPoint.symm.toEmbedding)).card := by
  have he : A.map bidualPoint.toEmbedding∩(UA.map bidualPoint.toEmbedding∩Y)=
      (A∩(UA∩Y.map bidualPoint.symm.toEmbedding)).map bidualPoint.toEmbedding := by
    ext x
    simp
  rw [he,Finset.card_map]

theorem orientedGuardedNode_original_capture
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ P : ℝ) (hδ : 0<δ)
    (t : OrientedNodeTape f r (1000*(Nat.card K)^2) (Nat.card K))
    (m : OrientedNodeMessage f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : orientedGuardedNodeEncoded f r σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ P hδ t=some m) :
    OriginalNodeReady A₀ UA B₀ UB δ τ ∧
    (9/10:ℝ)*δ*A₀.card≤
      (A₀∩(UA∩(orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).2)).card ∧
    (9/10:ℝ)*δ*B₀.card≤
      (B₀∩(UB∩(orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).1)).card := by
  unfold orientedGuardedNodeEncoded at hm
  split_ifs at hm with hAB
  · obtain ⟨m',hm',rfl⟩ := Option.map_eq_some_iff.mp hm
    have hv := (guardedNode_sent_valid f σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ
      (((A₀∩UA).card:ℝ)*Real.exp (10*P)) hδ t.1 m' hm').1
    exact ⟨hv,guardedNode_original_capture f σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ
      (((A₀∩UA).card:ℝ)*Real.exp (10*P)) hδ t.1 m' hm'⟩
  · obtain ⟨m',hm',rfl⟩ := Option.map_eq_some_iff.mp hm
    have hv := (guardedNode_sent_valid r σ hσ hq (by simpa using hd) B₀ UB
      (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) hB₀ hA₀.map c δ τ
      (((B₀∩UB).card:ℝ)*Real.exp (10*P)) hδ t.2 m' hm').1
    have hh := guardedNode_original_capture r σ hσ hq (by simpa using hd) B₀ UB
      (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) hB₀ hA₀.map c δ τ
      (((B₀∩UB).card:ℝ)*Real.exp (10*P)) hδ t.2 m' hm'
    refine ⟨(ready_bidual A₀ UA B₀ UB δ τ).mp hv,?_,hh.1⟩
    simpa only [Finset.card_map,bidual_inter_card,orientedNodeDecoded,reverseNodePair] using hh.2

end SharpRamseyFive.ProjectiveIncidence

end OAI
