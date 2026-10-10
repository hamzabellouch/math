import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.FourSelected
import OAI.Combinatorics.RamseyFive.Geometry.TwoAmbientCaps

namespace OAI


namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]

def pairOptions (p : Option α×Option β) : Option (α×β) :=
  p.1.bind fun a=>p.2.map fun b=>(a,b)

lemma pairOptions_none (p : Law (Option α×Option β)) :
    map p pairOptions none=eventMass p (Finset.univ.filter fun z=>z.1=none ∨ z.2=none) := by
  simp only [map,eventMass,Finset.sum_filter]
  apply Finset.sum_congr rfl
  rintro ⟨a,b⟩ _
  cases a <;> cases b <;> simp [pairOptions]

lemma pairOptions_positive (p : Law (Option α×Option β)) (a : α) (b : β)
    (h : 0 < map p pairOptions (some (a,b))) : 0<p (some a,some b) := by
  obtain ⟨⟨a',b'⟩,hh,he⟩ := map_positive p pairOptions _ h
  cases a' <;> cases b' <;> simp [pairOptions] at he
  obtain ⟨rfl,rfl⟩ := he
  exact hh
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def producedPairLaw (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty) (c : ℝ)
    (out : Option (Finset (ℙ K V))) :
    Law (Option (Finset (ℙ K (Dual K V))×Finset (ℙ K V))) :=
  match out with
  | none => pureLaw none
  | some W => if hW : W.Nonempty then
      let nA := reverseLength (Nat.card K) (Real.log ((UA.card:ℝ)/A.card))
      let nB := reverseLength (Nat.card K) (Real.log ((UB.card:ℝ)/B.card))
      let MA := (320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card
      let MB := (320/c+320)*(Nat.card K:ℝ)^5/A.card
      let firstCap := ambientCapLaw (fun b a=>Incident a b) B UB (A∩W) W hW nB (Nat.card K) MB
      map (adaptiveLaw firstCap (nextAmbientCapLaw A UA B UB hB nA (Nat.card K) MA MB)) pairOptions
    else pureLaw none

noncomputable def localNodeLaw (hd : finrank K V=5) (σ : ℝ)
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty)
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    Law (Option (Finset (ℙ K (Dual K V))×Finset (ℙ K V))) :=
  optionCompose (fourFreeLaw hd σ A UA B UB P τ R L₀)
    (producedPairLaw A UA B UB hB (9/100000))

lemma producedPairLaw_spec (hd : finrank K V=5) (hq : 3≤Nat.card K)
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (hA : A.Nonempty) (hB : B.Nonempty) (hAU : A⊆UA) (hBU : B⊆UB)
    (c M : ℝ) (hc : 0<c) (hc9 : c≤9/10)
    (W : Finset (ℙ K V)) (hcap : CaptureBound A UA c M W)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences A B≤c*A.card*B.card) :
    producedPairLaw A UA B UB hB c (some W) none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
    ∀Y Z,0<producedPairLaw A UA B UB hB c (some W) (some (Y,Z))→
      ValidCap B UB ((320/c+320)*(Nat.card K:ℝ)^5/A.card) (UB∩Y) ∧
      ValidCap A UA ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card) (UA∩Z) := by
  have hW : W.Nonempty := (hcap.nonempty hA hc).mono Finset.inter_subset_right
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast (by omega : 1≤Nat.card K)
  have hlenA := reverseLength_spec (Nat.card K) (Real.log ((UA.card:ℝ)/A.card)) hq1
    (Real.log_nonneg ((le_div_iff₀ (by exact_mod_cast hA.card_pos)).mpr
      (by simpa only [one_mul] using (show (A.card:ℝ)≤UA.card from by exact_mod_cast Finset.card_le_card hAU))))
  have hlenB := reverseLength_spec (Nat.card K) (Real.log ((UB.card:ℝ)/B.card)) hq1
    (Real.log_nonneg ((le_div_iff₀ (by exact_mod_cast hB.card_pos)).mpr
      (by simpa only [one_mul] using (show (B.card:ℝ)≤UB.card from by exact_mod_cast Finset.card_le_card hBU))))
  have hh := geometric_two_ambient_caps (d:=4) hd (by norm_num) hq A UA hA hAU B UB hB hBU
    W hW c hc hc9 (by simpa only [Finset.inter_comm] using hcap.2.2) hsparse
    (reverseLength (Nat.card K) (Real.log ((UA.card:ℝ)/A.card)))
    (reverseLength (Nat.card K) (Real.log ((UB.card:ℝ)/B.card)))
    hlenA.1 hlenB.1 hlenA.2.1 hlenB.2.1
  dsimp only [producedPairLaw]
  rw [dite_eq_left hW]
  exact ⟨by rw [pairOptions_none];exact hh.1,fun Y Z hp=>hh.2.2.2 Y Z (pairOptions_positive _ Y Z hp)⟩

theorem eventually_local_node {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (hd : finrank K V=5) (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
      (hB : B.Nonempty),
      Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-800*beta η) → A⊆UA → B⊆UB → A.card≤B.card →
      (Nat.card K:ℝ)*(incidences A B:ℝ)≤τ*A.card*B.card →
      (Nat.card K:ℝ)^5*Real.exp (-b)≤(A.card:ℝ)*B.card →
        let p := localNodeLaw hd σ A UA B UB hB (P η σ D R) τ R L₀
        p none≤5*Real.exp (-(Nat.card K:ℝ)) ∧
        ∀Y Z,0<p (some (Y,Z))→
          ValidCap B UB ((320/((9:ℝ)/100000)+320)*(Nat.card K:ℝ)^5/A.card) (UB∩Y) ∧
          ValidCap A UA ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card) (UA∩Z) ∧
          (incidences (UA∩Z) (UB∩Y):ℝ)≤
            2*((320/((9:ℝ)/10)+320)*(320/((9:ℝ)/100000)+320))*(Nat.card K:ℝ)^4*Real.exp b := by
  have ht : ∀ᶠ σ : ℝ in atTop,σ^(-800*beta η)<(9:ℝ)/100000000 := by
    have hp : 0<800*beta η := mul_pos (by norm_num) (beta_pos hη)
    simpa only [neg_mul] using (tendsto_rpow_neg_atTop hp).eventually_lt_const (by norm_num : (0:ℝ)<9/100000000)
  filter_upwards [eventually_four_free hη hη' Cb hCb,ht,eventually_ge_atTop (10:ℝ)] with σ hh ht hσ
  intro D b τ R L₀ q K V _ _ _ _ _ _ _ _ hd A UA B UB hB hcard hσq hr hL hb hbhi hτ hτhi hAU hBU hAB hdens hprod
  have hq : (Nat.card K:ℝ)=Real.exp σ := by rw [hcard,hσq]
  have hq3 : 3≤Nat.card K := by
    have he : (3:ℝ)≤Real.exp σ := by linarith only [Real.add_one_le_exp σ,hσ]
    rw [←hq] at he
    exact_mod_cast he
  have hA : A.Nonempty := by
    have ha : 0<(A.card:ℝ)*B.card := lt_of_lt_of_le (by rw [hq];positivity) hprod
    exact Finset.card_pos.mp (Nat.cast_pos.mp (pos_of_mul_pos_left ha (Nat.cast_nonneg _)))
  obtain ⟨hf,hgood⟩ := hh D b τ R L₀ q K V hd A UA B UB hcard hσq hr hL hb hbhi hτ hτhi hAU hBU hAB hdens hprod
  have hsparse : 1000*(Nat.card K:ℝ)*incidences A B≤(9:ℝ)/100000*A.card*B.card := by
    have hτc : 1000*τ≤(9:ℝ)/100000 := by linarith only [hτhi,ht]
    have h1 := mul_le_mul_of_nonneg_left hdens (by norm_num : (0:ℝ)≤1000)
    have h2 := mul_le_mul_of_nonneg_right hτc (mul_nonneg (Nat.cast_nonneg A.card) (Nat.cast_nonneg B.card))
    nlinarith only [h1,h2]
  have hs (W) (hW : 0<fourFreeLaw hd σ A UA B UB (P η σ D R) τ R L₀ (some W)) :=
    producedPairLaw_spec hd hq3 A UA B UB hA hB hAU hBU (9/100000) _ (by norm_num) (by norm_num) W (hgood W hW) hsparse
  refine ⟨?_,?_⟩
  · have hh := optionCompose_failure _ _ (3*Real.exp (-(Nat.card K:ℝ)))
        (2*Real.exp (-(Nat.card K:ℝ))) (by positivity) hf (fun W hW=>(hs W hW).1)
    simpa only [localNodeLaw,show (3:ℝ)*Real.exp (-(Nat.card K:ℝ))+2*Real.exp (-(Nat.card K:ℝ))=5*Real.exp (-(Nat.card K:ℝ)) by ring] using hh
  · intro Y Z hYZ
    obtain ⟨W,hW,hout⟩ := optionCompose_positive _ _ (Y,Z) hYZ
    obtain ⟨hy,hz⟩ := (hs W hW).2 Y Z hout
    exact ⟨hy,hz,validated_caps_flags hd A UA (UA∩Z) B UB (UB∩Y) hA hB (9/100000) b (by norm_num) hb hprod hz hy⟩
end SharpRamseyFive.ProjectiveIncidence

end OAI
