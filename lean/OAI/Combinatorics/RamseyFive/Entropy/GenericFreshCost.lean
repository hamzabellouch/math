import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.ReverseMessageCost
import OAI.Combinatorics.RamseyFive.Geometry.AmbientPairPublic

namespace OAI


namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]

omit [Fintype A] in
theorem universalFresh_cost_bound (R : A→B→Prop) (S U : Finset A)
    (X UX W : Finset B) (hX : X.Nonempty) (q : ℕ) (hq : 1≤q)
    (P gap c B₀ : ℝ) (hP : 1≤P) (hg : 0≤gap) (hc : 0<c) (hc1 : c≤1) (hB : 0≤B₀)
    (hv : CaptureBound X UX c ((X.card:ℝ)*Real.exp (B₀*P)) W)
    (hhead : Real.log (W.card+1:ℝ)≤6*(q:ℝ))
    (n : Fin (1000*q^2+1)) (hn : (n:ℝ)≤21*(q:ℝ)*(gap+1)) (M : ℝ)
    (t : UniversalFresh B (1000*q^2) (q:ℝ))
    (m : UniversalFreshMessage W (1000*q^2) (q:ℝ))
    (hm : universalFreshEncoded R S U (X∩W) W Finset.inter_subset_right (1000*q^2) n (q:ℝ) M t=some m) :
    universalFreshCost W (1000*q^2) (q:ℝ) m≤
      (1010+21*(B₀-Real.log c))*(q:ℝ)*P*(gap+P) := by
  have hC := hv.nonempty hX hc
  have hW := hC.mono Finset.inter_subset_right
  have hq' : (1:ℝ)≤q := by exact_mod_cast hq
  have hu := fresh_payload_cost (q:ℝ) hq' (X∩W) W hC hW Finset.inter_subset_right n
  have hr := capture_log_ratio X.card c W.card (X∩W).card (B₀*P)
    (by exact_mod_cast hX.card_pos) hc (by exact_mod_cast hW.card_pos)
    (by exact_mod_cast hC.card_pos) hv.2.2 hv.2.1
  have hrn := mul_le_mul_of_nonneg_left hr (show (0:ℝ)≤(n:ℕ) by positivity)
  have hs := general_reverse_cost_scalar (q:ℝ) P gap c B₀ (n:ℕ) hq' hP hg hc hc1 hB
    (Nat.cast_nonneg _) hn
  have hh := length_header_cost q hq
  have he := universalFresh_cost_exact R S U (X∩W) W Finset.inter_subset_right (1000*q^2) n (q:ℝ) M t m hm
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at he
  rw [he]
  linarith
end SharpRamseyFive.ReverseCap

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry Metadata
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem ambientPair_cost (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K)
    (hd : finrank K V≤5)
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (hA : A.Nonempty) (hAU : A⊆UA) (hB : B.Nonempty) (hBU : B⊆UB)
    (W : Finset (ℙ K V)) (c P b : ℝ) (hc : 0<c) (hc1 : c≤1) (hP : 1≤P) (hb : b≤P)
    (hprod : (Nat.card K:ℝ)^5*Real.exp (-b)≤(A.card:ℝ)*B.card)
    (hcoef : 320/c+320≤Real.exp P)
    (hcap : CaptureBound A UA c ((A.card:ℝ)*Real.exp (10*P)) W)
    (hnA : reverseLength (Nat.card K) (Real.log ((UA.card:ℝ)/A.card))≤1000*(Nat.card K)^2)
    (hnB : reverseLength (Nat.card K) (Real.log ((UB.card:ℝ)/B.card))≤1000*(Nat.card K)^2)
    (t : AmbientPairTape K V (1000*(Nat.card K)^2) (Nat.card K))
    (m : AmbientPairMessage UB W (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : ambientPairEncoded A UA B UB W _ ⟨_,Nat.lt_succ_of_le hnA⟩ ⟨_,Nat.lt_succ_of_le hnB⟩
      (Nat.card K) ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card)
      ((320/c+320)*(Nat.card K:ℝ)^5/A.card) t=some m) :
    ambientPairCost UB W (1000*(Nat.card K)^2) (Nat.card K) t m≤
      (2020+21*(12-Real.log c-Real.log ((9:ℝ)/10)))*(Nat.card K:ℝ)*P*
        (Real.log ((UA.card:ℝ)/A.card)+Real.log ((UB.card:ℝ)/B.card)+P) := by
  let : Finite V := Module.finite_of_finite K
  let : Fintype V := Fintype.ofFinite _
  let : Finite (Dual K V) := Module.finite_of_finite K
  let : Fintype (Dual K V) := Fintype.ofFinite _
  let : Finite (Dual K (Dual K V)) := Module.finite_of_finite K
  let : Fintype (ℙ K (Dual K (Dual K V))) := Fintype.ofFinite _
  have hqnat : 1≤Nat.card K := Nat.card_pos (α:=K)
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast hqnat
  have hga := projective_enclosure_gap σ hq hd A UA hA hAU
  have hgb := projective_enclosure_gap σ hq (show finrank K (Dual K V)≤5 by simpa using hd) B UB hB hBU
  have hnAl := (reverseLength_spec (Nat.card K) (Real.log ((UA.card:ℝ)/A.card)) hq1 hga.1).2.2
  have hnBl := (reverseLength_spec (Nat.card K) (Real.log ((UB.card:ℝ)/B.card)) hq1 hgb.1).2.2
  obtain ⟨hfirst,hvalid,hsecond⟩ := ambientPair_prefixes A UA B UB W _ _ _ _ _ _ t m hm
  let Y := universalFreshDecoded (fun b a=>Incident a b) W (1000*(Nat.card K)^2) (Nat.card K) t.1 m.1
  have hWhd : Real.log (W.card+1:ℝ)≤6*(Nat.card K:ℝ) :=
    (Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right (Finset.card_le_univ W) 1)).trans
      (projective_header_le (K:=K) (V:=V) σ hσ hq hd)
  have hfirstCost := universalFresh_cost_bound (fun b a=>Incident a b) B UB A UA W hA (Nat.card K) hqnat
    P (Real.log ((UB.card:ℝ)/B.card)) c 10 hP hgb.1 hc hc1 (by norm_num) hcap hWhd
    ⟨_,Nat.lt_succ_of_le hnB⟩ hnBl _ t.1 m.1 hfirst
  have hYhd : Real.log ((UB∩Y).card+1:ℝ)≤6*(Nat.card K:ℝ) :=
    (Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right (Finset.card_le_univ (UB∩Y)) 1)).trans
      (projective_header_le (K:=K) (V:=Dual K V) σ hσ hq (by simpa using hd))
  have hcapB : (320/c+320)*(Nat.card K:ℝ)^5/A.card≤(B.card:ℝ)*Real.exp (2*P) := by
    have hp : (Nat.card K:ℝ)^5*Real.exp (-b)≤(B.card:ℝ)*A.card := by simpa only [mul_comm] using hprod
    have ho := source_product_to_cap ((Nat.card K:ℝ)^5) B.card A.card b (320/c+320)
      (Nat.cast_nonneg _) (by exact_mod_cast hA.card_pos) (by positivity) hp
    have he : (320/c+320)*Real.exp b≤Real.exp (2*P) := by
      calc
        _≤Real.exp P*Real.exp P := mul_le_mul hcoef (Real.exp_le_exp.mpr hb) (Real.exp_pos _).le (Real.exp_pos _).le
        _=Real.exp (2*P) := by rw [←Real.exp_add];congr 1;ring
    exact ho.trans (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _))
  have hvcap : CaptureBound B UB ((9:ℝ)/10) ((B.card:ℝ)*Real.exp (2*P)) (UB∩Y) :=
    ⟨hvalid.1,hvalid.2.1.trans hcapB,hvalid.2.2⟩
  have hsecondCost := universalFresh_cost_bound Incident A UA B UB (UB∩Y) hB (Nat.card K) hqnat
    P (Real.log ((UA.card:ℝ)/A.card)) ((9:ℝ)/10) 2 hP hga.1 (by norm_num) (by norm_num) (by norm_num) hvcap hYhd
    ⟨_,Nat.lt_succ_of_le hnA⟩ hnAl _ t.2 m.2 hsecond
  have hlc : Real.log c≤0 := Real.log_nonpos hc.le hc1
  have hl9 : Real.log ((9:ℝ)/10)≤0 := Real.log_nonpos (by norm_num) (by norm_num)
  have hP0 : 0≤P := le_trans (by norm_num) hP
  have hcA : 0≤1010+21*(2-Real.log ((9:ℝ)/10)) := by linarith only [hl9]
  have hcB : 0≤1010+21*(10-Real.log c) := by linarith only [hlc]
  have hCa : 0≤(1010+21*(2-Real.log ((9:ℝ)/10)))*(Nat.card K:ℝ)*P := by positivity
  have hCb : 0≤(1010+21*(10-Real.log c))*(Nat.card K:ℝ)*P := by positivity
  have h₁ := mul_le_mul_of_nonneg_left (show Real.log ((UB.card:ℝ)/B.card)+P≤
    Real.log ((UA.card:ℝ)/A.card)+Real.log ((UB.card:ℝ)/B.card)+P by linarith only [hga.1]) hCb
  have h₂ := mul_le_mul_of_nonneg_left (show Real.log ((UA.card:ℝ)/A.card)+P≤
    Real.log ((UA.card:ℝ)/A.card)+Real.log ((UB.card:ℝ)/B.card)+P by linarith only [hgb.1]) hCa
  unfold ambientPairCost
  dsimp only [Y] at hfirstCost hsecondCost
  nlinarith only [hfirstCost,hsecondCost,h₁,h₂]
end SharpRamseyFive.ProjectiveIncidence

namespace SharpRamseyFive.FiniteEntropy
open MeasureTheory
open scoped Classical BigOperators
variable {Ω α β : Type*} [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
  [Fintype α] [DecidableEq α] [Fintype β]

omit [DecidableEq α] in
lemma finiteImageLaw_map (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω→α) (g : α→β) :
    map (finiteImageLaw μ f) g=finiteImageLaw μ (g∘f) := by
  apply Law.ext
  funext b
  have hh := finiteImageLaw_event μ f (Finset.univ.filter fun a=>g a=b)
  change (∑ a, if g a=b then finiteImageLaw μ f a else 0)=μ.real {ω | g (f ω)=b}
  simpa only [eventMass,Finset.sum_filter,Finset.mem_filter,Finset.mem_univ,true_and,
    Set.mem_ofPred_eq,Function.comp_apply] using hh

noncomputable def publicTableLaw (μ : Measure Ω) [IsProbabilityMeasure μ]
    (decode : Ω→α→β) : Law (α→β) := finiteImageLaw μ decode

noncomputable def tableEncoded (accept : β→Prop) (t : α→β) : Option α :=
  chooseMessage (fun u m=>accept (u m)) t

omit [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω] [DecidableEq α] [Fintype β] in
lemma tableEncoded_exact (decode : Ω→α→β) (accept : β→Prop) (ω : Ω) :
    tableEncoded accept (decode ω)=chooseMessage (fun u m=>accept (decode u m)) ω := by
  rfl

lemma publicTable_output (μ : Measure Ω) [IsProbabilityMeasure μ]
    (decode : Ω→α→β) (accept : β→Prop) :
    map (publicTableLaw μ decode) (fun t=>Option.map t (tableEncoded accept t))=
      finiteImageLaw μ (fun ω=>Option.map (decode ω)
        (chooseMessage (fun u m=>accept (decode u m)) ω)) := by
  rw [publicTableLaw,finiteImageLaw_map]
  rfl

lemma publicTable_restricted (μ : Measure Ω) [IsProbabilityMeasure μ]
    {γ : Type*} [Fintype γ] (decode : Ω→α→β) (embed : γ→α) (accept : β→Prop) :
    map (publicTableLaw μ decode)
      (fun t=>Option.map (fun m=>t (embed m))
        (chooseMessage (fun (u : α→β) m=>accept (u (embed m))) t))=
      finiteImageLaw μ (fun ω=>Option.map (fun m=>decode ω (embed m))
        (chooseMessage (fun u m=>accept (decode u (embed m))) ω)) := by
  rw [publicTableLaw,finiteImageLaw_map]
  rfl
end SharpRamseyFive.FiniteEntropy

end OAI
