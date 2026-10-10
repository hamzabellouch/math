import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.PhaseIntegrals

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open scoped Topology
open Set
open MeasureTheory Filter
open scoped NNReal Topology
open MeasureTheory Filter Set Metric Function ODE
open MeasureTheory ProbabilityTheory Filter Set
open Filter
open Filter Set
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open MeasureTheory
open scoped Classical
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEFiniteTilt ExactSLEStops MeasureTheory Set Filter
open scoped Classical NNReal ENNReal
lemma stopped_phaseProduct_integrable {m : ℕ} {a : ℝ} (ha : 1/4<a)
    (z : Fin m → ℂ) (hz : ∀ i,0<(z i).im) (cap U : Fin m → ℝ)
    (hc : ∀ i,0<cap i) (hr : ∀ i,cap i≤2*(z i).im) (hu : ∀ i,0≤U i)
    (η : ℝ) (hη : 0<η) (M : ℝ≥0)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (S : ExactSLEGenerator.Driver → ℝ≥0)
    (hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0)))
    (hsafe : ∀ b, (∃ i,(S b:ℝ≥0∞)≤levelTime a b (z i) (cap i) (U i)) →
      ‖vectorState a η hη z (S b) b‖≤M ∧ ∀ i,
      (S b:ℝ≥0∞)≤levelTime a b (z i) (cap i) (U i) → η≤Y (vectorState a η hη z (S b) b i)) :
    Integrable (fun b => phaseProduct a cap U (actualPhase a z cap U (S b) b) (vectorState a η hη z (S b) b)) W := by
  have ha0 : 0<a := by linarith
  let p := fun b => actualPhase a z cap U (S b) b
  have hm := (actualPhase_measurable a ha0 z hz cap U hc hr hu S hS).mono hS.measurableSpace_le le_rfl
  have he : (fun b => phaseProduct a cap U (p b) (vectorState a η hη z (S b) b))=
      fun b => ∑ q : PhaseVector m, if p b=q then phaseProduct a cap U q (vectorState a η hη z (S b) b) else 0 := by funext b; simp
  rw [he]
  apply integrable_finsetSum
  intro q hq
  by_cases hn : (phaseActive q).Nonempty
  · have hi : Integrable (fun b => if p b=q then regularizedProduct (phaseActive q) a cap (phaseSigma a q)
        (phaseOffset a U q) (vectorState a η hη z (S b) b) else 0) W := by
      have hs : ∀ b∈{b | p b=q}, ‖vectorState a η hη z (S b) b‖≤M ∧ ∀ i∈phaseActive q, η≤Y (vectorState a η hη z (S b) b i) := by
        intro b hb
        have hmem (i) (hi : i∈phaseActive q) : (S b:ℝ≥0∞)≤levelTime a b (z i) (cap i) (U i) := by
          have hp : p b i=1 ∨ p b i=2 := by rw [hb]; exact (phaseActive_mem q i).mp hi
          have hab := levelTime_mono a ha0 (z i) (hz i) (cap i) (hc i) (hr i) b 0 (U i/2) le_rfl (by have := hu i; linarith)
          have hbc := levelTime_mono a ha0 (z i) (hz i) (cap i) (hc i) (hr i) b (U i/2) (U i) (by have := hu i; linarith) (by have := hu i; linarith)
          rcases hp with hp|hp
          · exact (((phase_one_iff _ _ _ _ hab hbc).mp hp).2.trans_le hbc).le
          · exact ((phase_two_iff _ _ _ _ hab hbc).mp hp).2.le
        obtain ⟨i,hi⟩ := hn
        have h := hsafe b ⟨i,hmem i hi⟩
        exact ⟨h.1,fun j hj => h.2 j (hmem j hj)⟩
      convert regularizedProduct_indicator_integrable (phaseActive q) a η hη M cap (phaseSigma a q) (phaseOffset a U q) z W S hS {b | p b=q} (hm (measurableSet_singleton q)) hs using 1
      all_goals first | rfl | (funext b; by_cases hb : p b=q <;> simp [hb])
    convert hi.const_mul (phaseConstant a U q) using 1
    all_goals first | rfl | (funext b; dsimp only [phaseProduct]; split_ifs <;> simp)
  · have hq0 : phaseActive q=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [phaseProduct,hq0,regularizedProduct,Finset.prod_empty,mul_one]
    have hi : Integrable (fun _ : ExactSLEGenerator.Driver => phaseConstant a U q) W := integrable_const _
    convert hi.indicator (hm (measurableSet_singleton q)) using 1
    all_goals first | rfl | (funext b; by_cases hb : p b=q <;> simp [p] at hb ⊢ <;> simp [hb,Set.indicator])
end ExactSLEGreen
namespace ExactSLEStops
open scoped NNReal
variable {Ω : Type*} [MeasurableSpace Ω]
omit [MeasurableSpace Ω] in
lemma sort_first_zero (l : List (Ω → ℝ≥0)) (h0 : (fun _ => 0)∈l) (ω : Ω) :
    ((sort l)[0]'(by rw [sort_length]; exact List.length_pos_of_mem h0)) ω=0 := by
  let v := (sort l).map (fun τ => τ ω)
  have hz : 0∈v := (sort_perm l ω).mem_iff.mpr (List.mem_map_of_mem h0)
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hz
  have hv := List.pairwise_iff_getElem.mp (sort_sorted l ω)
  apply le_antisymm _ (show (0:ℝ≥0)≤_ from bot_le)
  cases i with
  | zero => simpa only [v,List.getElem_map] using he.le
  | succ i =>
    have h := hv 0 (i+1) (by simpa [v,sort_length] using List.length_pos_of_mem h0) hi (Nat.zero_lt_succ i)
    rw [he] at h
    simpa only [v,List.getElem_map] using h
omit [MeasurableSpace Ω] in
lemma sort_last_bound (l : List (Ω → ℝ≥0)) (B : Ω → ℝ≥0) (hB : B∈l)
    (hb : ∀ τ∈l, ∀ ω,τ ω≤B ω) (ω : Ω) (N : ℕ) (hN : (sort l).length=N+1) :
    ((sort l)[N]'(by omega)) ω=B ω := by
  let v := (sort l).map (fun τ => τ ω)
  have hz : B ω∈v := (sort_perm l ω).mem_iff.mpr (List.mem_map_of_mem hB)
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hz
  have hv := List.pairwise_iff_getElem.mp (sort_sorted l ω)
  apply le_antisymm (sort_bounded l B hb _ (List.getElem_mem _) ω)
  have hiN : i≤N := by
    have hvlen : v.length=N+1 := by simp [v,hN]
    omega
  rcases hiN.eq_or_lt with rfl|hlt
  · simpa only [v,List.getElem_map] using he.ge
  · have h := hv i N hi (by simp [hN]) hlt
    rw [he] at h
    simpa only [v,List.getElem_map] using h
end ExactSLEStops

 
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEFiniteTilt ExactSLEStops MeasureTheory ProbabilityTheory Set Filter
open scoped Classical NNReal ENNReal
lemma actual_phase_expectation_bound {m : ℕ} {a ε : ℝ} (ha : 1/4<a) (hε : 0<ε)
    (hsize : ε*((m:ℝ)-1)≤regK a/2)
    (z : Fin m → ℂ) (hz : ∀ i,0<(z i).im) (hinj : Function.Injective z)
    (cap U : Fin m → ℝ) (hc : ∀ i,0<cap i) (hr : ∀ i,cap i≤2*(z i).im)
    (hsep : ∀ i j,i≠j → cap i≤‖z i-z j‖) (hu : ∀ i,0≤U i)
    (η : ℝ) (hη : 0<η) (M : ℝ≥0)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (B : ExactSLEGenerator.Driver → ℝ≥0) (L : ℝ≥0)
    (hB : IsStoppingTime rawFiltration (fun b => (B b : WithTop ℝ≥0)))
    (hBL : ∀ b,B b≤L)
    (hsafe : ∀ b t, t≤B b → (∃ i, (t:ℝ≥0∞)≤levelTime a b (z i) (cap i) (U i)) →
      ‖vectorState a η hη z t b‖≤M ∧ ∀ i,
      (t:ℝ≥0∞)≤levelTime a b (z i) (cap i) (U i) →
      alive a b.1 t (z i) ∧ η≤Y (vectorState a η hη z t b i) ∧
      vectorState a η hη z t b i=actualState a b.1 t (z i)) :
    (∫ b, phaseProduct a cap U (actualPhase a z cap U (B b) b) (vectorState a η hη z (B b) b) ∂W)≤
      Real.exp (phaseDiscountConstant m a ε)^(3*m+1) := by
  classical
  have ha0 : 0<a := by linarith
  let C := fun (i : Fin m) (u : ℝ) => clip (fun b => levelTime a b (z i) (cap i) u) B
  let l : List (ExactSLEGenerator.Driver → ℝ≥0) := [(fun _ => 0),B] ++
    List.ofFn (fun i => C i 0) ++ List.ofFn (fun i => C i (U i/2)) ++ List.ofFn (fun i => C i (U i))
  have hlen : (sort l).length=3*m+2 := by simp only [sort_length,l,List.length_append,List.length_cons,List.length_nil,List.length_ofFn]; omega
  have hmem (τ) : τ∈l ↔ τ=(fun _ => 0) ∨ τ=B ∨
      (∃ i,τ=C i 0) ∨ (∃ i,τ=C i (U i/2)) ∨ (∃ i,τ=C i (U i)) := by
    simp only [l,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_ofFn,or_false]
    simp only [or_assoc]
    constructor
    · rintro (h|h|⟨i,h⟩|⟨i,h⟩|⟨i,h⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl ⟨i,h.symm⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i,h.symm⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i,h.symm⟩)))
    · rintro (h|h|⟨i,h⟩|⟨i,h⟩|⟨i,h⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl ⟨i,h.symm⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i,h.symm⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i,h.symm⟩)))
  have hbnd : ∀ τ∈l, ∀ b,τ b≤B b := by
    intro τ ht b
    rcases (hmem τ).mp ht with rfl|rfl|⟨i,rfl⟩|⟨i,rfl⟩|⟨i,rfl⟩
    · exact bot_le
    · exact le_rfl
    all_goals exact clip_le _ _ _
  have hstop : ∀ τ∈l, IsStoppingTime rawFiltration (fun b => (τ b : WithTop ℝ≥0)) := by
    intro τ ht
    rcases (hmem τ).mp ht with rfl|rfl|⟨i,rfl⟩|⟨i,rfl⟩|⟨i,rfl⟩
    · exact isStoppingTime_const _ _
    · exact hB
    all_goals apply clip_stopping rawFiltration _ B _ hB
    all_goals apply radialTime_stopping a ha0 (z i) (hz i) _ (levelRadius_pos _ _ _ (hc i))
    · exact (levelRadius_le ha0 (hc i) le_rfl).trans (by have := hr i; linarith)
    · exact (levelRadius_le ha0 (hc i) (by have := hu i; linarith : 0≤U i/2)).trans (by have := hr i; linarith)
    · exact (levelRadius_le ha0 (hc i) (hu i)).trans (by have := hr i; linarith)
  let S := fun (k : Fin (3*m+2)) => (sort l)[k.val]'(by rw [hlen]; exact k.isLt)
  have hS (k) : IsStoppingTime rawFiltration (fun b => (S k b : WithTop ℝ≥0)) :=
    sort_stopping rawFiltration l hstop _ (List.getElem_mem _)
  have hSB (k) (b) : S k b≤B b := sort_bounded l B hbnd _ (List.getElem_mem _) b
  have h0 : S 0=(fun _ => 0) := by
    funext b
    convert sort_first_zero l ((hmem _).mpr (Or.inl rfl)) b using 1
    simp [S]
    rfl
  have hlast : S ⟨3*m+1,by omega⟩=B := by
    funext b
    exact sort_last_bound l B ((hmem _).mpr (Or.inr (Or.inl rfl))) hbnd b (3*m+1) (by omega)
  let P := fun (Q : ExactSLEGenerator.Driver → ℝ≥0) (b : ExactSLEGenerator.Driver) =>
    phaseProduct a cap U (actualPhase a z cap U (Q b) b) (vectorState a η hη z (Q b) b)
  have hind : ∀ k : Fin (3*m+2), (∫ b,P (S k) b ∂W)≤Real.exp (phaseDiscountConstant m a ε)^k.val := by
    intro k
    induction k using Fin.induction with
    | zero =>
      rw [h0,Fin.val_zero,pow_zero]
      have hi := stopped_phaseProduct_integrable ha z hz cap U hc hr hu η hη M W (fun _ => 0)
        (isStoppingTime_const _ _) (fun b he => by
          have hh := hsafe b 0 bot_le he
          exact ⟨hh.1,fun i hi => (hh.2 i hi).2.1⟩)
      calc
        _ ≤ ∫ _ : ExactSLEGenerator.Driver, (1:ℝ) ∂W := integral_mono hi (integrable_const _) (fun b => actual_phaseProduct_initial ha z hz cap U hc hr hu η hη b)
        _ = 1 := by simp
    | succ k ih =>
      have hk : k.val+1<(sort l).length := by rw [hlen]; omega
      have hST (b) : S k.castSucc b≤S k.succ b := by
        have hh := List.pairwise_iff_getElem.mp (sort_sorted l b) k.val (k.val+1)
          (by simp only [List.length_map]; omega) (by simpa only [List.length_map] using hk) (by omega)
        simpa only [List.getElem_map,S,Fin.val_castSucc,Fin.val_succ] using hh
      have hboundary : ∀ b i, ∀ u∈({0,U i/2,U i}:Finset ℝ),
          levelTime a b (z i) (cap i) u≤(S k.castSucc b:ℝ≥0∞) ∨ (S k.succ b:ℝ≥0∞)≤levelTime a b (z i) (cap i) u := by
        intro b i u hu'
        apply no_actual_change_between l B (fun b => levelTime a b (z i) (cap i) u) _ b k.val hk (hSB k.succ b)
        change C i u∈l
        simp only [Finset.mem_insert,Finset.mem_singleton] at hu'
        rcases hu' with rfl|rfl|rfl
        · exact (hmem _).mpr (Or.inr (Or.inr (Or.inl ⟨i,rfl⟩)))
        · exact (hmem _).mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i,rfl⟩))))
        · exact (hmem _).mpr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i,rfl⟩))))
      have hs := actual_phase_expectation_step ha hε hsize z hz hinj cap U hc hr hsep hu η hη M W hW
        (S k.castSucc) (S k.succ) L (hS _) (hS _) hST (fun b => (hSB _ b).trans (hBL b)) hboundary
        (fun b t ht he => hsafe b t (ht.trans (hSB _ b)) he)
      calc
        _ ≤ Real.exp (phaseDiscountConstant m a ε)*(∫ b,P (S k.castSucc) b ∂W) := hs
        _ ≤ Real.exp (phaseDiscountConstant m a ε)*Real.exp (phaseDiscountConstant m a ε)^k.val := mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
        _ = _ := by simp only [Fin.val_succ,pow_succ]; ring
  simpa only [hlast] using hind ⟨3*m+1,by omega⟩
end ExactSLEGreen

 
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEFiniteTilt ExactSLEStops MeasureTheory ProbabilityTheory Set Filter
open scoped Classical NNReal ENNReal
lemma actual_all_clocks_bound {m : ℕ} {a ε : ℝ} (ha : 1/4<a) (hε : 0<ε)
    (hsize : ε*((m:ℝ)-1)≤regK a/2)
    (z : Fin m → ℂ) (hz : ∀ i,0<(z i).im) (hinj : Function.Injective z)
    (cap U : Fin m → ℝ) (hc : ∀ i,0<cap i) (hr : ∀ i,cap i≤2*(z i).im)
    (hsep : ∀ i j,i≠j → cap i≤‖z i-z j‖) (hu : ∀ i,0≤U i)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W) :
    W {b | ∀ i,levelTime a b (z i) (cap i) (U i)<∞}≤
      ENNReal.ofReal (Real.exp (phaseDiscountConstant m a ε)^(3*m+1) /
        (∏ i,Real.exp (regP a*U i/2)/3)) := by
  classical
  have ha0 : 0<a := by linarith
  let ρ := fun i => levelRadius a (cap i) (U i)
  have hρ (i) : 0<ρ i := levelRadius_pos _ _ _ (hc i)
  have hρz (i) : ρ i≤(z i).im := (levelRadius_le ha0 (hc i) (hu i)).trans (by have := hr i; linarith)
  let B := fun n => unfinishedCutoff a ha0 z hz ρ hρ hρz n
  have hB (n) : IsStoppingTime rawFiltration (fun b => (B n b : WithTop ℝ≥0)) := unfinishedCutoff_stopping a ha0 z hz ρ hρ hρz n
  have hBN (n) (b) : B n b≤(n:ℝ≥0) := by
    apply ENNReal.coe_le_coe.mp
    rw [show (B n b:ℝ≥0∞)=unfinishedCutoffTop a ha0 z hz ρ hρ hρz n b from unfinishedCutoff_coe a ha0 z hz ρ hρ hρz n b]
    exact unfinishedCutoffTop_le a ha0 z hz ρ hρ hρz n b
  let E := fun n => {b | ∀ i,levelTime a b (z i) (cap i) (U i)≤(B n b:ℝ≥0∞)}
  let H := ∏ i,Real.exp (regP a*U i/2)/3
  let A := Real.exp (phaseDiscountConstant m a ε)^(3*m+1)
  have hH : 0<H := Finset.prod_pos fun i _ => div_pos (Real.exp_pos _) (by norm_num)
  have hbound (n) : W (E n)≤ENNReal.ofReal (A/H) := by
    obtain ⟨η,hη,M,hs⟩ := actual_common_cutoff_safe a ha0 z hz ρ hρ hρz n
    have hsafe : ∀ b t, t≤B n b → (∃ i, (t:ℝ≥0∞)≤levelTime a b (z i) (cap i) (U i)) →
        ‖vectorState a η hη z t b‖≤M ∧ ∀ i,
        (t:ℝ≥0∞)≤levelTime a b (z i) (cap i) (U i) →
        alive a b.1 t (z i) ∧ η≤Y (vectorState a η hη z t b i) ∧
        vectorState a η hη z t b i=actualState a b.1 t (z i) := by
      intro b t ht he
      have hh := hs b t ht he
      refine ⟨hh.1,?_⟩
      intro i hi
      exact ⟨(actual_unfinished_cutoff a ha0 z hz ρ hρ hρz).2.1 n b t i ht hi,hh.2 i hi⟩
    let P := fun b => phaseProduct a cap U (actualPhase a z cap U (B n b) b) (vectorState a η hη z (B n b) b)
    have hi : Integrable P W := stopped_phaseProduct_integrable ha z hz cap U hc hr hu η hη M W (B n) (hB n)
      (fun b he => by have h := hsafe b (B n b) le_rfl he; exact ⟨h.1,fun i hi => (h.2 i hi).2.1⟩)
    have he : (∫ b,P b ∂W)≤A := actual_phase_expectation_bound ha hε hsize z hz hinj cap U hc hr hsep hu η hη M W hW (B n) n (hB n) (hBN n) hsafe
    have hsub : E n⊆{b | H≤P b} := by
      intro b hb
      exact (actual_phaseProduct_completed a z cap U η hη b (B n b) hb).ge
    have hm := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun b => (phaseProduct_pos a cap U _ _).le) hi H
    have hh : W.real (E n)≤A/H := by
      apply (le_div_iff₀ hH).mpr
      calc
        W.real (E n)*H = H*W.real (E n) := mul_comm _ _
        _ ≤ H*W.real {b | H≤P b} := mul_le_mul_of_nonneg_left (measureReal_mono hsub) hH.le
        _ ≤ A := hm.trans he
    rw [←ofReal_measureReal (μ := W) (s := E n)]
    exact ENNReal.ofReal_le_ofReal hh
  let F := fun N : ℕ => {b | ∀ n≥N,b∈E n}
  have hF : Monotone F := by
    intro N M hNM b hb n hn
    exact hb n (hNM.trans hn)
  have hsub : {b | ∀ i,levelTime a b (z i) (cap i) (U i)<∞}⊆⋃ N,F N := by
    intro b hb
    have he := (actual_unfinished_cutoff a ha0 z hz ρ hρ hρz).2.2 b hb
    obtain ⟨N,hN⟩ := eventually_atTop.mp he
    apply mem_iUnion.mpr
    refine ⟨N,?_⟩
    intro n hn i
    exact (hN n hn i).le
  calc
    _ ≤ W (⋃ N,F N) := measure_mono hsub
    _ = ⨆ N,W (F N) := hF.measure_iUnion
    _ ≤ ENNReal.ofReal (A/H) := iSup_le fun N => (measure_mono (show F N⊆E N from fun b hb => hb N le_rfl)).trans (hbound N)
end ExactSLEGreen

 
namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory Set ExactSLEGenerator ExactSLEMain ExactSLEFiniteTilt
open scoped Classical NNReal ENNReal
 

theorem actual_multipoint_hit_bound (a : ℝ) (ha : 1/4 < a) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W],
    IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W →
    ∀ z : Fin m → ℂ, Function.Injective z → (∀ i, 0 < (z i).im) →
    ∀ cap target : Fin m → ℝ,
      (∀ i, 0<cap i ∧ cap i≤2*(z i).im) →
      (∀ i j, i≠j → cap i≤‖z i-z j‖) →
      (∀ i, 0<target i ∧ target i≤cap i) →
      W {b | ∀ i, radialTime a b.1 (z i) (target i/2) < ∞} ≤
        ENNReal.ofReal (C*∏ i, (target i/cap i)^(alpha a)) := by
  classical
  have ha0 : 0<a := by linarith
  let ε := regK a/(2*((m:ℝ)+1))
  have hε : 0<ε := div_pos (regK_pos ha) (by positivity)
  have hsize : ε*((m:ℝ)-1)≤regK a/2 := by
    calc
      _ ≤ ε*((m:ℝ)+1) := mul_le_mul_of_nonneg_left (by linarith) hε.le
      _ = _ := by dsimp [ε]; field_simp
  let A := Real.exp (phaseDiscountConstant m a ε)^(3*m+1)
  refine ⟨3^m*A,by dsimp [A]; positivity,?_⟩
  intro W hprob hW z hinj hz cap target hc hsep ht
  let U := fun i => -Real.log (target i/cap i)/(2*a)
  have hrpos (i) : 0<target i/cap i := div_pos (ht i).1 (hc i).1
  have hrle (i) : target i/cap i≤1 := (div_le_one (hc i).1).mpr (ht i).2
  have hU (i) : 0≤U i := div_nonneg (neg_nonneg.mpr (Real.log_nonpos (hrpos i).le (hrle i))) (by positivity)
  have hρ (i) : levelRadius a (cap i) (U i)=target i/2 := by
    have he : -2*a*U i=Real.log (target i/cap i) := by dsimp [U]; field_simp
    rw [levelRadius,he,Real.exp_log (hrpos i)]
    field_simp [(hc i).1.ne']
  have h := actual_all_clocks_bound ha hε hsize z hz hinj cap U (fun i => (hc i).1) (fun i => (hc i).2) hsep hU W hW
  have hevent : {b | ∀ i,levelTime a b (z i) (cap i) (U i)<∞}={b | ∀ i,radialTime a b.1 (z i) (target i/2)<∞} := by
    simp only [levelTime,hρ]
  rw [hevent] at h
  have hexp (i) : (Real.exp (regP a*U i/2)/3)⁻¹=3*(target i/cap i)^(alpha a) := by
    have he : -(regP a*U i/2)=Real.log (target i/cap i)*alpha a := by
      dsimp [U,regP,alpha]
      field_simp
      ring
    rw [inv_div,div_eq_mul_inv,←Real.exp_neg,he,Real.rpow_def_of_pos (hrpos i)]
  have hden : (∏ i,Real.exp (regP a*U i/2)/3)⁻¹=3^m*∏ i,(target i/cap i)^(alpha a) := by
    rw [←Finset.prod_inv_distrib]
    simp_rw [hexp]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [div_eq_mul_inv,hden] at h
  simpa only [mul_assoc,mul_left_comm,A] using h
end ExactSLEGreen

open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped NNReal ENNReal Topology
namespace ExactSLEFlow
variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
theorem measurable_parameter_flow_on_interval
    (A : Ω → E → E) (L K : Ω → ℝ≥0)
    (hA : ∀ ω, LipschitzWith (K ω) (A ω)) (hb : ∀ ω x, ‖A ω x‖ ≤ L ω)
    (hmA : Measurable (Function.uncurry A))
    (u : ℝ → Ω → E) (huc : ∀ ω, Continuous (fun t => u t ω))
    (hum : ∀ t, Measurable (u t)) (x : Ω → E) (hxm : Measurable x) (T : ℝ≥0) :
    ∃ Y : ℝ → Ω → E,
      (∀ ω, Continuous (fun t => Y t ω)) ∧
      (∀ t, Measurable (Y t)) ∧
      (∀ ω t, t ∈ Icc (0 : ℝ) T →
        Y t ω = x ω + ∫ v in 0..t, A ω (Y v ω + u v ω)) ∧
      (∀ ω t, t ∈ Icc (0 : ℝ) T →
        HasDerivWithinAt (fun v => Y v ω) (A ω (Y t ω + u t ω)) (Icc (0 : ℝ) T) t) := by
  let t₀ : Icc (0 : ℝ) T := ⟨0, by simp⟩
  have hf (ω : Ω) : IsPicardLindelof (fun t y => A ω (y + u t ω))
      t₀ (x ω) (L ω*T) 0 (L ω) (K ω) := bounded_forcing_picard (A ω) (L ω) (K ω) (hA ω) (hb ω) _ (huc ω) _ _
  have hfix (ω : Ω) := ODE.FunSpace.exists_isFixedPt_next (hf ω)
    (mem_closedBall_self (by simp) : x ω ∈ closedBall (x ω) (0 : ℝ))
  choose α hα using hfix
  let Y : ℝ → Ω → E := fun t ω => (α ω).compProj t
  let β : (ω : Ω) → ODE.FunSpace t₀ (x ω) 0 (L ω) := fun ω => default
  let N (ω : Ω) := ODE.FunSpace.next (hf ω)
    (mem_closedBall_self (by simp) : x ω ∈ closedBall (x ω) (0 : ℝ))
  have hm (n : ℕ) (t : ℝ) : Measurable (fun ω => ((N ω)^[n] (β ω)).compProj t) := by
    induction n generalizing t with
    | zero => change Measurable x; exact hxm
    | succ n ih =>
      have hc (ω : Ω) : Continuous (fun v => A ω (((N ω)^[n] (β ω)).compProj v + u v ω)) :=
        (hA ω).continuous.comp ((ODE.FunSpace.continuous_compProj _).add (huc ω))
      have hi := stronglyMeasurable_intervalIntegral_of_continuous
        (fun v ω => A ω (((N ω)^[n] (β ω)).compProj v + u v ω)) hc
        (fun v => hmA.comp (measurable_id.prodMk ((ih v).add (hum v))))
        0 (projIcc (0 : ℝ) T T.coe_nonneg t)
      simp only [iterate_succ_apply']
      change Measurable (fun ω => x ω + ∫ v in (0 : ℝ)..
        (projIcc (0 : ℝ) T T.coe_nonneg t : ℝ),
          A ω (((N ω)^[n] (β ω)).compProj v + u v ω))
      exact hxm.add hi.measurable
  refine ⟨Y, fun ω => (α ω).continuous_compProj, fun t => ?_, ?_, ?_⟩
  · exact measurable_of_tendsto_metrizable (fun n => hm n t)
      (tendsto_pi_nhds.mpr (fun ω => picard_iterates_tendsto (hf ω) (α ω) (hα ω) (β ω) t))
  · intro ω t ht
    have he := (ODE.FunSpace.isFixedPt_next_iff (hf ω)
      (mem_closedBall_self (by simp))).mp (hα ω) ⟨t, ht⟩
    change (α ω).compProj t = x ω + ∫ v in 0..t, A ω ((α ω).compProj v + u v ω)
    rw [ODE.FunSpace.compProj_of_mem ht]
    exact he
  · intro ω t ht
    apply ODE.hasDerivWithinAt_picard_Icc t₀.2 (hf ω).continuousOn_uncurry
      (α ω).continuous_compProj.continuousOn
      (fun _ _ => (α ω).compProj_mem_closedBall (hf ω).mul_max_le) (x ω) ht |>.congr_of_mem _ ht
    intro v hv
    change (α ω).compProj v = _
    nth_rw 1 [← hα ω]
    rw [ODE.FunSpace.compProj_of_mem hv]
    rfl

theorem measurable_parameter_flow
    (A : Ω → E → E) (L K : Ω → ℝ≥0)
    (hA : ∀ ω, LipschitzWith (K ω) (A ω)) (hb : ∀ ω x, ‖A ω x‖ ≤ L ω)
    (hmA : Measurable (Function.uncurry A))
    (u : ℝ≥0 → Ω → E) (huc : ∀ ω, Continuous (fun t => u t ω))
    (hum : ∀ t, Measurable (u t)) (x : Ω → E) (hxm : Measurable x) :
    ∃ Y : ℝ≥0 → Ω → E,
      (∀ ω, Continuous (fun t => Y t ω)) ∧
      (∀ t, Measurable (Y t)) ∧
      (∀ ω t, Y t ω = x ω + ∫ v in (0 : ℝ)..(t : ℝ),
        A ω (Y v.toNNReal ω + u v.toNNReal ω)) := by
  have hex (T : ℝ≥0) := measurable_parameter_flow_on_interval A L K hA hb hmA
    (fun t ω => u t.toNNReal ω) (fun ω => (huc ω).comp continuous_real_toNNReal)
    (fun t => hum _) x hxm T
  choose F hFc hFm hFe hFd using hex
  have hF0 (T : ℝ≥0) (ω : Ω) : F T 0 ω = x ω := by
    simpa using hFe T ω 0 (by simp)
  have hcompat {S T : ℝ≥0} (hST : S ≤ T) (ω : Ω) (v : ℝ) (hv : v ∈ Icc 0 (S : ℝ)) :
      F S v ω = F T v ω := by
    have hsub : Icc (0 : ℝ) S ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right hST
    apply additive_flow_unique (hA ω) (hFc S ω).continuousOn (hFc T ω).continuousOn
      (hFd S ω) (fun t ht => (hFd T ω t (hsub ht)).mono hsub)
      (by rw [hF0, hF0]) hv
  let Y : ℝ≥0 → Ω → E := fun t ω => F t t ω
  have hYF {T t : ℝ≥0} (ht : t ≤ T) (ω : Ω) : Y t ω = F T t ω :=
    hcompat ht ω t (by simp)
  refine ⟨Y, ?_, fun t => hFm t t, ?_⟩
  · intro ω
    apply continuous_iff_continuousAt.mpr
    intro t
    have hc : ContinuousAt (fun v : ℝ≥0 => F (t+1) v ω) t :=
      ((hFc (t+1) ω).comp continuous_subtype_val).continuousAt
    apply hc.congr
    filter_upwards [eventually_lt_nhds (show t < t+1 by simp)] with v hv
    exact (hYF hv.le ω).symm
  · intro ω t
    rw [hYF le_rfl ω, hFe t ω t (by simp)]
    congr 1
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc (0 : ℝ) t := by simpa [uIcc_of_le t.coe_nonneg] using hv
    have hvt : v.toNNReal ≤ t := (Real.toNNReal_le_toNNReal hv'.2).trans_eq (by simp)
    dsimp only
    rw [hYF hvt ω, Real.coe_toNNReal _ hv'.1]

end ExactSLEFlow

namespace ExactSLEGreen
end ExactSLEGreen
end

end OAI
