import OAI.Probability.MatroidProphet.SafeParity
import OAI.Probability.MatroidProphet.Residual.Statistics

namespace OAI

namespace MatroidProphet
open Finset Pivots
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

omit [DecidableEq α] in
lemma nominalBirth_eq_iff_departure (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (d : α) (hd : d ∉ M.closure ∅) (b : ℤ) :
    nominalBirth M hE κ D C h d = b ↔
      d ∈ nominalPath M hE κ D C h b ∧ d ∉ nominalPath M hE κ D C h (b-1) := by
  rw [mem_nominal_iff_birth_le M hE κ D C h d hd b,
    mem_nominal_iff_birth_le M hE κ D C h d hd (b-1)]
  omega

omit [DecidableEq α] in
lemma isSafeSample_iff_window (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (U : Set α) (I C T : Finset α)
    (hIU : (I : Set α) ⊆ U) (d : α) (hdI : d ∈ I) (hd : d ∉ M.closure ∅) (parity : Bool) :
    IsSafeSample M hE κ D G h d C T parity ↔
      ∃ b : ParityWindow (activation h) (boolParity parity),
        d ∈ safeLayerSet M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
          (fun i => (T : Set α) ∩ (G i : Set α)) h U (I : Set α) (boolParity parity) b := by
  constructor
  · intro hs
    obtain ⟨hlo, hhi, hp, hex⟩ := hs
    let birth := nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d
    have hbwin : birth ∈ Set.Icc (activation h-2) 1 := by
      change activation h+2 ≤ birth at hlo
      change birth ≤ 0 at hhi
      constructor <;> omega
    have hbpar : birth % 2 = ((boolParity parity).val : ℤ) := by
      rw [boolParity_val]
      exact hp
    refine ⟨⟨⟨birth, hbwin⟩, hbpar⟩, ?_⟩
    have hdep := (nominalBirth_eq_iff_departure M hE κ D _ h d hd birth).mp rfl
    exact ⟨⟨hdI, hIU hdI, hlo, hhi, hdep.1, hdep.2⟩, hex⟩
  · rintro ⟨b, hb⟩
    rcases hb with ⟨⟨_, _, hlo, hhi, hmem, hnot⟩, hex⟩
    have hbirth := (nominalBirth_eq_iff_departure M hE κ D _ h d hd b.val.val).mpr ⟨hmem, hnot⟩
    unfold IsSafeSample
    rw [hbirth]
    have hp := b.property.trans (boolParity_val parity)
    exact ⟨hlo, hhi, hp, hex⟩

theorem safeSampleCount_eq_layerStatistic
    {α : Type u_1} [Fintype α] [DecidableEq α] (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (U : Set α) (I C T : Finset α)
    (hIU : (I : Set α) ⊆ U) (hIL : ∀ d ∈ I, d ∉ M.closure ∅) (parity : Bool) :
    safeSampleCount M hE κ D G h I C T parity =
      (safeLayerStatistic M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
        (fun i => (T : Set α) ∩ (G i : Set α)) h U (I : Set α) (boolParity parity) : ℝ) := by
  let W := ParityWindow (activation h) (boolParity parity)
  let L : W → Set α := safeLayerSet M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
    (fun i => (T : Set α) ∩ (G i : Set α)) h U (I : Set α) (boolParity parity)
  have hcount (b : W) : (L b).ncard = (I.filter (fun d => d ∈ L b)).card := by
    have hs : L b = ((I.filter (fun d => d ∈ L b) : Finset α) : Set α) := by
      ext d
      constructor
      · intro hd
        exact mem_filter.mpr ⟨hd.1.1, hd⟩
      · intro hd
        exact (mem_filter.mp hd).2
    exact (congrArg Set.ncard hs).trans (Set.ncard_coe_finset _)
  have hlabel (d : α) (hd : d ∈ I) :
      (∑ b : W, if d ∈ L b then (1:ℝ) else 0) = if IsSafeSample M hE κ D G h d C T parity then 1 else 0 := by
    rw [sum_unique_indicators]
    · have he : (∃ b ∈ (univ : Finset W), d ∈ L b) ↔ IsSafeSample M hE κ D G h d C T parity := by
        simp only [mem_univ, true_and]
        exact (isSafeSample_iff_window M hE κ D G h U I C T hIU d hd (hIL d hd) parity).symm
      simp only [he]
    · intro b hb c hc hdb hdc
      by_contra hbc
      have hdisj := nominalLayerSet_disjoint M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
        h U (boolParity parity) hbc
      exact Set.disjoint_left.mp hdisj hdb.1.2 hdc.1.2
  calc
    safeSampleCount M hE κ D G h I C T parity =
        ∑ d ∈ I, if IsSafeSample M hE κ D G h d C T parity then (1:ℝ) else 0 := by
      rw [safeSampleCount_eq_card]
      simp [safeSampleSet]
    _ = ∑ d ∈ I, ∑ b : W, if d ∈ L b then (1:ℝ) else 0 :=
      sum_congr rfl (fun d hd => (hlabel d hd).symm)
    _ = ∑ b : W, ∑ d ∈ I, if d ∈ L b then (1:ℝ) else 0 := sum_comm
    _ = ∑ b : W, ((L b).ncard : ℝ) := by
      apply sum_congr rfl
      intro b hb
      rw [hcount]
      simp
    _ = _ := by simp only [safeLayerStatistic, Nat.cast_sum]; rfl

theorem safeLayerStatistic_lower (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (h : ℕ) (U I : Set α) (hIU : I ⊆ U) (hI : M.Indep I) :
    (((2:ℝ)^12)⁻¹) / 4 * I.ncard - (D h).ncard / (κ:ℝ) ≤
      bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
        fairParityExpectation (fun parity => (safeLayerStatistic M hE κ D
          (fun i => (C : Set α) ∩ (G i : Set α)) (fun i => (T : Set α) ∩ (G i : Set α))
          h U I (boolParity parity) : ℝ)))) := by
  let J := I.toFinset
  have hJI : (J : Set α) = I := by simp [J]
  have hJcard : J.card = I.ncard := by rw [← Set.ncard_coe_finset, hJI]
  have hJ : M.Indep (J : Set α) := hJI.symm ▸ hI
  have hJU : (J : Set α) ⊆ U := hJI.symm ▸ hIU
  have hl := safeSampleCount_lower M hE κ hκ D G hG q hq0 hq1 h J hJ
  rw [hJcard] at hl
  have heq : bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
      fairParityExpectation (safeSampleCount M hE κ D G h J C T))) =
      bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
        fairParityExpectation (fun parity => (safeLayerStatistic M hE κ D
          (fun i => (C : Set α) ∩ (G i : Set α)) (fun i => (T : Set α) ∩ (G i : Set α))
          h U I (boolParity parity) : ℝ)))) := by
    apply bitsExpectation_congr
    intro C hC
    apply bitsExpectation_congr
    intro T hT
    congr 1
    funext parity
    rw [safeSampleCount_eq_layerStatistic M hE κ D G h U J C T hJU
      (fun d hd => indep_not_loop M J hJ hd) parity, hJI]
  exact hl.trans_eq heq

end MatroidProphet

end OAI
