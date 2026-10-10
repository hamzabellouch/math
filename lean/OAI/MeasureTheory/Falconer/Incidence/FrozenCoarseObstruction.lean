import OAI.MeasureTheory.Falconer.Incidence.WeakCoarsePacketGain
import OAI.MeasureTheory.Falconer.Incidence.FrozenPacketUpper
import OAI.MeasureTheory.Falconer.Estimates.PacketGrowthGap

namespace OAI

/-! The final contradiction for a regular coarse configuration whose
original fine packets have been frozen to comparable sizes. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem frozen_coarse_packet_impossible {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧
    ∀ n : ℕ, N0 ≤ n+2 →
      let Δ := 1/(2:ℝ)^n
      let δ := 1/(2:ℝ)^(n+3)
      let E := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      ∀ (s t m M mF MF L J B : ℝ) (C : Finset (Space 2))
        (T P : Space 2 → Finset (Space 2))
        (V : Space 2 → Space 2 → Finset (Space 2)) (q : Space 2 → Space 2 → Space 2)
        (G : Space 2 → Finset (Space 2)),
      κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 →
      0 < m → 0 ≤ M → M ≤ E/δ^s → 1/(E*δ^s) ≤ m →
      0 < L → L ≤ E/(δ^s)^2 → 0 < J → J ≤ E → 0 < B → B ≤ E/Δ^s →
      1/(E*(Δ^s)^2) ≤ mF → 0 < MF → MF ≤ E/(Δ^s)^2 →
      C.Nonempty → InBoundedLineChart C → FiniteSeparatedAt δ C →
      NormalizedFiniteBallBound δ t E C →
      (∀ x ∈ C, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
        InBoundedLineChart (T x) ∧ FiniteSeparatedAt δ (T x) ∧
        NormalizedFiniteBallBound δ s E (T x) ∧ ∀ a ∈ T x, TubeIncident δ x a) →
      ((C.biUnion T).card:ℝ) ≤ L →
      (∀ x ∈ C, (P x).Nonempty ∧
        (∀ p ∈ P x, |p 0-x 0| ≤ Δ ∧ |p 1-x 1| ≤ Δ) ∧
        NormalizedFiniteBallBound Δ t E ((P x).image (localPacketPoint Δ (x 0) (x 1)))) →
      (∀ x ∈ C, ∀ p ∈ P x, mF ≤ ((V x p).card:ℝ) ∧ ((V x p).card:ℝ) ≤ MF ∧
        FiniteSeparatedAt (Δ^2) (V x p) ∧ NormalizedFiniteBallBound (Δ^2) s E (V x p) ∧
        ∀ l ∈ V x p, |l 0| ≤ 1 ∧ TubeIncident (Δ^2) p l) →
      (∀ x ∈ C, ∀ p ∈ P x, ∀ l ∈ V x p, dist l (q x l) ≤ Δ) →
      (∀ x ∈ C, ∀ a ∈ T x,
        ((∑ p ∈ P x, (V x p).card):ℝ) ≤ 2*J*B*(coarsePencilWeight (P x) (V x) (q x) a:ℝ)) →
      (∀ x ∈ C, ∀ p ∈ P x, ∀ l ∈ V x p, l ∈ G (q x l)) →
      (∃ k : ℕ, ∀ a ∈ C.biUnion T, 2^k ≤ (G a).card ∧ (G a).card < 2^(k+1)) →
      (∑ a ∈ C.biUnion T, ((G a).card:ℝ)) ≤ E/(Δ^s)^4 → False := by
  obtain ⟨εg,η,N1,hεg,hη,hN1,hgain⟩ := weak_coarse_packet_gain hκ hκ1
  let C0 := 160*(1+projectionGapConstant κ)
  have hC0 : 0 ≤ C0 := by
    have := projectionGapConstant_pos hκ
    dsimp [C0]
    positivity
  obtain ⟨εb,N2,hεb,hN2,hgapmain⟩ := packet_growth_gap hη hC0
  let ε := min εg εb
  refine ⟨ε,max N1 N2,lt_min hεg hεb,lt_of_lt_of_le hN1 (le_max_left _ _),?_⟩
  intro n hn
  dsimp only
  intro s t m M mF MF L J B C T P V q G hs hs1 hgap ht hm hM hME hmE hL hLE
    hJ hJE hB hBE hmFE hMF hMFE hC hCchart hCsep hCball hT hunion hP hV hnear hweight hG hband htotal
  let Δ := 1/(2:ℝ)^n
  let δ := 1/(2:ℝ)^(n+3)
  let E := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let Eg := Real.exp (εg*((n+2:ℕ):ℝ)*Real.log 2)
  have hε : 0 < ε := lt_min hεg hεb
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (by positivity)
  have hEE : E ≤ Eg := Real.exp_le_exp.mpr (by
    apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by norm_num))
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hδs : 0 < δ^s := Real.rpow_pos_of_pos hδ _
  have hΔs : 0 < Δ^s := Real.rpow_pos_of_pos hΔ _
  have ball_mono {d u : ℝ} (hd : 0 ≤ d) {F : Finset (Space 2)}
      (h : NormalizedFiniteBallBound d u E F) : NormalizedFiniteBallBound d u Eg F := by
    intro z r hr hr1
    exact (h z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hEE (Real.rpow_nonneg (hd.trans hr) _)) (Nat.cast_nonneg _))
  have hMEg : M ≤ Eg/δ^s := hME.trans (div_le_div_of_nonneg_right hEE hδs.le)
  have hmEg : 1/(Eg*δ^s) ≤ m := le_trans (by gcongr) hmE
  have hLEg : L ≤ Eg/(δ^s)^2 := hLE.trans (div_le_div_of_nonneg_right hEE (sq_nonneg _))
  have hBEg : B ≤ Eg/Δ^s := hBE.trans (div_le_div_of_nonneg_right hEE hΔs.le)
  have hmFEg : 1/(Eg*(Δ^s)^2) ≤ mF := le_trans (by gcongr) hmFE
  have hMFEg : MF ≤ Eg/(Δ^s)^2 := hMFE.trans (div_le_div_of_nonneg_right hEE (sq_nonneg _))
  obtain ⟨a,ha,hlarge⟩ := hgain n ((le_max_left _ _).trans hn) s t m M mF MF L J B C T P V q G
    hs hs1 hgap ht hm hM hMEg hmEg hL hLEg hJ (hJE.trans hEE) hB hBEg hmFEg hMF hMFEg
    hC hCchart hCsep (ball_mono hδ.le hCball) (by
      intro x hx
      obtain ⟨hlo,hup,hchart,hsep,hball,hinc⟩ := hT x hx
      exact ⟨hlo,hup,hchart,hsep,ball_mono hδ.le hball,hinc⟩) hunion (by
      intro x hx
      obtain ⟨hp,hcell,hball⟩ := hP x hx
      exact ⟨hp,hcell,ball_mono hΔ.le hball⟩) (by
      intro x hx p hp
      obtain ⟨hlo,hup,hsep,hball,hinc⟩ := hV x hx p hp
      exact ⟨hlo,hup,hsep,ball_mono (sq_nonneg _) hball,hinc⟩) hnear hweight hG
  obtain ⟨k,hband⟩ := hband
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hsone : s ≤ 1 := by linarith only [hs1,hκ]
  have hst : s < t := by linarith only [hgap,hκ]
  have hge : κ ≤ t-s := by linarith only [hgap,hκ]
  have hfrozen := frozen_packet_card_upper (n+3) k hs0 hst hE hm hM C T G hC hCchart hCball
    (fun x hx => ⟨(hT x hx).1,(hT x hx).2.1,(hT x hx).2.2.1,
      (hT x hx).2.2.2.2.1,(hT x hx).2.2.2.2.2⟩) hband htotal a ha
  have hρΔ : δ ≤ Δ := by
    dsimp [δ,Δ]
    exact one_div_le_one_div_of_le (pow_pos (by norm_num : (0:ℝ) < 2) n)
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_add_right n 3))
  have hsmall := frozen_packet_upper_power (n+3) hκ hs0 hsone hge (zero_le_one.trans hE)
    le_rfl hm hM hME hmE (by positivity : 0 ≤ E/(Δ^s)^4) le_rfl hE hΔ hρΔ
  exact hgapmain n ε s ((G a).card:ℝ) ((le_max_right _ _).trans hn) hε.le (min_le_right _ _)
    hs0 hlarge (hfrozen.trans hsmall)

end Falconer

end OAI
