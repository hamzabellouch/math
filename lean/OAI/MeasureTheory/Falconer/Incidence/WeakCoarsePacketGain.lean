import OAI.MeasureTheory.Falconer.Incidence.CoarsePacketGain
import OAI.MeasureTheory.Falconer.Incidence.CoarsePacketParameters

namespace OAI

/-! The coarse packet gain with all numerical application costs absorbed
into a single weak-regularity exponent. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem weak_coarse_packet_gain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < η ∧ 0 < N0 ∧
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
      ∃ a ∈ C.biUnion T,
        Real.exp ((2*s+η)*((n+2:ℕ):ℝ)*Real.log 2) ≤ ((G a).card:ℝ) := by
  obtain ⟨θ,η,N1,hθ,hη,hN1,hmain⟩ := coarse_packet_gain hκ hκ1
  obtain ⟨ε,N2,hε,hN2,hpar⟩ := coarse_packet_parameters hκ hθ
  refine ⟨ε,η,max N1 N2,hε,hη,lt_of_lt_of_le hN1 (le_max_left _ _),?_⟩
  intro n hn
  dsimp only
  intro s t m M mF MF L J B C T P V q G hs hs1 hgap ht hm hM hME hmE hL hLE
    hJ hJE hB hBE hmFE hMF hMFE hC hCchart hCsep hCball hT hunion hP hV hnear hweight hG
  let E := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let D := Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2)
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hsone : s ≤ 1 := by linarith only [hs1,hκ]
  have hgap' : κ ≤ t-s := by linarith only [hκ,hgap]
  obtain ⟨hE,hD,hcost⟩ := hpar n ((le_max_right _ _).trans hn)
  obtain ⟨hfiber,hlo,hup,hreg,hsample⟩ := hcost s t E E E m M mF MF L J B hs0 hsone ht hgap'
    hE le_rfl (Real.exp_pos _).le le_rfl hE le_rfl hm hM hME hmE hL.le hLE hJ hJE hB hBE hmFE hMF hMFE
  have hmF : 0 < mF := (by positivity : 0 < 1/(E*((1/(2:ℝ)^n)^s)^2)).trans_le hmFE
  exact hmain n ((le_max_left _ _).trans hn) s t E E E m M mF MF L J B (D/100)
    C T P V q G hs hs1 hgap ht hE hE hE hm hL hmF hMF hJ hB
    ((le_div_iff₀ (by norm_num : (0:ℝ) < 100)).2 (by simpa only [one_mul] using hD))
    hC hCchart hCsep hCball hT hunion hP hV hnear hweight hG (hfiber C hC)
    (by dsimp [D]; linarith) ((by norm_num : (2:ℝ) ≤ 100).trans hD) hlo hup hreg hsample

end Falconer

end OAI
