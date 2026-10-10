import Mathlib
import OAI.GroupTheory.SimpleAmenable.Amenability.BarrierCore

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section BarrierSignalSystem
open Classical Set

structure BarrierSignalSystem (a : ℕ) (ha : 0 < a) (Q B : ℝ) where
  R₀ : ℝ
  R₁ : ℝ
  R₀_pos : 0 < R₀
  gap : R₀+1 < R₁
  first : FieldSignalData
  second : Fin 4 → FieldSignalData
  first_q : first.q=-3
  second_q : ∀j,(second j).q=-3
  first_pos : ∀x,‖x‖ ≤ R₀ → first.signal x=3
  first_neg : ∀x,R₁ ≤ ‖x‖ → first.signal x=-3
  second_pos : ∀j x,‖x‖ ≤ R₁ → |conjugateLineForm a j x| ≤ 1 → (second j).signal x=3
  second_neg : ∀j x,3  ≤  |conjugateLineForm a j x| → (second j).signal x=-3
  intersection_core : ∀N : ℝ,1 ≤ N → ∀i j : Fin 4,i ≠ j → ∀c d : CutRing,
    |conjugate c| ≤ 4*N+Q → |conjugate d| ≤ B → ∀p : ℝ×ℝ,
    conjugateLineForm a i p=conjugate c → conjugateLineForm a j p=conjugate d → ‖p‖ ≤ R₀*N
  incoming_core : ∀m : ℕ,∀i : Fin m,∀N : ℝ,1 ≤ N → ∀j : Fin 4,∀c : CutRing,
    ∀hc : c ∈ barrierCandidate a j N,‖flagSiteConjugate (barrierIncomingSite ha i hc)‖ ≤ R₀*N

theorem exists_barrierSignalSystem {a : ℕ} (ha : 0 < a) (Q B : ℝ) :
    Nonempty (BarrierSignalSystem a ha Q B) := by
  obtain ⟨R,hR,hcore⟩ := exists_barrierIntersection_core ha Q B
  obtain ⟨T,hT,hin⟩ := exists_barrierIncoming_core ha
  let R₀ := R+T+1
  let R₁ := R₀+2
  have hR₀ : 0 < R₀ := by dsimp [R₀]; linarith
  have hR₁ : 0 < R₁ := by dsimp [R₁]; linarith
  obtain ⟨first,hq,hp,hn⟩ := exists_firstBarrierSignal hR₀ (show R₀ < R₁ by dsimp [R₁]; linarith)
  choose second hsq hsp hsn using fun j : Fin 4 => exists_secondBarrierSignal (conjugateLineForm a j) hR₁
  refine ⟨⟨R₀,R₁,hR₀,by dsimp [R₁]; linarith,first,second,hq,hsq,hp,hn,hsp,hsn,?_,?_⟩⟩
  · intro N hN i j hij c d hc hd p hi hj
    exact (hcore N hN i j hij c d hc hd p hi hj).trans
      (mul_le_mul_of_nonneg_right (by dsimp [R₀]; linarith) (by linarith))
  · intro m i N hN j c hc
    exact (hin m i N hN j c hc).trans
      (mul_le_mul_of_nonneg_right (by dsimp [R₀]; linarith) (by linarith))

namespace BarrierSignalSystem
variable {a : ℕ} {ha : 0 < a} {Q B : ℝ} (S : BarrierSignalSystem a ha Q B)

theorem R₁_pos : 0 < S.R₁ := by linarith [S.R₀_pos,S.gap]

theorem incoming_first_true {m : ℕ} (i : Fin m) {N : ℝ} (hN : 1 ≤ N) {j : Fin 4}
    {c : CutRing} (hc : c ∈ barrierCandidate a j N)
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hs : signalSuccess (flagMeanSignal S.first.signal N) b) : b (barrierIncomingSite ha i hc)=true := by
  apply (hs _).1
  rw [flagMeanSignal,S.first_pos]
  · norm_num
  · rw [norm_scaledSiteConjugate (by linarith : 0 < N),div_le_iff₀ (by linarith : 0 < N)]
    exact S.incoming_core m i N hN j c hc

noncomputable def marks {m : ℕ} {N : ℝ} (hN : 0 < N) (j : Fin 4)
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool) :=
  finiteFirstMarks (commonVertexDenominator_pos ha) hN S.R₁_pos b

theorem mem_marks_iff {m : ℕ} {N : ℝ} (hN : 0 < N) (j : Fin 4)
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hs : signalSuccess (flagMeanSignal S.first.signal N) b) (z) :
    z ∈ S.marks hN j b ↔ b z=true :=
  mem_finiteFirstMarks_iff (commonVertexDenominator_pos ha) hN S.R₁_pos S.first.signal b S.first_neg hs z

theorem intersection_first_true {m : ℕ} {N : ℝ} (hN : 1 ≤ N) {i j : Fin 4} (hij : i ≠ j)
    {c d : CutRing} (hc : |conjugate c| ≤ 4*N+Q) (hd : |conjugate d| ≤ B)
    (z : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha i))
    (hz : cutForm a i (barrierSitePoint z)=ordinary c)
    (hzd : cutForm a j (barrierSitePoint z)=ordinary d)
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha i) → Bool)
    (hs : signalSuccess (flagMeanSignal S.first.signal N) b) : b z=true := by
  apply (hs z).1
  rw [flagMeanSignal,S.first_pos]
  · norm_num
  · rw [norm_scaledSiteConjugate (by linarith : 0 < N),div_le_iff₀ (by linarith : 0 < N)]
    exact S.intersection_core N hN i j hij c d hc hd _
      (conjugateLineForm_site (commonVertexDenominator_pos ha) z i c hz)
      (conjugateLineForm_site (commonVertexDenominator_pos ha) z j d hzd)

theorem central_line_barrier {m : ℕ} (i : Fin m) {N : ℝ} (hN : 1 ≤ N)
    (b₁ b₂ : ∀j,FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hs₁ : ∀j,signalSuccess (flagMeanSignal S.first.signal N) (b₁ j))
    (hs₂ : ∀j,signalSuccess (flagMeanSignal (S.second j).signal N) (b₂ j))
    {j : Fin 4} {c : CutRing} (hc : c ∈ barrierCandidate a j N) (hband : |conjugate c| ≤ N) :
    ∀p ∈ squareInterior,cutForm a j p=ordinary c →
      p ∈ sampledBarriers ha i N (fun j => S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j (b₁ j)) b₂ := by
  have hN₀ : 0 < N := by linarith
  apply sampledBarriers_contains_line ha i _ b₂ hc
  intro z hzt hzline hzstart
  have hzfirst : b₁ j z=true := by
    rcases hzstart with hz | hz
    · have he : z=barrierIncomingSite ha i hc :=
        flagSite_eq_of_track_point hzt hz
      rw [he]
      exact S.incoming_first_true i hN hc (b₁ j) (hs₁ j)
    · exact (S.mem_marks_iff hN₀ j (b₁ j) (hs₁ j) z).mp hz
  apply (hs₂ j z).1
  rw [flagMeanSignal,S.second_pos]
  · norm_num
  · exact (firstSignal_true_norm S.first.signal (b₁ j) S.first_neg (hs₁ j) z hzfirst).le
  · rw [conjugateLineForm_scaledSite (commonVertexDenominator_pos ha) z j c N hzline,
      abs_div,abs_of_pos hN₀,div_le_one hN₀]
    exact hband

end BarrierSignalSystem
end BarrierSignalSystem

section SubdivisionCovariance
open Classical Set

def subdivisionBarrier (E : Finset ℝ) (b : ℝ → Bool) : Set ℝ :=
  {x | ∃s t,ConsecutiveSubdivision E s t ∧ b s=true ∧ x ∈ Icc s t}

theorem consecutiveSubdivision_local {E : Finset ℝ} {L U x s t : ℝ}
    (hL : L ∈ E) (hU : U ∈ E) (hx : x ∈ Ioo L U)
    (hst : ConsecutiveSubdivision E s t) (hxi : x ∈ Icc s t) : L ≤ s ∧ t ≤ U := by
  constructor
  · by_contra h
    have hh := hst.2.2.2 L hL (lt_of_not_ge h)
    have hlx := hx.1
    have hxt := hxi.2
    linarith
  · exact hst.2.2.2 U hU (lt_of_le_of_lt hxi.1 hx.2)

theorem consecutiveSubdivision_translate {E F : Finset ℝ} {L U s t d : ℝ}
    (hE : ∀r ∈ Icc L U,r ∈ E ↔ r+d ∈ F) (hs : L ≤ s) (ht : t ≤ U)
    (hst : ConsecutiveSubdivision E s t) : ConsecutiveSubdivision F (s+d) (t+d) := by
  have hsU : s ≤ U := hst.2.2.1.le.trans ht
  have hLt : L ≤ t := hs.trans hst.2.2.1.le
  refine ⟨(hE s ⟨hs,hsU⟩).mp hst.1,(hE t ⟨hLt,ht⟩).mp hst.2.1,
    by linarith [hst.2.2.1],?_⟩
  intro r hr hsr
  by_contra htr
  have hrU : r-d ≤ U := by linarith
  have hLr : L ≤ r-d := by linarith
  have hrE : r-d ∈ E := (hE (r-d) ⟨hLr,hrU⟩).mpr (by simpa using hr)
  have hh := hst.2.2.2 (r-d) hrE (by linarith)
  linarith

theorem subdivisionBarrier_translate_iff {E F : Finset ℝ} {b c : ℝ → Bool}
    {L U d : ℝ} (hL : L ∈ E) (hU : U ∈ E)
    (hFL : L+d ∈ F) (hFU : U+d ∈ F)
    (hE : ∀r ∈ Icc L U,r ∈ E ↔ r+d ∈ F)
    (hb : ∀r ∈ E,r ∈ Ico L U → b r=c (r+d)) {x : ℝ} (hx : x ∈ Ioo L U) :
    x ∈ subdivisionBarrier E b ↔ x+d ∈ subdivisionBarrier F c := by
  constructor
  · rintro ⟨s,t,hst,hbs,hxi⟩
    obtain ⟨hs,ht⟩ := consecutiveSubdivision_local hL hU hx hst hxi
    refine ⟨s+d,t+d,consecutiveSubdivision_translate hE hs ht hst,?_,?_⟩
    · rw [←hb s hst.1 ⟨hs,lt_of_lt_of_le hst.2.2.1 ht⟩]
      exact hbs
    · exact ⟨by linarith [hxi.1],by linarith [hxi.2]⟩
  · rintro ⟨s,t,hst,hcs,hxi⟩
    have hx' : x+d ∈ Ioo (L+d) (U+d) := ⟨by linarith [hx.1],by linarith [hx.2]⟩
    obtain ⟨hs,ht⟩ := consecutiveSubdivision_local hFL hFU hx' hst hxi
    have hFinv : ∀r ∈ Icc (L+d) (U+d),r ∈ F ↔ r+(-d) ∈ E := by
      intro r hr
      have hr' : r-d ∈ Icc L U := ⟨by linarith [hr.1],by linarith [hr.2]⟩
      simpa [sub_eq_add_neg,add_assoc] using (hE (r-d) hr').symm
    have hst' := consecutiveSubdivision_translate hFinv hs ht hst
    refine ⟨s+(-d),t+(-d),hst',?_,?_⟩
    · rw [hb _ hst'.1 ⟨by linarith,by linarith [hst.2.2.1]⟩]
      simpa using hcs
    · exact ⟨by linarith [hxi.1],by linarith [hxi.2]⟩

theorem mem_barrierActiveIntervals_image_iff {a m : ℕ} (ha : 0 < a) (i : Fin m)
    (j : Fin 4) (c : CutRing)
    (M : Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool) (x : ℝ) :
    (∃st ∈ barrierActiveIntervals ha i j c M b,x ∈ Icc st.1 st.2) ↔
      x ∈ subdivisionBarrier (barrierSubdivision ha i j c M) (barrierActivation ha i j c b) := by
  constructor
  · rintro ⟨⟨s,t⟩,hst,hx⟩
    have hh := (Finset.mem_filter.mp hst).2
    exact ⟨s,t,hh.1,hh.2,hx⟩
  · rintro ⟨s,t,hst,hb,hx⟩
    exact ⟨(s,t),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hst.1,hst.2.1⟩,hst,hb⟩,hx⟩

end SubdivisionCovariance

end SimpleAmenable
end
end

end OAI
