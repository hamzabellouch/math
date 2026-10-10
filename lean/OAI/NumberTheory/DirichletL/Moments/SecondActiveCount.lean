import OAI.NumberTheory.DirichletL.Moments.ActiveSource
import OAI.NumberTheory.DirichletL.Moments.RankinScale
import OAI.NumberTheory.DirichletL.Moments.SecondSourceMask

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondActiveCount
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentCompleteCommon CenteredMomentRankinScale
open CenteredMomentRankinRadical
local notation "O" => ActualEisensteinCubic.O

def commonShell (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ) : Finset (Ideal O×Ideal O) :=
  (commonLabels (supportedColumns (activeSource S β)) (supportedColumns (activeSource S β))).filter
    (fun p=>(Ideal.absNorm (commonRadical p.1 p.2):ℝ)≤Y)

def partitionLabels (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ) :
    Finset ((Ideal O×Ideal O)×Finset (Ideal O)) :=
  (commonShell S β Y).biUnion (fun p=>(IdealMobiusDivisorSum.primeSupport (commonRadical p.1 p.2)).powerset.image
    (fun U=>(p,U)))

theorem mem_partitionLabels (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ)
    (p : (Ideal O×Ideal O)×Finset (Ideal O)) :
    p∈partitionLabels S β Y ↔ p.1∈commonShell S β Y ∧
      p.2⊆IdealMobiusDivisorSum.primeSupport (commonRadical p.1.1 p.1.2) := by
  simp only [partitionLabels,Finset.mem_biUnion,Finset.mem_image,Finset.mem_powerset]
  constructor
  · rintro ⟨q,hq,U,hU,rfl⟩
    exact ⟨hq,hU⟩
  · rintro ⟨hp,hU⟩
    exact ⟨p.1,hp,p.2,hU,rfl⟩

theorem active_common_data (S : Finset (Ideal O)) (β : Ideal O→ℂ) (s : Ideal O)
    (hs : Squarefree s) (hmask : ∀I∈S,β I≠0 → s∣I) (Y : ℝ)
    (p : Ideal O×Ideal O) (hp : p∈commonShell S β Y) :
    p.1≠0 ∧ p.2≠0 ∧ CompletedGauss.primeSupport p.1=CompletedGauss.primeSupport p.2 ∧
      s∣p.1 ∧ s∣p.2 := by
  have hm := (Finset.mem_filter.mp hp).1
  obtain ⟨I,hi,J,hj,hIs,hJs,hβi,hβj,hC,hD⟩ := commonLabel_witnesses S β p.1 p.2 hm
  have hsR := old_mask_dvd_commonRadical s I J hs hIs.1 hJs.1 (hmask I hi hβi) (hmask J hj hβj)
  refine ⟨hC ▸ commonPart_ne_zero I J,hD ▸ commonPart_ne_zero J I,?_,?_,?_⟩
  · rw [←hC,←hD]
    exact commonParts_equal_support I J
  · rw [←hC]
    exact hsR.trans (commonRadical_dvd_commonPart I J)
  · rw [←hD]
    have hr : commonRadical I J=commonRadical J I := by unfold commonRadical;rw [Finset.inter_comm]
    rw [hr] at hsR
    exact hsR.trans (commonRadical_dvd_commonPart J I)

theorem actual_partition_count (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C:ℝ,0<C ∧ ∀Z p s₀:ℝ,1≤Z → 0≤p → p≤B →
      ∀s:Ideal O,Squarefree s → s≠0 → Z^s₀≤(Ideal.absNorm s:ℝ) →
      ∀(S:Finset (Ideal O)) (β:Ideal O→ℂ),
      (∀I∈S,β I≠0 → s∣I) →
      (∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤Z^B) →
      ((partitionLabels S β (Z^p)).card:ℝ)≤C*Z^(p-s₀+δ) := by
  obtain ⟨C,hC,hcount⟩:=source_partition_count B δ hB hδ
  refine ⟨C,hC,?_⟩
  intro Z p s₀ hZ hp hpB s hs hs0 hNs S β hmask hN
  have hd (v) (hv:v∈partitionLabels S β (Z^p)) :=
    active_common_data S β s hs hmask (Z^p) v.1 ((mem_partitionLabels S β (Z^p) v).mp hv).1
  apply hcount Z p s₀ hZ hp hpB s hs hs0 hNs _
  · intro v hv
    exact ⟨(hd v hv).1,(hd v hv).2.1⟩
  · intro v hv
    exact (hd v hv).2.2.1
  · intro v hv
    exact (hd v hv).2.2.2
  · intro v hv
    exact ((mem_partitionLabels S β (Z^p) v).mp hv).2
  · intro v hv
    exact commonLabel_norm_bounds S β (Z^B) hN v.1.1 v.1.2
      (Finset.mem_filter.mp ((mem_partitionLabels S β (Z^p) v).mp hv).1).1
  · intro v hv
    exact (Finset.mem_filter.mp ((mem_partitionLabels S β (Z^p) v).mp hv).1).2

end SevenEighths.CenteredMomentSecondActiveCount

end

end OAI
