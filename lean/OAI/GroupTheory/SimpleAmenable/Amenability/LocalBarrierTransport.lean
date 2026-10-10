import Mathlib
import OAI.GroupTheory.SimpleAmenable.Amenability.BarrierChartRefinement

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section LocalBarrierTransport
open Classical Set

theorem inFlagLattice_add {D : ℕ} (hD : 0 < D) {p : ℝ×ℝ}
    (hp : InFlagLattice D p) (u : CutRing×CutRing) :
    InFlagLattice D (p+(ordinary u.1,ordinary u.2)) := by
  obtain ⟨v,rfl⟩ := hp
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  refine ⟨(v.1+D*u.1,v.2+D*u.2),?_⟩
  apply Prod.ext <;> simp only [scaledOrdinary,map_add,map_mul,map_natCast,Prod.fst_add,Prod.snd_add] <;> field_simp

theorem mem_barrierSubdivision_interior {a m : ℕ} (ha : 0 < a) (i : Fin m)
    {j : Fin 4} {c : CutRing} {N : ℝ} (hc : c ∈ barrierCandidate a j N)
    (M : Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    {s : ℝ} (hp : barrierLinePoint a j c s ∈ squareInterior) :
    s ∈ barrierSubdivision ha i j c M ↔
      ∃z ∈ M,z.val.1=i ∧ barrierSitePoint z=barrierLinePoint a j c s := by
  have hs := (barrierLinePoint_interior_iff hc s).mp hp
  simp only [barrierSubdivision,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  have hlo : s ≠ barrierLineLower a j c := ne_of_gt hs.1
  have hhi : s ≠ barrierLineUpper a j c := ne_of_lt hs.2
  simp only [hlo,hhi,false_or]
  constructor
  · intro h
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp h
    obtain ⟨hzM,hzi,hzp,hzc⟩ := Finset.mem_filter.mp hz
    refine ⟨z,hzM,hzi,?_⟩
    rw [←he,barrierLinePoint_parameter hzc]
  · rintro ⟨z,hz,hzi,hzp⟩
    apply Finset.mem_image.mpr
    refine ⟨z,Finset.mem_filter.mpr ⟨hz,hzi,?_,?_⟩,?_⟩
    · rwa [hzp]
    · rw [hzp,cutForm_barrierLinePoint]
    · rw [hzp,barrierLineParameter_point]

theorem barrierSubdivision_site_before_upper {a m : ℕ} (ha : 0 < a) (i : Fin m)
    {j : Fin 4} {c : CutRing} {N : ℝ} (hc : c ∈ barrierCandidate a j N)
    (M : Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    {s : ℝ} (hs : s ∈ barrierSubdivision ha i j c M)
    (hsU : s < barrierLineUpper a j c) :
    ∃z : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j),
      z.val.1=i ∧ barrierSitePoint z=barrierLinePoint a j c s := by
  simp only [barrierSubdivision,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with (rfl | rfl) | hs
  · exact ⟨barrierIncomingSite ha i hc,rfl,rfl⟩
  · exact False.elim (lt_irrefl _ hsU)
  · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨_,hzi,_,hzline⟩ := Finset.mem_filter.mp hz
    exact ⟨z,hzi,(barrierLinePoint_parameter hzline).symm⟩

namespace BarrierSignalSystem
variable {a : ℕ} {ha : 0 < a} {Q B : ℝ} (S : BarrierSignalSystem a ha Q B)

theorem local_line_transport {m : ℕ} (g : polygonFullGroup a m) (i k : Fin m)
    {N : ℝ} (hN : 0 < N) (j : Fin 4) (c : CutRing) (u : CutRing×CutRing)
    (hc : c ∈ barrierCandidate a j N)
    (hc' : c+integralCutForm a j u ∈ barrierCandidate a j N)
    (b₁ b₂ b₁' b₂' : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hs : signalSuccess (flagMeanSignal S.first.signal N) b₁)
    (hs' : signalSuccess (flagMeanSignal S.first.signal N) b₁')
    (hb₁ : ∀z,b₁' (flagSiteAction (commonVertexDenominator_pos ha) g z)=b₁ z)
    (hb₂ : ∀z,b₂' (flagSiteAction (commonVertexDenominator_pos ha) g z)=b₂ z)
    (L U : ℝ)
    (hinside : ∀r ∈ Ioo L U,barrierLinePoint a j c r ∈ squareInterior ∧
      barrierLinePoint a j (c+integralCutForm a j u)
        (r+barrierLineParameter j (ordinary u.1,ordinary u.2)) ∈ squareInterior)
    (hU : U ≤ barrierLineUpper a j c)
    (hL : L ∈ barrierSubdivision ha i j c (S.marks hN j b₁))
    (hT : U ∈ barrierSubdivision ha i j c (S.marks hN j b₁))
    (hL' : L+barrierLineParameter j (ordinary u.1,ordinary u.2) ∈
      barrierSubdivision ha k j (c+integralCutForm a j u) (S.marks hN j b₁'))
    (hT' : U+barrierLineParameter j (ordinary u.1,ordinary u.2) ∈
      barrierSubdivision ha k j (c+integralCutForm a j u) (S.marks hN j b₁'))
    (hchart : ∀(r : ℝ),r ∈ Ico L U →
      ∀z : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j),
      z.val.1=i → barrierSitePoint z=barrierLinePoint a j c r →
      flagAffineData g i z.val.2=(k,u))
    {x : ℝ} (hx : x ∈ Ioo L U) :
    x ∈ subdivisionBarrier (barrierSubdivision ha i j c (S.marks hN j b₁))
        (barrierActivation ha i j c b₂) ↔
    x+barrierLineParameter j (ordinary u.1,ordinary u.2) ∈
      subdivisionBarrier (barrierSubdivision ha k j (c+integralCutForm a j u) (S.marks hN j b₁'))
        (barrierActivation ha k j (c+integralCutForm a j u) b₂') := by
  let d := barrierLineParameter j (ordinary u.1,ordinary u.2)
  have haction (r : ℝ) (hr : r ∈ Ico L U)
      (z : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j))
      (hzi : z.val.1=i) (hzp : barrierSitePoint z=barrierLinePoint a j c r) :
      (flagSiteAction (commonVertexDenominator_pos ha) g z).val.1=k ∧
      barrierSitePoint (flagSiteAction (commonVertexDenominator_pos ha) g z)=
        barrierLinePoint a j (c+integralCutForm a j u) (r+d) := by
    have hh := flagAffineData_action g z.val
    rw [hzi,hchart r hr z hzi hzp] at hh
    refine ⟨hh.1,?_⟩
    change (flagAction g z.val).2.val=_
    rw [hh.2]
    change barrierSitePoint z+_= _
    rw [hzp,barrierLinePoint_translate]
  apply subdivisionBarrier_translate_iff hL hT hL' hT' _ _ hx
  · intro r hr
    by_cases heL : r=L
    · subst r
      exact iff_of_true hL hL'
    by_cases heU : r=U
    · subst r
      exact iff_of_true hT hT'
    have hr' : r ∈ Ioo L U := ⟨lt_of_le_of_ne hr.1 (Ne.symm heL),lt_of_le_of_ne hr.2 heU⟩
    obtain ⟨hp,hp'⟩ := hinside r hr'
    rw [mem_barrierSubdivision_interior ha i hc _ hp,
      mem_barrierSubdivision_interior ha k hc' _ hp']
    constructor
    · rintro ⟨z,hz,hzi,hzp⟩
      obtain ⟨hwi,hwp⟩ := haction r ⟨hr'.1.le,hr'.2⟩ z hzi hzp
      refine ⟨flagSiteAction (commonVertexDenominator_pos ha) g z,?_,hwi,hwp⟩
      rw [S.mem_marks_iff hN j b₁' hs',hb₁]
      exact (S.mem_marks_iff hN j b₁ hs z).mp hz
    · rintro ⟨w,hw,hwk,hwp⟩
      have hlat : InFlagLattice (commonVertexDenominator a) (barrierLinePoint a j c r) := by
        have hh := inFlagLattice_add (commonVertexDenominator_pos ha) w.property (-u)
        change InFlagLattice _ (barrierSitePoint w+_) at hh
        rw [hwp,barrierLinePoint_translate] at hh
        simpa only [Prod.fst_neg,Prod.snd_neg,map_neg,←Prod.neg_mk,add_neg_cancel_right] using hh
      let z := barrierInteriorSite ha i j hp hlat
      obtain ⟨hwi,hwp'⟩ := haction r ⟨hr'.1.le,hr'.2⟩ z rfl rfl
      have hew : flagSiteAction (commonVertexDenominator_pos ha) g z=w :=
        flagSite_eq_of_track_point (hwi.trans hwk.symm) (hwp'.trans hwp.symm)
      refine ⟨z,?_,rfl,rfl⟩
      rw [S.mem_marks_iff hN j b₁ hs,←hb₁,hew]
      exact (S.mem_marks_iff hN j b₁' hs' w).mp hw
  · intro r hr hrLU
    obtain ⟨z,hzi,hzp⟩ := barrierSubdivision_site_before_upper ha i hc _ hr (hrLU.2.trans_le hU)
    obtain ⟨hwi,hwp⟩ := haction r hrLU z hzi hzp
    rw [barrierActivation_at_site ha i j c b₂ r z hzi hzp,
      barrierActivation_at_site ha k j (c+integralCutForm a j u) b₂' _ _ hwi hwp,hb₂]

end BarrierSignalSystem
end LocalBarrierTransport

end SimpleAmenable
end
end

end OAI
