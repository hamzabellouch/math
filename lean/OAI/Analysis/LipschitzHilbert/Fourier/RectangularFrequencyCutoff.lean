import OAI.Analysis.LipschitzHilbert.Packets.AnnularPacketGeometry

namespace OAI

/-! A fixed rectangular plateau supplies both convolution factors in the
finite band representation. -/
noncomputable section
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

def unitPlaneBump : ContDiffBump (0 : ℝ×ℝ) := ⟨1,2,by norm_num,by norm_num⟩

def unitPlaneCutoff : SchwartzMap (ℝ×ℝ) ℂ :=
  (unitPlaneBump.hasCompactSupport.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp unitPlaneBump.contDiff)

def rectangularFrequencyCutoff (A B : ℝ) (hA : 0<A) (hB : 0<B) : SchwartzMap (ℝ×ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (packetCoordinates (A/2) (B/2) 0 (by positivity) (by positivity)) unitPlaneCutoff

theorem rectangularFrequencyCutoff_apply (A B : ℝ) (hA : 0<A) (hB : 0<B) (z : ℝ×ℝ) :
    rectangularFrequencyCutoff A B hA hB z=(unitPlaneBump (z.1/(A/2),z.2/(B/2)):ℂ) := by
  change (unitPlaneBump (z.1/(A/2),(z.2-0*z.1)/(B/2)):ℂ)=_
  simp only [zero_mul,sub_zero]

theorem rectangularFrequencyCutoff_one (A B : ℝ) (hA : 0<A) (hB : 0<B) (z : ℝ×ℝ)
    (hx : |z.1|≤A/2) (hy : |z.2|≤B/2) : rectangularFrequencyCutoff A B hA hB z=1 := by
  rw [rectangularFrequencyCutoff_apply]
  have hn : ‖(z.1/(A/2),z.2/(B/2))‖≤1 := by
    change max |z.1/(A/2)| |z.2/(B/2)|≤1
    simp only [abs_div,abs_of_pos hA,abs_of_pos hB,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact max_le ((div_le_one (by positivity)).mpr hx) ((div_le_one (by positivity)).mpr hy)
  have ho : unitPlaneBump (z.1/(A/2),z.2/(B/2))=1 :=
    unitPlaneBump.one_of_mem_closedBall (by
      change dist (z.1/(A/2),z.2/(B/2)) 0≤1
      rw [dist_zero_right]
      exact hn)
  rw [ho]
  norm_num

theorem rectangularFrequencyCutoff_support (A B : ℝ) (hA : 0<A) (hB : 0<B) (z : ℝ×ℝ)
    (hz : rectangularFrequencyCutoff A B hA hB z≠0) : |z.1|≤A ∧ |z.2|≤B := by
  have hn : ‖(z.1/(A/2),z.2/(B/2))‖<2 := by
    by_contra h
    have hzero : unitPlaneBump (z.1/(A/2),z.2/(B/2))=0 :=
      unitPlaneBump.zero_of_le_dist (by
        change 2≤dist (z.1/(A/2),z.2/(B/2)) 0
        rw [dist_zero_right]
        exact le_of_not_gt h)
    apply hz
    rw [rectangularFrequencyCutoff_apply,hzero]
    norm_num
  change max |z.1/(A/2)| |z.2/(B/2)|<2 at hn
  simp only [abs_div,abs_of_pos hA,abs_of_pos hB,abs_of_pos (by norm_num : (0:ℝ)<2),max_lt_iff] at hn
  constructor
  · have hh := (div_lt_iff₀ (by positivity : 0<A/2)).mp hn.1
    linarith
  · have hh := (div_lt_iff₀ (by positivity : 0<B/2)).mp hn.2
    linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
