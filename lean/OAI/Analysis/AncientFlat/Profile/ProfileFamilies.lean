import OAI.Analysis.AncientFlat.Kernel.ParameterDecay
import OAI.Analysis.AncientFlat.Profile.CompactificationIdentity
import OAI.Analysis.AncientFlat.Kernel.SymbolCore

namespace OAI
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace FlatSimilarity
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
def profileAf (G : ℝ → ℝ) (z : V) : ℝ := G (‖z‖^2)^2
def profileBf (G : ℝ → ℝ) (z : V) : ℝ := -(‖z‖^2*deriv G (‖z‖^2)/G (‖z‖^2))
omit [FiniteDimensional ℝ V] in
lemma profile_smooth (G : ℝ → ℝ) (κ : ℝ) (hκ : 0<κ)
    (hG : ContDiffOn ℝ ∞ G (Ici 0)) (hpos : ∀ y : ℝ, 0≤y → κ≤G y) :
    ContDiff ℝ ∞ (profileAf (V := V) G) ∧ ContDiff ℝ ∞ (profileBf (V := V) G) := by
  have hGV : ContDiff ℝ ∞ (fun z : V => G (‖z‖^2)) :=
    hG.comp_contDiff (contDiff_norm_sq ℝ) (fun z => sq_nonneg ‖z‖)
  have hGD : ContDiff ℝ ∞ (fun z : V => derivWithin G (Ici 0) (‖z‖^2)) :=
    (hG.derivWithin (uniqueDiffOn_Ici 0) (by simp)).comp_contDiff (contDiff_norm_sq ℝ)
      (fun z => sq_nonneg ‖z‖)
  refine ⟨hGV.pow 2,?_⟩
  have he : profileBf (V := V) G=(fun z => -(‖z‖^2*derivWithin G (Ici 0) (‖z‖^2)/G (‖z‖^2))) := by
    funext z
    dsimp [profileBf]
    by_cases hz : z=0
    · simp [hz]
    · rw [derivWithin_of_mem_nhds (Ici_mem_nhds (sq_pos_of_pos (norm_pos_iff.mpr hz)))]
  rw [he]
  exact (((contDiff_norm_sq ℝ).mul hGD).div hGV
    (fun z => (hκ.trans_le (hpos _ (sq_nonneg _))).ne')).neg
end FlatSimilarity
namespace ProfileDecay
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
def bump (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] : ContDiffBump (0:V) :=
  ⟨1,3/2,by norm_num,by norm_num⟩
def q (z : V) : ℝ := (‖z‖^2+bump V z)⁻¹^2
lemma q_pos (z : V) : 0<q z := by
  have h : 0<‖z‖^2+bump V z := by
    by_cases hz : z=0
    · subst z
      rw [(bump V).one_of_mem_closedBall (by simp [bump])]
      norm_num
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr hz)) (bump V).nonneg
  exact sq_pos_of_pos (inv_pos.mpr h)
lemma q_smooth : ContDiff ℝ ∞ (q : V → ℝ) := by
  apply (((contDiff_norm_sq ℝ).add (bump V).contDiff).inv ?_).pow 2
  intro z
  have hq := q_pos z
  intro he
  simp [q,he] at hq
lemma q_eq {z : V} (hz : 3/2≤‖z‖) : q z=‖z‖⁻¹^4 := by
  rw [q,(bump V).zero_of_le_dist (by simpa [bump,dist_zero_right] using hz),add_zero]
  simp only [inv_pow]
  ring

def arg (p : ℝ × V) : ℝ := p.1^2*q p.2
def familyA (H : ℝ → ℝ) (c : ℝ) (p : ℝ × V) : ℝ := H (arg p)^2-c^2
def familyB (H : ℝ → ℝ) (p : ℝ × V) : ℝ :=
  2*arg p*derivWithin H (Ici 0) (arg p)/H (arg p)
lemma arg_smooth : ContDiff ℝ ∞ (arg : ℝ × V → ℝ) :=
  (contDiff_fst.pow 2).mul (q_smooth.comp contDiff_snd)
lemma arg_nonneg (p : ℝ × V) : 0≤arg p := mul_nonneg (sq_nonneg _) (q_pos _).le
lemma families_smooth (H : ℝ → ℝ) (c : ℝ) (hH : ContDiffOn ℝ ∞ H (Ici 0))
    (hp : ∀ u∈Ici (0:ℝ), 0<H u) :
    ContDiff ℝ ∞ (familyA (V := V) H c) ∧ ContDiff ℝ ∞ (familyB (V := V) H) := by
  have hv : ContDiff ℝ ∞ (fun p : ℝ × V => H (arg p)) :=
    hH.comp_contDiff arg_smooth arg_nonneg
  have hd : ContDiff ℝ ∞ (fun p : ℝ × V => derivWithin H (Ici 0) (arg p)) :=
    (hH.derivWithin (uniqueDiffOn_Ici 0) (by simp)).comp_contDiff arg_smooth arg_nonneg
  exact ⟨(hv.pow 2).sub contDiff_const,
    ((contDiff_const.mul arg_smooth).mul hd).div hv (fun p => (hp _ (arg_nonneg p)).ne')⟩
lemma arg_even (s : ℝ) (z : V) : arg (-s,z)=arg (s,z) := by simp [arg]
lemma arg_zero (z : V) : arg (0,z)=0 := by simp [arg]
lemma families_decay (H : ℝ → ℝ) (c : ℝ) (hH : ContDiffOn ℝ ∞ H (Ici 0))
    (hp : ∀ u∈Ici (0:ℝ), 0<H u) (h0 : H 0=c) (n : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ s : ℝ, s∈Icc (0:ℝ) 1 → ∀ z : V, ‖z‖≤3 →
      ‖spaceJet (familyA H c) n (s,z)‖+‖spaceJet (familyB H) n (s,z)‖≤C*s^2 := by
  obtain ⟨C1,hC1,h1⟩ := parameter_decay (familyA (V := V) H c) (families_smooth H c hH hp).1
    (fun s z => by simp only [familyA,arg_even]) (fun z => by simp [familyA,arg_zero,h0]) n
  obtain ⟨C2,hC2,h2⟩ := parameter_decay (familyB (V := V) H) (families_smooth H c hH hp).2
    (fun s z => by simp only [familyB,arg_even]) (fun z => by simp [familyB,arg_zero]) n
  refine ⟨C1+C2,add_nonneg hC1 hC2,?_⟩
  intro s hs z hz
  simpa only [add_mul] using add_le_add (h1 s hs z hz) (h2 s hs z hz)
end ProfileDecay

end

end OAI
