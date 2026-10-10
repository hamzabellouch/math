import OAI.Analysis.AncientFlat.Evolution.TimePaste

namespace OAI
noncomputable section
open Set Filter
namespace ParabolicInitial
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def initialCoeff (f : V × ℝ → E) : V × ℝ → E := timeJoin (fun p => f (p.1,0)) f
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedSpace ℝ E] in
lemma holder_initial_trace {α K R h a : ℝ} (hα : 0≤α) (hK : 0≤K) (hh : 0≤h)
    {f : V × ℝ → E} (hf : HolderBound α (slab R h) f K) :
    HolderBound α {p : V × ℝ | ‖p.1‖<R ∧ p.2∈Icc a 0} (fun p => f (p.1,0)) K := by
  refine ⟨fun p hp => hf.1 (p.1,0) ⟨hp.1,le_rfl,hh⟩,?_⟩
  intro p hp q hq
  apply (hf.2 (p.1,0) ⟨hp.1,le_rfl,hh⟩ (q.1,0) ⟨hq.1,le_rfl,hh⟩).trans
  apply mul_le_mul_of_nonneg_left _ hK
  apply Real.rpow_le_rpow (pdist_nonneg _ _) _ hα
  simp only [pdist,sub_self,abs_zero,
    Real.zero_rpow (by norm_num : (1:ℝ)/4≠0),add_zero]
  exact le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedSpace ℝ E] in
lemma holder_initialCoeff {α K R h a : ℝ} (hα : 0≤α) (hK : 0≤K) (hh : 0≤h) (ha : a≤0)
    {f : V × ℝ → E} (hf : HolderBound α (slab R h) f K) :
    HolderBound α {p : V × ℝ | ‖p.1‖<R ∧ p.2∈Icc a h} (initialCoeff f) (2*K) := by
  exact holder_timeJoin α K a h hα hK ha hh {x : V | ‖x‖<R}
    _ _ (holder_initial_trace hα hK hh hf) hf (fun _ _ => rfl)
omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma initialCoeff_pos (f : V × ℝ → E) (p : V × ℝ) (hp : 0≤p.2) : initialCoeff f p=f p := by
  simp [initialCoeff,timeJoin,not_lt_of_ge hp]
omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma initialCoeff_neg (f : V × ℝ → E) (p : V × ℝ) (hp : p.2<0) : initialCoeff f p=f (p.1,0) := by
  simp [initialCoeff,timeJoin,hp]
end ParabolicInitial

end

end OAI
