import Mathlib
import OAI.Analysis.Commutator.AtomicCoefficients

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

open Filter

namespace Kadison.AtomicFactor.Decomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} (D : Decomposition M p)

def finiteShift (f : D.I → D.I) (s : Finset D.I) : H →L[ℂ] H :=
  ∑ i∈s,D.v (f i)*star (D.v i)

lemma finiteShift_star_mul (f : D.I → D.I) (hf : Function.Injective f) (s : Finset D.I) :
    star (D.finiteShift f s)*D.finiteShift f s=D.support s := by
  classical
  rw [finiteShift,star_sum,Finset.sum_mul,support]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum,Finset.sum_eq_single_of_mem i hi]
  · simp only [star_mul,star_star]
    calc
      _=(D.v i*(star (D.v (f i))*D.v (f i)))*star (D.v i) := by noncomm_ring
      _=D.v i*star (D.v i) := by rw [D.initial,D.source]
  · intro j hj hne
    simp only [star_mul,star_star]
    calc
      _=(D.v i*(star (D.v (f i))*D.v (f j)))*star (D.v j) := by noncomm_ring
      _=0 := by rw [D.cross (f i) (f j) (fun h => hne (hf h).symm),mul_zero,zero_mul]

lemma finiteShift_norm_le (f : D.I → D.I) (hf : Function.Injective f) (s : Finset D.I) :
    ‖D.finiteShift f s‖≤1 := by
  have he := D.support_norm_le s
  rw [←D.finiteShift_star_mul f hf s,CStarRing.norm_star_mul_self] at he
  nlinarith [norm_nonneg (D.finiteShift f s)]

lemma finiteShift_mul_val (f : D.I → D.I) (s : Finset D.I) {i : D.I} (hi : i∈s) :
    D.finiteShift f s*D.v i=D.v (f i) := by
  classical
  rw [finiteShift,Finset.sum_mul,Finset.sum_eq_single_of_mem i hi,mul_assoc,D.initial,D.source]
  intro j hj hne
  rw [mul_assoc,D.cross j i hne,mul_zero]

theorem exists_shift (f : D.I → D.I) (hf : Function.Injective f) :
    ∃ W : H →L[ℂ] H,W∈M ∧ ∀ i,W*D.v i=D.v (f i) := by
  classical
  let ω : Ultrafilter (Finset D.I) := Ultrafilter.of atTop
  have hω : (ω : Filter (Finset D.I))≤atTop := Ultrafilter.of_le _
  obtain ⟨W,hW,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω (D.finiteShift f) 1
    (by norm_num) (D.finiteShift_norm_le f hf)
  have hWM : W∈M := WeakOperatorLimit.mem_vonNeumann hlim M
    (Eventually.of_forall fun s => M.sum_mem (fun i _ => M.mul_mem (D.mem (f i)) (M.star_mem' (D.mem i))))
  refine ⟨W,hWM,?_⟩
  intro i
  ext x
  apply ext_inner_right ℂ
  intro y
  apply tendsto_nhds_unique (hlim (D.v i x) y)
  apply tendsto_const_nhds.congr'
  filter_upwards [hω (eventually_ge_atTop ({i}:Finset D.I))] with s hs
  have he := D.finiteShift_mul_val f s (i:=i) (hs (Finset.mem_singleton_self i))
  exact congrArg (fun T : H →L[ℂ] H => inner ℂ (T x) y) he.symm

lemma shift_isometry (f : D.I → D.I) (hf : Function.Injective f)
    {W : H →L[ℂ] H} (hW : ∀ i,W*D.v i=D.v (f i)) : star W*W=1 := by
  apply D.eq_of_coefficients_eq
  intro i j
  calc
    star (D.v i)*(star W*W)*D.v j=star (W*D.v i)*(W*D.v j) := by
      rw [star_mul]; noncomm_ring
    _=star (D.v (f i))*D.v (f j) := by rw [hW i,hW j]
    _=star (D.v i)*D.v j := by
      by_cases hij : i=j
      · subst j; rw [D.initial,D.initial]
      · rw [D.cross i j hij,D.cross (f i) (f j) (fun h => hij (hf h))]
    _=star (D.v i)*1*D.v j := by rw [mul_one]

lemma shifts_orthogonal (f g : D.I → D.I) (hfg : ∀ i j,f i≠g j)
    {W V : H →L[ℂ] H} (hW : ∀ i,W*D.v i=D.v (f i))
    (hV : ∀ i,V*D.v i=D.v (g i)) : star W*V=0 := by
  apply D.eq_zero_of_coefficients_zero
  intro i j
  calc
    _=star (W*D.v i)*(V*D.v j) := by rw [star_mul]; noncomm_ring
    _=star (D.v (f i))*D.v (g j) := by rw [hW i,hV j]
    _=0 := D.cross _ _ (hfg i j)

end Kadison.AtomicFactor.Decomposition

end

end
end

end OAI
