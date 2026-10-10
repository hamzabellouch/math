import Mathlib
import OAI.Analysis.Commutator.PartialDecomposition
import OAI.Analysis.Commutator.ProperIsometryReplicas
import OAI.Analysis.Commutator.WeakOperatorLimit
import OAI.Analysis.Commutator.WeakOperatorAlgebra

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

open Filter

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace PartialDecomposition

variable {M : VonNeumannAlgebra H} {r : H →L[ℂ] H}

variable (D : PartialDecomposition M r) (R : Replicas M r) (hr : IsStarProjection r)

def finitePacking (f : D.I → ℕ) (s : Finset D.I) : H →L[ℂ] H :=
  ∑ i∈s,R.a (f i)*star (D.v i).val

include hr in
lemma finitePacking_star_mul (f : D.I → ℕ) (hf : Function.Injective f) (s : Finset D.I) :
    star (D.finitePacking R f s)*D.finitePacking R f s=D.support s := by
  classical
  rw [finitePacking,star_sum,Finset.sum_mul,support]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum,Finset.sum_eq_single_of_mem i hi]
  · simp only [star_mul,star_star]
    calc
      _=((D.v i).val*(star (R.a (f i))*R.a (f i)))*star (D.v i).val := by noncomm_ring
      _=(D.v i).final := by rw [R.initial,(D.v i).mul_source hr]; rfl
  · intro j hj hne
    simp only [star_mul,star_star]
    calc
      _=((D.v i).val*(star (R.a (f i))*R.a (f j)))*star (D.v j).val := by noncomm_ring
      _=0 := by rw [R.cross (f i) (f j) (fun h => hne (hf h).symm),mul_zero,zero_mul]

include hr in
lemma finitePacking_norm_le (f : D.I → ℕ) (hf : Function.Injective f) (s : Finset D.I) :
    ‖D.finitePacking R f s‖≤1 := by
  have he := D.support_norm_le s
  rw [←D.finitePacking_star_mul R hr f hf s,CStarRing.norm_star_mul_self] at he
  nlinarith [norm_nonneg (D.finitePacking R f s)]

lemma finitePacking_mul_val (f : D.I → ℕ) (s : Finset D.I) {i : D.I} (hi : i∈s) :
    D.finitePacking R f s*(D.v i).val=R.a (f i)*(D.v i).initial := by
  classical
  rw [finitePacking,Finset.sum_mul,Finset.sum_eq_single_of_mem i hi,mul_assoc]
  · rfl
  · intro j hj hne
    rw [mul_assoc,D.cross j i hne,mul_zero]

include hr in
theorem exists_packing (f : D.I → ℕ) (hf : Function.Injective f) :
    ∃ W : H →L[ℂ] H,W∈M ∧ ∀ i,W*(D.v i).val=R.a (f i)*(D.v i).initial := by
  classical
  let ω : Ultrafilter (Finset D.I) := Ultrafilter.of atTop
  have hω : (ω : Filter (Finset D.I))≤atTop := Ultrafilter.of_le _
  obtain ⟨W,hW,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω (D.finitePacking R f) 1
    (by norm_num) (D.finitePacking_norm_le R hr f hf)
  have hWM : W∈M := WeakOperatorLimit.mem_vonNeumann hlim M
    (Eventually.of_forall fun s => M.sum_mem (fun i _ =>
      M.mul_mem (R.mem (f i)) (M.star_mem' (D.v i).mem)))
  refine ⟨W,hWM,?_⟩
  intro i
  apply WeakOperatorLimit.right_eq hlim (D.v i).val (R.a (f i)*(D.v i).initial)
  filter_upwards [hω (eventually_ge_atTop ({i}:Finset D.I))] with s hs
  exact D.finitePacking_mul_val R f s (i:=i) (hs (Finset.mem_singleton_self i))

include hr in
lemma packing_isometry (f : D.I → ℕ) (hf : Function.Injective f)
    {W : H →L[ℂ] H} (hW : ∀ i,W*(D.v i).val=R.a (f i)*(D.v i).initial) : star W*W=1 := by
  apply D.eq_of_coefficients_eq
  intro i j
  calc
    star (D.v i).val*(star W*W)*(D.v j).val=star (W*(D.v i).val)*(W*(D.v j).val) := by
      rw [star_mul]; noncomm_ring
    _=star (R.a (f i)*(D.v i).initial)*(R.a (f j)*(D.v j).initial) := by rw [hW i,hW j]
    _=star (D.v i).val*(D.v j).val := by
      rw [star_mul,(D.v i).initial_projection.isSelfAdjoint.star_eq]
      rw [show (D.v i).initial*star (R.a (f i))*(R.a (f j)*(D.v j).initial)=
        (D.v i).initial*(star (R.a (f i))*R.a (f j))*(D.v j).initial by noncomm_ring]
      by_cases hij : i=j
      · subst j
        rw [R.initial,((D.v i).initial_projection.le_iff_mul_eq_left hr).mp (D.v i).source_le,
          (D.v i).initial_projection.isIdempotentElem.eq]
        rfl
      · rw [R.cross (f i) (f j) (fun h => hij (hf h)),mul_zero,zero_mul,D.cross i j hij]
    _=star (D.v i).val*1*(D.v j).val := by rw [mul_one]

lemma packings_orthogonal (f g : D.I → ℕ) (hfg : ∀ i j,f i≠g j)
    {W V : H →L[ℂ] H} (hW : ∀ i,W*(D.v i).val=R.a (f i)*(D.v i).initial)
    (hV : ∀ i,V*(D.v i).val=R.a (g i)*(D.v i).initial) : star W*V=0 := by
  apply D.eq_zero_of_coefficients_zero
  intro i j
  calc
    _=star (W*(D.v i).val)*(V*(D.v j).val) := by rw [star_mul]; noncomm_ring
    _=star (R.a (f i)*(D.v i).initial)*(R.a (g j)*(D.v j).initial) := by rw [hW i,hV j]
    _=star (D.v i).initial*(star (R.a (f i))*R.a (g j))*(D.v j).initial := by
      rw [star_mul]; noncomm_ring
    _=0 := by rw [R.cross _ _ (hfg i j),mul_zero,zero_mul]

end PartialDecomposition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
