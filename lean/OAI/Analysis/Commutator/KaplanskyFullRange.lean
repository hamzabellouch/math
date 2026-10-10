import Mathlib
import OAI.Analysis.Commutator.KaplanskyFull
import OAI.Analysis.Commutator.KaplanskyRange

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace Topology

open Filter

namespace Kadison.Kaplansky

open OperatorAmplification CyclicColumns CyclicSpatial

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance : DecidableEq (Fin 2) := Classical.decEq (Fin 2)

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

lemma matrixUnit_mem_matrixRange (i j : Fin 2) :
    matrixUnit (H:=H) (Fin 2) i j ∈ (matrixRepresentation (ι:=Fin 2) φ).range := by
  let X : CStarMatrix (Fin 2) (Fin 2) A := CStarMatrix.ofMatrix
    (fun k l => if k=i ∧ l=j then 1 else 0)
  refine ⟨X,?_⟩
  ext x k
  change (∑ l,φ (X k l) (x l))=single (Fin 2) i (x j) k
  change (∑ l,φ (if k=i ∧ l=j then 1 else 0) (x l))=single (Fin 2) i (x j) k
  by_cases hk : k=i
  · fin_cases j <;> simp [hk,single_apply]
  · simp [hk,single_apply]

lemma diagonal_mem_matrixRange (a : A) :
    diagonal (H:=H) (Fin 2) (φ a) ∈ (matrixRepresentation (ι:=Fin 2) φ).range := by
  let X : CStarMatrix (Fin 2) (Fin 2) A := CStarMatrix.ofMatrix
    (fun k l => if k=l then a else 0)
  refine ⟨X,?_⟩
  ext x k
  change (∑ l,φ (if k=l then a else 0) (x l))=φ a (x k)
  fin_cases k <;> simp

lemma offDiagonal_matrixRange_bicommutant {T : H →L[ℂ] H}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range φ))) :
    offDiagonal T∈Set.centralizer (Set.centralizer
      (Set.range (matrixRepresentation (ι:=Fin 2) φ))) := by
  intro R hR
  have hU : ∀ i j,matrixUnit (Fin 2) i j*R=R*matrixUnit (Fin 2) i j :=
    fun i j => hR _ (matrixUnit_mem_matrixRange φ i j)
  let a := entry (Fin 2) R 0 0
  have he : R=diagonal (H:=H) (Fin 2) a := diagonal_of_matrixUnits (Fin 2) 0 R hU
  have ha : a∈Set.centralizer (Set.range φ) := by
    rintro _ ⟨b,rfl⟩
    exact entry_commutes (Fin 2) R (φ b) (hR _ (diagonal_mem_matrixRange φ b)) 0 0
  rw [he]
  apply commutes_of_entries (Fin 2)
  intro i j
  rw [entry_offDiagonal]
  split_ifs
  · exact hT a ha
  · exact star_bicommutant φ.range hT a ha
  · simp

theorem range_contraction_finite_approx (ι : Type*) [Fintype ι] [DecidableEq ι]
    {T : H →L[ℂ] H} (hT : T∈Set.centralizer (Set.centralizer (Set.range φ)))
    (hnT : ‖T‖≤1) (x : ι → H) (ε : ℝ) (hε : 0<ε) :
    ∃ a : A,‖a‖≤1 ∧ ∀ i,‖φ a (x i)-T (x i)‖<ε := by
  obtain ⟨X,_,hnX,he⟩ := range_selfAdjoint_contraction_finite_approx ι
    (matrixRepresentation (ι:=Fin 2) φ) (offDiagonal_matrixRange_bicommutant φ hT)
    (offDiagonal_selfAdjoint T) (offDiagonal_norm_le hnT)
    (fun i => single (Fin 2) 1 (x i)) ε hε
  refine ⟨X 0 1,CStarMatrix.norm_entry_le_norm.trans hnX,?_⟩
  intro i
  have h := (PiLp.norm_apply_le
    (matrixRepresentation φ X (single (Fin 2) 1 (x i))-offDiagonal T (single (Fin 2) 1 (x i))) 0).trans_lt (he i)
  simpa [represented_matrix_apply,single_apply,apply_ite] using h

variable (T : H →L[ℂ] H)
  (hT : T∈Set.centralizer (Set.centralizer (Set.range φ))) (hnT : ‖T‖≤1)

include hT hnT in
lemma fullNet_exists (j : Finset H × ℕ) : ∃ a : A,
    ‖a‖≤1 ∧ ∀ x∈j.1,‖φ a x-T x‖<(j.2+1:ℝ)⁻¹ := by
  classical
  obtain ⟨a,ha,he⟩ := range_contraction_finite_approx φ j.1 hT hnT
    (fun x => (x:H)) ((j.2+1:ℝ)⁻¹) (by positivity)
  exact ⟨a,ha,fun x hx => he ⟨x,hx⟩⟩

def fullNet (j : Finset H × ℕ) : A := (fullNet_exists φ T hT hnT j).choose

lemma fullNet_spec (j : Finset H × ℕ) :
    ‖fullNet φ T hT hnT j‖≤1 ∧ ∀ x∈j.1,‖φ (fullNet φ T hT hnT j) x-T x‖<(j.2+1:ℝ)⁻¹ :=
  (fullNet_exists φ T hT hnT j).choose_spec

lemma fullNet_tendsto (x : H) :
    Tendsto (fun j => φ (fullNet φ T hT hnT j) x) atTop (𝓝 (T x)) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := exists_nat_one_div_lt hε
  filter_upwards [eventually_ge_atTop (({x}:Finset H),N)] with j hj
  rw [dist_eq_norm]
  apply (fullNet_spec φ T hT hnT j).2 x (hj.1 (Finset.mem_singleton_self x)) |>.trans_le
  have hn : (N+1:ℝ)≤j.2+1 := by exact_mod_cast Nat.succ_le_succ hj.2
  exact (inv_anti₀ (by positivity) hn).trans (by simpa only [one_div] using hN.le)

end Kadison.Kaplansky

end

end
end

end OAI
