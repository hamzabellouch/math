import Mathlib
import OAI.Analysis.Commutator.KaplanskyFullRange
import OAI.Analysis.Commutator.StrongDenseTests

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped Topology

namespace Kadison

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [TopologicalSpace.SeparableSpace A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

abbrev CStarContractions (A : Type*) [CStarAlgebra A] := {a : A // ‖a‖≤1}

instance contraction_nonempty : Nonempty (CStarContractions A) := ⟨⟨0,by simp⟩⟩

def countableContractions : ℕ → A := fun n =>
  (TopologicalSpace.denseSeq (CStarContractions A) n).val

omit [PartialOrder A] [StarOrderedRing A] in
lemma countableContractions_norm (n : ℕ) : ‖countableContractions (A:=A) n‖≤1 :=
  (TopologicalSpace.denseSeq (CStarContractions A) n).property

omit [PartialOrder A] [StarOrderedRing A] in
lemma countableContractions_approx (a : A) (ha : ‖a‖≤1) {ε : ℝ} (hε : 0<ε) :
    ∃ n,‖countableContractions (A:=A) n-a‖<ε := by
  obtain ⟨n,hn⟩ := Metric.denseRange_iff.mp
    (TopologicalSpace.denseRange_denseSeq (CStarContractions A)) ⟨a,ha⟩ ε hε
  exact ⟨n,by simpa only [Subtype.dist_eq,dist_eq_norm,norm_sub_rev,countableContractions] using hn⟩

theorem countableContractions_strong_dense (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (T : H →L[ℂ] H)
    (hT : T∈Set.centralizer (Set.centralizer (Set.range φ))) (hnT : ‖T‖≤1) :
    ∃ k : ℕ → ℕ,∀ ξ,Tendsto
      (fun n => φ (countableContractions (A:=A) (k n)) ξ) atTop (𝓝 (T ξ)) := by
  classical
  let v : ℕ → H := TopologicalSpace.denseSeq H
  have hap (n : ℕ) : ∃ k : ℕ,∀ j : Fin n,
      ‖φ (countableContractions (A:=A) k) (v j)-T (v j)‖<1/((n:ℝ)+1) := by
    let ε : ℝ := 1/((n:ℝ)+1)
    have hε : 0<ε := by dsimp [ε]; positivity
    obtain ⟨a,ha,he⟩ := Kaplansky.range_contraction_finite_approx φ (Fin n) hT hnT
      (fun j => v j) (ε/2) (by positivity)
    let M : ℝ := 1+∑ j : Fin n,‖v j‖
    have hM : 0<M := by dsimp [M]; positivity
    obtain ⟨k,hk⟩ := countableContractions_approx a ha (div_pos (half_pos hε) hM)
    refine ⟨k,?_⟩
    intro j
    have hvM : ‖v j‖≤M := by
      have hh := Finset.single_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin n))) => norm_nonneg (v i))
        (Finset.mem_univ j)
      dsimp only [M]
      linarith
    have hsmall : ‖φ (countableContractions (A:=A) k-a) (v j)‖<ε/2 := by
      calc
        ‖φ (countableContractions (A:=A) k-a) (v j)‖≤
            ‖φ (countableContractions (A:=A) k-a)‖*‖v j‖ :=
          (φ (countableContractions (A:=A) k-a)).le_opNorm _
        _≤‖countableContractions (A:=A) k-a‖*‖v j‖ :=
          mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le φ _) (norm_nonneg _)
        _≤‖countableContractions (A:=A) k-a‖*M :=
          mul_le_mul_of_nonneg_left hvM (norm_nonneg _)
        _<(ε/2/M)*M := mul_lt_mul_of_pos_right hk hM
        _=ε/2 := div_mul_cancel₀ _ (ne_of_gt hM)
    have hid : φ (countableContractions (A:=A) k) (v j)-T (v j)=
        φ (countableContractions (A:=A) k-a) (v j)+(φ a (v j)-T (v j)) := by
      simp only [map_sub,sub_apply]
      abel
    rw [hid]
    exact (norm_add_le _ _).trans_lt (by linarith [he j])
  choose k hk using hap
  have hlim (j : ℕ) : Tendsto (fun n => φ (countableContractions (A:=A) (k n)) (v j))
      atTop (𝓝 (T (v j))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [eventually_ge_atTop (j+1)] with n hn
    exact (hk n ⟨j,by omega⟩).le
  exact ⟨k,strong_tendsto_of_dense_tests v (TopologicalSpace.denseRange_denseSeq H)
    (fun n => φ (countableContractions (A:=A) (k n))) T
    (fun n => (NonUnitalStarAlgHom.norm_apply_le φ _).trans (countableContractions_norm _))
    hnT hlim⟩

end Kadison

end

end
end

end OAI
