import OAI.Analysis.TracialSplitting.BlockSampling

namespace OAI


section

noncomputable section

open Pureness

open scoped ComplexOrder

namespace CurrentMain

namespace BistochasticTest

variable {A D N : Type} [CStarAlgebra A] [CStarAlgebra D] [Fintype N]

def ofFamily (v : N → A) (hcol : ∑ i, star (v i)*v i = 1)
    (hrow : ∑ i, v i*star (v i) = 1) : BistochasticTest A where
  size := Fintype.card N
  coeff := fun i => v ((Fintype.equivFin N).symm i)
  col := by rw [(Fintype.equivFin N).symm.sum_comp (fun i => star (v i)*v i)]; exact hcol
  row := by rw [(Fintype.equivFin N).symm.sum_comp (fun i => v i*star (v i))]; exact hrow

lemma ofFamily_average (ι : A →⋆ₐ[ℂ] D) (v : N → A)
    (hcol : ∑ i, star (v i)*v i = 1) (hrow : ∑ i, v i*star (v i) = 1) (r : D) :
    weightedAverage (fun _ => (1 : ℝ)) ((ofFamily v hcol hrow).map ι).coeff r =
      weightedAverage (fun _ : N => (1 : ℝ)) (fun i => ι (v i)) r := by
  simp only [weightedAverage,one_smul,map,ofFamily]
  exact (Fintype.equivFin N).symm.sum_comp (fun i => ι (v i)*r*star (ι (v i)))

variable [PartialOrder D] [StarOrderedRing D]

lemma average_le_one (V : BistochasticTest D) {r : D} (hr : IsStarProjection r) :
    weightedAverage (fun _ => (1 : ℝ)) V.coeff r ≤ 1 := by
  have h (i : Fin V.size) : V.coeff i*r*star (V.coeff i) ≤ V.coeff i*star (V.coeff i) := by
    simpa only [mul_one] using star_right_conjugate_le_conjugate hr.le_one (V.coeff i)
  simpa only [weightedAverage,one_smul,V.row] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)

end BistochasticTest

section Prepared

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

theorem nuclear_prepared_row_blocks
    (hA : IsNuclear.{0,0} A) (ι : A →⋆ₐ[ℂ] D) (hRR : RealRankZero D)
    (hT : Nonempty (TracialState D)) (K : Finset (unitary A)) (S : Finset (BistochasticTest A))
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ (M σ : ℝ) (L : Finset (unitary A)) (V : BistochasticTest A),
      1 ≤ M ∧ 0 < σ ∧ σ ≤ η ∧ M*σ ≤ η ∧ K ⊆ L ∧
      (∀ W ∈ S, ∀ (J : Type) [Fintype J] (y : J → D) (τ : TracialState D)
        (B : ℝ), 0 ≤ B →
        (∀ u ∈ L, ∑ j, traceTwoNorm τ (ι (u : A)*y j-y j*ι (u : A))^2 ≤ B) →
        ∑ j, (W.map ι).energy τ (y j) ≤ M*B) ∧
      ∀ r : D, IsStarProjection r → ∃ F : WeightedBlockFamily r,
        (∀ j, ∀ x ∈ L, ∃ H : Matrix (Fin (F.columns j)) (Fin (F.columns j)) ℂ,
          ‖F.range j*ι (x : A)*F.range j-(F.row j).matrix (F.base j) H‖ < σ) ∧
        (∀ τ : TracialState D,
          traceOneNorm τ (F.weightedSum-weightedAverage (fun _ => (1 : ℝ)) (V.map ι).coeff r) ≤ η^2) ∧
        (∀ x ∈ L, ∀ τ : TracialState D,
          ∑ j, F.weight j*traceTwoNorm τ (ι (x : A)*F.range j-F.range j*ι (x : A))^2 ≤ 6*σ) := by
  classical
  choose L₀ hL₀ using fun W : BistochasticTest A => W.relative_unitary_tests ι
  let L := K ∪ S.biUnion L₀
  let M : ℝ := 1+∑ W ∈ S, 4*(W.size : ℝ)
  have hM : 1 ≤ M := by
    have hs : 0 ≤ ∑ W ∈ S, 4*(W.size : ℝ) := Finset.sum_nonneg fun W _ => by positivity
    dsimp [M]
    linarith
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let σ := η/M
  have hσ : 0 < σ := div_pos hη hMpos
  have hση : σ ≤ η := (div_le_self hη.le hM)
  have hσ1 : σ < 1 := hση.trans_lt hη1
  obtain ⟨N,instN,v,hv,hv',hblocks⟩ := nuclear_weighted_block_family hA ι hRR hT L hσ hσ1
  let V := BistochasticTest.ofFamily v hv hv'
  refine ⟨M,σ,L,V,hM,hσ,hση,?_,Finset.subset_union_left,?_,?_⟩
  · dsimp [σ]; rw [mul_div_cancel₀ _ (ne_of_gt hMpos)]
  · intro W hW J _ y τ B hB htest
    have hcoeff : 4*(W.size : ℝ) ≤ M := by
      have hh := Finset.single_le_sum (f := fun W : BistochasticTest A => 4*(W.size : ℝ))
        (fun W _ => by positivity) hW
      dsimp [M]
      linarith
    exact (hL₀ W J y τ B hB (fun u hu => htest u
      (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨W,hW,hu⟩)))).trans
        (mul_le_mul_of_nonneg_right hcoeff hB)
  · intro r hr
    obtain ⟨F,hcomp,hmass,henergy⟩ := hblocks r hr
    refine ⟨F,hcomp,?_,henergy⟩
    intro τ
    rw [show (V.map ι).coeff = ((BistochasticTest.ofFamily v hv hv').map ι).coeff from rfl,
      BistochasticTest.ofFamily_average ι v hv hv' r]
    exact (hmass τ).trans ((sq_le_sq₀ hσ.le hη.le).mpr hση)

end Prepared

end CurrentMain

end

end

end OAI
