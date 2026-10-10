import OAI.NumberTheory.SiegelZeros.Structure.RealCutoff

namespace OAI

namespace SiegelZeros


namespace WeightedTorusJets.W62

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {H C M : ℕ}

noncomputable def orderedSelected (row : Index H → V)
    (hcard : (selected (K := K) H C row).card = M) : Fin M ↪o Index H :=
  SiegelZerosAwei.W30.orderedIndex (selected (K := K) H C row) hcard

theorem orderedSelected_mem (row : Index H → V)
    (hcard : (selected (K := K) H C row).card = M) (i : Fin M) :
    orderedSelected row hcard i ∈ selected (K := K) H C row :=
  SiegelZerosAwei.W30.orderedIndex_mem _ hcard i

theorem orderedSelected_weight_le (hH : 0 < H) (row : Index H → V)
    (hcard : (selected (K := K) H C row).card = M) (i : Fin M) :
    weight (orderedSelected row hcard i) ≤ C :=
  selected_weight_le hH row (orderedSelected_mem row hcard i)

theorem lower_weight_mem_cutoff (hH : 0 < H) (row : Index H → V)
    (hcard : (selected (K := K) H C row).card = M) (i : Fin M) (a : Index H)
    (ha : weight a < weight (orderedSelected row hcard i)) : a ∈ cutoff H C :=
  (mem_cutoff hH a).mpr (ha.le.trans (orderedSelected_weight_le hH row hcard i))

theorem lower_weight_ordered_span (hH : 0 < H) (row : Index H → V)
    (hcard : (selected (K := K) H C row).card = M) (i : Fin M) (a : Index H)
    (ha : weight a < weight (orderedSelected row hcard i)) :
    row a ∈ Submodule.span K
      ((fun j => row (orderedSelected row hcard j)) '' Set.Iio i) := by
  apply SiegelZerosAwei.W30.greedy_ordered_earlier_span row (cutoff H C)
    (zeroIndex H) hcard i
  · exact lower_weight_mem_cutoff hH row hcard i a ha
  · exact lt_of_weight_lt ha

theorem orderedSelected_det_of_spanning (row : Index H → Fin M → K)
    (hspan : W29.rowSpan (K := K) row (cutoff H C) = ⊤) :
    ∃ hcard : (selected (K := K) H C row).card = M,
      Matrix.det (fun i j => row (orderedSelected row hcard i) j) ≠ 0 :=
  SiegelZerosAwei.W30.greedy_ordered_det_of_spanning row (cutoff H C) (zeroIndex H) hspan

noncomputable def orderedCoords (row : Index H → V)
    (hcard : (selected (K := K) H C row).card = M) (i : Fin M) : Fin 3 → ℕ :=
  (orderedSelected row hcard i).coords

theorem orderedCoords_injective (row : Index H → V)
    (hcard : (selected (K := K) H C row).card = M) :
    Function.Injective (orderedCoords row hcard) :=
  coords_injective.comp (orderedSelected row hcard).injective

theorem orderedCoords_weight_le (hH : 0 < H) (row : Index H → V)
    (hcard : (selected (K := K) H C row).card = M) (i : Fin M) :
    SiegelZerosAwei.W31.weight (H : ℝ) (orderedCoords row hcard i) ≤ (C : ℝ) := by
  rw [orderedCoords, real_weight_eq]
  exact_mod_cast orderedSelected_weight_le hH row hcard i

end WeightedTorusJets.W62


end SiegelZeros

end OAI
