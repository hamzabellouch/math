import OAI.Geometry.PeriodicTiling.PeriodicVolumeMass
import Mathlib.Tactic.Tauto

namespace OAI

noncomputable section

open Set MeasureTheory Filter
open scoped Pointwise ENNReal

namespace PeriodicTilingThree.PeriodicVolume

variable {d : ℕ}

def typedPiece (Ω0 Ω1 C1 : Set (Space d)) (c : Space d) : Set (Space d) := by
  classical
  exact if c ∈ C1 then Ω1 else Ω0

theorem typedPiece_measurable (Ω0 Ω1 C1 : Set (Space d))
    (h0 : MeasurableSet Ω0) (h1 : MeasurableSet Ω1) (c : Space d) :
    MeasurableSet (typedPiece Ω0 Ω1 C1 c) := by
  classical
  unfold typedPiece
  split_ifs <;> assumption

theorem typedPiece_periodic (b : Module.Basis (Fin d) ℝ (Space d))
    (Ω0 Ω1 C1 : Set (Space d))
    (ht : ∀ v ∈ latticeOfBasis b, Period C1 v)
    (g : latticeOfBasis b) (x : Space d) :
    typedPiece Ω0 Ω1 C1 (x + (g : Space d)) = typedPiece Ω0 Ω1 C1 x := by
  classical
  simp only [typedPiece, ht g g.property x]

theorem typedPiece_volume (Ω0 Ω1 C1 : Set (Space d))
    (hv : volume Ω1 = volume Ω0) (c : Space d) :
    volume (typedPiece Ω0 Ω1 C1 c) = volume Ω0 := by
  classical
  unfold typedPiece
  split_ifs
  · exact hv
  · rfl

theorem typed_aedisjoint (Ω0 Ω1 C C1 : Set (Space d))
    (htile : TypedAETiles Ω0 Ω1 C C1) :
    Pairwise fun c c' : C => AEDisjoint volume
      (translate c (typedPiece Ω0 Ω1 C1 c))
      (translate c' (typedPiece Ω0 Ω1 C1 c')) := by
  classical
  intro c c' hne
  have ha : ∀ᵐ x ∂volume,
      x ∉ translate c (typedPiece Ω0 Ω1 C1 c) ∩
        translate c' (typedPiece Ω0 Ω1 C1 c') := by
    filter_upwards [htile] with x hx
    intro hmem
    exact hne (hx.unique hmem.1 hmem.2)
  simpa only [AEDisjoint, not_not, Set.ofPred_mem_eq] using (ae_iff.mp ha)

theorem typed_assembly_ae_eq_univ (Ω0 Ω1 C C1 : Set (Space d))
    (htile : TypedAETiles Ω0 Ω1 C C1) :
    assembly C (typedPiece Ω0 Ω1 C1) =ᵐ[volume] Set.univ := by
  classical
  filter_upwards [htile] with x hx
  apply propext
  exact ⟨fun _ => mem_univ x, fun _ => mem_assembly.mpr hx.exists⟩

theorem typed_cell_mass (b : Module.Basis (Fin d) ℝ (Space d))
    (Ω0 Ω1 C C1 : Set (Space d))
    (hC : C.Countable)
    (hfin : ∀ B : Set (Space d), Bornology.IsBounded B → (C ∩ B).Finite)
    (h0 : MeasurableSet Ω0) (h1 : MeasurableSet Ω1)
    (hv : volume Ω1 = volume Ω0)
    (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (ht : ∀ v ∈ latticeOfBasis b, Period C1 v)
    (htile : TypedAETiles Ω0 Ω1 C C1) :
    volume (ZSpan.fundamentalDomain b) =
      Nat.card (representatives b C) • volume Ω0 := by
  classical
  let := (representatives_finite b C hfin).fintype
  have hu := ae_eq_set_inter (typed_assembly_ae_eq_univ Ω0 Ω1 C C1 htile)
    (Filter.EventuallyEq.rfl : ZSpan.fundamentalDomain b =ᵐ[volume]
      ZSpan.fundamentalDomain b)
  calc
    volume (ZSpan.fundamentalDomain b) =
        volume (assembly C (typedPiece Ω0 Ω1 C1) ∩ ZSpan.fundamentalDomain b) := by
      simpa only [univ_inter] using (measure_congr hu).symm
    _ = ∑' r : representatives b C, volume (typedPiece Ω0 Ω1 C1 r) :=
      packed_assembly_mass b C hC hp (typedPiece Ω0 Ω1 C1)
        (typedPiece_periodic b Ω0 Ω1 C1 ht)
        (fun c _ => typedPiece_measurable Ω0 Ω1 C1 h0 h1 c)
        (typed_aedisjoint Ω0 Ω1 C C1 htile)
    _ = Nat.card (representatives b C) • volume Ω0 := by
      simp only [typedPiece_volume Ω0 Ω1 C1 hv, tsum_fintype,
        Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]

theorem assembly_period (b : Module.Basis (Fin d) ℝ (Space d))
    (C : Set (Space d)) (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (K : Space d → Set (Space d))
    (hKp : ∀ (g : latticeOfBasis b) x, K (x + (g : Space d)) = K x)
    (g : latticeOfBasis b) : Period (assembly C K) (g : Space d) := by
  intro x
  rw [mem_assembly, mem_assembly]
  constructor
  · rintro ⟨c, hc⟩
    have hcg : (c : Space d) - (g : Space d) ∈ C := by
      simpa only [sub_eq_add_neg] using
        (hp _ ((latticeOfBasis b).neg_mem g.property) c).2 c.property
    refine ⟨⟨(c : Space d) - (g : Space d), hcg⟩, ?_⟩
    have hKm : K ((c : Space d) - (g : Space d)) = K c := by
      simpa only [NegMemClass.coe_neg, sub_eq_add_neg] using hKp (-g) c
    change x - ((c : Space d) - (g : Space d)) ∈ K ((c : Space d) - (g : Space d))
    rw [hKm]
    have he : x - ((c : Space d) - (g : Space d)) =
        (x + (g : Space d)) - (c : Space d) := by abel
    rw [he]
    exact hc
  · rintro ⟨c, hc⟩
    have hcg : (c : Space d) + (g : Space d) ∈ C :=
      (hp g g.property c).2 c.property
    refine ⟨⟨(c : Space d) + (g : Space d), hcg⟩, ?_⟩
    change (x + (g : Space d)) - ((c : Space d) + (g : Space d)) ∈
      K ((c : Space d) + (g : Space d))
    rw [hKp g c, add_sub_add_right_eq_sub]
    exact hc

theorem lattice_vadd_assembly (b : Module.Basis (Fin d) ℝ (Space d))
    (C : Set (Space d)) (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (K : Space d → Set (Space d))
    (hKp : ∀ (g : latticeOfBasis b) x, K (x + (g : Space d)) = K x)
    (g : latticeOfBasis b) : g +ᵥ assembly C K = assembly C K := by
  ext x
  rw [mem_vadd_set_iff_neg_vadd_mem]
  change -(g : Space d) + x ∈ assembly C K ↔ x ∈ assembly C K
  simpa only [NegMemClass.coe_neg, add_comm] using
    assembly_period b C hp K hKp (-g) x

theorem ae_covers_of_cell_mass (b : Module.Basis (Fin d) ℝ (Space d))
    (C : Set (Space d)) (hC : C.Countable)
    (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (K : Space d → Set (Space d))
    (hKp : ∀ (g : latticeOfBasis b) x, K (x + (g : Space d)) = K x)
    (hK : ∀ c ∈ C, MeasurableSet (K c))
    (hmass : volume (assembly C K ∩ ZSpan.fundamentalDomain b) =
      volume (ZSpan.fundamentalDomain b)) :
    ∀ᵐ x ∂volume, ∃ c : C, x - (c : Space d) ∈ K c := by
  let : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  have hU := measurableSet_assembly C hC K hK
  have hP := ZSpan.fundamentalDomain_measurableSet b
  have hPfin : volume (ZSpan.fundamentalDomain b) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded b).measure_lt_top.ne
  have hae : (assembly C K ∩ ZSpan.fundamentalDomain b : Set (Space d)) =ᵐ[volume]
      ZSpan.fundamentalDomain b :=
    ae_eq_of_subset_of_measure_ge inter_subset_right hmass.symm.le
      (hU.inter hP).nullMeasurableSet hPfin
  have hnull := (ae_eq_set.mp hae).2
  have hdiff : ZSpan.fundamentalDomain b \
      (assembly C K ∩ ZSpan.fundamentalDomain b) =
      (assembly C K)ᶜ ∩ ZSpan.fundamentalDomain b := by
    ext x
    simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff]
    tauto
  rw [hdiff] at hnull
  have hglobal : volume (assembly C K)ᶜ = 0 :=
    (ZSpan.isAddFundamentalDomain' b volume).measure_zero_of_invariant
      ((assembly C K)ᶜ)
      (fun g => by
        ext x
        rw [mem_vadd_set_iff_neg_vadd_mem]
        change (-(g : Space d) + x ∉ assembly C K) ↔ x ∉ assembly C K
        simpa only [NegMemClass.coe_neg, add_comm] using
          not_congr (assembly_period b C hp K hKp (-g) x))
      hnull
  have hcover : ∀ᵐ x ∂volume, x ∈ assembly C K := ae_iff.mpr hglobal
  exact hcover.mono fun _ hx => mem_assembly.mp hx

theorem replacement_ae_covers (b : Module.Basis (Fin d) ℝ (Space d))
    (Ω0 Ω1 J C C1 : Set (Space d))
    (hC : C.Countable)
    (hfin : ∀ B : Set (Space d), Bornology.IsBounded B → (C ∩ B).Finite)
    (h0 : MeasurableSet Ω0) (h1 : MeasurableSet Ω1) (hJ : MeasurableSet J)
    (hv : volume Ω1 = volume Ω0) (hJv : volume J = volume Ω0)
    (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (ht : ∀ v ∈ latticeOfBasis b, Period C1 v)
    (htile : TypedAETiles Ω0 Ω1 C C1)
    (hpack : Pairwise fun c c' : C =>
      AEDisjoint volume (translate c J) (translate c' J)) :
    ∀ᵐ x ∂volume, ∃ c : C, x - (c : Space d) ∈ J := by
  classical
  let := (representatives_finite b C hfin).fintype
  apply ae_covers_of_cell_mass b C hC hp (fun _ => J) (fun _ _ => rfl)
    (fun _ _ => hJ)
  calc
    volume (assembly C (fun _ => J) ∩ ZSpan.fundamentalDomain b) =
        ∑' _r : representatives b C, volume J :=
      packed_assembly_mass b C hC hp (fun _ => J) (fun _ _ => rfl)
        (fun _ _ => hJ) hpack
    _ = Nat.card (representatives b C) • volume Ω0 := by
      simp only [hJv, tsum_fintype, Finset.sum_const, Finset.card_univ,
        Nat.card_eq_fintype_card]
    _ = volume (ZSpan.fundamentalDomain b) :=
      (typed_cell_mass b Ω0 Ω1 C C1 hC hfin h0 h1 hv hp ht htile).symm

end PeriodicTilingThree.PeriodicVolume

end

end OAI
