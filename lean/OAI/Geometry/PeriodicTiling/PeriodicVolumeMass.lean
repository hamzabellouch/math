import OAI.Geometry.PeriodicTiling.PeriodicVolumeOrbits
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic.Abel

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped Pointwise ENNReal

namespace PeriodicTilingThree.PeriodicVolume

variable {d : ℕ}

def translate (c : Space d) (K : Set (Space d)) : Set (Space d) :=
  {x | x - c ∈ K}

@[simp] theorem mem_translate {c x : Space d} {K : Set (Space d)} :
    x ∈ translate c K ↔ x - c ∈ K := Iff.rfl

theorem translate_eq_vadd (c : Space d) (K : Set (Space d)) :
    translate c K = c +ᵥ K := by
  ext x
  simp only [mem_translate, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  rw [sub_eq_add_neg, add_comm x (-c)]

@[simp] theorem measure_translate (c : Space d) (K : Set (Space d)) :
    volume (translate c K) = volume K := by
  rw [translate_eq_vadd, measure_vadd]

theorem measurableSet_translate (c : Space d) {K : Set (Space d)}
    (hK : MeasurableSet K) : MeasurableSet (translate c K) :=
  hK.preimage (measurable_id.sub measurable_const)

theorem lattice_vadd_translate (b : Module.Basis (Fin d) ℝ (Space d))
    (g : latticeOfBasis b) (r : Space d) (K : Set (Space d)) :
    g +ᵥ translate r K = translate (r + (g : Space d)) K := by
  ext x
  rw [mem_vadd_set_iff_neg_vadd_mem]
  change (-(g : Space d) + x) - r ∈ K ↔ x - (r + (g : Space d)) ∈ K
  have he : (-(g : Space d) + x) - r = x - (r + (g : Space d)) := by abel
  rw [he]

def assembly (C : Set (Space d)) (K : Space d → Set (Space d)) : Set (Space d) :=
  ⋃ c : C, translate c (K c)

@[simp] theorem mem_assembly {C : Set (Space d)} {K : Space d → Set (Space d)}
    {x : Space d} : x ∈ assembly C K ↔ ∃ c : C, x - (c : Space d) ∈ K c := by
  simp only [assembly, mem_iUnion, mem_translate]

theorem measurableSet_assembly (C : Set (Space d)) (hC : C.Countable)
    (K : Space d → Set (Space d)) (hK : ∀ c ∈ C, MeasurableSet (K c)) :
    MeasurableSet (assembly C K) := by
  let : Countable C := hC.to_subtype
  exact MeasurableSet.iUnion fun c : C => measurableSet_translate c (hK c c.property)

theorem periodic_piece_mass (b : Module.Basis (Fin d) ℝ (Space d))
    (C : Set (Space d)) (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (K : Space d → Set (Space d))
    (hKp : ∀ (g : latticeOfBasis b) x, K (x + (g : Space d)) = K x) :
    (∑' c : C, volume (translate c (K c) ∩ ZSpan.fundamentalDomain b)) =
      ∑' r : representatives b C, volume (K r) := by
  let : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  have hP := ZSpan.isAddFundamentalDomain' b (volume : Measure (Space d))
  calc
    (∑' c : C, volume (translate c (K c) ∩ ZSpan.fundamentalDomain b)) =
        ∑' p : representatives b C × latticeOfBasis b,
          volume (translate (orbitEquiv b C hp p) (K (orbitEquiv b C hp p)) ∩
            ZSpan.fundamentalDomain b) :=
      ((orbitEquiv b C hp).tsum_eq _).symm
    _ = ∑' r : representatives b C, ∑' g : latticeOfBasis b,
          volume (translate ((r : Space d) + (g : Space d))
            (K ((r : Space d) + (g : Space d))) ∩ ZSpan.fundamentalDomain b) :=
      ENNReal.tsum_prod'
    _ = ∑' r : representatives b C, volume (K r) := by
      apply tsum_congr
      intro r
      calc
        (∑' g : latticeOfBasis b,
            volume (translate ((r : Space d) + (g : Space d))
              (K ((r : Space d) + (g : Space d))) ∩ ZSpan.fundamentalDomain b)) =
            ∑' g : latticeOfBasis b,
              volume ((g +ᵥ translate r (K r)) ∩ ZSpan.fundamentalDomain b) := by
          apply tsum_congr
          intro g
          rw [hKp g r, lattice_vadd_translate]
        _ = volume (translate r (K r)) := (hP.measure_eq_tsum _).symm
        _ = volume (K r) := measure_translate _ _

theorem periodic_piece_mass_eq_card (b : Module.Basis (Fin d) ℝ (Space d))
    (C : Set (Space d)) (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (hfin : ∀ B : Set (Space d), Bornology.IsBounded B → (C ∩ B).Finite)
    (K : Space d → Set (Space d))
    (hKp : ∀ (g : latticeOfBasis b) x, K (x + (g : Space d)) = K x)
    (v : ℝ≥0∞) (hv : ∀ c ∈ C, volume (K c) = v) :
    (∑' c : C, volume (translate c (K c) ∩ ZSpan.fundamentalDomain b)) =
      Nat.card (representatives b C) • v := by
  let := (representatives_finite b C hfin).fintype
  rw [periodic_piece_mass b C hp K hKp]
  have hvr : ∀ r : representatives b C, volume (K r) = v := fun r => hv r r.property.1
  simp only [hvr, tsum_fintype, Finset.sum_const,
    Finset.card_univ, Nat.card_eq_fintype_card]

theorem packed_assembly_mass (b : Module.Basis (Fin d) ℝ (Space d))
    (C : Set (Space d)) (hC : C.Countable)
    (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (K : Space d → Set (Space d))
    (hKp : ∀ (g : latticeOfBasis b) x, K (x + (g : Space d)) = K x)
    (hK : ∀ c ∈ C, MeasurableSet (K c))
    (hpack : Pairwise fun c c' : C =>
      AEDisjoint volume (translate c (K c)) (translate c' (K c'))) :
    volume (assembly C K ∩ ZSpan.fundamentalDomain b) =
      ∑' r : representatives b C, volume (K r) := by
  let : Countable C := hC.to_subtype
  calc
    volume (assembly C K ∩ ZSpan.fundamentalDomain b) =
        ∑' c : C, volume (translate c (K c) ∩ ZSpan.fundamentalDomain b) := by
      rw [assembly, iUnion_inter]
      apply measure_iUnion₀
      · intro c c' hne
        exact (hpack hne).mono inter_subset_left inter_subset_left
      · intro c
        exact ((measurableSet_translate c (hK c c.property)).inter
          (ZSpan.fundamentalDomain_measurableSet b)).nullMeasurableSet
    _ = ∑' r : representatives b C, volume (K r) :=
      periodic_piece_mass b C hp K hKp

end PeriodicTilingThree.PeriodicVolume

end

end OAI
