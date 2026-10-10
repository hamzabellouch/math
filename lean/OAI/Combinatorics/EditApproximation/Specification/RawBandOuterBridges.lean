import OAI.Combinatorics.EditApproximation.Specification.RawBandOuter
import OAI.Combinatorics.EditApproximation.Specification.RawBandBridges
import OAI.Combinatorics.EditApproximation.Definitions

namespace OAI.EditApproximation.BinaryFraction

theorem dyadicSampledGroupActionReadWithWorkRaw_eq {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent Q : ℕ) (tau F : BinaryFraction)
    (child : Fin M → TargetInterval target.length → BinaryFraction)
    (initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (raw : List BinaryFraction) (hraw : raw.map value = groupDyadicScales M b F.value)
    (draw : ∀ t : Fin (groupDyadicScales M b F.value).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F.value t)) → Fin M)
    (members : List (UnskippedBand source target parent b P exponent tau.value F.value
      (fun i q => (child i q).value) (fun i q => (initial i q).1.value))) (hne : members ≠ []) :
    dyadicSampledGroupActionReadWithWorkRaw b exponent Q F initial current raw hraw draw
      (members.map UnskippedBand.raw) (by simpa using hne) =
      dyadicSampledGroupActionReadWithWork source target parent b P exponent Q tau F child initial current
        raw hraw draw members hne := by
  exact sampledGroupActionReadWithWorkRaw_eq source target parent b P exponent Q tau F child initial current
    _ _ members hne

theorem preparedOnlineReadWithWorkRaw_eq : @preparedOnlineReadWithWorkRaw = @preparedOnlineReadWithWork := by
  funext α source target M parent P F exponent H b hb hP tau eta kappa child initial table R hc hi t center integer
  unfold preparedOnlineReadWithWorkRaw preparedOnlineReadWithWork
  rw [preparedUnskippedReadWithWorkRaw_eq source target parent b P exponent hb hP tau (nat F)
    child initial R R hc hi center]
  simp only [Prod.map, id_eq, Option.isSome_map]

theorem preparedOnlineReadAllocationRaw_eq : @preparedOnlineReadAllocationRaw = @preparedOnlineReadAllocation := by
  funext α source target M parent P F exponent H b hb hP tau eta kappa child initial table R hc hi
    childAllocation initialAllocation tableAllocation t center integer
  unfold preparedOnlineReadAllocationRaw preparedOnlineReadAllocation
  rw [preparedUnskippedReadWithWorkRaw_eq source target parent b P exponent hb hP tau (nat F)
    child initial R R hc hi center]
  simp only [Prod.map, Option.isSome_map]

theorem preparedCellGroupReadWithWorkRaw_eq : @preparedCellGroupReadWithWorkRaw = @preparedCellGroupReadWithWork := by
  funext α source target M parent b P F exponent Q hb hP tau a parentInitial child initial current
    R C hr hi raw hraw draw cell
  have hreader := funext (preparedUnskippedReadWithWorkRaw_eq source target parent b P exponent hb hP tau (nat F)
    child initial R C hr hi)
  let centers := (cellCentersReadWithWork P F b a (inversePowerTwo exponent) parentInitial cell).1
  have hmembers : filterMapWithWork
      (preparedUnskippedReadWithWorkRaw parent b P exponent tau (nat F) child initial) centers =
      Prod.map (List.map UnskippedBand.raw) id (filterMapWithWork
        (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
          child initial R C hr hi) centers) := by
    rw [hreader]
    exact filterMapWithWork_map_raw _ _ _
  dsimp only [centers] at hmembers
  unfold preparedCellGroupReadWithWorkRaw preparedCellGroupReadWithWork
  simp only [hmembers]
  simp only [Prod.map, id_eq, List.map_eq_nil_iff]
  split_ifs with h
  · rfl
  · rw [dyadicSampledGroupActionReadWithWorkRaw_eq]

theorem preparedCellGroupSourceWithWorkRaw_eq : @preparedCellGroupSourceWithWorkRaw = @preparedCellGroupSourceWithWork := by
  funext α source target M parent b P F exponent Q hb hP tau a parentInitial child initial current
    R C hr hi raw hraw draw cell
  have hreader := funext (preparedUnskippedReadWithWorkRaw_eq source target parent b P exponent hb hP tau (nat F)
    child initial R C hr hi)
  let centers := (cellCentersReadWithWork P F b a (inversePowerTwo exponent) parentInitial cell).1
  have hmembers : filterMapWithWork
      (preparedUnskippedReadWithWorkRaw parent b P exponent tau (nat F) child initial) centers =
      Prod.map (List.map UnskippedBand.raw) id (filterMapWithWork
        (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
          child initial R C hr hi) centers) := by
    rw [hreader]
    exact filterMapWithWork_map_raw _ _ _
  dsimp only [centers] at hmembers
  unfold preparedCellGroupSourceWithWorkRaw preparedCellGroupSourceWithWork
  simp only [hmembers]
  simp only [Prod.map, id_eq, List.map_eq_nil_iff]
  split_ifs with h
  · rfl
  · rw [sampledGroupActionSourceWithWorkRaw_eq]

theorem preparedCellGroupSourceAllocationRaw_eq : @preparedCellGroupSourceAllocationRaw = @preparedCellGroupSourceAllocation := by
  funext α source target M parent b P F exponent Q hb hP tau a parentInitial child initial current
    R C hr hi raw hraw draw parentAllocation childAllocation initialAllocation currentAllocation drawAllocation cell
  have hreader := funext (preparedUnskippedReadWithWorkRaw_eq source target parent b P exponent hb hP tau (nat F)
    child initial R C hr hi)
  let centers := (cellCentersReadWithWork P F b a (inversePowerTwo exponent) parentInitial cell).1
  have hmembers : filterMapWithWork
      (preparedUnskippedReadWithWorkRaw parent b P exponent tau (nat F) child initial) centers =
      Prod.map (List.map UnskippedBand.raw) id (filterMapWithWork
        (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
          child initial R C hr hi) centers) := by
    rw [hreader]
    exact filterMapWithWork_map_raw _ _ _
  have hallocation : filterMapAllocation
      (preparedUnskippedReadWithWorkRaw parent b P exponent tau (nat F) child initial)
      (fun center => preparedUnskippedReadAllocation parent center b P exponent tau (nat F)
        child initial childAllocation initialAllocation) centers =
      filterMapAllocation
        (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
          child initial R C hr hi)
        (fun center => preparedUnskippedReadAllocation parent center b P exponent tau (nat F)
          child initial childAllocation initialAllocation) centers := by
    rw [hreader]
    exact filterMapAllocation_map_raw _ _ _ _
  dsimp only [centers] at hmembers hallocation
  unfold preparedCellGroupSourceAllocationRaw preparedCellGroupSourceAllocation
  simp only [hmembers, hallocation]
  simp only [Prod.map, id_eq, List.map_eq_nil_iff]
  split_ifs with h
  · rfl
  · rw [sampledGroupActionSourceAllocationRaw_eq]

end OAI.EditApproximation.BinaryFraction
