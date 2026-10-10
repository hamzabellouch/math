import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedOnline
import OAI.Combinatorics.EditApproximation.Binary.BinaryOnlineSetupWork
import OAI.Combinatorics.EditApproximation.Binary.BinarySampledOnlinePolynomial
import OAI.Combinatorics.EditApproximation.Geometry.PreparedBandPolynomial
import OAI.Combinatorics.EditApproximation.Geometry.LocalOnlineMassBound

namespace OAI

/-! The complete local online call: materialized endpoint grids, all band
guards, explicit index/range construction and the actual sampled optimizer. -/

namespace EditApproximation
namespace BinaryFraction

def preparedOnlineBitBudget (M P B S : ℕ) : ℕ :=
  2 * S ^ preparedBandBitDegree +
    onlineIndexBitBudget M ((40 * P + 2) ^ (2 * M)) B +
    reduceOnlineBitBudget B + S ^ sampledOnlineBitDegree + 3

theorem onlineIndexBitBudget_mono_vertices (M B vertices vertices' : ℕ)
    (hvertices : vertices ≤ vertices') :
    onlineIndexBitBudget M vertices B ≤ onlineIndexBitBudget M vertices' B := by
  unfold onlineIndexBitBudget bandCoordinatesBitBudget
  gcongr

theorem preparedOnlineWithWork_cost {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b B E S : ℕ)
    (hbpos : 0 < b) (hPpos : 0 < P) (hMpos : 0 < M)
    (tau eta kappa : BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction)
    (t : ℕ) (center : TargetInterval target.length) (integer : ℕ)
    (hB : 7 ≤ B) (hnx : Nat.size source.length + 2 ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hMb : Nat.size M ≤ B)
    (hb : Nat.size b + 2 ≤ B) (hP : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
    (he : exponent + 1 ≤ B) (hH : Nat.size H ≤ B)
    (hdBits : Nat.size (M * (40 * P + 2) ^ 2) ≤ B)
    (hKBits : Nat.size ((H + M * (40 * P + 2) ^ 2 + 2) ^ 80) ≤ B)
    (hInteger : Nat.size integer ≤ B)
    (htau : tau.width ≤ B) (heta : eta.width ≤ B) (hkappa : kappa.width ≤ B)
    (hchild : ∀ i q, (child i q).width ≤ B)
    (hinitial : ∀ i q, (initial i q).width ≤ B)
    (htable : ∀ s ≤ t + 1, ∀ i q, (table s (i, q)).width ≤ B)
    (hetaValue : |eta.value| ≤ E) (hkappaValue : 0 ≤ kappa.value ∧ kappa.value ≤ 1)
    (hvalues : ∀ s ≤ t + 1, ∀ i q, 0 ≤ (table s (i, q)).value ∧
      (table s (i, q)).value ≤ (initial i q).value)
    (hS : 2 ≤ S) (hMS : M ≤ S) (hPS : P ≤ S) (hES : E ≤ S) (htS : t ≤ S)
    (hBS : 3 * B + 4 ≤ S) (hvS : (40 * P + 2) ^ (2 * M) ≤ S)
    (hcartS : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ S)
    (hKS : (H + M * (40 * P + 2) ^ 2 + 2) ^ 80 ≤ S) :
    (preparedOnlineWithWork source target parent P F exponent H b hbpos hPpos tau eta kappa
      child initial table t center integer).2 ≤ preparedOnlineBitBudget M P B S := by
  let band := preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
    tau (inversePowerTwo exponent) child
  let setup := onlineIndexSetupWithWork H band.1
  let G := setup.1
  let accepted := reduceOnlineIntegerWithWork (G ^ 80) (by
    dsimp only [G, setup]
    rw [onlineIndexSetupWithWork_value]
    positivity) integer
  let V := (40 * P + 2) ^ (2 * M)
  let D := M * (40 * P + 2) ^ 2
  have hbandValue : band.1 = representativeBandActions source target parent center b P tau.value
      (inversePowerTwo exponent).value (fun i q => (child i q).value) :=
    preparedRepresentativeWithWork_value source target parent center b P hPpos tau (inversePowerTwo exponent) child
  have hbandLen : band.1.length ≤ V := by
    rw [hbandValue]
    exact (representativeBandActions_length_le source target parent center b P tau.value
      (inversePowerTwo exponent).value (fun i q => (child i q).value)).trans
      (wideActionList_length_le M parent center b P hPpos)
  have hd : (listedBandCoordinates band.1).length ≤ D := by
    rw [listedBandCoordinates_length, hbandValue]
    exact bandCoordinates_card_le parent center hPpos _
      (fun action ha => representativeBandActions_wide source target parent center b P tau.value
        (inversePowerTwo exponent).value (fun i q => (child i q).value) action ha)
  have hg : G ≤ H + D + 2 := by
    dsimp only [G, setup]
    rw [onlineIndexSetupWithWork_value]
    omega
  have hgp : 0 < G := by
    dsimp only [G, setup]
    rw [onlineIndexSetupWithWork_value]
    omega
  have hK : G ^ 80 ≤ (H + D + 2) ^ 80 := Nat.pow_le_pow_left hg 80
  have hGtotal : H + D + 2 ≤ S :=
    (Nat.le_pow (by omega : 0 < 80)).trans hKS
  have hdimS : (listedBandCoordinates band.1).length ≤ S := hd.trans (by omega)
  have hbS : B ≤ S := by omega
  have hguard := (preparedUnskippedCandidateWithWork_uniform_cost source target parent b P exponent B
    hbpos hPpos tau (nat F) child initial center hnx hny hMb hb hP he htau
    ((nat_width_le F).trans hF) hchild hinitial).trans
    (preparedUnskippedBitBudget_fixedPower exponent b M P V V B S hS (by omega) (by omega)
      hMS hPS hvS hvS hbS hcartS)
  have hwide : (wideActionGridWithWork M parent center b P).1.length ≤ V := by
    have hh := congrArg List.length (wideActionGridWithWork_value M parent center b P hPpos)
    simp only [List.length_map] at hh
    rw [hh]
    exact wideActionList_length_le M parent center b P hPpos
  have hbandCost := preparedRepresentativeWithWork_complete_cost parent center b P B hPpos tau
    (inversePowerTwo exponent) child (by omega) (by omega) hMb (by omega) hP htau
    (by rw [inversePowerTwo_width]; exact he) hchild
  have hrepMono := representativeCompleteBitBudget_mono_vertices M _ V (4 * B + 20) hwide
  have hbandPower : band.2 ≤ S ^ preparedBandBitDegree := by
    have hcap := preparedUnskippedBitBudget_fixedPower exponent b M P V V B S hS (by omega)
      (by omega) hMS hPS hvS hvS hbS hcartS
    apply le_trans _ hcap
    unfold preparedUnskippedBitBudget
    change band.2 ≤ _ at hbandCost
    omega
  have hsetup := onlineIndexSetupWithWork_bounds H B band.1 (by omega) hH hMb (by omega)
    ((Nat.size_le_size hd).trans hdBits)
  have hsetupCost : setup.2 ≤ onlineIndexBitBudget M V B :=
    hsetup.2.trans (onlineIndexBitBudget_mono_vertices M B _ _ hbandLen)
  have hKsize : Nat.size (G ^ 80) ≤ B := (Nat.size_le_size hK).trans hKBits
  have haccepted := reduceOnlineIntegerWithWork_bounds (G ^ 80) integer B (pow_pos hgp _) hKsize hInteger
  have hsample (hne : band.1 ≠ []) :
      (countedSampledOnlineWithWork center b initial table eta kappa band.1 hne G (G ^ 80) t accepted.1).2 ≤
        S ^ sampledOnlineBitDegree := by
    apply countedSampledOnlineWithWork_fixedPower center b initial table eta kappa band.1 hne
      G (G ^ 80) t (3 * B + 4) E S accepted.1 hS hMpos hbpos hMS
      (hbandLen.trans hvS) hdimS (hg.trans hGtotal) (hK.trans hKS) htS hBS hES (by omega)
      (by omega) (by omega) (by omega) haccepted.1
      (heta.trans (by omega)) (hkappa.trans (by omega))
      (fun i q => (hinitial i q).trans (by omega))
      (fun s hs i q => (htable s hs i q).trans (by omega)) hetaValue hkappaValue hvalues
  dsimp only [V] at hsetupCost
  unfold preparedOnlineWithWork
  dsimp only
  split_ifs with hempty hactive
  · change band.2 + setup.2 + accepted.2 + 1 ≤ _
    have hc : accepted.2 ≤ reduceOnlineBitBudget B := haccepted.2
    unfold preparedOnlineBitBudget
    omega
  · have hs := hsample hempty
    have hc : accepted.2 ≤ reduceOnlineBitBudget B := haccepted.2
    change band.2 + setup.2 + accepted.2 +
      (preparedUnskippedCandidateWithWork source target parent b P exponent hbpos hPpos tau (nat F)
        child initial center).2 +
      (countedSampledOnlineWithWork center b initial table eta kappa band.1 hempty
        G (G ^ 80) t accepted.1).2 + 2 ≤ _
    unfold preparedOnlineBitBudget
    omega
  · have hc : accepted.2 ≤ reduceOnlineBitBudget B := haccepted.2
    change band.2 + setup.2 + accepted.2 + _ + 1 ≤ _
    unfold preparedOnlineBitBudget
    omega

end BinaryFraction
end EditApproximation

end OAI
