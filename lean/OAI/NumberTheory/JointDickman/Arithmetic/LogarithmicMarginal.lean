import OAI.NumberTheory.JointDickman.Probability.ResidueAverageMass
import OAI.NumberTheory.JointDickman.Amplification.CoarseCompactness

namespace OAI

/-! # The logarithmic marginal is the channel used by coarse compactness -/

namespace JointDickman
open Finset Filter

open Classical in
theorem logarithmicCell_eq_some {D : Type*} [DecidableEq D]
    (B : ℕ) (lower upper : D → ℝ)
    (hdisjoint : ∀ d e s, s ∈ Set.Ioc (lower d) (upper d) →
      s ∈ Set.Ioc (lower e) (upper e) → d = e)
    (n : ℕ) (i : D) :
    logarithmicCell B lower upper n = some i ↔
      Real.log n/B ∈ Set.Ioc (lower i) (upper i) := by
  unfold logarithmicCell
  constructor
  · intro he
    obtain ⟨⟨d,r⟩,hc,hi⟩ := Option.map_eq_some_iff.mp he
    change d = i at hi
    subst d
    exact ((logResidueCell_eq_some B 1 lower upper hdisjoint n i r).mp hc).1
  · intro hi
    have hc : logResidueCell B 1 lower upper n = some (i,1) :=
      (logResidueCell_eq_some B 1 lower upper hdisjoint n i 1).mpr
        ⟨hi,Subsingleton.elim _ _⟩
    simp [hc,trivialResidueEquiv]

theorem groupedManuscriptChannel_log_mass {m B : ℕ}
    (hm : 0 < m) (hB : 0 < B) (g : (auxiliaryPrimes B → Bool) → ℝ)
    (a : Fin m × Fin (channelBlockCount m B)) :
    channelMesh (channelFineCount m B)*groupedManuscriptChannel m B g a =
      logCellSignedMass m B g (finProdFinEquiv a) := by
  classical
  have hk : 0 < channelBlockCount m B := by
    have hh := channelFineCount_pos hm hB
    change 0 < m*channelBlockCount m B at hh
    exact Nat.pos_of_ne_zero (by intro he; simp [he] at hh)
  have he := signedSplitProductMass_channel (auxiliaryPrimes B) g
    (logarithmicCell B (groupedLower m (channelBlockCount m B))
      (groupedUpper m (channelBlockCount m B)))
    (fun _ => channelMesh (channelFineCount m B)) a
    (channelMesh_pos (channelFineCount_pos hm hB)).ne'
  change _ = channelMesh (channelFineCount m B)*groupedManuscriptChannel m B g a at he
  rw [← he]
  unfold logCellSignedMass
  apply sum_congr rfl
  intro n _
  simp only [logarithmicCell_eq_some B _ _ (groupedCells_disjoint hm hk)]
  rfl

theorem groupedManuscriptChannel_eq_modulus_one {m B : ℕ}
    (hm : 0 < m) (hB : 0 < B) (g : (auxiliaryPrimes B → Bool) → ℝ)
    (a : Fin m × Fin (channelBlockCount m B)) :
    groupedManuscriptChannel m B g a =
      manuscriptChannel m B 1 g (finProdFinEquiv a,1) := by
  apply mul_left_cancel₀ (channelMesh_pos (channelFineCount_pos hm hB)).ne'
  rw [groupedManuscriptChannel_log_mass hm hB]
  have hcut : 1 ≤ auxiliaryCutoff B := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hB.ne')
  have ht := manuscript_residue_average_mass (q := 1) hm hB hcut g
    (finProdFinEquiv a : Fin (channelFineCount m B))
  simpa only [finiteResidueAverage,Fintype.sum_unique,Fintype.card_unique,Nat.cast_one,
    div_one,show (default : (ZMod 1)ˣ) = 1 from Subsingleton.elim _ _] using ht.symm

theorem groupedManuscriptChannel_square_bound
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in Filter.atTop,
      ∀ g : (auxiliaryPrimes B → Bool) → ℝ,
      (∑ a : Fin m × Fin (channelBlockCount m B), channelMesh (channelFineCount m B)*
        groupedManuscriptChannel m B g a^2) ≤
        C*∑ x, fullPrimeMass (auxiliaryPrimes B) x*g x^2 := by
  obtain ⟨C,hC,hbound⟩ := manuscriptChannel_square_bound hSD hSW hM hMP
  refine ⟨C,hC,?_⟩
  intro m hm
  filter_upwards [hbound m hm, Filter.eventually_gt_atTop 0] with B hb hB
  intro g
  have hh := hb 1 (by omega) g
  simp only [Fintype.sum_prod_type,Fintype.sum_unique,Nat.totient_one,Nat.cast_one,div_one] at hh
  let e : Fin m × Fin (channelBlockCount m B) ≃ Fin (channelFineCount m B) := finProdFinEquiv
  rw [← e.sum_comp] at hh
  simp only [show (default : (ZMod 1)ˣ) = 1 from Subsingleton.elim _ _] at hh
  convert hh using 1
  apply sum_congr rfl
  intro a _
  change channelMesh (channelFineCount m B)*groupedManuscriptChannel m B g a^2 =
    channelMesh (channelFineCount m B)*manuscriptChannel m B 1 g (finProdFinEquiv a,1)^2
  rw [groupedManuscriptChannel_eq_modulus_one hm hB g a]

end JointDickman

end OAI
