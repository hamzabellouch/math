import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ResidualRankPrivateFamily
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Witness

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.SourceCylinder OrdinaryCorrelations.FiniteIntegration
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L ℓ t : ℕ}

namespace PrivateFamily
variable {w : ClosedLine h ℓ}

lemma data_injective : Function.Injective
    (fun F : PrivateFamily w D L t => (F.witness,F.key)) := by
  intro F G he
  cases F
  cases G
  cases he
  rfl

instance : Finite (PrivateFamily w D L t) :=
  Finite.of_injective _ data_injective

noncomputable instance : Fintype (PrivateFamily w D L t) := Fintype.ofFinite _

end PrivateFamily

lemma listIndicator_nonneg (w : ClosedLine h ℓ) (l : List (AttachedSpec w D L)) (r : S.Residues) :
    0 ≤ listIndicator w l r := by unfold listIndicator; split_ifs <;> norm_num

lemma listIndicator_append_length (w : ClosedLine h ℓ) (l : List (AttachedSpec w D L))
    (F : PrivateFamily w D L t) (hl : l.length ≤ t) :
    (l++List.ofFn F.witness).length ≤ 2*t := by simp only [List.length_append,List.length_ofFn]; omega

theorem witnessCount_le_joint_lists (w : ClosedLine h ℓ) (a : S.FixedResidues w)
    (z : S.FreeResidues w) (ht : 0 < t) :
    (witnessCount (residualEvents w D L a) t z : ℝ) ≤
      ∑ l ∈ boundedLists (AttachedSpec w D L) t,
        ∑ F : PrivateFamily w D L t,
          listIndicator w (l++List.ofFn F.witness) (mergeResidues w a z) := by
  let V := univ.filter (fun s : AttachedSpec w D L => s.Compatible a)
  let f : AttachedSpec w D L → Cylinder (fun p : S.FreeIndex w => ZMod (p.val:ℕ)) :=
    AttachedSpec.residualCylinder
  change (witnessCount (V.image f) t z : ℝ) ≤ _
  apply witnessCount_le_list_sum V f t z
    (fun l => ∑ F : PrivateFamily w D L t,
      listIndicator w (l++List.ofFn F.witness) (mergeResidues w a z))
  · intro l
    exact sum_nonneg (fun F _ => listIndicator_nonneg _ _ _)
  · intro I hz
    obtain ⟨F,hF⟩ := residual_rank_private_family w a I.val.val ht
      (mem_filter.mp I.property).2.1 z hz
    have hg := witnessGenerator_holds V f t I z hz
    have ho : listIndicator w (witnessGenerator V f t I++List.ofFn F.witness)
        (mergeResidues w a z) = 1 := by
      apply ite_eq_left
      intro s hs p
      rcases List.mem_append.mp hs with hs|hs
      · have hh := hg s hs
        apply (s.fullCylinder_holds _).mp ((s.fullCylinder_merge a z).mpr
          ⟨(mem_filter.mp hh.1).2,hh.2⟩) p
      · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hs
        exact hF j p
    rw [←ho]
    exact single_le_sum (f:=fun F' : PrivateFamily w D L t =>
      listIndicator w (witnessGenerator V f t I++List.ofFn F'.witness) (mergeResidues w a z))
      (fun F' hF' => listIndicator_nonneg w _ _) (mem_univ F)

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
